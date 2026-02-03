#!/usr/bin/env python3
# -*- coding: utf-8 -*-

"""
zepp_localizer.py — local web UI for translating Zepp OS packages (.zpk/.zip/.zab)

Features:
- Upload .zpk/.zip/.zab
- Finds device.zip (at root or inside .zab -> .zpk)
- Reads assets/raw/locale/TID.btxt and chosen locale *.btxt
- Shows a table: key/index, original, translation
- Builds a new <target_locale>.btxt and repacks the package
- Experimental scan of page/pages *.bin for potential UI strings

Dependencies: flask (pip install flask)
"""

import io
import os
import re
import json
import time
import shutil
import struct
import zipfile
import tempfile
import zlib
from dataclasses import dataclass
from typing import Dict, List, Optional, Tuple, Any

from flask import Flask, request, redirect, url_for, send_file, render_template_string, abort

# -----------------------------
# Config
# -----------------------------
APP_NAME = "Zepp OS Localizer (BTXT ⇄ UI)"
MAX_UPLOAD_BYTES = 50_000_000
JOB_ROOT = os.path.join(tempfile.gettempdir(), "zepp_localizer_jobs")

os.makedirs(JOB_ROOT, exist_ok=True)

app = Flask(__name__)
app.secret_key = os.urandom(24)

# -----------------------------
# BTXT (BE u32 count + BE u32 offsets + UTF-8 pool)
# -----------------------------
class ZeppBtxt:
    @staticmethod
    def parse_be_offsets(b: bytes) -> List[str]:
        if len(b) < 4:
            raise ValueError("BTXT too small")
        n = struct.unpack_from(">I", b, 0)[0]
        if not (1 <= n <= 200000):
            raise ValueError(f"Suspicious BTXT count: {n}")
        table_end = 4 + n * 4
        if table_end > len(b):
            raise ValueError("Offsets table out of file bounds")
        offsets = [struct.unpack_from(">I", b, 4 + i * 4)[0] for i in range(n)]
        if offsets[0] != table_end:
            raise ValueError(f"BTXT layout mismatch: offsets[0]={offsets[0]} expected {table_end}")
        last = -1
        for off in offsets:
            if off < 0 or off > len(b):
                raise ValueError(f"Offset out of file: {off}")
            if off < last:
                raise ValueError("Offsets not sorted")
            last = off
        out = []
        for i in range(n):
            start = offsets[i]
            end = offsets[i+1] if i+1 < n else len(b)
            out.append(b[start:end].decode("utf-8", errors="replace"))
        return out

    @staticmethod
    def build_be_offsets(strings: List[str]) -> bytes:
        if not strings:
            raise ValueError("Empty strings list")
        n = len(strings)
        if n > 200000:
            raise ValueError("Too many strings")
        encoded = [s.encode("utf-8") for s in strings]
        pool_start = 4 + n * 4
        offsets = []
        cur = pool_start
        for bb in encoded:
            offsets.append(cur)
            cur += len(bb)
        out = bytearray()
        out += struct.pack(">I", n)
        for off in offsets:
            out += struct.pack(">I", off)
        for bb in encoded:
            out += bb
        return bytes(out)

    @staticmethod
    def placeholders_compatible(orig: str, tr: str) -> bool:
        def extract(s: str) -> List[str]:
            out = []
            out += re.findall(r"%(?:\d+\$)?[dsf]", s)
            out += re.findall(r"\{\d+\}", s)
            return sorted(out)
        return extract(orig) == extract(tr)


# -----------------------------
# Package handling
# -----------------------------
@dataclass
class PackageAnalysis:
    ok: bool
    mode: str  # 'root' or 'zab'
    inner_zpk_name: Optional[str]
    locales: List[str]
    has_locale: bool

def _safe_name(s: str) -> str:
    return re.sub(r"[^A-Za-z0-9._-]+", "_", s)

def analyze_package(path: str) -> PackageAnalysis:
    with zipfile.ZipFile(path, "r") as outer:
        names = outer.namelist()

        if "device.zip" in names:
            mode = "root"
            inner = None
            device_bytes = outer.read("device.zip")
        else:
            # maybe zab contains zpk
            zpk = None
            for n in names:
                if n.lower().endswith(".zpk"):
                    zpk = n
                    break
            if not zpk:
                return PackageAnalysis(False, "", None, [], False)
            mode = "zab"
            inner = zpk
            zpk_bytes = outer.read(zpk)
            with zipfile.ZipFile(io.BytesIO(zpk_bytes), "r") as z:
                if "device.zip" not in z.namelist():
                    return PackageAnalysis(False, "", None, [], False)
                device_bytes = z.read("device.zip")

    with zipfile.ZipFile(io.BytesIO(device_bytes), "r") as dev:
        locales = []
        for n in dev.namelist():
            nn = n.replace("\\", "/")
            if nn.startswith("assets/raw/locale/") and nn.lower().endswith(".btxt"):
                locales.append(os.path.basename(nn))
        locales.sort()
        has_locale = any(l.lower() != "tid.btxt" for l in locales)
        return PackageAnalysis(True, mode, inner, locales, has_locale)

def extract_device_zip(path: str, analysis: PackageAnalysis, out_path: str) -> None:
    with zipfile.ZipFile(path, "r") as outer:
        if analysis.mode == "root":
            device_bytes = outer.read("device.zip")
        else:
            assert analysis.inner_zpk_name
            zpk_bytes = outer.read(analysis.inner_zpk_name)
            with zipfile.ZipFile(io.BytesIO(zpk_bytes), "r") as z:
                device_bytes = z.read("device.zip")
    with open(out_path, "wb") as f:
        f.write(device_bytes)

def repack_package_with_device(original_pkg: str, analysis: PackageAnalysis, new_device_zip_path: str, out_pkg: str) -> None:
    new_device_bytes = open(new_device_zip_path, "rb").read()

    if analysis.mode == "root":
        with zipfile.ZipFile(original_pkg, "r") as zin, zipfile.ZipFile(out_pkg, "w", compression=zipfile.ZIP_DEFLATED) as zout:
            for item in zin.infolist():
                if item.filename == "device.zip":
                    continue
                zout.writestr(item, zin.read(item.filename))
            zout.writestr("device.zip", new_device_bytes)
        return

    # zab: replace inner zpk; inside zpk replace device.zip
    assert analysis.inner_zpk_name
    with zipfile.ZipFile(original_pkg, "r") as outer:
        zpk_bytes = outer.read(analysis.inner_zpk_name)

    # rebuild zpk
    zpk_out_bytes = io.BytesIO()
    with zipfile.ZipFile(io.BytesIO(zpk_bytes), "r") as zin, zipfile.ZipFile(zpk_out_bytes, "w", compression=zipfile.ZIP_DEFLATED) as zout:
        for item in zin.infolist():
            if item.filename == "device.zip":
                continue
            zout.writestr(item, zin.read(item.filename))
        zout.writestr("device.zip", new_device_bytes)

    # rebuild outer zab
    with zipfile.ZipFile(original_pkg, "r") as zin, zipfile.ZipFile(out_pkg, "w", compression=zipfile.ZIP_DEFLATED) as zout:
        for item in zin.infolist():
            if item.filename == analysis.inner_zpk_name:
                continue
            zout.writestr(item, zin.read(item.filename))
        zout.writestr(analysis.inner_zpk_name, zpk_out_bytes.getvalue())

def read_locale_pairs(device_zip_path: str, lang_file: str) -> Tuple[List[str], List[str], List[Dict[str, str]]]:
    with zipfile.ZipFile(device_zip_path, "r") as dev:
        lang_path = f"assets/raw/locale/{lang_file}"
        values_bytes = dev.read(lang_path)
        values = ZeppBtxt.parse_be_offsets(values_bytes)

        keys = []
        pairs = []
        try:
            tid_bytes = dev.read("assets/raw/locale/TID.btxt")
            keys = ZeppBtxt.parse_be_offsets(tid_bytes)
            if len(keys) != len(values):
                keys = []
        except KeyError:
            keys = []

        for i, v in enumerate(values):
            k = keys[i] if keys else str(i)
            pairs.append({"k": k, "v": v})
        return keys, values, pairs

def write_locale_file(device_zip_path: str, file_name: str, content: bytes) -> None:
    # rewrite by recreating zip (zipfile can't truly delete+replace easily without copy)
    tmp_out = device_zip_path + ".tmp"
    with zipfile.ZipFile(device_zip_path, "r") as zin, zipfile.ZipFile(tmp_out, "w", compression=zipfile.ZIP_DEFLATED) as zout:
        target = f"assets/raw/locale/{file_name}"
        for item in zin.infolist():
            if item.filename == target:
                continue
            zout.writestr(item, zin.read(item.filename))
        zout.writestr(target, content)
    os.replace(tmp_out, device_zip_path)

# -----------------------------
# BIN scanning (improved heuristics)
# -----------------------------
def _is_likely_ui_text(s: str) -> bool:
    t = s.strip()
    if len(t) < 2 or len(t) > 160:
        return False
    if re.match(r"^(page/|assets/|app/|data/|https?://)", t, re.I):
        return False
    if re.search(r"\.(png|jpe?g|gif|svg|webp|mp3|wav|js|bin|json|zip)\b", t, re.I):
        return False
    # filter noisy internal identifiers
    if re.search(r"__\$\$|DeviceRuntime|beforePageCreate|afterPageCreate|Mini Program Error|/var/folders/", t):
        return False
    # too many weird chars
    if re.search(r"[\x00-\x08\x0B\x0C\x0E-\x1F]", t):
        return False
    # mostly identifier-like?
    if re.fullmatch(r"[A-Za-z0-9_.$/@-]{2,}", t) and not re.search(r"\s", t):
        return False
    # obvious gibberish (hex/base64/uuid-like)
    if re.fullmatch(r"[A-Fa-f0-9]{12,}", t):
        return False
    if re.fullmatch(r"0x[0-9A-Fa-f]{6,}", t):
        return False
    if re.fullmatch(r"[A-Za-z0-9+/=]{16,}", t):
        return False
    if re.fullmatch(r"[0-9a-f]{8}-[0-9a-f]{4}-[0-9a-f]{4}-[0-9a-f]{4}-[0-9a-f]{12}", t, re.I):
        return False
    if len(set(t)) <= 3 and len(t) >= 8:
        return False
    if "/" in t and " " not in t and len(t) > 12:
        return False
    if re.search(r"[{}\[\]<>]{2,}", t):
        return False
    if re.search(r"[=;]{2,}", t):
        return False
    if re.search(r"(?:\bfunction\b|\breturn\b|\bvar\b|\bconst\b|\blet\b|=>|\bnew\s)", t):
        return False
    if re.search(r"\b[A-Za-z_][A-Za-z0-9_]*\s*\(", t):
        return False
    if re.search(r"\b[A-Za-z_][A-Za-z0-9_]*::[A-Za-z_]", t):
        return False
    if "." in t and " " not in t:
        return False
    if " " not in t and re.search(r"[a-z][A-Z]", t) and len(t) > 16:
        return False
    if " " not in t and re.search(r"[A-Za-z]\d{2,}[A-Za-z]", t):
        return False
    tl = t.lower()
    if re.search(r"\bhm\s*ui\b", tl) or "hmui" in tl:
        return False
    if " " not in t and re.fullmatch(r"[A-Za-z_][A-Za-z0-9_]*", t):
        return False

    letters = sum(ch.isalpha() for ch in t)
    digits = sum(ch.isdigit() for ch in t)
    spaces = sum(ch.isspace() for ch in t)
    alnum = letters + digits
    if alnum == 0:
        return False
    if len(t) >= 8 and (alnum / len(t)) < 0.3 and spaces == 0:
        return False
    if spaces == 0 and letters < 2 and digits >= 6:
        return False
    words = t.split()
    if len(words) == 1:
        if words[0].lower() in {
            "radius","padding","margin","opacity","alpha","scale","width","height","pos","posx","posy",
            "x","y","color","bg","fg","image","icon","font","size"
        }:
            return False
    if 2 <= len(words) <= 5:
        w0 = words[0].lower()
        if w0 in {"get","set","init","update","create","render","build","calc","load","save","open","close","draw",
                  "bind","unbind","request","fetch","sync","async"}:
            if any(w[:1].isupper() for w in words[1:]) or any(w.lower() in {"info","data","device","config","option","options","property","properties","state","context"} for w in words[1:]):
                return False
    if 2 <= len(words) <= 4:
        if words[0].lower() in {"get","set","init","update","create","render","build","calc","load","save","open","close","draw",
                                "bind","unbind","request","fetch","sync","async","register","unregister","emit","dispatch","handle"}:
            return False
    return True

def clean_and_split_text(s: str) -> List[str]:
    t = s.strip()
    if not t:
        return []
    # drop long camelCase chains without spaces (code-ish)
    if " " not in t and re.search(r"[a-z][A-Z]", t) and len(t) > 18:
        return []
    # separate extension from following letters/digits (png6Note -> png | 6Note)
    t = re.sub(r"(\.(?:png|jpe?g|gif|svg|webp|mp3|wav|json|js|bin|zip))(?=[A-Za-z0-9])", r"\1 | ", t, flags=re.I)
    # remove obvious file paths/extensions
    t = re.sub(r"\b[\w./-]+\.(png|jpe?g|gif|svg|webp|mp3|wav|json|js|bin|zip)\b", " | ", t, flags=re.I)
    # drop short snake_case tokens (pos_x, pos_y) that are usually layout identifiers
    t = re.sub(r"\b[a-zA-Z]{1,12}_[a-zA-Z0-9]{1,12}\b", " | ", t)
    # add spaces to camelCase and digit-letter boundaries
    t = re.sub(r"(?<=[a-z])(?=[A-Z])", " ", t)
    t = re.sub(r"(?<=[A-Za-z])(?=\d)", " ", t)
    t = re.sub(r"(?<=\d)(?=[A-Za-z])", " ", t)
    # normalize separators
    t = re.sub(r"[|;]+", " | ", t)
    t = re.sub(r"[&]+", " | ", t)
    t = re.sub(r"[\r\n\t]+", " | ", t)
    t = re.sub(r"[\x00-\x1f]", " ", t)
    t = re.sub(r"[{}\[\]<>$*()]+", " | ", t)
    t = re.sub(r"[_]+", " ", t)
    t = re.sub(r"\s+", " ", t).strip()

    parts = []
    for p in re.split(r"\s*\|\s*", t):
        p = p.strip(" -–—:.,")
        p = re.sub(r"^\d+\s*", "", p)
        if not p:
            continue
        parts.append(p)
    return parts

def harvest_utf8_strings(b: bytes, min_len: int = 3) -> List[str]:
    s = b.decode("utf-8", errors="ignore")
    out = []
    cur = []
    for ch in s:
        o = ord(ch)
        if ch in "\r\n\t":
            if len(cur) >= min_len:
                out.append("".join(cur).strip())
            cur = []
            continue
        if o >= 0x20:
            cur.append(ch)
        else:
            if len(cur) >= min_len:
                out.append("".join(cur).strip())
            cur = []
    if len(cur) >= min_len:
        out.append("".join(cur).strip())
    # dedup keep order
    seen = set()
    uniq = []
    for x in out:
        if not x or x in seen:
            continue
        seen.add(x)
        uniq.append(x)
    return uniq

def try_extract_zlib_json(b: bytes) -> List[str]:
    """
    Tries to find zlib streams at any offset (0x78 0x9C / 0x78 0xDA / 0x78 0x01),
    decompress, parse JSON, and collect text/label/title fields.
    """
    texts = []
    candidates = []
    for i in range(len(b) - 2):
        if b[i] == 0x78 and b[i+1] in (0x01, 0x9C, 0xDA):
            candidates.append(i)
    for off in candidates[:200]:  # cap
        try:
            dec = zlib.decompress(b[off:])
        except Exception:
            continue
        dec = dec.strip()
        if not dec:
            continue
        if not (dec.startswith(b"{") or dec.startswith(b"[") or b'"text"' in dec or b'"label"' in dec):
            continue
        try:
            j = json.loads(dec.decode("utf-8", errors="ignore"))
        except Exception:
            continue

        def walk(node: Any):
            if isinstance(node, dict):
                for k, v in node.items():
                    if isinstance(k, str) and k.lower() in ("text", "label", "title"):
                        if isinstance(v, str):
                            texts.append(v)
                    walk(v)
            elif isinstance(node, list):
                for it in node:
                    walk(it)

        walk(j)
    # dedup
    seen = set()
    uniq = []
    for t in texts:
        t = t.strip()
        if not t or t in seen:
            continue
        seen.add(t)
        uniq.append(t)
    return uniq

def try_parse_btxt_like(b: bytes) -> Optional[List[str]]:
    """
    Some bins contain BTXT-like string tables. Try a few layouts quickly.
    """
    # BE u32 count at start
    if len(b) >= 8:
        for endian in (">", "<"):
            n = struct.unpack_from(endian + "I", b, 0)[0]
            if 1 <= n <= 50000:
                table_end = 4 + 4 * n
                if table_end <= len(b):
                    offsets = [struct.unpack_from(endian + "I", b, 4 + i*4)[0] for i in range(n)]
                    if offsets and offsets[0] == table_end and all(offsets[i] <= offsets[i+1] for i in range(len(offsets)-1)) and offsets[-1] <= len(b):
                        out = []
                        for i in range(n):
                            s = b[offsets[i]:(offsets[i+1] if i+1<n else len(b))].decode("utf-8", "ignore").strip()
                            if s:
                                out.append(s)
                        return out if out else None
    return None

def scan_bins_for_text(device_zip_path: str) -> List[Dict[str, str]]:
    out = []
    with zipfile.ZipFile(device_zip_path, "r") as dev:
        for name in dev.namelist():
            nn = name.replace("\\", "/")
            if not nn.lower().endswith(".bin"):
                continue
            if not (nn.startswith("page/") or nn.startswith("pages/") or "/page/" in nn or "/pages/" in nn):
                continue
            b = dev.read(name)

            # 1) btxt-like tables
            bt = try_parse_btxt_like(b)
            if bt:
                for s in bt:
                    for c in clean_and_split_text(s):
                        if _is_likely_ui_text(c):
                            out.append({"file": nn, "method": "btxt-like", "text": c})

            # 2) zlib+json at any offset
            zj = try_extract_zlib_json(b)
            for s in zj:
                for c in clean_and_split_text(s):
                    if _is_likely_ui_text(c):
                        out.append({"file": nn, "method": "zlib+json", "text": c})

            # 3) raw utf8 harvest
            for s in harvest_utf8_strings(b, 4):
                for c in clean_and_split_text(s):
                    if _is_likely_ui_text(c):
                        out.append({"file": nn, "method": "utf8-scan", "text": c})

    # dedup
    seen = set()
    uniq = []
    for r in out:
        k = r["file"] + "|" + r["text"]
        if k in seen:
            continue
        seen.add(k)
        uniq.append(r)
    return uniq


def _patch_bin_bytes(b: bytes, replacements: List[Tuple[str, str]]) -> Tuple[bytes, Dict[str, int]]:
    """
    Best-effort in-place replacement:
    - Replace if translation byte length == original byte length
    - If translation is shorter, allow only when the original is null-terminated (next byte == 0x00),
      then pad the remainder with 0x00
    - Longer translations are skipped
    """
    if not replacements:
        return b, {"replaced": 0, "skipped": 0, "not_found": 0}
    buf = bytearray(b)
    replaced = 0
    skipped = 0
    not_found = 0
    for orig, tr in replacements:
        if not orig or not tr or orig == tr:
            continue
        orig_b = orig.encode("utf-8")
        tr_b = tr.encode("utf-8")
        if not orig_b:
            continue
        start = 0
        found_any = False
        while True:
            idx = buf.find(orig_b, start)
            if idx == -1:
                break
            found_any = True
            if len(tr_b) == len(orig_b):
                buf[idx:idx + len(orig_b)] = tr_b
                replaced += 1
            elif len(tr_b) < len(orig_b):
                end_idx = idx + len(orig_b)
                next_b = buf[end_idx] if end_idx < len(buf) else 0
                if next_b == 0:
                    buf[idx:idx + len(tr_b)] = tr_b
                    pad_len = len(orig_b) - len(tr_b)
                    if pad_len:
                        buf[idx + len(tr_b): idx + len(orig_b)] = b"\x00" * pad_len
                    replaced += 1
                else:
                    skipped += 1
            else:
                skipped += 1
            start = idx + len(orig_b)
        if not found_any:
            not_found += 1
    return bytes(buf), {"replaced": replaced, "skipped": skipped, "not_found": not_found}


def apply_bin_translations(device_zip_path: str, rows: List[Dict[str, str]]) -> Dict[str, int]:
    """
    Apply saved BIN translations into device.zip (best-effort, in-place).
    """
    by_file: Dict[str, List[Tuple[str, str]]] = {}
    for r in rows:
        file = (r.get("file") or "").replace("\\", "/")
        text = r.get("text") or ""
        tr = r.get("translation") or ""
        if not file or not text or not tr:
            continue
        by_file.setdefault(file, []).append((text, tr))
    if not by_file:
        return {"files": 0, "replaced": 0, "skipped": 0, "not_found": 0}

    tmp_out = device_zip_path + ".bintmp"
    stats = {"files": 0, "replaced": 0, "skipped": 0, "not_found": 0}
    with zipfile.ZipFile(device_zip_path, "r") as zin, zipfile.ZipFile(tmp_out, "w", compression=zipfile.ZIP_DEFLATED) as zout:
        for item in zin.infolist():
            data = zin.read(item.filename)
            nn = item.filename.replace("\\", "/")
            if nn in by_file:
                new_data, s = _patch_bin_bytes(data, by_file[nn])
                if new_data != data:
                    stats["files"] += 1
                stats["replaced"] += s["replaced"]
                stats["skipped"] += s["skipped"]
                stats["not_found"] += s["not_found"]
                data = new_data
            zout.writestr(item, data)
    os.replace(tmp_out, device_zip_path)
    return stats


# -----------------------------
# HTML templates (inline)
# -----------------------------
STYLE = """
<style>
@import url('https://fonts.googleapis.com/css2?family=Fraunces:opsz,wght@9..144,600;9..144,800&family=Space+Grotesk:wght@400;500;600;700&family=JetBrains+Mono:wght@400;600&display=swap');

:root{
  --bg:#f6f0e6;
  --paper:#fffaf2;
  --card:#ffffff;
  --ink:#1a1b1e;
  --muted:#5c6675;
  --line:#e6ddcf;
  --accent:#ff6a00;
  --accent-2:#1e9a68;
  --accent-3:#0ea5e9;
  --ok:#1e9a68;
  --warn:#e08b2d;
  --err:#d64545;
  --radius:18px;
  --shadow:0 18px 50px rgba(23,26,32,.12);
  --shadow-soft:0 6px 24px rgba(23,26,32,.08);
  --display:"Fraunces","Iowan Old Style","Times New Roman",serif;
  --sans:"Space Grotesk","IBM Plex Sans","Work Sans","Segoe UI",sans-serif;
  --mono:"JetBrains Mono",ui-monospace,Menlo,Consolas,"Liberation Mono",monospace;
}
*{box-sizing:border-box}
body{
  margin:0;
  font-family:var(--sans);
  color:var(--ink);
  background:var(--bg);
  min-height:100vh;
}
body::before{
  content:"";
  position:fixed;
  inset:0;
  background:
    radial-gradient(900px 600px at 12% -10%, rgba(255,106,0,.12), transparent 60%),
    radial-gradient(700px 500px at 95% 0%, rgba(14,165,233,.10), transparent 60%),
    linear-gradient(180deg, rgba(255,255,255,.45), rgba(255,255,255,0));
  z-index:-2;
  pointer-events:none;
}
.bg{
  position:fixed;
  inset:0;
  z-index:-1;
  overflow:hidden;
  pointer-events:none;
}
.blob{
  position:absolute;
  border-radius:999px;
  filter: blur(1px);
  opacity:.65;
  mix-blend-mode:multiply;
  animation: float 16s ease-in-out infinite;
}
.blob.b1{
  width:520px;height:520px;
  background:radial-gradient(circle at 30% 30%, rgba(255,106,0,.35), rgba(255,106,0,0) 65%);
  top:-140px;left:-120px;
}
.blob.b2{
  width:480px;height:480px;
  background:radial-gradient(circle at 40% 40%, rgba(30,154,104,.28), rgba(30,154,104,0) 68%);
  bottom:-180px;right:-140px;
  animation-delay:-3s;
}
.blob.b3{
  width:360px;height:360px;
  background:radial-gradient(circle at 30% 30%, rgba(14,165,233,.25), rgba(14,165,233,0) 70%);
  top:20%;right:-120px;
  animation-delay:-6s;
}
@keyframes float{
  0%,100%{transform:translateY(0) translateX(0)}
  50%{transform:translateY(18px) translateX(-12px)}
}
@keyframes rise{
  from{transform:translateY(10px);opacity:.6}
  to{transform:translateY(0);opacity:1}
}
.wrap{max-width:1180px;margin:0 auto;padding:22px}
.top{
  display:flex;align-items:center;justify-content:space-between;gap:16px;
  padding:12px 16px;margin-bottom:18px;
  background:rgba(255,255,255,.85);
  border:1px solid var(--line);
  border-radius:var(--radius);
  box-shadow:var(--shadow-soft);
  backdrop-filter: blur(8px);
  animation: rise .5s ease;
}
.brand{display:flex;align-items:center;gap:14px}
.logo{
  width:46px;height:46px;border-radius:14px;display:flex;align-items:center;justify-content:center;
  background:linear-gradient(135deg, var(--accent), #ffb45f);
  color:#1d1204;font-weight:800;font-family:var(--display);font-size:20px;
  box-shadow:0 10px 24px rgba(255,106,0,.25);
}
.name{font-family:var(--display);font-weight:800;font-size:20px}
.sub{color:var(--muted);font-size:13px}
.card{
  background:rgba(255,255,255,.9);
  border:1px solid var(--line);
  border-radius:calc(var(--radius) + 2px);
  box-shadow:var(--shadow);
  padding:22px;
  animation: rise .6s ease;
}
h1{margin:0 0 10px;font-family:var(--display);font-size:30px;letter-spacing:.2px}
h2{margin:0 0 8px;font-family:var(--display)}
p{line-height:1.6}
.muted{color:var(--muted)}
.row{display:flex;flex-direction:column;gap:6px;margin:12px 0}
label{font-weight:600;color:#2a2f37}
input[type="file"],input[type="text"],input[type="search"],select{
  background:var(--paper);
  border:1px solid var(--line);
  color:var(--ink);
  padding:10px 12px;
  border-radius:12px;
  outline:none;
  font-size:14px;
  box-shadow: inset 0 0 0 1px rgba(255,255,255,.6);
}
input[type="file"]::file-selector-button{
  padding:8px 12px;
  border-radius:10px;
  border:1px solid var(--line);
  background:#fff;
  cursor:pointer;
  margin-right:10px;
  font-weight:600;
}
input[type="search"]{width:min(320px, 100%)}
input:focus,select:focus,textarea:focus{
  border-color:rgba(255,106,0,.7);
  box-shadow:0 0 0 3px rgba(255,106,0,.18);
}
.btn{
  display:inline-flex;align-items:center;justify-content:center;gap:8px;
  padding:10px 16px;border-radius:999px;border:1px solid var(--line);
  background:#fff;color:var(--ink);cursor:pointer;text-decoration:none;
  font-weight:600;box-shadow:0 3px 0 rgba(0,0,0,.04);
  transition:transform .08s ease, box-shadow .12s ease, border-color .12s ease;
}
.btn:hover{border-color:#d6cbb8;box-shadow:0 6px 16px rgba(18,20,25,.1);transform:translateY(-1px)}
.btn:active{transform:translateY(0);box-shadow:0 2px 0 rgba(0,0,0,.04)}
.btn.primary{
  background:linear-gradient(135deg, var(--accent), #ff9d42);
  color:#1f1203;border-color:#ff9d42;
}
.btn.success{
  background:linear-gradient(135deg, var(--accent-2), #5ad1a0);
  color:#072019;border-color:#5ad1a0;
}
.toolbar{display:flex;flex-wrap:wrap;gap:10px;align-items:center;margin:16px 0}
.rowbar{display:flex;align-items:center;gap:10px;flex-wrap:wrap;margin:14px 0}
.formbar{
  padding:10px 12px;
  background:var(--paper);
  border:1px solid var(--line);
  border-radius:14px;
  box-shadow:var(--shadow-soft);
}
.spacer{flex:1}
.flash{
  padding:12px 14px;border-radius:14px;margin:12px 0;border:1px solid var(--line);
  background:#fff;box-shadow:var(--shadow-soft)
}
.flash.ok{border-left:4px solid var(--ok)}
.flash.warn{border-left:4px solid var(--warn)}
.flash.err{border-left:4px solid var(--err)}
.tablewrap{
  overflow:auto;border-radius:16px;border:1px solid var(--line);
  background:#fff;box-shadow:var(--shadow-soft)
}
table{width:100%;border-collapse:separate;border-spacing:0;min-width:980px}
thead th{
  position:sticky;top:0;background:linear-gradient(180deg, #fff, #f7f4ee);
  z-index:1;text-align:left;padding:12px;border-bottom:1px solid var(--line);
  font-weight:700;font-size:13px;text-transform:uppercase;letter-spacing:.4px;
}
tbody tr:nth-child(odd){background:rgba(255,255,255,.6)}
tbody tr:hover{background:rgba(255,106,0,.06)}
td{padding:12px;vertical-align:top;border-bottom:1px solid #efe7db}
th.k,td.k{width:190px}
.key{font-family:var(--mono);color:#3b4352;font-size:12px}
.ta{
  width:100%;min-height:78px;resize:vertical;background:#fff;
  border:1px solid var(--line);color:var(--ink);padding:10px;border-radius:12px;line-height:1.4;
  font-family:var(--sans);font-size:14px;
}
.ta.ro{color:#4b5563;background:#fbfaf8}
.foot{margin-top:16px;color:var(--muted);font-size:12px}
details{
  margin-top:16px;padding:12px 14px;border:1px dashed #d8cbb8;border-radius:14px;background:var(--paper)
}
summary{cursor:pointer;font-weight:700}
.hero{
  display:grid;grid-template-columns:1.15fr .85fr;gap:24px;align-items:start;
}
.hero-copy{padding:6px 4px}
.panel{
  background:var(--paper);
  border:1px solid var(--line);
  border-radius:16px;
  padding:16px;
  box-shadow:var(--shadow-soft);
}
.panel.soft{background:rgba(255,255,255,.75)}
.chips{display:flex;flex-wrap:wrap;gap:8px;margin:12px 0}
.chip{
  padding:6px 10px;border-radius:999px;border:1px solid var(--line);background:#fff;
  font-size:12px;font-weight:600;color:#3c4654;
}
.chip.accent{background:#fff1e3;border-color:#ffd4ad;color:#9a3b00}
.chip.ghost{background:transparent}
.callout{
  margin-top:14px;padding:12px 14px;border-radius:14px;background:rgba(14,165,233,.08);
  border:1px solid rgba(14,165,233,.25)
}
.callout-title{font-weight:700;margin-bottom:4px}
.meta{display:flex;flex-wrap:wrap;gap:10px;margin-bottom:14px}
.pill{
  display:inline-flex;align-items:center;gap:8px;padding:8px 12px;border-radius:999px;
  background:#fff;border:1px solid var(--line);font-size:13px;box-shadow:var(--shadow-soft)
}
.pill.accent{background:#fff1e3;border-color:#ffd4ad}
.pill-label{font-size:11px;text-transform:uppercase;letter-spacing:.4px;color:var(--muted)}
.pill-value{font-weight:600}
.upload .row{margin:10px 0}
@media (max-width: 980px){
  .wrap{padding:18px}
  .hero{grid-template-columns:1fr}
  .top{flex-direction:column;align-items:flex-start}
  table{min-width:820px}
}
@media (max-width: 640px){
  h1{font-size:26px}
  .card{padding:16px}
  .top{padding:12px}
  .btn{width:100%;justify-content:center}
  input[type="search"]{width:100%}
}
</style>
"""

SCRIPT = """
<script>
function fillEmptyWithOriginal(){
  const rows = document.querySelectorAll('table tbody tr');
  rows.forEach(tr=>{
    const orig = tr.querySelector('textarea.ro');
    const dst = tr.querySelector('textarea:not(.ro)');
    if(!orig || !dst) return;
    if(dst.value.trim()==="") dst.value = orig.value;
  });
}
(function(){
  const filter = document.getElementById('filter');
  if(!filter) return;
  filter.addEventListener('input', ()=>{
    const q = filter.value.toLowerCase().trim();
    const rows = document.querySelectorAll('table tbody tr');
    rows.forEach(r=>{
      if(q===""){ r.style.display=""; return; }
      const key = r.querySelector('.key')?.innerText.toLowerCase() ?? "";
      const orig = r.querySelector('textarea.ro')?.value.toLowerCase() ?? "";
      const dst = r.querySelector('textarea:not(.ro)')?.value.toLowerCase() ?? "";
      const ok = key.includes(q) || orig.includes(q) || dst.includes(q);
      r.style.display = ok ? "" : "none";
    });
  });
})();
</script>
"""

BASE_TPL = """
<!doctype html><html lang="en"><head>
<meta charset="utf-8"><meta name="viewport" content="width=device-width, initial-scale=1">
<title>{{title}}</title>
""" + STYLE + """
</head><body>
<div class="bg">
  <div class="blob b1"></div>
  <div class="blob b2"></div>
  <div class="blob b3"></div>
</div>
<div class="wrap">
<header class="top">
  <div class="brand">
    <div class="logo">Z</div>
    <div>
      <div class="name">""" + APP_NAME + """</div>
      <div class="sub">Local web UI for translating Zepp OS packages (.btxt)</div>
    </div>
  </div>
  <nav><a class="btn" href="{{url_for('home')}}">Upload</a></nav>
</header>
<main class="card">
{% if flash %}
<div class="flash {{flash.type}}">{{flash.msg}}</div>
{% endif %}
{{body|safe}}
</main>
<footer class="foot">
Tip: keep placeholders intact (%d/%s/{0}) and avoid changing the string count if you replace files inside an app.
</footer>
</div>
""" + SCRIPT + """
</body></html>
"""

def render(body: str, title: str, flash: Optional[Dict[str, str]] = None):
    return render_template_string(BASE_TPL, body=body, title=title, flash=flash)

# -----------------------------
# Job storage
# -----------------------------
def job_dir(job_id: str) -> str:
    return os.path.join(JOB_ROOT, job_id)

def load_json(path: str) -> Any:
    with open(path, "r", encoding="utf-8") as f:
        return json.load(f)

def save_json(path: str, obj: Any) -> None:
    with open(path, "w", encoding="utf-8") as f:
        json.dump(obj, f, ensure_ascii=False, indent=2)

# -----------------------------
# Routes
# -----------------------------
@app.route("/", methods=["GET"])
def home():
    body = """
<div class="hero">
  <div class="hero-copy">
    <h1>Upload package</h1>
    <p class="muted">Supported: <b>.zpk</b>, <b>.zip</b>, <b>.zab</b>. The app extracts <code>device.zip</code>, renders a table from <code>assets/raw/locale/*.btxt</code>, and repacks the package.</p>
    <div class="chips">
      <span class="chip accent">.zpk</span>
      <span class="chip accent">.zip</span>
      <span class="chip accent">.zab</span>
      <span class="chip ghost">device.zip</span>
      <span class="chip ghost">assets/raw/locale/*.btxt</span>
    </div>
    <div class="callout">
      <div class="callout-title">BIN pages fallback</div>
      <p class="muted">If no .btxt is found, the BIN scan opens automatically and shows likely UI strings.</p>
    </div>
  </div>
  <form class="upload panel" method="post" action="/upload" enctype="multipart/form-data">
    <div class="row">
      <label>Package file</label>
      <input type="file" name="pkg" accept=".zpk,.zip,.zab" required>
    </div>
    <div class="row">
      <label>Target locale (file name)</label>
      <input type="text" name="target_locale" value="ru-RU" required>
      <div class="muted" style="font-size:12px">Creates or overwrites <code>assets/raw/locale/&lt;locale&gt;.btxt</code></div>
    </div>
    <div class="row">
      <button class="btn primary" type="submit">Upload and open editor</button>
    </div>
  </form>
</div>
<details class="panel soft">
  <summary>BIN pages</summary>
  <p class="muted">There is a viewer for "suspicious" strings from <code>page/pages *.bin</code> (heuristics). In some projects it is mostly identifiers and runtime strings.</p>
</details>
"""
    return render(body, "Upload")

@app.route("/upload", methods=["POST"])
def upload():
    f = request.files.get("pkg")
    if not f or f.filename == "":
        return render("<h1>Error</h1><p>No file selected.</p>", "Error", {"type":"err","msg":"No file selected"})

    if request.content_length and request.content_length > MAX_UPLOAD_BYTES:
        return render("<h1>Error</h1><p>File is too large.</p>", "Error", {"type":"err","msg":"File is too large (50MB limit)"})

    target_locale = (request.form.get("target_locale") or "ru-RU").strip()
    if not re.fullmatch(r"[A-Za-z]{2,3}(?:-[A-Za-z0-9]{2,8})*", target_locale):
        return render("<h1>Error</h1><p>Invalid locale.</p>", "Error", {"type":"err","msg":"Invalid locale, e.g. ru-RU"})

    ext = os.path.splitext(f.filename)[1].lower().lstrip(".")
    if ext not in ("zpk","zip","zab"):
        return render("<h1>Error</h1><p>Expected .zpk/.zip/.zab.</p>", "Error", {"type":"err","msg":"Expected .zpk/.zip/.zab"})

    job_id = os.urandom(8).hex()
    jd = job_dir(job_id)
    os.makedirs(jd, exist_ok=True)

    in_path = os.path.join(jd, f"input.{ext}")
    f.save(in_path)

    analysis = analyze_package(in_path)
    if not analysis.ok:
        shutil.rmtree(jd, ignore_errors=True)
        return render("<h1>Error</h1><p>device.zip not found.</p>", "Error", {"type":"err","msg":"device.zip not found"})

    device_zip_path = os.path.join(jd, "device.zip")
    extract_device_zip(in_path, analysis, device_zip_path)

    meta = {
        "job_id": job_id,
        "input_path": in_path,
        "input_name": f.filename,
        "ext": ext,
        "target_locale": target_locale,
        "mode": analysis.mode,
        "inner_zpk_name": analysis.inner_zpk_name,
        "locales": analysis.locales,
        "has_locale": analysis.has_locale,
        "device_zip_path": device_zip_path,
        "created": time.time(),
    }
    save_json(os.path.join(jd, "meta.json"), meta)

    if analysis.has_locale:
        # pick first non TID as default
        src = next((x for x in analysis.locales if x.lower() != "tid.btxt"), analysis.locales[0])
        return redirect(url_for("edit", job=job_id, src=src))

    return redirect(url_for("bin_export", job=job_id, reason="no_btxt"))

@app.route("/edit", methods=["GET"])
def edit():
    job_id = request.args.get("job","")
    src = request.args.get("src","")
    jd = job_dir(job_id)
    meta_path = os.path.join(jd, "meta.json")
    if not job_id or not os.path.isfile(meta_path):
        return redirect(url_for("home"))

    meta = load_json(meta_path)
    locales = meta["locales"]
    if not locales or all(l.lower() == "tid.btxt" for l in locales):
        return redirect(url_for("bin_export", job=job_id, reason="no_btxt"))
    if not src or src not in locales or src.lower() == "tid.btxt":
        src = next((x for x in locales if x.lower() != "tid.btxt"), locales[0])

    device_zip_path = meta["device_zip_path"]
    _, _, pairs = read_locale_pairs(device_zip_path, src)

    tr_path = os.path.join(jd, "translations.json")
    translations = load_json(tr_path) if os.path.isfile(tr_path) else {}

    # render
    opt = "".join([f'<option value="{l}" {"selected" if l==src else ""}>{l}</option>' for l in locales if l.lower()!="tid.btxt"])
    rows = []
    for p in pairs:
        k = p["k"]
        orig = p["v"]
        tr = translations.get(k, "")
        rows.append(f"""
<tr>
  <td class="k"><div class="key">{k}</div></td>
  <td><textarea class="ta ro" readonly>{html_escape(orig)}</textarea></td>
  <td><textarea class="ta" name="tr[{html_escape_attr(k)}]">{html_escape(tr)}</textarea></td>
</tr>""")
    table = "\n".join(rows)

    body = f"""
<h1>Localization editor</h1>
<div class="meta">
  <div class="pill"><span class="pill-label">File</span><span class="pill-value">{html_escape(meta["input_name"])}</span></div>
  <div class="pill accent"><span class="pill-label">Target</span><span class="pill-value">{html_escape(meta["target_locale"])}.btxt</span></div>
</div>

<form class="rowbar formbar" method="get" action="/edit">
  <input type="hidden" name="job" value="{job_id}">
  <label>Source</label>
  <select name="src">{opt}</select>
  <button class="btn" type="submit">Open</button>
  <div class="spacer"></div>
  <input id="filter" type="search" placeholder="Filter by key/text...">
</form>

<form method="post" action="/save">
  <input type="hidden" name="job" value="{job_id}">
  <input type="hidden" name="src" value="{html_escape_attr(src)}">

  <div class="toolbar">
    <button class="btn primary" type="submit" name="do" value="save">Save</button>
    <button class="btn success" type="submit" name="do" value="build">Build & download</button>
    <button class="btn" type="button" onclick="fillEmptyWithOriginal()">Empty = original</button>
    <label class="muted" style="display:inline-flex;gap:8px;align-items:center">
      <input type="checkbox" name="check_ph" checked> Validate placeholders
    </label>
  </div>

  <div class="tablewrap">
    <table>
      <thead><tr><th class="k">Key/index</th><th>Original ({html_escape(src)})</th><th>Translation ({html_escape(meta["target_locale"])})</th></tr></thead>
      <tbody>
        {table}
      </tbody>
    </table>
  </div>
</form>

<details class="panel soft">
  <summary>Experimental: scan text in BIN</summary>
  <p class="muted">The scanner tries to extract strings from <code>page/pages *.bin</code>. In some apps this yields "text/label/title", but often it is mostly technical strings.</p>
  <form method="post" action="/bin_export">
    <input type="hidden" name="job" value="{job_id}">
    <button class="btn" type="submit">Show strings found in BIN</button>
  </form>
</details>
"""
    return render(body, "Editor")

@app.route("/bin_export", methods=["GET", "POST"])
def bin_export():
    job_id = request.values.get("job","")
    reason = request.values.get("reason","")
    jd = job_dir(job_id)
    meta_path = os.path.join(jd, "meta.json")
    if not job_id or not os.path.isfile(meta_path):
        return redirect(url_for("home"))
    meta = load_json(meta_path)
    flash = None
    if reason == "no_btxt":
        flash = {"type":"warn","msg":"No locale .btxt found. Showing BIN strings instead."}
    back_url = url_for("edit", job=job_id) if meta.get("has_locale") else url_for("home")

    found = scan_bins_for_text(meta["device_zip_path"])
    tr_path = os.path.join(jd, "bin_translations.json")
    tr_list = load_json(tr_path) if os.path.isfile(tr_path) else []
    tr_map = {f"{r['file']}|{r['text']}": r.get("translation","") for r in tr_list}
    if not found:
        body = f"""
<h1>BIN strings</h1>
<div class="flash warn">No "UI-like" strings found. This is normal for many projects (text comes from .btxt).</div>
<div class="rowbar">
  <a class="btn" href="{back_url}">Back</a>
</div>
"""
        return render(body, "BIN strings", flash)

    rows = []
    for i, r in enumerate(found):
        key = f"{r['file']}|{r['text']}"
        tr_val = tr_map.get(key, "")
        rows.append(
            "<tr>"
            f"<td class='k'><div class='key'>{html_escape(r['file'])}</div></td>"
            f"<td>{html_escape(r['method'])}</td>"
            f"<td><textarea class='ta ro' readonly>{html_escape(r['text'])}</textarea></td>"
            f"<td><textarea class='ta' name='tr[{i}]'>{html_escape(tr_val)}</textarea>"
            f"<input type='hidden' name='file[{i}]' value='{html_escape_attr(r['file'])}'>"
            f"<input type='hidden' name='text[{i}]' value='{html_escape_attr(r['text'])}'>"
            f"<input type='hidden' name='method[{i}]' value='{html_escape_attr(r['method'])}'>"
            f"</td>"
            "</tr>"
        )
    table_rows = "\n".join(rows)
    body = f"""
<h1>BIN strings (experimental)</h1>
<div class="rowbar">
  <a class="btn" href="{back_url}">Back</a>
</div>
<p class="muted">Translations are saved and will be applied on build (best-effort, in-place). Longer translations are skipped.</p>
<form method="post" action="/bin_save">
  <input type="hidden" name="job" value="{job_id}">
  <div class="toolbar">
    <button class="btn primary" type="submit" name="do" value="save">Save translations</button>
    <button class="btn success" type="submit" name="do" value="build">Save & build</button>
  </div>
  <div class="tablewrap">
  <table>
    <thead><tr><th>File</th><th>Method</th><th>String</th><th>Translation</th></tr></thead>
    <tbody>{table_rows}</tbody>
  </table>
  </div>
</form>
"""
    return render(body, "BIN strings", flash)

@app.route("/bin_save", methods=["POST"])
def bin_save():
    job_id = request.form.get("job","")
    jd = job_dir(job_id)
    meta_path = os.path.join(jd, "meta.json")
    if not job_id or not os.path.isfile(meta_path):
        return redirect(url_for("home"))

    def _collect(prefix: str) -> Dict[int, str]:
        out: Dict[int, str] = {}
        for k, v in request.form.items():
            m = re.fullmatch(rf"{prefix}\[(\d+)\]", k)
            if m:
                out[int(m.group(1))] = v
        return out

    files = _collect("file")
    texts = _collect("text")
    methods = _collect("method")
    trs = _collect("tr")

    rows = []
    for idx in sorted(texts.keys()):
        text = texts.get(idx, "")
        file = files.get(idx, "")
        method = methods.get(idx, "")
        tr = (trs.get(idx, "") or "").strip()
        if not text or not file:
            continue
        if not tr:
            continue
        rows.append({"file": file, "method": method, "text": text, "translation": tr})

    save_json(os.path.join(jd, "bin_translations.json"), rows)
    do = request.form.get("do","save")
    if do == "build":
        return redirect(url_for("build", job=job_id))
    return redirect(url_for("bin_export", job=job_id))

@app.route("/save", methods=["POST"])
def save():
    job_id = request.form.get("job","")
    src = request.form.get("src","")
    jd = job_dir(job_id)
    meta_path = os.path.join(jd, "meta.json")
    if not job_id or not os.path.isfile(meta_path):
        return redirect(url_for("home"))
    meta = load_json(meta_path)

    tr = request.form.getlist("dummy")  # unused
    translations = {}
    # Flask doesn't parse tr[KEY] into dict automatically, so do manual:
    for k, v in request.form.items():
        m = re.fullmatch(r"tr\[(.*)\]", k)
        if not m:
            continue
        key = m.group(1)
        translations[key] = v

    # placeholder check (optional)
    flash = {"type":"ok","msg":"Saved."}
    if "check_ph" in request.form:
        try:
            _, _, pairs = read_locale_pairs(meta["device_zip_path"], src)
            orig_map = {p["k"]: p["v"] for p in pairs}
            bad = []
            for k, v in translations.items():
                if not v.strip():
                    continue
                o = orig_map.get(k)
                if o is None:
                    continue
                if not ZeppBtxt.placeholders_compatible(o, v):
                    bad.append(k)
            if bad:
                flash = {"type":"warn","msg":f"Warning: placeholders differ for keys: {', '.join(bad[:25])}{'…' if len(bad)>25 else ''}"}
        except Exception as e:
            flash = {"type":"warn","msg":f"Placeholder check failed: {e}"}

    save_json(os.path.join(jd, "translations.json"), translations)

    do = request.form.get("do","save")
    if do == "build":
        return redirect(url_for("build", job=job_id, src=src))
    return redirect(url_for("edit", job=job_id, src=src))

@app.route("/build", methods=["GET"])
def build():
    job_id = request.args.get("job","")
    src = (request.args.get("src","") or "").strip()
    jd = job_dir(job_id)
    meta_path = os.path.join(jd, "meta.json")
    if not job_id or not os.path.isfile(meta_path):
        return redirect(url_for("home"))
    meta = load_json(meta_path)

    # if src not provided, try to pick a reasonable default
    if not src:
        src = next((x for x in meta.get("locales", []) if x.lower() != "tid.btxt"), "")

    if src:
        tr_path = os.path.join(jd, "translations.json")
        translations = load_json(tr_path) if os.path.isfile(tr_path) else {}

        # read src pairs and build strings list
        _, values, pairs = read_locale_pairs(meta["device_zip_path"], src)
        strings_out = []
        for p in pairs:
            k = p["k"]
            orig = p["v"]
            t = translations.get(k, "").strip()
            strings_out.append(t if t else orig)

        btxt_bytes = ZeppBtxt.build_be_offsets(strings_out)
        target_file_name = meta["target_locale"] + ".btxt"

        # write new locale into device.zip
        write_locale_file(meta["device_zip_path"], target_file_name, btxt_bytes)

    # apply BIN translations if any
    bin_tr_path = os.path.join(jd, "bin_translations.json")
    if os.path.isfile(bin_tr_path):
        try:
            bin_rows = load_json(bin_tr_path)
            stats = apply_bin_translations(meta["device_zip_path"], bin_rows)
            if stats["files"] or stats["replaced"]:
                print(f"[+] BIN patch: files={stats['files']} replaced={stats['replaced']} skipped={stats['skipped']} not_found={stats['not_found']}")
        except Exception as e:
            print(f"[!] BIN patch failed: {e}")

    # repack outer package
    out_name = _safe_name(os.path.splitext(meta["input_name"])[0]) + "_localized." + meta["ext"]
    out_path = os.path.join(jd, out_name)

    analysis = analyze_package(meta["input_path"])
    repack_package_with_device(meta["input_path"], analysis, meta["device_zip_path"], out_path)

    return send_file(out_path, as_attachment=True, download_name=out_name)

# -----------------------------
# Small HTML escape helpers (since we generate rows manually)
# -----------------------------
def html_escape(s: str) -> str:
    return (s.replace("&","&amp;").replace("<","&lt;").replace(">","&gt;")
            .replace('"',"&quot;").replace("'","&#39;"))

def html_escape_attr(s: str) -> str:
    # same as escape
    return html_escape(s)

# -----------------------------
# Run
# -----------------------------
if __name__ == "__main__":
    print(f"[+] Job dir: {JOB_ROOT}")
    print("[+] Open: http://127.0.0.1:5000")
    app.run(host="127.0.0.1", port=5000, debug=False)
