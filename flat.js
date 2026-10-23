// Geometry and pixel work for FlatScan. Pure functions, no DOM, so they can be tested in Node.
(function (root) {
  const cross = (a, b) => [a[1] * b[2] - a[2] * b[1], a[2] * b[0] - a[0] * b[2], a[0] * b[1] - a[1] * b[0]];
  const dot = (a, b) => a[0] * b[0] + a[1] * b[1] + a[2] * b[2];
  const dist = (a, b) => Math.hypot(a.x - b.x, a.y - b.y);

  /** Put four points in TL, TR, BR, BL order regardless of how the user dragged them. */
  function orderCorners(pts) {
    const cx = pts.reduce((s, p) => s + p.x, 0) / 4, cy = pts.reduce((s, p) => s + p.y, 0) / 4;
    const sorted = pts.slice().sort((a, b) => Math.atan2(a.y - cy, a.x - cx) - Math.atan2(b.y - cy, b.x - cx));
    // Clockwise in screen space starting from the corner nearest the top-left.
    let start = 0;
    for (let i = 1; i < 4; i++) if (sorted[i].x + sorted[i].y < sorted[start].x + sorted[start].y) start = i;
    return [0, 1, 2, 3].map((k) => sorted[(start + k) % 4]);
  }

  /**
   * Real width/height ratio of a rectangle seen in perspective (Zhang & He, "Whiteboard scanning"),
   * assuming the principal point is the image centre. `focal` (pixels) comes from the photo's EXIF;
   * without it we try to recover it from the quad, which fails when the surface is tilted about
   * only one axis, so then we assume the iPhone 0.5x lens.
   */
  function estimateAspect([tl, tr, br, bl], imgW, imgH, focal) {
    const u0 = imgW / 2, v0 = imgH / 2, diag = Math.hypot(imgW, imgH);
    const h = (p) => [p.x - u0, p.y - v0, 1];
    const m1 = h(tl), m2 = h(tr), m3 = h(bl), m4 = h(br);
    const c14 = cross(m1, m4);
    const k2 = dot(c14, m3) / dot(cross(m2, m4), m3);
    const k3 = dot(c14, m2) / dot(cross(m3, m4), m2);
    const n2 = m2.map((v, i) => k2 * v - m1[i]);
    const n3 = m3.map((v, i) => k3 * v - m1[i]);
    let f2 = focal ? focal * focal : NaN, method = focal ? "exif" : "recovered";
    if (!focal) {
      f2 = -(n2[0] * n3[0] + n2[1] * n3[1]) / (n2[2] * n3[2]);
      const f = Math.sqrt(f2);
      if (!(f2 > 0) || !isFinite(f2) || f < 0.15 * diag || f > 5 * diag) {
        f2 = (ULTRA_WIDE_FOCAL * diag) ** 2;
        method = "assumed 0.5x";
      }
    }
    const ratio = Math.sqrt((n2[0] ** 2 + n2[1] ** 2) / f2 + n2[2] ** 2) /
                  Math.sqrt((n3[0] ** 2 + n3[1] ** 2) / f2 + n3[2] ** 2);
    if (isFinite(ratio) && ratio > 0) return { ratio, method };
    const edges = (dist(tl, tr) + dist(bl, br)) / (dist(tl, bl) + dist(tr, br));
    return { ratio: edges, method: "edges" };
  }

  // iPhone ultra-wide: 13 mm full-frame equivalent; focal length as a fraction of the image diagonal.
  const ULTRA_WIDE_FOCAL = 13 / Math.hypot(36, 24);

  /** Focal length in pixels from 35 mm-equivalent focal length and the image size. */
  const focalFromEquiv = (mm35, imgW, imgH) => mm35 > 0 ? mm35 / Math.hypot(36, 24) * Math.hypot(imgW, imgH) : 0;

  /** Reads FocalLengthIn35mmFilm (0xA405) from a JPEG's EXIF, or 0. */
  function exifFocal35(buf) {
    const v = new DataView(buf);
    if (v.byteLength < 4 || v.getUint16(0) !== 0xffd8) return 0;
    let off = 2;
    while (off + 4 < v.byteLength) {
      const marker = v.getUint16(off), size = v.getUint16(off + 2);
      if (marker === 0xffe1 && v.getUint32(off + 4) === 0x45786966) return readTiff(v, off + 10);
      if ((marker & 0xff00) !== 0xff00) break;
      off += 2 + size;
    }
    return 0;
  }
  function readTiff(v, t) {
    const le = v.getUint16(t) === 0x4949;
    const u16 = (o) => v.getUint16(t + o, le), u32 = (o) => v.getUint32(t + o, le);
    const findTag = (ifd, tag) => {
      const n = u16(ifd);
      for (let i = 0; i < n; i++) { const e = ifd + 2 + i * 12; if (u16(e) === tag) return e; }
      return -1;
    };
    try {
      const ifd0 = u32(4), exifPtr = findTag(ifd0, 0x8769);
      if (exifPtr < 0) return 0;
      const e = findTag(u32(exifPtr + 8), 0xa405);
      return e < 0 ? 0 : u16(e + 8);
    } catch { return 0; }
  }

  /** Homography H (row-major, h8 = 1) mapping output rect (0,0)-(W,H) onto the source quad. */
  function rectToQuad(W, H, [tl, tr, br, bl]) {
    const src = [[0, 0], [W, 0], [W, H], [0, H]], dst = [tl, tr, br, bl];
    const A = [], b = [];
    for (let i = 0; i < 4; i++) {
      const [x, y] = src[i], u = dst[i].x, v = dst[i].y;
      A.push([x, y, 1, 0, 0, 0, -u * x, -u * y]); b.push(u);
      A.push([0, 0, 0, x, y, 1, -v * x, -v * y]); b.push(v);
    }
    // Gaussian elimination with partial pivoting.
    for (let c = 0; c < 8; c++) {
      let p = c;
      for (let r = c + 1; r < 8; r++) if (Math.abs(A[r][c]) > Math.abs(A[p][c])) p = r;
      [A[c], A[p]] = [A[p], A[c]]; [b[c], b[p]] = [b[p], b[c]];
      for (let r = c + 1; r < 8; r++) {
        const k = A[r][c] / A[c][c];
        for (let j = c; j < 8; j++) A[r][j] -= k * A[c][j];
        b[r] -= k * b[c];
      }
    }
    const h = new Array(8);
    for (let r = 7; r >= 0; r--) {
      let s = b[r];
      for (let j = r + 1; j < 8; j++) s -= A[r][j] * h[j];
      h[r] = s / A[r][r];
    }
    return h;
  }

  /** Output size for a given ratio, keeping about as many pixels as the quad covers in the source. */
  function outputSize([tl, tr, br, bl], ratio, maxPixels) {
    const pts = [tl, tr, br, bl];
    let area = 0;
    for (let i = 0; i < 4; i++) { const a = pts[i], c = pts[(i + 1) % 4]; area += a.x * c.y - c.x * a.y; }
    area = Math.min(Math.abs(area) / 2, maxPixels);
    let W = Math.sqrt(area * ratio), H = Math.sqrt(area / ratio);
    const cap = 8192 / Math.max(W, H);
    if (cap < 1) { W *= cap; H *= cap; }
    return { W: Math.max(1, Math.round(W)), H: Math.max(1, Math.round(H)) };
  }

  /** Perspective-warp the quad in `src` (RGBA, sw×sh) into a W×H RGBA buffer with bilinear sampling. */
  function warp(src, sw, sh, quad, W, H) {
    const [h0, h1, h2, h3, h4, h5, h6, h7] = rectToQuad(W, H, quad);
    const out = new Uint8ClampedArray(W * H * 4);
    const maxX = sw - 1.001, maxY = sh - 1.001;
    let o = 0;
    for (let y = 0; y < H; y++) {
      const yc = y + 0.5;
      let nx = h0 * 0.5 + h1 * yc + h2, ny = h3 * 0.5 + h4 * yc + h5, dz = h6 * 0.5 + h7 * yc + 1;
      for (let x = 0; x < W; x++, o += 4) {
        let sx = nx / dz - 0.5, sy = ny / dz - 0.5;
        nx += h0; ny += h3; dz += h6;
        if (sx < 0) sx = 0; else if (sx > maxX) sx = maxX;
        if (sy < 0) sy = 0; else if (sy > maxY) sy = maxY;
        const x0 = sx | 0, y0 = sy | 0, fx = sx - x0, fy = sy - y0;
        const i00 = (y0 * sw + x0) * 4, i10 = i00 + 4, i01 = i00 + sw * 4, i11 = i01 + 4;
        const w00 = (1 - fx) * (1 - fy), w10 = fx * (1 - fy), w01 = (1 - fx) * fy, w11 = fx * fy;
        out[o] = src[i00] * w00 + src[i10] * w10 + src[i01] * w01 + src[i11] * w11;
        out[o + 1] = src[i00 + 1] * w00 + src[i10 + 1] * w10 + src[i01 + 1] * w01 + src[i11 + 1] * w11;
        out[o + 2] = src[i00 + 2] * w00 + src[i10 + 2] * w10 + src[i01 + 2] * w01 + src[i11 + 2] * w11;
        out[o + 3] = 255;
      }
    }
    return out;
  }

  /**
   * Flatbed look: divide out the uneven lighting (a heavily blurred copy of the image), then
   * stretch levels. `mono` turns it into a crisp greyscale scan.
   */
  function scannerLook(px, W, H, mono) {
    // Illumination map on a coarse grid, blurred a few times.
    const gw = Math.max(2, Math.min(48, Math.round(W / 40))), gh = Math.max(2, Math.min(48, Math.round(H / 40)));
    let grid = new Float32Array(gw * gh * 3);
    const counts = new Float32Array(gw * gh);
    for (let y = 0; y < H; y += 2) {
      const gy = Math.min(gh - 1, (y * gh / H) | 0);
      for (let x = 0; x < W; x += 2) {
        const gx = Math.min(gw - 1, (x * gw / W) | 0), g = gy * gw + gx, i = (y * W + x) * 4;
        grid[g * 3] += px[i]; grid[g * 3 + 1] += px[i + 1]; grid[g * 3 + 2] += px[i + 2]; counts[g]++;
      }
    }
    for (let g = 0; g < gw * gh; g++) for (let c = 0; c < 3; c++) grid[g * 3 + c] /= Math.max(1, counts[g]);
    for (let pass = 0; pass < 4; pass++) {
      const next = new Float32Array(grid.length);
      for (let y = 0; y < gh; y++) for (let x = 0; x < gw; x++) {
        let n = 0;
        for (let dy = -1; dy <= 1; dy++) for (let dx = -1; dx <= 1; dx++) {
          const xx = x + dx, yy = y + dy;
          if (xx < 0 || yy < 0 || xx >= gw || yy >= gh) continue;
          const s = (yy * gw + xx) * 3, d = (y * gw + x) * 3;
          next[d] += grid[s]; next[d + 1] += grid[s + 1]; next[d + 2] += grid[s + 2]; n++;
        }
        const d = (y * gw + x) * 3; next[d] /= n; next[d + 1] /= n; next[d + 2] /= n;
      }
      grid = next;
    }
    const mean = [0, 0, 0];
    for (let g = 0; g < gw * gh; g++) for (let c = 0; c < 3; c++) mean[c] += grid[g * 3 + c] / (gw * gh);
    // Neutralise the colour cast too: every channel's lighting is scaled to the same grey.
    const target = (mean[0] + mean[1] + mean[2]) / 3;

    const out = new Uint8ClampedArray(px.length);
    const hist = new Uint32Array(256);
    for (let y = 0; y < H; y++) {
      const gyf = Math.min(gh - 1.001, Math.max(0, (y + 0.5) * gh / H - 0.5)), gy = gyf | 0, fy = gyf - gy;
      for (let x = 0; x < W; x++) {
        const gxf = Math.min(gw - 1.001, Math.max(0, (x + 0.5) * gw / W - 0.5)), gx = gxf | 0, fx = gxf - gx;
        const a = (gy * gw + gx) * 3, b = a + 3, c = a + gw * 3, d = c + 3;
        const i = (y * W + x) * 4;
        let l = 0;
        for (let ch = 0; ch < 3; ch++) {
          const illum = (grid[a + ch] * (1 - fx) + grid[b + ch] * fx) * (1 - fy) + (grid[c + ch] * (1 - fx) + grid[d + ch] * fx) * fy;
          const v = px[i + ch] * target / Math.max(8, illum);
          out[i + ch] = v;
          l += v;
        }
        out[i + 3] = 255;
        hist[Math.min(255, (l / 3) | 0)]++;
      }
    }
    // Levels: clip 0.4% at each end.
    const total = W * H, clip = total * 0.004;
    let lo = 0, hi = 255, acc = 0;
    while (lo < 255 && (acc += hist[lo]) < clip) lo++;
    acc = 0;
    while (hi > lo + 1 && (acc += hist[hi]) < clip) hi--;
    const scale = 255 / (hi - lo);
    for (let i = 0; i < out.length; i += 4) {
      if (mono) {
        let l = ((0.299 * out[i] + 0.587 * out[i + 1] + 0.114 * out[i + 2]) - lo) * scale;
        l = (l - 128) * 1.12 + 128;
        out[i] = out[i + 1] = out[i + 2] = l;
      } else {
        out[i] = (out[i] - lo) * scale;
        out[i + 1] = (out[i + 1] - lo) * scale;
        out[i + 2] = (out[i + 2] - lo) * scale;
      }
    }
    return out;
  }

  root.Flat = { orderCorners, estimateAspect, focalFromEquiv, exifFocal35, rectToQuad, outputSize, warp, scannerLook };
})(typeof window !== "undefined" ? window : globalThis);
