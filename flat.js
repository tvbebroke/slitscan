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
    if (isFinite(ratio) && ratio > 0) return { ratio, method, focal: Math.sqrt(f2) };
    const edges = (dist(tl, tr) + dist(bl, br)) / (dist(tl, bl) + dist(tr, br));
    return { ratio: edges, method: "edges", focal: Math.sqrt(f2) || ULTRA_WIDE_FOCAL * diag };
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
        if (px[i + 3] === 0) continue;
        grid[g * 3] += px[i]; grid[g * 3 + 1] += px[i + 1]; grid[g * 3 + 2] += px[i + 2]; counts[g]++;
      }
    }
    // Cells with no surface (holes) borrow the average so they don't drag the lighting down.
    let filled = 0; const avg = [0, 0, 0];
    for (let g = 0; g < gw * gh; g++) if (counts[g]) { filled++; for (let c = 0; c < 3; c++) avg[c] += grid[g * 3 + c] / counts[g]; }
    for (let g = 0; g < gw * gh; g++) for (let c = 0; c < 3; c++)
      grid[g * 3 + c] = counts[g] ? grid[g * 3 + c] / counts[g] : avg[c] / Math.max(1, filled);
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
        if (px[i + 3] === 0) continue; // hole: stays transparent
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
    let total = 0;
    for (let k = 0; k < 256; k++) total += hist[k];
    const clip = total * 0.004;
    let lo = 0, hi = 255, acc = 0;
    while (lo < 255 && (acc += hist[lo]) < clip) lo++;
    acc = 0;
    while (hi > lo + 1 && (acc += hist[hi]) < clip) hi--;
    const scale = 255 / (hi - lo);
    for (let i = 0; i < out.length; i += 4) {
      if (out[i + 3] === 0) continue;
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


  // ---------- Whole-scene flattening (depth from one photo) ----------

  /**
   * Camera pose of the picked rectangle: rotation columns r1 (along its width), r2 (along its
   * height), normal r3, and t = its top-left corner, in units where the rectangle is ratio × 1.
   */
  function planeFromQuad(quad, ratio, focal, imgW, imgH) {
    const h = rectToQuad(ratio, 1, quad), cx = imgW / 2, cy = imgH / 2;
    const col = (c0, c1, c2) => [(c0 - cx * c2) / focal, (c1 - cy * c2) / focal, c2];
    const m1 = col(h[0], h[3], h[6]), m2 = col(h[1], h[4], h[7]), m3 = col(h[2], h[5], 1);
    let lambda = 1 / Math.hypot(...m1);
    if (lambda * m3[2] < 0) lambda = -lambda;
    const norm = (a) => { const l = Math.hypot(...a); return a.map((v) => v / l); };
    const r1 = norm(m1.map((v) => v * lambda));
    const r3 = norm(cross(r1, m2.map((v) => v * lambda)));
    const r2 = cross(r3, r1);
    return { r1, r2, r3, t: m3.map((v) => v * lambda), focal, cx, cy };
  }

  function insideConvex(quad, x, y) {
    let sign = 0;
    for (let i = 0; i < 4; i++) {
      const a = quad[i], b = quad[(i + 1) % 4];
      const c = (b.x - a.x) * (y - a.y) - (b.y - a.y) * (x - a.x);
      if (c !== 0) { if (sign && Math.sign(c) !== sign) return false; sign = Math.sign(c); }
    }
    return true;
  }

  /**
   * Turns a relative depth map (disparity: bigger = nearer, any scale and offset) into a mesh laid
   * out on the picked plane, seen straight-on with no perspective (orthographic).
   * The picked surface calibrates the disparity's scale and offset to real distances.
   */
  function buildScene({ disparity, dw, dh, srcW, srcH, quad, ratio, focal, maxCols = 360, maxSide = 4096, maxPixels = 12e6 }) {
    const P = planeFromQuad(quad, ratio, focal, srcW, srcH);
    const { r1, r2, r3, t, cx, cy } = P;
    const nt = dot(r3, t);
    const step = Math.max(1, Math.ceil(dw / maxCols));
    const gw = Math.floor((dw - 1) / step) + 1, gh = Math.floor((dh - 1) / step) + 1;
    const kx = srcW / dw, ky = srcH / dh;
    const ray = (sx, sy) => [(sx - cx) / focal, (sy - cy) / focal, 1];

    // Calibrate disparity D ≈ a · (1/Z) + b against the plane's known depth inside the quad.
    const ws = [], ds = [];
    for (let gy = 0; gy < gh; gy++) for (let gx = 0; gx < gw; gx++) {
      const x = gx * step, y = gy * step, sx = (x + 0.5) * kx, sy = (y + 0.5) * ky;
      if (!insideConvex(quad, sx, sy)) continue;
      const Z = nt / dot(r3, ray(sx, sy));
      if (Z > 0) { ws.push(1 / Z); ds.push(disparity[y * dw + x]); }
    }
    if (ws.length < 12) throw new Error("surface-too-small");
    // Robust line fit: things standing on the surface (furniture, people) disagree with the plane,
    // so refit a few times keeping the points that agree best.
    let keep = ws.map((_, i) => i), a = 0, b = 0;
    for (let iter = 0; iter < 5; iter++) {
      const n = keep.length;
      let mw = 0, md = 0;
      for (const i of keep) { mw += ws[i]; md += ds[i]; }
      mw /= n; md /= n;
      let cov = 0, vw = 0;
      for (const i of keep) { cov += (ws[i] - mw) * (ds[i] - md); vw += (ws[i] - mw) ** 2; }
      if (Math.sqrt(vw / n) / mw > 0.03 && cov > 0) { a = cov / vw; b = md - a * mw; }
      else { a = md / mw; b = 0; } // surface seen straight-on: scale only
      if (!(a > 0)) { a = md / mw; b = 0; }
      const res = keep.map((i) => [Math.abs(ds[i] - (a * ws[i] + b)), i]).sort((p, q) => p[0] - q[0]);
      keep = res.slice(0, Math.max(12, Math.ceil(res.length * 0.75))).map((r) => r[1]);
    }
    const zPlane = 1 / (ws.reduce((s, v) => s + v, 0) / ws.length);
    const wMin = 1 / (zPlane * 25); // anything farther is treated as 25× the surface distance

    const camSide = Math.sign(-nt) || 1;
    const count = gw * gh;
    const positions = new Float32Array(count * 3), texcoords = new Float32Array(count * 2), wv = new Float32Array(count);
    for (let gy = 0, i = 0; gy < gh; gy++) for (let gx = 0; gx < gw; gx++, i++) {
      const x = gx * step, y = gy * step, sx = (x + 0.5) * kx, sy = (y + 0.5) * ky;
      const w = Math.max(wMin, (disparity[y * dw + x] - b) / a);
      const Z = 1 / w, d = ray(sx, sy);
      const rel = [d[0] * Z - t[0], d[1] * Z - t[1], Z - t[2]];
      positions[i * 3] = dot(r1, rel);
      positions[i * 3 + 1] = dot(r2, rel);
      positions[i * 3 + 2] = dot(r3, rel) * camSide; // bigger = closer to the camera side, drawn on top
      texcoords[i * 2] = sx / srcW;
      texcoords[i * 2 + 1] = sy / srcH;
      wv[i] = w;
    }

    // Two triangles per cell, dropped where depth jumps (an object's edge against what's behind it).
    const jump = Math.min(0.3, 0.02 + 0.015 * step);
    const idx = [];
    const ok = (i, j, k) => {
      const lo = Math.min(wv[i], wv[j], wv[k]), hi = Math.max(wv[i], wv[j], wv[k]);
      return hi / lo - 1 <= jump && lo > wMin;
    };
    for (let gy = 0; gy < gh - 1; gy++) for (let gx = 0; gx < gw - 1; gx++) {
      const i = gy * gw + gx, j = i + 1, k = i + gw, l = k + 1;
      if (ok(i, j, k)) idx.push(i, j, k);
      if (ok(j, l, k)) idx.push(j, l, k);
    }
    const indices = new Uint32Array(idx);

    // Bounds: what's actually drawn, without letting far-away points blow the canvas up.
    const used = new Uint8Array(count);
    for (const v of indices) used[v] = 1;
    const us = [], vs = [];
    let zmin = Infinity, zmax = -Infinity;
    for (let i = 0; i < count; i++) if (used[i]) {
      us.push(positions[i * 3]); vs.push(positions[i * 3 + 1]);
      zmin = Math.min(zmin, positions[i * 3 + 2]); zmax = Math.max(zmax, positions[i * 3 + 2]);
    }
    if (!us.length) throw new Error("no-geometry");
    const pct = (arr, p) => { const s = Float32Array.from(arr).sort(); return s[Math.min(s.length - 1, Math.floor(p * s.length))]; };
    const reach = 2.5 * Math.max(ratio, 1);
    const bounds = {
      umin: Math.min(0, Math.max(-reach, pct(us, 0.01))), umax: Math.max(ratio, Math.min(ratio + reach, pct(us, 0.99))),
      vmin: Math.min(0, Math.max(-reach, pct(vs, 0.01))), vmax: Math.max(1, Math.min(1 + reach, pct(vs, 0.99))),
    };

    // Keep the picked surface at about the same pixel density it has in the photo.
    let area = 0;
    for (let i = 0; i < 4; i++) { const p = quad[i], q = quad[(i + 1) % 4]; area += p.x * q.y - q.x * p.y; }
    let ppu = Math.sqrt(Math.abs(area) / 2 / ratio);
    const bw = bounds.umax - bounds.umin, bh = bounds.vmax - bounds.vmin;
    ppu = Math.min(ppu, maxSide / Math.max(bw, bh), Math.sqrt(maxPixels / (bw * bh)));
    return {
      positions, texcoords, indices, bounds, zmin, zmax: zmax > zmin ? zmax : zmin + 1,
      W: Math.max(1, Math.round(bw * ppu)), H: Math.max(1, Math.round(bh * ppu)),
      calibration: { a, b, samples: ws.length },
    };
  }

  /**
   * Retro flatbed finish on top of the scanner look: slight RGB misregistration along the scan
   * direction, CCD column streaks, lamp falloff at the bed edges, grain, a warm cast and dust.
   * Holes (alpha 0) become the black of an open scanner lid.
   */
  function retroScan(px, W, H, seed = 7) {
    let s = seed >>> 0 || 1;
    const rand = () => { s ^= s << 13; s >>>= 0; s ^= s >>> 17; s ^= s << 5; s >>>= 0; return s / 4294967296; };
    const gain = new Float32Array(W);
    for (let x = 0; x < W; x++) {
      const e = (x / W - 0.5) * 2;
      gain[x] = (1 + (rand() - 0.5) * 0.035) * (1 - 0.14 * e * e);
    }
    for (let n = Math.max(2, Math.round(W / 260)); n > 0; n--) {
      const x0 = (rand() * W) | 0, g = rand() < 0.5 ? 0.86 : 1.12, wid = 1 + (rand() * 2 | 0);
      for (let x = x0; x < Math.min(W, x0 + wid); x++) gain[x] *= g;
    }
    const out = new Uint8ClampedArray(px.length);
    const shift = Math.max(1, Math.round(H / 900)); // misregistration in pixels
    for (let y = 0; y < H; y++) {
      const yr = Math.max(0, y - shift) * W, yb = Math.min(H - 1, y + shift) * W, row = y * W;
      for (let x = 0; x < W; x++) {
        const i = (row + x) * 4;
        const grain = (rand() - 0.5) * 20;
        if (px[i + 3] === 0) {
          const v = 6 + rand() * 7;
          out[i] = v; out[i + 1] = v; out[i + 2] = v + 2; out[i + 3] = 255;
          continue;
        }
        const ir = (yr + x) * 4, ib = (yb + x) * 4;
        let r = px[ir + 3] ? px[ir] : px[i], g = px[i + 1], bl = px[ib + 3] ? px[ib + 2] : px[i + 2];
        const l = 0.299 * r + 0.587 * g + 0.114 * bl;
        r = l + (r - l) * 0.8; g = l + (g - l) * 0.8; bl = l + (bl - l) * 0.8;
        const k = gain[x];
        out[i] = ((r - 128) * 1.1 + 128) * 1.05 * k + 6 + grain;
        out[i + 1] = ((g - 128) * 1.1 + 128) * 1.0 * k + 2 + grain;
        out[i + 2] = ((bl - 128) * 1.1 + 128) * 0.88 * k + grain;
        out[i + 3] = 255;
      }
    }
    // Dust and the odd hair on the glass.
    const specks = Math.round(W * H / 60000);
    for (let n = 0; n < specks; n++) {
      let x = rand() * W, y = rand() * H;
      const light = rand() < 0.7, len = rand() < 0.12 ? 18 + rand() * 40 : 1 + rand() * 2;
      let ang = rand() * Math.PI * 2;
      for (let k = 0; k < len; k++) {
        const xi = x | 0, yi = y | 0;
        if (xi >= 0 && yi >= 0 && xi < W && yi < H) {
          const i = (yi * W + xi) * 4, v = light ? 235 : 25;
          out[i] = (out[i] + v) / 2; out[i + 1] = (out[i + 1] + v) / 2; out[i + 2] = (out[i + 2] + v) / 2;
        }
        ang += (rand() - 0.5) * 0.5; x += Math.cos(ang); y += Math.sin(ang);
      }
    }
    return out;
  }

  root.Flat = { planeFromQuad, buildScene, retroScan, orderCorners, estimateAspect, focalFromEquiv, exifFocal35, rectToQuad, outputSize, warp, scannerLook };
})(typeof window !== "undefined" ? window : globalThis);
