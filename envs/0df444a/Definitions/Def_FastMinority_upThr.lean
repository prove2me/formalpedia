-- Prove2me | Definitions.Def_FastMinority_upThr
-- name    : FastMinority_upThr
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T03:04:17.804256+00:00
-- url     : https://prove2.me/theorems/d69c49b6-493f-44de-a980-e433fd41ffaa
-- title:
--   Upper threshold $R=\lfloor n/2-n\sqrt{(2D\log n)/k}\rfloor$
-- statement:
--   For the region constant $D>2$, the **upper threshold** is
--   $$
--   R=\left\lfloor \frac n2-n\sqrt{\frac{2D\log n}{k}}\right\rfloor
--   $$
--   (natural logarithm). The upper region $\mathcal U=[R,\lfloor n/2\rfloor]$ consists of the minority sizes within $n\sqrt{2D\log n/k}$ of $n/2$.
--
--   **Formalization Note** Natural-number floor; for small $n$ the argument can be negative and the value is then $0$. For $k=\Theta(\log^2 n)$ and large $n$, $R\ge 2n/5$.
-- source:
--   Berenbrink–Giriyan–Götte–Richa, Fast Minority Dynamics with Θ(log² n)-Size Samples, STOC 2027 submission (manuscript sha256 841077e0…abcdd1), Section 3, p.6 (PDF p.8)

import Mathlib

set_option autoImplicit false

open Classical

namespace FastMinority

/-- The upper threshold `R = ⌊n/2 − n √((2D log n)/k)⌋` (Berenbrink–Giriyan–Götte–Richa, *Fast Minority Dynamics with Θ(log² n)-Size Samples*, STOC 2027 submission manuscript (sha256 841077e0…abcdd1), §3, p.6 = PDF p.8, rendered with
floor brackets), for the region constant `D > 2`, natural logarithm.

**Formalization Note** `⌊·⌋₊` is the natural-number floor; for small `n` the argument can be negative
and the value is then `0` (every region bounded by `R` is then empty or degenerate). For the band
`k = Θ(log² n)` and large `n`, `R ≥ 2n/5`. -/
noncomputable def upThr (n k : ℕ) (D : ℝ) : ℕ :=
  ⌊(n : ℝ) / 2 - n * Real.sqrt (2 * D * Real.log n / k)⌋₊

end FastMinority


