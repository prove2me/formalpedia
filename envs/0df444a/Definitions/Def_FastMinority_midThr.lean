-- Prove2me | Definitions.Def_FastMinority_midThr
-- name    : FastMinority_midThr
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T03:04:18.24597+00:00
-- url     : https://prove2.me/theorems/883c1eb3-33d5-4dd1-be0e-dd4b8284b6d5
-- title:
--   Threshold $M=\lfloor Dn\log n/k\rfloor$
-- statement:
--   For the region constant $D>2$, the threshold
--   $$
--   M=\left\lfloor \frac{Dn\log n}{k}\right\rfloor
--   $$
--   (natural logarithm) bounds from below the minority sizes from which the next round reaches consensus with probability $1-O(n^{1-D})$ (Lemma 5.7): above $M$, a unanimous-majority sample has probability at most $n^{-D}$.
--
--   **Formalization Note** Natural-number floor; the argument is nonnegative for $n\ge1$ and $D>0$.
-- source:
--   Berenbrink–Giriyan–Götte–Richa, Fast Minority Dynamics with Θ(log² n)-Size Samples, STOC 2027 submission (manuscript sha256 841077e0…abcdd1), Section 3, p.6 (PDF p.8)

import Mathlib

set_option autoImplicit false

open Classical

namespace FastMinority

/-- The threshold `M = ⌊(D n log n)/k⌋` (Berenbrink–Giriyan–Götte–Richa, *Fast Minority Dynamics with Θ(log² n)-Size Samples*, STOC 2027 submission manuscript (sha256 841077e0…abcdd1), §3, p.6 = PDF p.8), for the region constant
`D > 2`; the logarithm is natural (p.5 = PDF p.7: "All logarithms used in the calculations in this
paper are natural").

**Formalization Note** `⌊·⌋₊` is the natural-number floor (`0` on negative reals; the argument is
nonnegative for `n ≥ 1`, `D > 0`). -/
noncomputable def midThr (n k : ℕ) (D : ℝ) : ℕ :=
  ⌊D * n * Real.log n / k⌋₊

end FastMinority


