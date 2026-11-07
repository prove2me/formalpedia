-- Prove2me | Definitions.Def_SecondBestBT_gridInterimS
-- name    : SecondBestBT_gridInterimS
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T22:42:43.851912+00:00
-- url     : https://prove2.me/theorems/8edc8f16-ff1c-4ad7-a8ab-33a7054a7bd8
-- title:
--   Grid seller interim $x_S(i)=\sum_j f_B(j)x(i,j)$
-- statement:
--   For a grid allocation matrix $x(i,j)$ and buyer masses $f_B$, the seller's interim allocation at grid index $i$ is
--   $$
--   x_S(i)=\sum_{j=0}^{N} f_B(j)\,x(i,j).
--   $$
-- source:
--   Liu–Qin–Ren–Wang, Second-Best Bilateral Trade is 1/2 Efficient, arXiv:2606.03849 (held version, sha256 17184930…), Section 3, p.6

import Mathlib

namespace SecondBestBT

/-- The seller's interim allocation of a grid allocation matrix,
`x_S(i) = ∑_{j=0}^N f_B(j) x(i, j)` (Liu–Qin–Ren–Wang, arXiv:2606.03849, held version sha256
17184930…, Section 3, p.6; with `N = W`, also Section 4.1, p.8). -/
def gridInterimS (fB : ℕ → ℝ) (N : ℕ) (x : ℕ → ℕ → ℝ) (i : ℕ) : ℝ :=
  ∑ j ∈ Finset.range (N + 1), fB j * x i j

end SecondBestBT


