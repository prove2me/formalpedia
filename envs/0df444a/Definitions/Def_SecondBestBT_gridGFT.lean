-- Prove2me | Definitions.Def_SecondBestBT_gridGFT
-- name    : SecondBestBT_gridGFT
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T22:42:47.296702+00:00
-- url     : https://prove2.me/theorems/6807f178-bdb9-4982-87e6-5b41f365784b
-- title:
--   Grid gains from trade $\sum_{i,j}(t_j-t_i)x(i,j)f_S(i)f_B(j)$
-- statement:
--   The gains from trade of a grid allocation matrix $x$ under grid priors are
--   $$
--   \sum_{i,j=0}^{N}(t_j-t_i)\,x(i,j)\,f_S(i)\,f_B(j).
--   $$
-- source:
--   Liu–Qin–Ren–Wang, Second-Best Bilateral Trade is 1/2 Efficient, arXiv:2606.03849 (held version, sha256 17184930…), Corollary 3.2, p.6

import Mathlib

namespace SecondBestBT

/-- The gains from trade of a grid allocation matrix under grid priors,
`∑_{i,j=0}^N (t_j − t_i) x(i, j) f_S(i) f_B(j)` (Liu–Qin–Ren–Wang, arXiv:2606.03849, held version
sha256 17184930…, Corollary 3.2, p.6). -/
def gridGFT (t : ℕ → ℝ) (fS fB : ℕ → ℝ) (N : ℕ) (x : ℕ → ℕ → ℝ) : ℝ :=
  ∑ i ∈ Finset.range (N + 1), ∑ j ∈ Finset.range (N + 1), (t j - t i) * x i j * fS i * fB j

end SecondBestBT


