-- Prove2me | Definitions.Def_SecondBestBT_gridInterimB
-- name    : SecondBestBT_gridInterimB
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T22:42:45.437563+00:00
-- url     : https://prove2.me/theorems/08f68dfa-ab01-4286-9912-6f5134cccf9c
-- title:
--   Grid buyer interim $x_B(j)=\sum_i f_S(i)x(i,j)$
-- statement:
--   For a grid allocation matrix $x(i,j)$ (seller index $i$, buyer index $j$) and seller masses $f_S$, the buyer's interim allocation at grid index $j$ is
--   $$
--   x_B(j)=\sum_{i=0}^{N} f_S(i)\,x(i,j).
--   $$
-- source:
--   Liu–Qin–Ren–Wang, Second-Best Bilateral Trade is 1/2 Efficient, arXiv:2606.03849 (held version, sha256 17184930…), Section 3, p.6

import Mathlib

namespace SecondBestBT

/-- The buyer's interim allocation of a grid allocation matrix,
`x_B(j) = ∑_{i=0}^N f_S(i) x(i, j)` (Liu–Qin–Ren–Wang, arXiv:2606.03849, held version sha256
17184930…, Section 3, p.6; with `N = W`, also the interim of Section 4.1, p.8).

**Formalization Note** A grid allocation is a matrix `x : ℕ → ℕ → ℝ` indexed by (seller index,
buyer index); only the entries with both indices at most `N` are used. -/
def gridInterimB (fS : ℕ → ℝ) (N : ℕ) (x : ℕ → ℕ → ℝ) (j : ℕ) : ℝ :=
  ∑ i ∈ Finset.range (N + 1), fS i * x i j

end SecondBestBT


