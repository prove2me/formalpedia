-- Prove2me | Definitions.Def_TSPSDPGap_Bmat
-- name    : TSPSDPGap_Bmat
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T02:39:19.394065+00:00
-- url     : https://prove2.me/theorems/540a1fa7-a7c7-4da8-b501-a03cccfd9d05
-- title:
--   Circulant matrix $B=\sum_{i=1}^d b_iC_i$
-- statement:
--   $$
--   B=\sum_{i=1}^{d}b_i\,C^{(n)}_i,\qquad d=n/2,
--   $$
--   a symmetric circulant $n\times n$ matrix with zero diagonal. It fills the blocks of $Y$ between cities of different groups.
-- source:
--   Gutekunst & Williamson, SDP Relaxations of the TSP and Their Integrality Gaps, arXiv:1907.09054v1, §4.1, pp.14–15

import Mathlib
import Definitions.Def_TSPSDPGap_circBasis
import Definitions.Def_TSPSDPGap_coeffB

namespace TSPSDPGap

/-- **The symmetric circulant matrix `B = Σ_{i=1}^d b_i C_i`.**
Gutekunst & Williamson, *SDP Relaxations of the TSP and Their Integrality Gaps*,
arXiv:1907.09054v1, §4.1, pp.14–15: "where A = Σ_{i=1}^d a_i C_i, B = Σ_{i=1}^d b_i C_i are
symmetric circulant matrices defined in terms of parameters a_1, ..., a_d and b_1, ..., b_d."

**Formalization Note.** `C_i = C^{(n)}_i` is `circBasis n i`, `d = n/2`, and the sum runs over
`i ∈ {1, …, d}` (`Finset.Icc 1 (n / 2)`). -/
noncomputable def Bmat (g n : ℕ) : Matrix (Fin n) (Fin n) ℝ :=
  ∑ i ∈ Finset.Icc 1 (n / 2), coeffB g n i • circBasis n i

end TSPSDPGap


