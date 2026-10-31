-- Prove2me | Definitions.Def_TSPSDPGap_Amat
-- name    : TSPSDPGap_Amat
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T02:38:07.489047+00:00
-- url     : https://prove2.me/theorems/1f3077ab-b7a6-413a-9f59-6ac5c86e28dc
-- title:
--   Circulant matrix $A=\sum_{i=1}^d a_iC_i$
-- statement:
--   $$
--   A=\sum_{i=1}^{d}a_i\,C^{(n)}_i,\qquad d=n/2,
--   $$
--   a symmetric circulant $n\times n$ matrix with zero diagonal. It fills the blocks of $Y$ between distinct cities of the same group.
-- source:
--   Gutekunst & Williamson, SDP Relaxations of the TSP and Their Integrality Gaps, arXiv:1907.09054v1, §4.1, pp.14–15

import Mathlib
import Definitions.Def_TSPSDPGap_circBasis
import Definitions.Def_TSPSDPGap_coeffA

namespace TSPSDPGap

/-- **The symmetric circulant matrix `A = Σ_{i=1}^d a_i C_i`.**
Gutekunst & Williamson, *SDP Relaxations of the TSP and Their Integrality Gaps*,
arXiv:1907.09054v1, §4.1, pp.14–15: "where A = Σ_{i=1}^d a_i C_i, B = Σ_{i=1}^d b_i C_i are
symmetric circulant matrices defined in terms of parameters a_1, ..., a_d and b_1, ..., b_d."

**Formalization Note.** `C_i = C^{(n)}_i` is `circBasis n i`, `d = n/2`, and the sum runs over
`i ∈ {1, …, d}` (`Finset.Icc 1 (n / 2)`). -/
noncomputable def Amat (g n : ℕ) : Matrix (Fin n) (Fin n) ℝ :=
  ∑ i ∈ Finset.Icc 1 (n / 2), coeffA g n i • circBasis n i

end TSPSDPGap


