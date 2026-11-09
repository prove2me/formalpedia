-- Prove2me | Definitions.Def_OddPermSum_Evaluation_crossedSum
-- name    : OddPermSum_Evaluation_crossedSum
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T07:09:25.875359+00:00
-- url     : https://prove2.me/theorems/502c9610-21e3-447a-bdb4-42f49759d45c
-- title:
--   Crossed sum
-- statement:
--   For square matrices $A,B$ of equal order over a commutative ring, set
--
--   $$T(A,B)=\sum_{i<j,\ k>l}A_{i,k}B_{k,j}A_{j,l}B_{l,i}.$$
--
--   The source uses $B=A^{-1}$ for invertible $A$. The definition separates this ordered four-index sum from its evaluation algorithm; it is zero for orders zero and one.
-- source:
--   Boxuan Chen, Bin Cui, Hanqing Li, Xupeng Miao, Haoze Wang, STOC 2027 submission #716 (October 2026), p. 6, Eq. (3.5)

import Mathlib

set_option autoImplicit false

namespace OddPermSum.Evaluation

/-- Section 3.1, (3.5), with the row and column inequalities in their source directions. -/
noncomputable def crossedSum {R : Type*} [CommRing R] {n : ℕ}
    (A B : Matrix (Fin n) (Fin n) R) : R :=
  ∑ i, ∑ j, ∑ k, ∑ l, if i < j ∧ l < k then A i k * B k j * A j l * B l i else 0

end OddPermSum.Evaluation


