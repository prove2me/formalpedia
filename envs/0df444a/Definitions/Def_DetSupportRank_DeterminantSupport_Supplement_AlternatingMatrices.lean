-- Prove2me | Definitions.Def_DetSupportRank_DeterminantSupport_Supplement_AlternatingMatrices
-- name    : DetSupportRank_DeterminantSupport_Supplement_AlternatingMatrices
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-15T20:05:37.225202+00:00
-- url     : https://prove2.me/theorems/db5f89f9-5040-46c2-b516-6c4edfa40cdd
-- title:
--   Alternating matrices in arbitrary characteristic
-- statement:
--   A square matrix $A$ over a ring is alternating when
--   $$A_{ii}=0,\qquad A_{ji}=-A_{ij}\quad\text{for every }i,j.$$
--   The zero-diagonal condition is retained in characteristic two. This generic predicate states no Pfaffian identity and imposes no invertibility or characteristic restriction.
-- source:
--   Neil Krishnan, Guy Moshkovitz, Optimal partition rank bounds for the determinant and other multilinear polynomials, STOC 2027 submission #631 (October 2026), §4.1, alternating-matrix setting, p. 9 (PDF p. 9); https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/631.pdf

import Mathlib

noncomputable section
open scoped BigOperators

namespace DetSupportRank.DeterminantSupport.Supplement

/-- Alternation includes the zero diagonal also in characteristic two; §4.1, p.9. -/
def IsAlternating {R : Type*} [Zero R] [Neg R] {n : ℕ}
    (A : Matrix (Fin n) (Fin n) R) : Prop :=
  (∀ i, A i i = 0) ∧ ∀ i j, A j i = -A i j
end DetSupportRank.DeterminantSupport.Supplement


