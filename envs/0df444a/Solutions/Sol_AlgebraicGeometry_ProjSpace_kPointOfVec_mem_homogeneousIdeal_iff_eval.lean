-- Prove2me | solution 1 for AlgebraicGeometry.ProjSpace.kPointOfVec_mem_homogeneousIdeal_iff_eval
-- status  : ACCEPTED   (prove)
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:09:27.60023+00:00
-- url     : https://prove2.me/submissions/efd0676f-9db2-4776-882d-649b0d27890f

import Mathlib
import Definitions.Def_AlgebraicGeometry_ProjSpacePoints
import Theorems.Thm_AlgebraicGeometry_ProjSpace_kPointOfVec_mem_iff_eval

set_option autoImplicit false

noncomputable section

attribute [local instance] MvPolynomial.gradedAlgebra

open CategoryTheory AlgebraicGeometry HomogeneousLocalization MvPolynomial

namespace AlgebraicGeometry.ProjSpace

/-- Containment in the prime of a coordinate point is equivalent to vanishing
of every polynomial in a homogeneous ideal on its representative vector. -/
theorem _root_.solution {K : Type} [Field K] {N : ℕ}
    (z : Fin (N + 1) → K) (hz : z ≠ 0)
    (I : HomogeneousIdeal (homogeneousSubmodule (Fin (N + 1)) K)) :
    I ≤ ((kPointOfVec K N z hz).1 (IsLocalRing.closedPoint K)).asHomogeneousIdeal ↔
      ∀ p ∈ I.toIdeal, eval z p = 0 := by
  constructor
  · intro h p hp
    rw [← sum_homogeneousComponent p, map_sum]
    apply Finset.sum_eq_zero
    intro d hd
    apply (kPointOfVec_mem_iff_eval z hz _ d (homogeneousComponent_isHomogeneous d p)).mp
    exact h (homogeneousComponent_mem_of_mem I.isHomogeneous hp d)
  · intro h p hp
    apply (mem_iff_homogeneousComponent_mem
      ((kPointOfVec K N z hz).1 (IsLocalRing.closedPoint K)).asHomogeneousIdeal.isHomogeneous p).mpr
    intro d
    apply (kPointOfVec_mem_iff_eval z hz _ d (homogeneousComponent_isHomogeneous d p)).mpr
    exact h _ (homogeneousComponent_mem_of_mem I.isHomogeneous hp d)

end AlgebraicGeometry.ProjSpace
