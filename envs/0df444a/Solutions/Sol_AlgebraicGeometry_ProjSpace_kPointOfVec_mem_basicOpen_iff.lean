-- Prove2me | solution 1 for AlgebraicGeometry.ProjSpace.kPointOfVec_mem_basicOpen_iff
-- status  : ACCEPTED   (prove)
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:07:47.604104+00:00
-- url     : https://prove2.me/submissions/60d89466-1a1b-4107-bf4d-494ca6513c98

import Mathlib
import Theorems.Thm_AlgebraicGeometry_ProjSpace_kPointOfVec_chart
import Definitions.Def_AlgebraicGeometry_ProjSpacePoints

set_option autoImplicit false

noncomputable section

attribute [local instance] MvPolynomial.gradedAlgebra

open CategoryTheory AlgebraicGeometry NeronModelInfra HomogeneousLocalization

namespace AlgebraicGeometry.ProjSpace

/-- A homogeneous coordinate is nonzero precisely on its standard chart. -/
theorem _root_.solution (K : Type) [Field K] (N : ℕ)
    (v : Fin (N + 1) → K) (hv : v ≠ 0) (i : Fin (N + 1)) :
    (kPointOfVec K N v hv).1 (IsLocalRing.closedPoint K) ∈
      Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) K)
        (MvPolynomial.X i) ↔ v i ≠ 0 := by
  classical
  obtain ⟨j, hj⟩ : ∃ j, v j ≠ 0 := by
    by_contra h
    apply hv
    funext j
    exact not_ne_iff.mp (fun hj => h ⟨j, hj⟩)
  obtain ⟨φ, hφ, hpoint⟩ := kPointOfVec_chart K N v hv j hj
  have helem : Away.isLocalizationElem (X_mem_one K N j) (X_mem_one K N i) =
      ratio K N j i := by
    apply HomogeneousLocalization.val_injective
    simp [ratio, Away.val_mk]
  have hpre := Proj.awayι_preimage_basicOpen
    (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) K)
    (X_mem_one K N j) one_pos (X_mem_one K N i) one_pos
  rw [helem] at hpre
  change IsLocalRing.closedPoint K ∈ (kPointOfVec K N v hv).1 ⁻¹ᵁ
    Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) K)
      (MvPolynomial.X i) ↔ v i ≠ 0
  rw [hpoint, Scheme.Hom.comp_preimage, hpre]
  change φ (ratio K N j i) ∉ IsLocalRing.maximalIdeal K ↔ v i ≠ 0
  simp [hφ, IsLocalRing.mem_maximalIdeal, hj]

end AlgebraicGeometry.ProjSpace
