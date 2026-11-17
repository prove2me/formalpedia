-- Prove2me | solution 1 for AlgebraicGeometry.Proj.zeroLocus_vanishingIdeal_sup_span_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:01:44.446879+00:00
-- url     : https://prove2.me/submissions/c954db9c-3ed5-46f5-9ae9-721a577e6d9e

import Mathlib
import Theorems.Thm_AlgebraicGeometry_Proj_exists_point_mem_ideal_iff_aeval

set_option autoImplicit false

noncomputable section

attribute [local instance] MvPolynomial.gradedAlgebra

open MvPolynomial

namespace AlgebraicGeometry.Proj

/-- If the coordinates in a block cover a closed projective set, their common
zero locus on its affine cone consists only of the origin. -/
theorem _root_.solution
    {K S T : Type} [Field K] [Fintype S] [Fintype T]
    (V : Set (ProjectiveSpectrum (homogeneousSubmodule S K)))
    (hV : IsClosed V) (inc : T → S)
    (hcover : ∀ x ∈ V, ∃ i : T,
      (X (inc i) : MvPolynomial S K) ∉ x.asHomogeneousIdeal) :
    ∀ z : S → AlgebraicClosure K,
      z ∈ MvPolynomial.zeroLocus (AlgebraicClosure K)
        ((ProjectiveSpectrum.vanishingIdeal V).toIdeal ⊔
          Ideal.span (Set.range (fun i : T => (X (inc i) : MvPolynomial S K)))) →
      z = 0 := by
  classical
  intro z hz
  by_contra hne
  obtain ⟨x, hhom, hideal⟩ := exists_point_mem_ideal_iff_aeval (K := K) z hne
  have hle : ProjectiveSpectrum.vanishingIdeal V ≤ x.asHomogeneousIdeal := by
    apply (hideal _).mpr
    intro p hp
    exact hz p ((show (ProjectiveSpectrum.vanishingIdeal V).toIdeal ≤ _ from le_sup_left) hp)
  have hx : x ∈ V := by
    have hx' : x ∈ ProjectiveSpectrum.zeroLocus (homogeneousSubmodule S K)
        (ProjectiveSpectrum.vanishingIdeal V : Set (MvPolynomial S K)) := hle
    rw [ProjectiveSpectrum.zeroLocus_vanishingIdeal_eq_closure, hV.closure_eq] at hx'
    exact hx'
  obtain ⟨i, hi⟩ := hcover x hx
  apply hi
  apply (hhom (X (inc i)) 1 (isHomogeneous_X K (inc i))).mpr
  exact hz _ ((show Ideal.span (Set.range (fun i : T => (X (inc i) : MvPolynomial S K))) ≤ _ from le_sup_right) (Ideal.subset_span ⟨i, rfl⟩))

end AlgebraicGeometry.Proj
