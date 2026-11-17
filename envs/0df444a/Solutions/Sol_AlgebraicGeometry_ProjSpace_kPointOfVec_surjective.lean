-- Prove2me | solution 1 for AlgebraicGeometry.ProjSpace.kPointOfVec_surjective
-- status  : ACCEPTED   (prove)
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:09:28.246061+00:00
-- url     : https://prove2.me/submissions/9d8b569e-1b93-46da-a19c-cf2405e8e7e9

import Mathlib
import Theorems.Thm_AlgebraicGeometry_ProjSpace_kPointOfVec_eq_of_chart
import Definitions.Def_AlgebraicGeometry_ProjSpacePoints

set_option autoImplicit false

noncomputable section

attribute [local instance] MvPolynomial.gradedAlgebra

open CategoryTheory AlgebraicGeometry NeronModelInfra

namespace AlgebraicGeometry

theorem _root_.solution (K : Type) [Field K] (N : ℕ)
    (x : Scheme.KPoint (ProjSpace.π K N)) :
    ∃ (v : Fin (N + 1) → K) (hv : v ≠ 0), ProjSpace.kPointOfVec K N v hv = x := by
  classical
  let p : Spec (CommRingCat.of K) := IsLocalRing.closedPoint K
  have hcover := Proj.iSup_basicOpen_eq_top
    (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) K)
    (fun i : Fin (N + 1) => MvPolynomial.X i) (ProjSpace.irrelevant_le_span_X K N)
  have hp : x.1 p ∈ (⨆ i : Fin (N + 1), Proj.basicOpen
      (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) K) (MvPolynomial.X i)) := by
    rw [hcover]
    trivial
  obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.mp hp
  let ι := Proj.awayι (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) K)
    (MvPolynomial.X i) (ProjSpace.X_mem_one K N i) one_pos
  have hrange : Set.range x.1.base ⊆ Set.range ι.base := by
    rintro y ⟨q, rfl⟩
    have hq : q = p := Subsingleton.elim _ _
    subst q
    change x.1 p ∈ ι.opensRange
    rw [Proj.opensRange_awayι]
    exact hi
  let g := IsOpenImmersion.lift ι x.1 hrange
  obtain ⟨φ, hφ⟩ := Spec.map_surjective g
  have hx : x.1 = Spec.map φ ≫ ι := by
    rw [hφ]
    exact (IsOpenImmersion.lift_fac ι x.1 hrange).symm
  let v : Fin (N + 1) → K := fun j => φ.hom (ProjSpace.ratio K N i j)
  have hvi : v i = 1 := by simp [v, ProjSpace.ratio_self]
  have hv : v ≠ 0 := by
    intro h
    have : (0 : K) = 1 := by simpa [h] using hvi
    exact zero_ne_one this
  refine ⟨v, hv, ProjSpace.kPointOfVec_eq_of_chart x v hv i ?_ φ.hom ?_ hx⟩
  · rw [hvi]
    exact one_ne_zero
  · intro j
    simp only [hvi, div_one]
    rfl

end AlgebraicGeometry
