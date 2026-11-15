-- Prove2me | solution 1 for AlgebraicGeometry.exists_regular_integral_projective_finite_cover_of_dimension_le_one
-- status  : ACCEPTED   (prove)
-- author  : @tomasz
-- created : 2026-11-14T18:07:40.75398+00:00
-- url     : https://prove2.me/submissions/30d0ad21-d92a-4f6a-82e4-f86424c34ea8

import Mathlib
import Definitions.Def_AlgebraicGeometry_ProjSpace
import Theorems.Thm_AlgebraicGeometry_exists_normal_integral_projective_finite_cover

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
set_option linter.style.haveILetI false
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
universe u
attribute [local instance] MvPolynomial.gradedAlgebra

namespace PhilipponRegularProjectiveCurveAlteration

-- These two proofs reuse PhilipponCurveAlteration's local argument,
-- without importing its algebraically closed smooth-cover theorem.
lemma regularLocalRing_of_integrallyClosed_of_dimension_le_one
    (R : Type*) [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    [IsDomain R] [IsIntegrallyClosed R] (hdim : ringKrullDim R ≤ 1) :
    IsRegularLocalRing R := by
  letI : Ring.KrullDimLE 1 R := Ring.krullDimLE_iff.mpr hdim
  have hprime : ∀ P : Ideal R, P ≠ ⊥ → P.IsPrime → P = IsLocalRing.maximalIdeal R := by
    intro P hP hp
    exact IsLocalRing.eq_maximalIdeal (hp.isMaximal_of_ne_bot hP)
  have hT : IsPrincipalIdealRing R ↔
      (IsIntegrallyClosed R ∧ ∀ P : Ideal R, P ≠ ⊥ → P.IsPrime → P = IsLocalRing.maximalIdeal R) :=
    (tfae_of_isNoetherianRing_of_isLocalRing_of_isDomain R).out 0 3
  letI : IsPrincipalIdealRing R := hT.mpr ⟨inferInstance, hprime⟩
  infer_instance

lemma stalk_dimension_le_topological {X : Scheme.{u}} (x : X) :
    ringKrullDim (X.presheaf.stalk x) ≤ topologicalKrullDim X := by
  rw [ringKrullDim_stalk_eq_coheight]
  exact (Order.coheight_le_krullDim x).trans_eq
    (Order.krullDim_eq_of_orderIso (irreducibleSetEquivPoints (α := X))).symm

/-- Normalization proves the full regular projective alteration conclusion
in dimension at most one over an arbitrary field. The map is finite everywhere. -/
theorem exists_cover
    (K : Type u) [Field K] {X : Scheme.{u}} [IsIntegral X]
    (π : X ⟶ Spec (.of K))
    (n : ℕ) (ι : X ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) K))
    [IsClosedImmersion ι] (hι : ι ≫ ProjSpace.π K n = π)
    (hdim : topologicalKrullDim X ≤ 1) :
    ∃ (Y : Scheme.{u}) (a : Y ⟶ X),
      IsIntegral Y ∧ IsFinite a ∧ Surjective a ∧
      (∀ y : Y, IsRegularLocalRing (Y.presheaf.stalk y)) ∧
      topologicalKrullDim Y = topologicalKrullDim X ∧
      ∃ (m : ℕ) (j : Y ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (m + 1)) K)),
        IsClosedImmersion j ∧ j ≫ ProjSpace.π K m = a ≫ π := by
  haveI : IsProper π := by rw [← hι]; infer_instance
  obtain ⟨Y, a, hY, hnormal, hfinite, hsurj, hdimY, m, j, hj, hjbase⟩ :=
    AlgebraicGeometry.exists_normal_integral_projective_finite_cover K π n ι hι
  letI := hY
  letI := hfinite
  letI : IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian (a ≫ π)
  have hreg : ∀ y : Y, IsRegularLocalRing (Y.presheaf.stalk y) := by
    intro y
    letI := hnormal y
    apply regularLocalRing_of_integrallyClosed_of_dimension_le_one
    exact (stalk_dimension_le_topological y).trans (hdimY.trans_le hdim)
  exact ⟨Y, a, hY, hfinite, hsurj, hreg, hdimY, m, j, hj, hjbase⟩

/-- The finite normalization supplies every clause of the frontier
alteration statement, including its explicit nonempty finite locus. -/
theorem exists_alteration
    (K : Type u) [Field K] {X : Scheme.{u}} [IsIntegral X]
    (π : X ⟶ Spec (.of K))
    (n : ℕ) (ι : X ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) K))
    [IsClosedImmersion ι] (hι : ι ≫ ProjSpace.π K n = π)
    (hdim : topologicalKrullDim X ≤ 1) :
    ∃ (Y : Scheme.{u}) (a : Y ⟶ X),
      IsIntegral Y ∧ IsProper a ∧ Surjective a ∧
      (∀ y : Y, IsRegularLocalRing (Y.presheaf.stalk y)) ∧
      (∃ V : X.Opens, Nonempty V ∧ IsFinite (a ∣_ V)) ∧
      ∃ (m : ℕ) (j : Y ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (m + 1)) K)),
        IsClosedImmersion j ∧ j ≫ ProjSpace.π K m = a ≫ π := by
  obtain ⟨Y, a, hY, hfinite, hsurj, hreg, _, m, j, hj, hjbase⟩ :=
    exists_cover K π n ι hι hdim
  letI := hfinite
  refine ⟨Y, a, hY, inferInstance, hsurj, hreg,
    ⟨⊤, ?_, inferInstance⟩, m, j, hj, hjbase⟩
  obtain ⟨x⟩ := (inferInstance : Nonempty X)
  exact ⟨⟨x, trivial⟩⟩

end PhilipponRegularProjectiveCurveAlteration

#print axioms PhilipponRegularProjectiveCurveAlteration.regularLocalRing_of_integrallyClosed_of_dimension_le_one
#print axioms PhilipponRegularProjectiveCurveAlteration.stalk_dimension_le_topological
#print axioms PhilipponRegularProjectiveCurveAlteration.exists_cover
#print axioms PhilipponRegularProjectiveCurveAlteration.exists_alteration

theorem solution
    (K : Type u) [Field K] {X : Scheme.{u}} [IsIntegral X]
    (π : X ⟶ Spec (.of K))
    (n : ℕ) (ι : X ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) K))
    [IsClosedImmersion ι] (hι : ι ≫ ProjSpace.π K n = π)
    (hdim : topologicalKrullDim X ≤ 1) :
    ∃ (Y : Scheme.{u}) (a : Y ⟶ X),
      IsIntegral Y ∧ IsFinite a ∧ Surjective a ∧
      (∀ y : Y, IsRegularLocalRing (Y.presheaf.stalk y)) ∧
      topologicalKrullDim Y = topologicalKrullDim X ∧
      ∃ (m : ℕ) (j : Y ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (m + 1)) K)),
        IsClosedImmersion j ∧ j ≫ ProjSpace.π K m = a ≫ π := by
  exact PhilipponRegularProjectiveCurveAlteration.exists_cover K π n ι hι hdim

#print axioms solution
