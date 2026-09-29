-- Prove2me | solution 1 for AlgebraicGeometry.flat_and_locallyOfFinitePresentation_of_isFinite_of_forall_free_localizedModule
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.553648+00:00
-- url     : https://prove2.me/submissions/82cb108c-337e-5e9f-86ad-c11af5992c7a

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_flat_and_locallyOfFinitePresentation_of_isFinite_of_forall_free_localizedModule

set_option autoImplicit false

universe u

p2m_open "CategoryTheory AlgebraicGeometry P2MW.S_AlgebraicGeometry_flat_and_locallyOfFinitePresentation_of_isFinite_of_forall_free_localizedModule.AlgebraicGeometry TopologicalSpace"

namespace AlgebraicGeometry
p2m_export "AlgebraicGeometry" "HasRingHomProperty.iff_of_isAffine IsLocallyNoetherian Scheme.mem_basicOpen Flat.of_stalkMap morphismRestrict_appTop IsFinite IsAffine Spec Scheme morphismRestrictStalkMap Flat.stalkMap Flat IsFinite.finite_app IsLocallyNoetherian.component_noetherian IsAffineOpen.isLocalization_stalk IsAffineOpen Scheme.Opens LocallyOfFinitePresentation Scheme.Opens.ι_image_top HasRingHomProperty"
namespace FlatOfFreeStalks
p2m_open "AlgebraicGeometry"

attribute [local instance] RingHomInvPair.of_ringEquiv in

theorem free_of_isLocalizedModule {R : Type*} [CommRing R] (S : Submonoid R)
    {M : Type*} [AddCommGroup M] [Module R M]
    (Rₛ : Type*) [CommRing Rₛ] [Algebra R Rₛ] [IsLocalization S Rₛ]
    {Mₛ : Type*} [AddCommGroup Mₛ] [Module R Mₛ] [Module Rₛ Mₛ] [IsScalarTower R Rₛ Mₛ]
    (f : M →ₗ[R] Mₛ) [IsLocalizedModule S f]
    [Module.Free (Localization S) (LocalizedModule S M)] : Module.Free Rₛ Mₛ := by
  set e := (IsLocalization.algEquiv S (Localization S) Rₛ).toRingEquiv
  have key : Module.Free (Localization S) (LocalizedModule S M) ↔ Module.Free Rₛ Mₛ := by
    apply Module.Free.iff_of_equiv (σ := e)
    refine { __ := IsLocalizedModule.iso S f, map_smul' := ?_ }
    intro r x
    obtain ⟨r, s, rfl⟩ := IsLocalization.exists_mk'_eq S r
    apply ((Module.End.isUnit_iff _).mp (IsLocalizedModule.map_units f s)).1
    simp only [e, AddHom.toFun_eq_coe, LinearMap.coe_toAddHom, LinearEquiv.coe_coe,
      Module.algebraMap_end_apply,
      AlgEquiv.toRingEquiv_toRingHom, RingHom.coe_coe, IsLocalization.algEquiv_apply,
      IsLocalization.map_id_mk']
    simp only [← map_smul, ← smul_assoc, IsLocalization.smul_mk'_self, algebraMap_smul]
  exact key.mp ‹_›

theorem flat_away_map {A B A' B' : Type*} [CommRing A] [CommRing B] [CommRing A'] [CommRing B']
    [Algebra A B] (r : A) [Algebra A A'] [IsLocalization.Away r A'] [Algebra B B']
    [IsLocalization.Away (algebraMap A B r) B']
    (hfree : Module.Free (Localization.Away r) (LocalizedModule (Submonoid.powers r) B)) :
    (IsLocalization.Away.map A' B' (algebraMap A B) r).Flat := by
  letI alg : Algebra A' B' := (IsLocalization.Away.map A' B' (algebraMap A B) r).toAlgebra
  letI algAB' : Algebra A B' := ((algebraMap B B').comp (algebraMap A B)).toAlgebra
  haveI : IsScalarTower A B B' := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  haveI : IsScalarTower A A' B' := IsScalarTower.of_algebraMap_eq (fun a => by
    show algebraMap B B' (algebraMap A B a) = IsLocalization.Away.map A' B' (algebraMap A B) r (algebraMap A A' a)
    rw [IsLocalization.Away.map, IsLocalization.map_eq])
  have hS : Algebra.algebraMapSubmonoid B (Submonoid.powers r) = Submonoid.powers (algebraMap A B r) := by
    simp [Algebra.algebraMapSubmonoid, Submonoid.map_powers]
  haveI : IsLocalizedModule (Submonoid.powers r) (IsScalarTower.toAlgHom A B B').toLinearMap := by
    rw [isLocalizedModule_iff_isLocalization, hS]; infer_instance
  haveI : Module.Free (Localization (Submonoid.powers r)) (LocalizedModule (Submonoid.powers r) B) := hfree
  haveI : Module.Free A' B' :=
    free_of_isLocalizedModule (Submonoid.powers r) A' (IsScalarTower.toAlgHom A B B').toLinearMap
  show Module.Flat A' B'
  infer_instance

end AlgebraicGeometry.FlatOfFreeStalks

open AlgebraicGeometry.FlatOfFreeStalks in

theorem solution
    {X Y : Scheme.{u}} (π : X ⟶ Y) [IsFinite π] [IsLocallyNoetherian Y]
    (h : ∀ y : Y, ∃ (U : Y.Opens) (hU : IsAffineOpen U) (hy : y ∈ U),
      letI := (π.app U).hom.toAlgebra
      Module.Free (Localization.AtPrime (hU.primeIdealOf ⟨y, hy⟩).asIdeal)
        (LocalizedModule (hU.primeIdealOf ⟨y, hy⟩).asIdeal.primeCompl Γ(X, π ⁻¹ᵁ U))) :
    Flat π ∧ LocallyOfFinitePresentation π := by
  classical
  refine ⟨?_, inferInstance⟩

  have key : ∀ y : Y, ∃ W : Y.Opens, Flat (π ∣_ W) ∧ y ∈ W := by
    intro y
    obtain ⟨U, hU, hyU, hfree𝔭⟩ := h y
    have hπU : IsAffineOpen (π ⁻¹ᵁ U) := hU.preimage π
    letI algAB : Algebra Γ(Y, U) Γ(X, π ⁻¹ᵁ U) := (π.app U).hom.toAlgebra
    haveI : IsNoetherianRing Γ(Y, U) := IsLocallyNoetherian.component_noetherian ⟨U, hU⟩
    haveI : Module.Finite Γ(Y, U) Γ(X, π ⁻¹ᵁ U) := IsFinite.finite_app π U hU
    haveI : Module.FinitePresentation Γ(Y, U) Γ(X, π ⁻¹ᵁ U) := Module.finitePresentation_of_finite _ _
    set 𝔭 := hU.primeIdealOf ⟨y, hyU⟩ with h𝔭
    haveI : Module.Free (Localization.AtPrime 𝔭.asIdeal) (LocalizedModule 𝔭.asIdeal.primeCompl Γ(X, π ⁻¹ᵁ U)) := hfree𝔭
    obtain ⟨r, hr, hfree, -⟩ := Module.FinitePresentation.exists_free_localizedModule_powers 𝔭.asIdeal.primeCompl
      (LocalizedModule.mkLinearMap 𝔭.asIdeal.primeCompl Γ(X, π ⁻¹ᵁ U)) (Localization.AtPrime 𝔭.asIdeal)
    refine ⟨Y.basicOpen r, ?_, ?_⟩
    · haveI : IsAffine (Y.basicOpen r) := hU.basicOpen r
      haveI : IsAffine (π ⁻¹ᵁ Y.basicOpen r) := (hU.basicOpen r).preimage π
      have hQ : ∀ W : Y.Opens, W = Y.basicOpen r → (π.app W).hom.Flat := by
        rintro W rfl
        haveI := hU.isLocalization_basicOpen r
        haveI := hπU.isLocalization_basicOpen (π.app U r)
        refine (RingHom.Flat.respectsIso.arrow_mk_iso_iff (hU.appBasicOpenIsoAwayMap π hπU r)).mpr ?_
        simp only [CommRingCat.hom_ofHom]
        exact flat_away_map r hfree
      rw [HasRingHomProperty.iff_of_isAffine (P := @Flat), morphismRestrict_appTop]
      refine (RingHom.RespectsIso.cancel_right_isIso RingHom.Flat.respectsIso _ _).mpr ?_
      exact hQ _ (Scheme.Opens.ι_image_top _)
    · letI := Y.presheaf.algebra_section_stalk (⟨y, hyU⟩ : U)
      haveI : IsLocalization.AtPrime (Y.presheaf.stalk y) 𝔭.asIdeal := hU.isLocalization_stalk ⟨y, hyU⟩
      rw [Scheme.mem_basicOpen (hx := hyU)]
      exact (IsLocalization.AtPrime.isUnit_to_map_iff (Y.presheaf.stalk y) 𝔭.asIdeal r).mpr hr

  refine Flat.of_stalkMap _ fun x => ?_
  obtain ⟨W, hW, hxW⟩ := key (π x)
  haveI : Flat (π ∣_ W) := hW
  have h1 := Flat.stalkMap (π ∣_ W) ⟨x, hxW⟩
  exact (RingHom.Flat.respectsIso.arrow_mk_iso_iff (morphismRestrictStalkMap π W ⟨x, hxW⟩)).mp h1

end S_AlgebraicGeometry_flat_and_locallyOfFinitePresentation_of_isFinite_of_forall_free_localizedModule
end P2MW
export P2MW.S_AlgebraicGeometry_flat_and_locallyOfFinitePresentation_of_isFinite_of_forall_free_localizedModule (solution)
