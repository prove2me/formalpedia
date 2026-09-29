-- Prove2me | solution 1 for AlgebraicGeometry.exists_isOpenImmersion_of_formallySmooth_stalk_of_isFractionRing_of_isDiscreteValuationRing
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.122355+00:00
-- url     : https://prove2.me/submissions/646c0b39-e2f2-516c-ac4b-bb3dea34e066

import Mathlib
import Theorems.Thm_IsDiscreteValuationRing_bijective_algebraMap_of_flat_of_isLocalHom_of_isFractionRing
import Theorems.Thm_AlgebraicGeometry_exists_isOpenImmersion_of_isIso_stalkMap_of_locallyOfFiniteType
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_exists_isOpenImmersion_of_formallySmooth_stalk_of_isFractionRing_of_isDiscreteValuationRing

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry

universe u

namespace OpenImmNearDVR

set_option maxHeartbeats 3200000 in
set_option synthInstance.maxHeartbeats 800000 in
theorem main
    {U W : Scheme.{u}} (v : U ⟶ W) [LocallyOfFiniteType v] [IsLocallyNoetherian W]
    (x : U) [IsDomain (U.presheaf.stalk x)] [IsDiscreteValuationRing (U.presheaf.stalk x)]
    (π : W.presheaf.stalk (v.base x)) (hπ0 : π ≠ 0) (hπ : (Ideal.span {π}).IsPrime)
    (hfrac : letI : Algebra (W.presheaf.stalk (v.base x)) (FractionRing (U.presheaf.stalk x)) :=
        ((algebraMap (U.presheaf.stalk x) (FractionRing (U.presheaf.stalk x))).comp (v.stalkMap x).hom).toAlgebra
      IsFractionRing (W.presheaf.stalk (v.base x)) (FractionRing (U.presheaf.stalk x)))
    (hfs : letI : Algebra (W.presheaf.stalk (v.base x)) (U.presheaf.stalk x) := (v.stalkMap x).hom.toAlgebra
      Algebra.FormallySmooth (W.presheaf.stalk (v.base x)) (U.presheaf.stalk x)) :
    ∃ V : U.Opens, x ∈ V ∧ IsOpenImmersion (V.ι ≫ v) := by
  classical

  let O := U.presheaf.stalk x
  let O' := W.presheaf.stalk (v.base x)
  let F := FractionRing O
  let φ : O' →+* O := (v.stalkMap x).hom
  letI instOO : Algebra O' O := φ.toAlgebra
  letI instOF : Algebra O' F := ((algebraMap O F).comp φ).toAlgebra
  haveI instT : @IsScalarTower O' O F instOO.toSMul Algebra.toSMul instOF.toSMul :=
    IsScalarTower.of_algebraMap_eq fun _ => rfl
  haveI : IsFractionRing O' F := hfrac
  have hφF : Function.Injective (algebraMap O' F) := IsFractionRing.injective O' F
  have hinj : Function.Injective (algebraMap O' O) := by
    intro a b hab
    apply hφF
    change algebraMap O F (φ a) = algebraMap O F (φ b)
    exact congrArg (algebraMap O F) hab

  obtain ⟨_, ⟨U₀, hU₀, rfl⟩, hxU₀, -⟩ :=
    W.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ (v.base x)) isOpen_univ
  obtain ⟨_, ⟨V₀, hV₀, rfl⟩, hxV₀, hle⟩ :=
    U.isBasis_affineOpens.exists_subset_of_mem_open (show x ∈ v ⁻¹ᵁ U₀ from hxU₀) (v ⁻¹ᵁ U₀).2
  have e : V₀ ≤ v ⁻¹ᵁ U₀ := hle
  let A := Γ(W, U₀)
  let B := Γ(U, V₀)
  letI instAB : Algebra A B := (v.appLE U₀ V₀ e).hom.toAlgebra
  haveI : IsNoetherianRing A := IsLocallyNoetherian.component_noetherian ⟨U₀, hU₀⟩
  have hft : (v.appLE U₀ V₀ e).hom.FiniteType :=
    HasRingHomProperty.appLE (P := @LocallyOfFiniteType) v inferInstance ⟨U₀, hU₀⟩ ⟨V₀, hV₀⟩ e
  haveI : Algebra.FiniteType A B := hft
  haveI : Algebra.FinitePresentation A B := (Algebra.FinitePresentation.of_finiteType).mp inferInstance

  let 𝔓 := hV₀.primeIdealOf ⟨x, hxV₀⟩
  have hsmooth : 𝔓 ∈ Algebra.smoothLocus A B := by
    rw [← formallySmooth_stalkMap_iff U₀ hU₀ V₀ hV₀ e hxV₀]
    exact hfs
  haveI : Algebra.IsSmoothAt A 𝔓.asIdeal := hsmooth
  obtain ⟨s, hs𝔓, hsm⟩ := Algebra.IsSmoothAt.exists_notMem_smooth A 𝔓.asIdeal
  haveI := hsm

  letI instBO : Algebra B O := TopCat.Presheaf.algebra_section_stalk U.presheaf (⟨x, hxV₀⟩ : V₀)
  haveI hlocO : IsLocalization.AtPrime O 𝔓.asIdeal := hV₀.isLocalization_stalk ⟨x, hxV₀⟩

  letI instAO : Algebra A O := ((algebraMap B O).comp (algebraMap A B)).toAlgebra
  haveI : IsScalarTower A B O := IsScalarTower.of_algebraMap_eq fun _ => rfl
  letI instAO' : Algebra A O' := TopCat.Presheaf.algebra_section_stalk W.presheaf (⟨v.base x, hxU₀⟩ : U₀)
  haveI hlocO' : IsLocalization.AtPrime O' (hU₀.primeIdealOf ⟨v.base x, hxU₀⟩).asIdeal :=
    hU₀.isLocalization_stalk ⟨v.base x, hxU₀⟩
  have htower : ∀ a : A, algebraMap O' O (algebraMap A O' a) = algebraMap A O a := by
    intro a
    change (v.stalkMap x).hom ((W.presheaf.germ U₀ (v.base x) hxU₀).hom a) =
      (U.presheaf.germ V₀ x hxV₀).hom ((v.appLE U₀ V₀ e).hom a)
    rw [← CommRingCat.comp_apply, Scheme.Hom.germ_stalkMap v U₀ x hxU₀, ← CommRingCat.comp_apply,
      Scheme.Hom.appLE, Category.assoc, U.presheaf.germ_res (homOfLE e) x hxV₀]
  haveI : IsScalarTower A O' O := IsScalarTower.of_algebraMap_eq fun a => (htower a).symm

  let Bs := Localization.Away s
  let 𝔓s : Ideal Bs := Ideal.map (algebraMap B Bs) 𝔓.asIdeal
  have hdisj : Disjoint (Submonoid.powers s : Set B) ↑𝔓.asIdeal :=
    (Ideal.disjoint_powers_iff_notMem_of_isPrime s).mpr hs𝔓
  haveI h𝔓s : 𝔓s.IsPrime := IsLocalization.isPrime_of_isPrime_disjoint (Submonoid.powers s) Bs _ inferInstance hdisj
  have hcomap : 𝔓s.comap (algebraMap B Bs) = 𝔓.asIdeal :=
    IsLocalization.under_map_of_isPrime_disjoint (Submonoid.powers s) Bs inferInstance hdisj
  let O₂ := Localization.AtPrime 𝔓s
  haveI : IsLocalization.AtPrime O₂ 𝔓.asIdeal := by
    have h := IsLocalization.isLocalization_isLocalization_atPrime_isLocalization (Submonoid.powers s) O₂ 𝔓s
    convert h using 2
    exact hcomap.symm
  haveI : Module.Flat A Bs := inferInstance
  haveI : Module.Flat Bs O₂ := IsLocalization.flat O₂ 𝔓s.primeCompl
  haveI : Module.Flat A O₂ := Module.Flat.trans A Bs O₂
  let eO : O₂ ≃ₐ[B] O := IsLocalization.algEquiv 𝔓.asIdeal.primeCompl O₂ O
  haveI : Module.Flat A O :=
    Module.Flat.of_linearEquiv ((eO.restrictScalars A).toLinearEquiv).symm

  haveI : Module.Flat O' O :=
    (Module.flat_iff_of_isLocalization O' (hU₀.primeIdealOf ⟨v.base x, hxU₀⟩).asIdeal.primeCompl O).mpr inferInstance

  haveI : IsLocalHom (algebraMap O' O) := inferInstanceAs (IsLocalHom (v.stalkMap x).hom)
  have hbij : Function.Bijective (algebraMap O' O) :=
    IsDiscreteValuationRing.bijective_algebraMap_of_flat_of_isLocalHom_of_isFractionRing
      (O' := O') (O := O) (F := F) hinj π hπ0 hπ
  haveI : IsIso (v.stalkMap x) := by
    have : v.stalkMap x = (RingEquiv.ofBijective φ hbij).toCommRingCatIso.hom := by
      ext a; rfl
    rw [this]
    infer_instance
  exact AlgebraicGeometry.exists_isOpenImmersion_of_isIso_stalkMap_of_locallyOfFiniteType v x

end OpenImmNearDVR

theorem solution
    {U W : Scheme.{u}} (v : U ⟶ W) [LocallyOfFiniteType v] [IsLocallyNoetherian W]
    (x : U) [IsDomain (U.presheaf.stalk x)] [IsDiscreteValuationRing (U.presheaf.stalk x)]
    (π : W.presheaf.stalk (v.base x)) (hπ0 : π ≠ 0) (hπ : (Ideal.span {π}).IsPrime)
    (hfrac : letI : Algebra (W.presheaf.stalk (v.base x)) (FractionRing (U.presheaf.stalk x)) :=
        ((algebraMap (U.presheaf.stalk x) (FractionRing (U.presheaf.stalk x))).comp (v.stalkMap x).hom).toAlgebra
      IsFractionRing (W.presheaf.stalk (v.base x)) (FractionRing (U.presheaf.stalk x)))
    (hfs : letI : Algebra (W.presheaf.stalk (v.base x)) (U.presheaf.stalk x) := (v.stalkMap x).hom.toAlgebra
      Algebra.FormallySmooth (W.presheaf.stalk (v.base x)) (U.presheaf.stalk x)) :
    ∃ V : U.Opens, x ∈ V ∧ IsOpenImmersion (V.ι ≫ v) :=
  OpenImmNearDVR.main v x π hπ0 hπ hfrac hfs

end S_AlgebraicGeometry_exists_isOpenImmersion_of_formallySmooth_stalk_of_isFractionRing_of_isDiscreteValuationRing
end P2MW
export P2MW.S_AlgebraicGeometry_exists_isOpenImmersion_of_formallySmooth_stalk_of_isFractionRing_of_isDiscreteValuationRing (solution)
