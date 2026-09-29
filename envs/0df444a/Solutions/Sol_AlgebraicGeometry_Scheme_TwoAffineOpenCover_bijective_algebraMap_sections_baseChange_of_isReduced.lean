-- Prove2me | solution 1 for AlgebraicGeometry.Scheme.TwoAffineOpenCover.bijective_algebraMap_sections_baseChange_of_isReduced
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.122355+00:00
-- url     : https://prove2.me/submissions/9d2cfe15-c585-5cd7-a345-f4ef3e15cb89

import Definitions.Def_AlgebraicGeometry_TwoAffineOpenCover
import Theorems.Thm_AlgebraicGeometry_Scheme_TwoAffineOpenCover_toH0_bijective
import Theorems.Thm_AlgebraicGeometry_Scheme_TwoAffineOpenCover_exists_baseChangeIsos_structureSheaf
import Theorems.Thm_TwoChartCech_exists_twoTermComplex_kerMapBaseChange_bijective
import Theorems.Thm_TwoChartCech_projective_ker_of_isReduced_of_kerMapBaseChange_bijective
import Mathlib.RingTheory.LocalProperties.Exactness
import Mathlib.RingTheory.Localization.BaseChange
import Mathlib.Algebra.Module.LocalizedModule.Basic
import Mathlib.RingTheory.Flat.Localization
import Mathlib.AlgebraicGeometry.Morphisms.Flat
import Mathlib.RingTheory.LocalRing.Module
import Mathlib.LinearAlgebra.Dimension.Free
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.RingTheory.OrzechProperty
import Mathlib.LinearAlgebra.TensorProduct.Prod
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_Scheme_TwoAffineOpenCover_bijective_algebraMap_sections_baseChange_of_isReduced

set_option autoImplicit false

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits Opposite TensorProduct

namespace AlgebraicGeometry
p2m_export "AlgebraicGeometry" "Spec.map_comp Surjective IsAffineOpen.fromSpec_top IsAffineOpen.SpecMap_appLE_fromSpec Spec Spec.map Scheme Scheme.isoSpec_Spec_inv Flat IsReduced HasRingHomProperty.Spec_iff isAffineOpen_top IsAffineOpen HasRingHomProperty geometrically Scheme.ΓSpecIso Scheme.TwoAffineOpenCover Scheme.TwoAffineOpenCover.specMap Scheme.TwoAffineOpenCover.algebraOfHom"
namespace Scheme
p2m_export "AlgebraicGeometry.Scheme" "mk Γ isoSpec_Spec_inv Opens ΓSpecIso TwoAffineOpenCover TwoAffineOpenCover.specMap TwoAffineOpenCover.algebraOfHom"
namespace TwoAffineOpenCover
p2m_export "AlgebraicGeometry.Scheme.TwoAffineOpenCover" "specMap algebraOfHom restrictAlgHom cover structureSheafSections toH0 toH0_apply_coe pullback isAffineOpen_U0 isAffineOpen_inf U1 U0 mk isAffineOpen_U1 toH0_bijective exists_baseChangeIsos_structureSheaf"
p2m_open "AlgebraicGeometry.Scheme.TwoAffineOpenCover AlgebraicGeometry.Scheme AlgebraicGeometry"

namespace PushforwardStructureSheaf

variable {R : Type u} [CommRing R] {X : Scheme.{u}} (c : X ⟶ Spec (.of R))

theorem specMap_algebraMap_eq' (U : X.Opens) (hU : IsAffineOpen U) :
    letI := algebraOfHom c U
    Spec.map (CommRingCat.ofHom (algebraMap R Γ(X, U))) = hU.fromSpec ≫ c := by
  letI := algebraOfHom c U
  have halg : (algebraMap R Γ(X, U)) = ((Scheme.ΓSpecIso (.of R)).inv ≫ c.appLE ⊤ U le_top).hom := rfl
  rw [halg, CommRingCat.ofHom_hom, Spec.map_comp, ← Scheme.isoSpec_Spec_inv, ← IsAffineOpen.fromSpec_top,
    IsAffineOpen.SpecMap_appLE_fromSpec c (isAffineOpen_top (Spec (.of R))) hU (le_top : U ≤ c ⁻¹ᵁ ⊤)]

theorem flat_sections [Flat c] (U : X.Opens) (hU : IsAffineOpen U) :
    letI := algebraOfHom c U; Module.Flat R Γ(X, U) := by
  letI := algebraOfHom c U
  have hflat : Flat (Spec.map (CommRingCat.ofHom (algebraMap R Γ(X, U)))) := by
    rw [specMap_algebraMap_eq' c U hU]; infer_instance
  exact (HasRingHomProperty.Spec_iff (P := @Flat)).mp hflat

theorem flat_prod' {M N : Type u} [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    [Module.Flat R M] [Module.Flat R N] : Module.Flat R (M × N) := by
  rw [Module.Flat.iff_rTensor_injectiveₛ]
  intro P _ _ Q
  have hM : Function.Injective (Q.subtype.rTensor M) :=
    Module.Flat.rTensor_preserves_injective_linearMap _ Q.subtype_injective
  have hN : Function.Injective (Q.subtype.rTensor N) :=
    Module.Flat.rTensor_preserves_injective_linearMap _ Q.subtype_injective
  have key : (TensorProduct.prodRight R R P M N).toLinearMap ∘ₗ (Q.subtype.rTensor (M × N))
      = ((Q.subtype.rTensor M).prodMap (Q.subtype.rTensor N)) ∘ₗ (TensorProduct.prodRight R R Q M N).toLinearMap := by
    apply TensorProduct.ext'; intro a mn; simp [TensorProduct.prodRight_tmul]
  intro x y hxy
  have hL : ((TensorProduct.prodRight R R P M N).toLinearMap ∘ₗ (Q.subtype.rTensor (M × N))) x
      = ((TensorProduct.prodRight R R P M N).toLinearMap ∘ₗ (Q.subtype.rTensor (M × N))) y := by
    simp only [LinearMap.comp_apply, hxy]
  rw [key] at hL
  simp only [LinearMap.comp_apply] at hL
  exact (TensorProduct.prodRight R R Q M N).injective ((hM.prodMap hN) hL)

theorem bijective_algebraMap_of_finrank_eq_one {B : Type u} [CommRing B] [Algebra R B] [IsLocalRing R]
    [Module.Finite R B] [Module.Free R B]
    (h1 : Module.finrank (IsLocalRing.ResidueField R) ((IsLocalRing.ResidueField R) ⊗[R] B) = 1) :
    Function.Bijective (algebraMap R B) := by
  classical
  let κ := IsLocalRing.ResidueField R
  haveI : Nontrivial (κ ⊗[R] B) := Module.nontrivial_of_finrank_pos (R := κ) (by rw [h1]; exact Nat.one_pos)
  have hne : ((1 : κ) ⊗ₜ[R] (1 : B)) ≠ 0 := by rw [← Algebra.TensorProduct.one_def]; exact one_ne_zero
  let b : Module.Basis Unit κ (κ ⊗[R] B) := FiniteDimensional.basisSingleton Unit h1 _ hne
  have hspan : Submodule.span R (Set.range fun _ : Unit => (1 : B)) = ⊤ :=
    IsLocalRing.span_eq_top_of_tmul_eq_basis (fun _ : Unit => (1 : B)) b
      (fun i => by rw [FiniteDimensional.basisSingleton_apply])
  have hsurj : Function.Surjective (algebraMap R B) := by
    intro x
    have hx : x ∈ Submodule.span R (Set.range fun _ : Unit => (1 : B)) := by rw [hspan]; trivial
    rw [Set.range_const, Submodule.mem_span_singleton] at hx
    obtain ⟨r, rfl⟩ := hx
    exact ⟨r, by rw [Algebra.smul_def, mul_one]⟩
  have hrank : Module.finrank R B = 1 := by rw [← Module.finrank_baseChange (R := κ)]; exact h1
  let e : B ≃ₗ[R] R := LinearEquiv.ofFinrankEq B R (by rw [hrank, Module.finrank_self])
  let f : R →ₗ[R] R := e.toLinearMap ∘ₗ (Algebra.linearMap R B)
  have hf : Function.Surjective f := e.surjective.comp hsurj
  have hfinj : Function.Injective f := OrzechProperty.injective_of_surjective_endomorphism f hf
  refine ⟨fun x y hxy => hfinj ?_, hsurj⟩
  show e (algebraMap R B x) = e (algebraMap R B y)
  rw [hxy]

theorem bijective_algebraMap_of_forall_finrank_eq_one {B : Type u} [CommRing B] [Algebra R B]
    [Module.Finite R B] [Module.Projective R B]
    (h1 : ∀ 𝔭 : PrimeSpectrum R, Module.finrank 𝔭.asIdeal.ResidueField (𝔭.asIdeal.ResidueField ⊗[R] B) = 1) :
    Function.Bijective (algebraMap R B) := by

  change Function.Bijective (Algebra.linearMap R B)
  refine bijective_of_isLocalized_maximal
    (fun P _ => Localization.AtPrime P) (fun P _ => Algebra.linearMap R (Localization.AtPrime P))
    (fun P _ => Localization.AtPrime P ⊗[R] B) (fun P _ => TensorProduct.mk R (Localization.AtPrime P) B 1)
    (Algebra.linearMap R B) ?_
  intro P hP
  let R' := Localization.AtPrime P

  haveI : Module.Finite R' (R' ⊗[R] B) := inferInstance
  haveI : Module.Projective R' (R' ⊗[R] B) := inferInstance
  haveI : Module.Flat R' (R' ⊗[R] B) := inferInstance
  haveI : Module.Free R' (R' ⊗[R] B) := Module.free_of_flat_of_isLocalRing
  have hdim : Module.finrank (IsLocalRing.ResidueField R') ((IsLocalRing.ResidueField R') ⊗[R'] (R' ⊗[R] B)) = 1 := by
    rw [(TensorProduct.AlgebraTensorModule.cancelBaseChange R R' (IsLocalRing.ResidueField R')
      (IsLocalRing.ResidueField R') B).finrank_eq]
    exact h1 ⟨P, hP.isPrime⟩
  have hloc : Function.Bijective (algebraMap R' (R' ⊗[R] B)) := bijective_algebraMap_of_finrank_eq_one hdim

  have hmap : (IsLocalizedModule.map P.primeCompl (Algebra.linearMap R (Localization.AtPrime P))
      (TensorProduct.mk R (Localization.AtPrime P) B 1)) (Algebra.linearMap R B)
      = (Algebra.linearMap R' (R' ⊗[R] B)).restrictScalars R := by
    apply IsLocalizedModule.ext P.primeCompl (Algebra.linearMap R (Localization.AtPrime P))
      (IsLocalizedModule.map_units (TensorProduct.mk R (Localization.AtPrime P) B 1))
    rw [IsLocalizedModule.map_comp]
    ext
    simp [Algebra.algebraMap_eq_smul_one]
    rw [Algebra.linearMap_apply, map_one, Algebra.TensorProduct.one_def]
  rw [hmap]
  exact hloc

end PushforwardStructureSheaf

open PushforwardStructureSheaf

theorem bijective_algebraMap_sections_baseChange_of_isReduced'
    {R : Type u} [CommRing R] [IsNoetherianRing R] [_root_.IsReduced R]
    {X : Scheme.{u}} (𝒱 : X.TwoAffineOpenCover) (c : X ⟶ Spec (.of R)) [Flat c]
    (hfin : Module.Finite R (𝒱.structureSheafSections c).H0 ∧ Module.Finite R (𝒱.structureSheafSections c).H1)
    (hH0 : ∀ (K : Type u) [Field K] [Algebra R K],
      Module.finrank K (LinearMap.ker ((𝒱.structureSheafSections c).cechDiff.baseChange K)) = 1)
    (A : Type u) [CommRing A] [Algebra R A] :
    letI := algebraOfHom (Limits.pullback.snd c (specMap R A)) ⊤
    Function.Bijective (algebraMap A Γ(Limits.pullback c (specMap R A), ⊤)) := by
  classical
  letI instA := algebraOfHom (Limits.pullback.snd c (specMap R A)) ⊤

  set S := 𝒱.structureSheafSections c with hS
  haveI : Module.Flat R (𝒱.cover c).A0 := flat_sections c 𝒱.U0 𝒱.isAffineOpen_U0
  haveI : Module.Flat R (𝒱.cover c).A1 := flat_sections c 𝒱.U1 𝒱.isAffineOpen_U1
  haveI : Module.Flat R (𝒱.cover c).A01 := flat_sections c (𝒱.U0 ⊓ 𝒱.U1) 𝒱.isAffineOpen_inf
  haveI : Module.Flat R (S.M0 × S.M1) := flat_prod'
  haveI : Module.Flat R S.M01 := inferInstanceAs (Module.Flat R (𝒱.cover c).A01)
  haveI : Module.Finite R (LinearMap.ker S.cechDiff) := hfin.1
  haveI : Module.Finite R (S.M01 ⧸ LinearMap.range S.cechDiff) := hfin.2
  obtain ⟨G, ι0, ι1, comm, hG⟩ := TwoChartCech.exists_twoTermComplex_kerMapBaseChange_bijective S.cechDiff
  obtain ⟨hproj, hbc, hrank⟩ :=
    TwoChartCech.projective_ker_of_isReduced_of_kerMapBaseChange_bijective G ι0 ι1 comm hG (n := 1)
      (fun 𝔭 => hH0 𝔭.asIdeal.ResidueField)

  letI instB := algebraOfHom c ⊤
  let eB : Γ(X, ⊤) ≃ₗ[R] S.H0 := LinearEquiv.ofBijective (𝒱.toH0 c) (toH0_bijective 𝒱 c)
  haveI : Module.Finite R Γ(X, ⊤) := Module.Finite.equiv eB.symm
  haveI : Module.Projective R Γ(X, ⊤) := Module.Projective.of_equiv eB.symm

  have hdim : ∀ 𝔭 : PrimeSpectrum R,
      Module.finrank 𝔭.asIdeal.ResidueField (𝔭.asIdeal.ResidueField ⊗[R] Γ(X, ⊤)) = 1 := by
    intro 𝔭
    rw [(eB.baseChange R 𝔭.asIdeal.ResidueField _ _).finrank_eq]
    exact hrank 𝔭
  have hB : Function.Bijective (algebraMap R Γ(X, ⊤)) := bijective_algebraMap_of_forall_finrank_eq_one hdim

  obtain ⟨e0, e1, e01, eH0, eH1, he0, he1, he01, heH0, -⟩ := exists_baseChangeIsos_structureSheaf 𝒱 c A
  have hA : Function.Bijective (letI := algebraOfHom (Limits.pullback.snd c (specMap R A)) ⊤;
      (𝒱.pullback c A).toH0 (Limits.pullback.snd c (specMap R A))) := toH0_bijective _ _

  let u : S.H0 := 𝒱.toH0 c 1
  have hu : (u : S.M0 × S.M1)
      = ((X.presheaf.map (homOfLE (le_top : 𝒱.U0 ≤ ⊤)).op).hom 1,
          (X.presheaf.map (homOfLE (le_top : 𝒱.U1 ≤ ⊤)).op).hom 1) := toH0_apply_coe 𝒱 c 1

  let eR : R ≃ₗ[R] S.H0 :=
    LinearEquiv.ofBijective ((𝒱.toH0 c) ∘ₗ Algebra.linearMap R Γ(X, ⊤)) ((toH0_bijective 𝒱 c).comp hB)
  have heR : eR 1 = u := by
    show 𝒱.toH0 c (algebraMap R Γ(X, ⊤) 1) = 𝒱.toH0 c 1
    rw [RingHom.map_one]
  let ι : A → A ⊗[R] S.H0 := fun a => a ⊗ₜ[R] u
  have hιbij : Function.Bijective ι := by
    have hι : ι = (eR.baseChange R A _ _) ∘ (TensorProduct.rid R A).symm := by
      funext a
      show a ⊗ₜ[R] u = (eR.baseChange R A _ _) ((TensorProduct.rid R A).symm a)
      rw [TensorProduct.rid_symm_apply, LinearEquiv.baseChange_tmul, heR]
    rw [hι]
    exact (eR.baseChange R A _ _).bijective.comp (TensorProduct.rid R A).symm.bijective

  have hE0 : ∀ a : A, e0 (a ⊗ₜ[R] ((X.presheaf.map (homOfLE (le_top : 𝒱.U0 ≤ ⊤)).op).hom 1))
      = algebraMap A ((𝒱.pullback c A).cover (Limits.pullback.snd c (specMap R A))).A0 a := by
    intro a
    have hsm : ∀ x : (𝒱.cover c).A0, a ⊗ₜ[R] x = a • ((1 : A) ⊗ₜ[R] x) := fun x => by
      rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
    rw [hsm, map_smul, he0, map_one, map_one, Algebra.smul_def]
    exact mul_one _
  have hE1 : ∀ a : A, e1 (a ⊗ₜ[R] ((X.presheaf.map (homOfLE (le_top : 𝒱.U1 ≤ ⊤)).op).hom 1))
      = algebraMap A ((𝒱.pullback c A).cover (Limits.pullback.snd c (specMap R A))).A1 a := by
    intro a
    have hsm : ∀ x : (𝒱.cover c).A1, a ⊗ₜ[R] x = a • ((1 : A) ⊗ₜ[R] x) := fun x => by
      rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
    rw [hsm, map_smul, he1, map_one, map_one, Algebra.smul_def]
    exact mul_one _

  have key : ∀ a : A,
      (letI := algebraOfHom (Limits.pullback.snd c (specMap R A)) ⊤;
        (𝒱.pullback c A).toH0 (Limits.pullback.snd c (specMap R A))
          (algebraMap A Γ(Limits.pullback c (specMap R A), ⊤) a))
        = eH0 (TwoChartCech.kerBaseChangeHom S.cechDiff A (ι a)) := by
    intro a
    letI := algebraOfHom (Limits.pullback.snd c (specMap R A)) ⊤
    letI := algebraOfHom (Limits.pullback.snd c (specMap R A)) (𝒱.pullback c A).U0
    letI := algebraOfHom (Limits.pullback.snd c (specMap R A)) (𝒱.pullback c A).U1
    apply Subtype.ext
    rw [heH0, toH0_apply_coe, TwoChartCech.kerBaseChangeHom_apply_coe]
    show _ = (e0 (TensorProduct.prodRight R A A _ _ (((LinearMap.ker S.cechDiff).subtype.baseChange A) (a ⊗ₜ[R] u))).1,
      e1 (TensorProduct.prodRight R A A _ _ (((LinearMap.ker S.cechDiff).subtype.baseChange A) (a ⊗ₜ[R] u))).2)
    rw [LinearMap.baseChange_tmul, Submodule.subtype_apply, hu, TensorProduct.prodRight_tmul, hE0, hE1]
    exact Prod.ext
      ((restrictAlgHom (Limits.pullback.snd c (specMap R A)) (le_top : (𝒱.pullback c A).U0 ≤ ⊤)).commutes a)
      ((restrictAlgHom (Limits.pullback.snd c (specMap R A)) (le_top : (𝒱.pullback c A).U1 ≤ ⊤)).commutes a)

  have hcomp : (letI := algebraOfHom (Limits.pullback.snd c (specMap R A)) ⊤;
      ((𝒱.pullback c A).toH0 (Limits.pullback.snd c (specMap R A)))
        ∘ (algebraMap A Γ(Limits.pullback c (specMap R A), ⊤)))
      = eH0 ∘ (TwoChartCech.kerBaseChangeHom S.cechDiff A) ∘ ι := funext key
  have hbij : Function.Bijective (letI := algebraOfHom (Limits.pullback.snd c (specMap R A)) ⊤;
      ((𝒱.pullback c A).toH0 (Limits.pullback.snd c (specMap R A)))
        ∘ (algebraMap A Γ(Limits.pullback c (specMap R A), ⊤))) := by
    rw [hcomp]; exact eH0.bijective.comp ((hbc A).comp hιbij)
  exact (Function.Bijective.of_comp_iff' hA _).mp hbij

end AlgebraicGeometry.Scheme.TwoAffineOpenCover

open _root_.AlgebraicGeometry _root_.P2MW.S_AlgebraicGeometry_Scheme_TwoAffineOpenCover_bijective_algebraMap_sections_baseChange_of_isReduced.AlgebraicGeometry in
theorem solution
    {R : Type u} [CommRing R] [IsNoetherianRing R] [_root_.IsReduced R]
    {X : Scheme.{u}} (𝒱 : X.TwoAffineOpenCover) (c : X ⟶ Spec (.of R)) [Flat c]
    (hfin : Module.Finite R (𝒱.structureSheafSections c).H0 ∧ Module.Finite R (𝒱.structureSheafSections c).H1)
    (hH0 : ∀ (K : Type u) [Field K] [Algebra R K],
      Module.finrank K (LinearMap.ker ((𝒱.structureSheafSections c).cechDiff.baseChange K)) = 1)
    (A : Type u) [CommRing A] [Algebra R A] :
    letI := Scheme.TwoAffineOpenCover.algebraOfHom
      (Limits.pullback.snd c (Scheme.TwoAffineOpenCover.specMap R A)) ⊤
    Function.Bijective (algebraMap A Γ(Limits.pullback c (Scheme.TwoAffineOpenCover.specMap R A), ⊤)) :=
  AlgebraicGeometry.Scheme.TwoAffineOpenCover.bijective_algebraMap_sections_baseChange_of_isReduced' 𝒱 c hfin hH0 A

end

end S_AlgebraicGeometry_Scheme_TwoAffineOpenCover_bijective_algebraMap_sections_baseChange_of_isReduced
end P2MW
export P2MW.S_AlgebraicGeometry_Scheme_TwoAffineOpenCover_bijective_algebraMap_sections_baseChange_of_isReduced (solution)
