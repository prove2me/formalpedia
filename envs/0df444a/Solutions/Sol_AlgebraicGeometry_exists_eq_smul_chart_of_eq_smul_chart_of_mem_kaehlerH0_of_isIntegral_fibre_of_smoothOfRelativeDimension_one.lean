-- Prove2me | solution 1 for AlgebraicGeometry.exists_eq_smul_chart_of_eq_smul_chart_of_mem_kaehlerH0_of_isIntegral_fibre_of_smoothOfRelativeDimension_one
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.122355+00:00
-- url     : https://prove2.me/submissions/5eeb9103-98ed-5b9f-a221-111371c18290

import Mathlib
import Definitions.Def_AlgebraicGeometry_TwoAffineOpenCover
import Definitions.Def_AlgebraicGeometry_TwoAffineOpenCoverKaehler
import Definitions.Def_AlgebraicCurve_KaehlerToFunctionField
import Theorems.Thm_AlgebraicGeometry_Scheme_TwoAffineOpenCover_exists_baseChangeIsos_kaehlerSections
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_exists_eq_smul_chart_of_eq_smul_chart_of_mem_kaehlerH0_of_isIntegral_fibre_of_smoothOfRelativeDimension_one

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TensorProduct AlgebraicCurve
open scoped Pointwise

noncomputable section

namespace RESINJ

theorem kaehlerDifferential_map_injective_of_isFractionRing_of_flat
    (R A K : Type*) [CommRing R] [CommRing A] [IsDomain A] [Algebra R A]
    [CommRing K] [Algebra A K] [IsFractionRing A K] [Algebra R K] [IsScalarTower R A K]
    [Module.Flat A Ω[A⁄R]] :
    Function.Injective (KaehlerDifferential.map R R A K) := by
  haveI : Algebra.FormallyEtale A K := Algebra.FormallyEtale.of_isLocalization (nonZeroDivisors A)
  have hbc : IsBaseChange K (KaehlerDifferential.map R R A K) :=
    KaehlerDifferential.isBaseChange_of_formallyEtale R A K

  have hfac : ∀ m : Ω[A⁄R], KaehlerDifferential.map R R A K m = hbc.equiv ((1 : K) ⊗ₜ[A] m) := by
    intro m; rw [IsBaseChange.equiv_tmul, one_smul]

  have hinj1 : Function.Injective (fun m : Ω[A⁄R] => (1 : K) ⊗ₜ[A] m) := by
    have h := Module.Flat.rTensor_preserves_injective_linearMap (M := Ω[A⁄R]) (Algebra.linearMap A K)
      (IsFractionRing.injective A K)
    intro m m' hmm'
    have : (Algebra.linearMap A K).rTensor Ω[A⁄R] ((1 : A) ⊗ₜ[A] m) =
        (Algebra.linearMap A K).rTensor Ω[A⁄R] ((1 : A) ⊗ₜ[A] m') := by
      simpa [LinearMap.rTensor_tmul] using hmm'
    have h2 := h this
    simpa using (TensorProduct.lid A Ω[A⁄R]).congr_arg h2
  intro m m' hmm'
  rw [hfac, hfac] at hmm'
  exact hinj1 (hbc.equiv.injective hmm')

end RESINJ

namespace L4

theorem formallySmooth_algebraOfHom {R : Type u} [CommRing R] {X : Scheme.{u}} (c : X ⟶ Spec (.of R))
    [Smooth c] (U : X.Opens) (hU : IsAffineOpen U) :
    letI := Scheme.TwoAffineOpenCover.algebraOfHom c U
    Algebra.FormallySmooth R Γ(X, U) := by
  have h1 : (c.appLE ⊤ U le_top).hom.FormallySmooth :=
    (AlgebraicGeometry.Smooth.smooth_appLE (f := c)
      (AlgebraicGeometry.isAffineOpen_top (Spec (.of R))) hU le_top).formallySmooth
  have h2 : ((Scheme.ΓSpecIso (.of R)).inv ≫ c.appLE ⊤ U le_top).hom.FormallySmooth := by
    rw [CommRingCat.hom_comp]
    exact (RingHom.FormallySmooth.respectsIso.cancel_left_isIso _ _).mpr h1
  exact h2.toAlgebra

theorem kaehlerToFunctionField_injective {k : Type u} [Field k] {X : Scheme.{u}} (c : X ⟶ Spec (.of k))
    [IsIntegral X] [SmoothOfRelativeDimension 1 c] (U : X.Opens) (hU : IsAffineOpen U) [Nonempty U] :
    Function.Injective (kaehlerToFunctionField c U) := by
  letI := Scheme.TwoAffineOpenCover.algebraOfHom c U
  letI : Algebra k X.functionField := (baseToFunctionField c).toAlgebra
  haveI : IsFractionRing Γ(X, U) X.functionField := functionField_isFractionRing_of_isAffineOpen X U hU
  haveI : @IsScalarTower k Γ(X, U) X.functionField Algebra.toSMul Algebra.toSMul Algebra.toSMul :=
    IsScalarTower.of_algebraMap_eq fun r =>
      (RingHom.congr_fun (germToFunctionField_comp_algebraMap c U) r).symm
  haveI : Smooth c := SmoothOfRelativeDimension.smooth 1 c
  haveI : Algebra.FormallySmooth k Γ(X, U) := formallySmooth_algebraOfHom c U hU
  have e : ∀ z, kaehlerToFunctionField c U z = KaehlerDifferential.map k k Γ(X, U) X.functionField z := fun z =>
    KaehlerDifferential.mapOfRingHom_apply_eq_map (RingHom.id k) (X.germToFunctionField U).hom
      (germToFunctionField_comp_algebraMap c U) rfl z
  intro x y hxy
  rw [e, e] at hxy
  exact RESINJ.kaehlerDifferential_map_injective_of_isFractionRing_of_flat k Γ(X, U) X.functionField hxy

end L4

namespace CCb

theorem mem_ker_smul_top_of_one_tmul_eq_zero
    {R : Type*} [CommRing R] {κ : Type*} [Field κ] [Algebra R κ]
    (hmax : (RingHom.ker (algebraMap R κ)).IsMaximal)
    {M : Type*} [AddCommGroup M] [Module R M] (m : M) (h : (1 : κ) ⊗ₜ[R] m = 0) :
    m ∈ (RingHom.ker (algebraMap R κ)) • (⊤ : Submodule R M) := by
  classical
  set I : Ideal R := RingHom.ker (algebraMap R κ) with hI
  haveI : I.IsMaximal := hmax
  letI : Field (R ⧸ I) := Ideal.Quotient.field I
  let qk : R ⧸ I →+* κ := Ideal.Quotient.lift I (algebraMap R κ) (fun r hr => hr)
  letI : Algebra (R ⧸ I) κ := qk.toAlgebra
  haveI : IsScalarTower R (R ⧸ I) κ :=
    IsScalarTower.of_algebraMap_eq (fun r => (Ideal.Quotient.lift_mk I _ _).symm)

  have h1 : (1 : κ) ⊗ₜ[R ⧸ I] ((1 : R ⧸ I) ⊗ₜ[R] m) = 0 := by
    apply (TensorProduct.AlgebraTensorModule.cancelBaseChange R (R ⧸ I) κ κ M).injective
    rw [TensorProduct.AlgebraTensorModule.cancelBaseChange_tmul, one_smul, map_zero, h]

  have h2 : ((1 : R ⧸ I) ⊗ₜ[R] m) = 0 := by
    obtain ⟨ρ, hρ⟩ := LinearMap.exists_leftInverse_of_injective (Algebra.linearMap (R ⧸ I) κ)
      (LinearMap.ker_eq_bot.mpr qk.injective)
    have hρ1 : ρ 1 = 1 := by
      have := LinearMap.congr_fun hρ 1
      rwa [LinearMap.comp_apply, Algebra.linearMap_apply, map_one, LinearMap.id_apply] at this
    have := congrArg (fun z => TensorProduct.lid (R ⧸ I) _ (ρ.rTensor _ z)) h1
    simp only [LinearMap.rTensor_tmul, TensorProduct.lid_tmul, hρ1, one_smul, map_zero] at this
    exact this

  have h3 : (TensorProduct.quotTensorEquivQuotSMul M I) ((1 : R ⧸ I) ⊗ₜ[R] m) = 0 := by rw [h2, map_zero]
  rw [TensorProduct.quotTensorEquivQuotSMul_mk_one_tmul, Submodule.Quotient.mk_eq_zero] at h3
  exact h3

end CCb

set_option maxHeartbeats 3200000 in
theorem solution
    {R : Type u} [CommRing R] [IsDomain R] (ϖ : R) (hϖ : ϖ ≠ 0)
    (hmax : (Ideal.span {ϖ} : Ideal R).IsMaximal)
    {κ : Type u} [Field κ] (q : R →+* κ) (hker : RingHom.ker q = Ideal.span {ϖ})
    {X : Scheme.{u}} (c : X ⟶ Spec (.of R)) [SmoothOfRelativeDimension 1 c] (𝒱 : X.TwoAffineOpenCover)
    [IsIntegral (Limits.pullback c (Spec.map (CommRingCat.ofHom q)))]
    (ω : ↥((𝒱.kaehlerSections c).H0)) :
    (∀ x : X, x ∈ 𝒱.U0 → x ∈ Set.range (Limits.pullback.fst c (Spec.map (CommRingCat.ofHom q))).base →
        (∃ ω₀ : Ω[(𝒱.cover c).A0⁄R], ω.val.1 = ϖ • ω₀) → ∃ ω₁ : Ω[(𝒱.cover c).A1⁄R], ω.val.2 = ϖ • ω₁) ∧
    (∀ x : X, x ∈ 𝒱.U1 → x ∈ Set.range (Limits.pullback.fst c (Spec.map (CommRingCat.ofHom q))).base →
        (∃ ω₁ : Ω[(𝒱.cover c).A1⁄R], ω.val.2 = ϖ • ω₁) → ∃ ω₀ : Ω[(𝒱.cover c).A0⁄R], ω.val.1 = ϖ • ω₀) := by
  classical
  letI algRκ : Algebra R κ := q.toAlgebra
  have hkerA : RingHom.ker (algebraMap R κ) = Ideal.span {ϖ} := hker
  have hmaxker : (RingHom.ker (algebraMap R κ)).IsMaximal := by rw [hkerA]; exact hmax
  have hqϖ : algebraMap R κ ϖ = 0 := by
    rw [← RingHom.mem_ker, hkerA]; exact Ideal.mem_span_singleton_self ϖ

  haveI hint : IsIntegral (pullback c (Scheme.TwoAffineOpenCover.specMap R κ)) :=
    inferInstanceAs (IsIntegral (Limits.pullback c (Spec.map (CommRingCat.ofHom q))))
  set c' : pullback c (Scheme.TwoAffineOpenCover.specMap R κ) ⟶ Spec (.of κ) :=
    pullback.snd c (Scheme.TwoAffineOpenCover.specMap R κ) with hc'
  haveI : SmoothOfRelativeDimension 1 c' := by
    haveI := smoothOfRelativeDimension_isStableUnderBaseChange (n := 1)
    exact MorphismProperty.pullback_snd (P := @SmoothOfRelativeDimension 1) c _ inferInstance
  refine ⟨?_, ?_⟩
  · show ∀ x : X, x ∈ 𝒱.U0 → x ∈ Set.range (pullback.fst c (Scheme.TwoAffineOpenCover.specMap R κ)).base →
        (∃ ω₀ : Ω[(𝒱.cover c).A0⁄R], ω.val.1 = ϖ • ω₀) → ∃ ω₁ : Ω[(𝒱.cover c).A1⁄R], ω.val.2 = ϖ • ω₁
    intro x hxU hxfib hdiv
    obtain ⟨α, hα⟩ := hdiv
    obtain ⟨y, hy⟩ := hxfib

    obtain ⟨e0, e1, e01, eH0, eH1, he0, he1, he01, -, -⟩ :=
      AlgebraicGeometry.Scheme.TwoAffineOpenCover.exists_baseChangeIsos_kaehlerSections 𝒱 c κ

    have hsrc : (Scheme.TwoAffineOpenCover.HomOver.baseChange 𝒱 c κ).kaehlerMap0 ω.val.1 = 0 := by
      rw [hα, LinearMap.map_smulₛₗ, hqϖ, zero_smul]

    have hres : ((𝒱.pullback c κ).kaehlerSections c').r1
        ((Scheme.TwoAffineOpenCover.HomOver.baseChange 𝒱 c κ).kaehlerMap1 ω.val.2) = 0 := by
      rw [← Scheme.TwoAffineOpenCover.HomOver.kaehlerMap01_r1, ((TwoChartCech.Sections.mem_H0_iff _ _).mp ω.2).symm,
        Scheme.TwoAffineOpenCover.HomOver.kaehlerMap01_r0, hsrc, map_zero]

    have htgt : (Scheme.TwoAffineOpenCover.HomOver.baseChange 𝒱 c κ).kaehlerMap1 ω.val.2 = 0 := by
      by_cases hne : Nonempty (𝒱.pullback c κ).U1
      · haveI := hne
        letI := Scheme.TwoAffineOpenCover.algebraOfHom c' (𝒱.pullback c κ).U0
        letI := Scheme.TwoAffineOpenCover.algebraOfHom c' (𝒱.pullback c κ).U1
        letI := Scheme.TwoAffineOpenCover.algebraOfHom c' ((𝒱.pullback c κ).U0 ⊓ (𝒱.pullback c κ).U1)
        letI : Algebra κ (pullback c (Scheme.TwoAffineOpenCover.specMap R κ)).functionField :=
          (baseToFunctionField c').toAlgebra
        haveI : Nonempty (𝒱.pullback c κ).U0 := ⟨⟨y, show (pullback.fst c (Scheme.TwoAffineOpenCover.specMap R κ)).base y ∈ 𝒱.U0 by rw [hy]; exact hxU⟩⟩
        haveI : Nonempty ((𝒱.pullback c κ).U0 ⊓ (𝒱.pullback c κ).U1 : (pullback c (Scheme.TwoAffineOpenCover.specMap R κ)).Opens) := by
          obtain ⟨x₀⟩ := (inferInstance : Nonempty (𝒱.pullback c κ).U0)
          obtain ⟨x₁⟩ := (inferInstance : Nonempty (𝒱.pullback c κ).U1)
          obtain ⟨z, hz⟩ := nonempty_preirreducible_inter (𝒱.pullback c κ).U0.isOpen (𝒱.pullback c κ).U1.isOpen
            ⟨x₀.1, x₀.2⟩ ⟨x₁.1, x₁.2⟩
          exact ⟨⟨z, hz⟩⟩
        have key : kaehlerToFunctionField c' (𝒱.pullback c κ).U1
            ((Scheme.TwoAffineOpenCover.HomOver.baseChange 𝒱 c κ).kaehlerMap1 ω.val.2) = 0 := by
          rw [← Scheme.TwoAffineOpenCover.kaehlerToFunctionField_r1 (𝒱.pullback c κ) c', hres]
          exact LinearMap.map_zero _
        exact L4.kaehlerToFunctionField_injective c' (𝒱.pullback c κ).U1 (𝒱.pullback c κ).isAffineOpen_U1
          (key.trans (LinearMap.map_zero _).symm)
      ·
        have hU : (𝒱.pullback c κ).U1 = ⊥ := by
          ext z
          simp only [TopologicalSpace.Opens.coe_bot, Set.mem_empty_iff_false, iff_false]
          exact fun hz => hne ⟨⟨z, hz⟩⟩
        haveI : Subsingleton ((𝒱.pullback c κ).cover c').A1 := by
          show Subsingleton Γ(pullback c (Scheme.TwoAffineOpenCover.specMap R κ), (𝒱.pullback c κ).U1)
          exact CommRingCat.subsingleton_of_isTerminal ((pullback c (Scheme.TwoAffineOpenCover.specMap R κ)).sheaf.isTerminalOfEqEmpty hU)
        haveI : Subsingleton Ω[((𝒱.pullback c κ).cover c').A1⁄κ] := Module.subsingleton ((𝒱.pullback c κ).cover c').A1 _
        exact Subsingleton.elim _ _

    have h1 : (1 : κ) ⊗ₜ[R] ω.val.2 = 0 := e1.injective (by rw [he1, one_smul, htgt, map_zero])
    have hmem := CCb.mem_ker_smul_top_of_one_tmul_eq_zero hmaxker ω.val.2 h1
    rw [hkerA, Submodule.ideal_span_singleton_smul] at hmem
    obtain ⟨β, -, hβ⟩ := (Submodule.mem_smul_pointwise_iff_exists _ _ _).mp hmem
    exact ⟨β, hβ.symm⟩
  · show ∀ x : X, x ∈ 𝒱.U1 → x ∈ Set.range (pullback.fst c (Scheme.TwoAffineOpenCover.specMap R κ)).base →
        (∃ ω₁ : Ω[(𝒱.cover c).A1⁄R], ω.val.2 = ϖ • ω₁) → ∃ ω₀ : Ω[(𝒱.cover c).A0⁄R], ω.val.1 = ϖ • ω₀
    intro x hxU hxfib hdiv
    obtain ⟨α, hα⟩ := hdiv
    obtain ⟨y, hy⟩ := hxfib

    obtain ⟨e0, e1, e01, eH0, eH1, he0, he1, he01, -, -⟩ :=
      AlgebraicGeometry.Scheme.TwoAffineOpenCover.exists_baseChangeIsos_kaehlerSections 𝒱 c κ

    have hsrc : (Scheme.TwoAffineOpenCover.HomOver.baseChange 𝒱 c κ).kaehlerMap1 ω.val.2 = 0 := by
      rw [hα, LinearMap.map_smulₛₗ, hqϖ, zero_smul]

    have hres : ((𝒱.pullback c κ).kaehlerSections c').r0
        ((Scheme.TwoAffineOpenCover.HomOver.baseChange 𝒱 c κ).kaehlerMap0 ω.val.1) = 0 := by
      rw [← Scheme.TwoAffineOpenCover.HomOver.kaehlerMap01_r0, ((TwoChartCech.Sections.mem_H0_iff _ _).mp ω.2),
        Scheme.TwoAffineOpenCover.HomOver.kaehlerMap01_r1, hsrc, map_zero]

    have htgt : (Scheme.TwoAffineOpenCover.HomOver.baseChange 𝒱 c κ).kaehlerMap0 ω.val.1 = 0 := by
      by_cases hne : Nonempty (𝒱.pullback c κ).U0
      · haveI := hne
        letI := Scheme.TwoAffineOpenCover.algebraOfHom c' (𝒱.pullback c κ).U0
        letI := Scheme.TwoAffineOpenCover.algebraOfHom c' (𝒱.pullback c κ).U1
        letI := Scheme.TwoAffineOpenCover.algebraOfHom c' ((𝒱.pullback c κ).U0 ⊓ (𝒱.pullback c κ).U1)
        letI : Algebra κ (pullback c (Scheme.TwoAffineOpenCover.specMap R κ)).functionField :=
          (baseToFunctionField c').toAlgebra
        haveI : Nonempty (𝒱.pullback c κ).U1 := ⟨⟨y, show (pullback.fst c (Scheme.TwoAffineOpenCover.specMap R κ)).base y ∈ 𝒱.U1 by rw [hy]; exact hxU⟩⟩
        haveI : Nonempty ((𝒱.pullback c κ).U0 ⊓ (𝒱.pullback c κ).U1 : (pullback c (Scheme.TwoAffineOpenCover.specMap R κ)).Opens) := by
          obtain ⟨x₀⟩ := (inferInstance : Nonempty (𝒱.pullback c κ).U0)
          obtain ⟨x₁⟩ := (inferInstance : Nonempty (𝒱.pullback c κ).U1)
          obtain ⟨z, hz⟩ := nonempty_preirreducible_inter (𝒱.pullback c κ).U0.isOpen (𝒱.pullback c κ).U1.isOpen
            ⟨x₀.1, x₀.2⟩ ⟨x₁.1, x₁.2⟩
          exact ⟨⟨z, hz⟩⟩
        have key : kaehlerToFunctionField c' (𝒱.pullback c κ).U0
            ((Scheme.TwoAffineOpenCover.HomOver.baseChange 𝒱 c κ).kaehlerMap0 ω.val.1) = 0 := by
          rw [← Scheme.TwoAffineOpenCover.kaehlerToFunctionField_r0 (𝒱.pullback c κ) c', hres]
          exact LinearMap.map_zero _
        exact L4.kaehlerToFunctionField_injective c' (𝒱.pullback c κ).U0 (𝒱.pullback c κ).isAffineOpen_U0
          (key.trans (LinearMap.map_zero _).symm)
      ·
        have hU : (𝒱.pullback c κ).U0 = ⊥ := by
          ext z
          simp only [TopologicalSpace.Opens.coe_bot, Set.mem_empty_iff_false, iff_false]
          exact fun hz => hne ⟨⟨z, hz⟩⟩
        haveI : Subsingleton ((𝒱.pullback c κ).cover c').A0 := by
          show Subsingleton Γ(pullback c (Scheme.TwoAffineOpenCover.specMap R κ), (𝒱.pullback c κ).U0)
          exact CommRingCat.subsingleton_of_isTerminal ((pullback c (Scheme.TwoAffineOpenCover.specMap R κ)).sheaf.isTerminalOfEqEmpty hU)
        haveI : Subsingleton Ω[((𝒱.pullback c κ).cover c').A0⁄κ] := Module.subsingleton ((𝒱.pullback c κ).cover c').A0 _
        exact Subsingleton.elim _ _

    have h1 : (1 : κ) ⊗ₜ[R] ω.val.1 = 0 := e0.injective (by rw [he0, one_smul, htgt, map_zero])
    have hmem := CCb.mem_ker_smul_top_of_one_tmul_eq_zero hmaxker ω.val.1 h1
    rw [hkerA, Submodule.ideal_span_singleton_smul] at hmem
    obtain ⟨β, -, hβ⟩ := (Submodule.mem_smul_pointwise_iff_exists _ _ _).mp hmem
    exact ⟨β, hβ.symm⟩

end
end S_AlgebraicGeometry_exists_eq_smul_chart_of_eq_smul_chart_of_mem_kaehlerH0_of_isIntegral_fibre_of_smoothOfRelativeDimension_one
end P2MW
export P2MW.S_AlgebraicGeometry_exists_eq_smul_chart_of_eq_smul_chart_of_mem_kaehlerH0_of_isIntegral_fibre_of_smoothOfRelativeDimension_one (solution)
