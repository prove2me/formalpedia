-- Prove2me | solution 1 for AutomorphicForm.CuspidalConstituent.rightConv_mem_isotypicCuspSubmodule_inf_archCutSubmodule
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.553648+00:00
-- url     : https://prove2.me/submissions/fe26f25e-5996-5d7d-bfc3-b39430fc9004

import Definitions.Def_AutomorphicForm_CuspidalSpectrumCarrier
import Definitions.Def_AutomorphicForm_FactorizableTestFn
import Definitions.Def_AutomorphicForm_ArchSpherical
import Theorems.Thm_AutomorphicForm_CuspidalConstituent_rightConv_mem_levelInvariantSubmodule_inf_archCutSubmodule_of_isArchBiFinite
import Theorems.Thm_AutomorphicForm_isCuspidalFn_isKfSmooth_levelInvariant_isHeckeCosetEigenfunctionAt_rightConv_of_isFactorizableTestFn_of_support_subset
import Theorems.Thm_AutomorphicForm_memLp_two_rightConv_restrict_of_isCuspAutomorphicFnAt_of_coversModCentre_of_pos
import Theorems.Thm_AutomorphicForm_continuous_rightConv_of_continuous_of_hasCompactSupport
import Theorems.Thm_AutomorphicForm_continuous_and_hasCompactSupport_of_isFactorizableTestFn
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_CuspidalConstituent_rightConv_mem_isotypicCuspSubmodule_inf_archCutSubmodule
p2m_attr_erase "instance" "RestrictedProduct.SecondCountableTopology_of_principal instCountableElemSetSetsCofinite_definitions instCountableOfNumberField_definitions instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions"
p2m_attr_erase "simp" "AutomorphicForm.whittakerCoefficient_zero NumberField.StandardAddChar.ratArchLine_apply NumberField.StandardAddChar.AdelicTraceData.mk.sizeOf_spec NumberField.StandardAddChar.AdelicTraceData.mk.injEq NumberField.AdelicTrace.traceDiag_apply NumberField.AdelicTrace.diag_apply ContinuousAddEquiv.restrictedProductPi_apply RestrictedProduct.flatten_homeomorph_apply RestrictedProduct.flatten_homeomorph'_symm_apply ContinuousMulEquiv.restrictedProductPi_symm_apply RestrictedProduct.flatten_homeomorph'_apply RestrictedProduct.flatten_homeomorph_symm_apply ContinuousMulEquiv.restrictedProductPi_apply ContinuousAddEquiv.restrictedProductPi_symm_apply RingEquiv.restrictedProductCongr_symm_apply RingEquiv.restrictedProductCongrRight_apply MulEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductProd_symm_apply_coe Equiv.restrictedProductCongrRight_apply AddEquiv.restrictedProductCongr_apply Equiv.restrictedProductCongrLeft'_symm_apply_apply Equiv.restrictedProductCongr_apply_apply Equiv.restrictedProductCongrLeft_apply_apply RestrictedProduct.flatten_equiv'_apply AddEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductCongr_symm_apply Equiv.restrictedProductCongrRight_symm_apply RestrictedProduct.flatten_equiv'_symm_apply AddEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductCongrLeft'_apply RestrictedProduct.flatten_apply RingEquiv.restrictedProductCongr_apply_apply RingEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductProd_apply RestrictedProduct.flatten_equiv_apply RestrictedProduct.flatten_equiv_symm_apply LinearEquiv.restrictedProductCongrLeft'_apply RestrictedProduct.not_mem_support RestrictedProduct.mem_structureSubring_iff RestrictedProduct.not_mem_mulSupport"
p2m_attr_erase "simp" "RestrictedProduct.support_neg RestrictedProduct.mem_indexSupport_iff RestrictedProduct.mulSupport_inv RestrictedProduct.mapAlongLinearMap_apply LanglandsTunnell.TateLocal.charExt_coe_units LanglandsTunnell.TateLocal.modulus_one LanglandsTunnell.TateLocal.modulus_zero LanglandsTunnell.TateLocal.modulus_coe_units LanglandsTunnell.TateLocal.charExt_zero"

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicHaar NumberField.AdelicLevel NumberField.AdelicBox IsDedekindDomain
open AutomorphicForm AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering
open AutomorphicForm.CuspidalConstituent AutomorphicForm.CuspidalSpectrum
open scoped ComplexConjugate ENNReal InnerProductSpace BigOperators

attribute [local instance] NumberField.AdelicHaar.glBorel

theorem solution
    (F : Type) [Field F] [NumberField F] (c u d₁ d₂ : ℝ) (T : Finset (AdelicGL2 (𝓞 F) F))
    (hc : 0 < c) (hd₁ : 0 < d₁) (hd : d₁ < d₂)
    (hcov : CoversModCentre F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂))
    (ξ : (productionPinsOf F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂)
        (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F) (fun v => heckeGen (𝓞 F) F v)
        (adelicBox F)).Z →* ℂˣ)
    (N : Ideal (𝓞 F)) (hN : N ≠ ⊥) (S : Finset (HeightOneSpectrum (𝓞 F)))
    (tys : AutomorphicForm.ArchTypeFamily F) (Ψ : HeckeEigensystem F ℂ)
    (f : AdelicGL2 (𝓞 F) F → ℂ) (hf : IsFactorizableTestFn F f) (hbf : IsArchBiFinite F tys f)
    (hfs : ∀ x, f x ≠ 0 → ∃ a k : AdelicGL2 (𝓞 F) F,
      glFin (𝓞 F) F a = 1 ∧ k ∈ (productionPinsOf F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂)
        (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F) (fun v => heckeGen (𝓞 F) F v)
        (adelicBox F)).U N ∧ x = a * k)
    (φ : AdelicGL2 (𝓞 F) F → ℂ)
    (hφ : φ ∈ isotypicCuspSubmodule F (productionPinsOf F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂)
        (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F) (fun v => heckeGen (𝓞 F) F v)
        (adelicBox F)) ξ N S Ψ ⊓ archCutSubmodule F tys) :
    rightConv F φ f ∈ isotypicCuspSubmodule F (productionPinsOf F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂)
        (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F) (fun v => heckeGen (𝓞 F) F v)
        (adelicBox F)) ξ N S Ψ ⊓ archCutSubmodule F tys := by
  haveI := isHaarMeasure_adelicGLHaar (Fin 2) (𝓞 F) F
  haveI : BorelSpace (AdelicGL2 (𝓞 F) F) := NumberField.AdelicHaar.borelSpace_glBorel (Fin 2) (𝓞 F) F
  obtain ⟨hiso, -⟩ := hφ
  obtain ⟨hfc, hfcs⟩ := AutomorphicForm.continuous_and_hasCompactSupport_of_isFactorizableTestFn F f hf
  have hRC : ∀ (ψ : AdelicGL2 (𝓞 F) F → ℂ) (g : AdelicGL2 (𝓞 F) F),
      rightConv F ψ f g = ∫ x, ψ (g * x) * f x ∂(adelicGLHaar (Fin 2) (𝓞 F) F) := fun ψ g => rfl
  have hφc : Continuous φ := continuous_of_mem_isotypicCuspSubmodule hiso

  have hlev_le : isotypicCuspSubmodule F (productionPinsOf F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂)
        (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F) (fun v => heckeGen (𝓞 F) F v)
        (adelicBox F)) ξ N S Ψ ≤
      levelInvariantSubmodule F (productionPinsOf F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂)
        (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F) (fun v => heckeGen (𝓞 F) F v)
        (adelicBox F)) N := by
    refine Submodule.span_le.mpr ?_
    intro ψ hψ g u' hu'
    exact hψ.level_invariant g u' hu'
  have hφU := hlev_le hiso

  have hB := AutomorphicForm.CuspidalConstituent.rightConv_mem_levelInvariantSubmodule_inf_archCutSubmodule_of_isArchBiFinite
    F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂) N tys f hf hbf hfs φ hφc hφU
  refine ⟨?_, hB.2⟩

  have hint : ∀ (ψ : AdelicGL2 (𝓞 F) F → ℂ), Continuous ψ → ∀ g : AdelicGL2 (𝓞 F) F,
      Integrable (fun x => ψ (g * x) * f x) (adelicGLHaar (Fin 2) (𝓞 F) F) := by
    intro ψ hψc g
    refine Continuous.integrable_of_hasCompactSupport ((hψc.comp (continuous_const.mul continuous_id)).mul hfc) ?_
    exact hfcs.mul_left

  have hgen : ∀ ψ : AdelicGL2 (𝓞 F) F → ℂ, IsIsotypicCuspFormAt F (productionPinsOf F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂)
        (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F) (fun v => heckeGen (𝓞 F) F v)
        (adelicBox F)) ξ N S Ψ ψ →
      rightConv F ψ f ∈ isotypicCuspSubmodule F (productionPinsOf F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂)
        (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F) (fun v => heckeGen (𝓞 F) F v)
        (adelicBox F)) ξ N S Ψ := by
    intro ψ hψ
    by_cases h0 : ψ = 0
    · subst h0
      have : rightConv F (0 : AdelicGL2 (𝓞 F) F → ℂ) f = 0 := by
        funext g; rw [hRC]; simp
      rw [this]
      exact Submodule.zero_mem _
    have hψc : Continuous ψ := hψ.continuous

    let E : HeckeEigensystem F ℂ :=
      { level := N, level_ne_bot := hN, a := Ψ.a, b := Ψ.toRawCentral.b }
    let R : SmoothCuspRealizationAt F (productionPinsOf F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂)
        (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F) (fun v => heckeGen (𝓞 F) F v)
        (adelicBox F)) E :=
      { toFun := ψ
        exists_ne_zero := Function.ne_iff.mp h0
        centralChar := ξ
        smoothCusp := hψ.smoothCusp
        level_invariant := hψ.level_invariant
        exceptionalSet := S
        hecke_eigen := hψ.hecke_eigen
        central_eigen := hψ.central_eigen }
    obtain ⟨hcusp', hKf', hlev', hhecke'⟩ :=
      AutomorphicForm.isCuspidalFn_isKfSmooth_levelInvariant_isHeckeCosetEigenfunctionAt_rightConv_of_isFactorizableTestFn_of_support_subset
        F c u d₁ d₂ T E R hψc f hf hfs
    obtain ⟨⟨hleft, hcentral⟩, -⟩ :=
      (isAutomorphicFnAt_fdPins_iff F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂) ξ ψ).mp hψ.smoothCusp.1.1
    have hLs' : IsLsXiFunction (𝓞 F) F ⊤ ξ (rightConv F ψ f) := by
      refine ⟨fun γ g => ?_, fun z g => ?_⟩
      · rw [hRC, hRC]
        refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
        show ψ (globalPoints (𝓞 F) F γ * g * x) * f x = ψ (g * x) * f x
        rw [mul_assoc, hleft]
      · rw [hRC, hRC, ← integral_const_mul]
        refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
        show ψ (centralScalar (𝓞 F) F (z : (AdeleRing (𝓞 F) F)ˣ) * g * x) * f x
          = ((ξ z : ℂˣ) : ℂ) * (ψ (g * x) * f x)
        rw [mul_assoc, hcentral, mul_assoc]
        rfl
    have hL2' := AutomorphicForm.memLp_two_rightConv_restrict_of_isCuspAutomorphicFnAt_of_coversModCentre_of_pos
      F c u d₁ d₂ T hc hd hcov ξ ψ hψ.smoothCusp.1 hψc f hf
    have haut' : IsAutomorphicFnAt F (productionPinsOf F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂)
        (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F) (fun v => heckeGen (𝓞 F) F v)
        (adelicBox F)) ξ (rightConv F ψ f) :=
      (isAutomorphicFnAt_fdPins_iff F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂) ξ _).mpr ⟨hLs', hL2'⟩
    have hcontc : Continuous (rightConv F ψ f) :=
      AutomorphicForm.continuous_rightConv_of_continuous_of_hasCompactSupport F ψ hψc f hfc hfcs
    have hce : ∀ v : HeightOneSpectrum (𝓞 F), v ∉ S → ∀ g : AdelicGL2 (𝓞 F) F,
        rightConv F ψ f (centralScalar (𝓞 F) F (Matrix.GeneralLinearGroup.det ((productionPinsOf F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂)
        (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F) (fun v => heckeGen (𝓞 F) F v)
        (adelicBox F)).gen v)) * g)
          = Ψ.toRawCentral.b v * rightConv F ψ f g := by
      intro v hv g
      rw [hRC, hRC, ← integral_const_mul]
      refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
      show ψ (centralScalar (𝓞 F) F (Matrix.GeneralLinearGroup.det ((productionPinsOf F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂)
        (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F) (fun v => heckeGen (𝓞 F) F v)
        (adelicBox F)).gen v)) * g * x) * f x
        = Ψ.toRawCentral.b v * (ψ (g * x) * f x)
      rw [mul_assoc, hψ.central_eigen v hv, mul_assoc]
    have hiso' : IsIsotypicCuspFormAt F (productionPinsOf F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂)
        (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F) (fun v => heckeGen (𝓞 F) F v)
        (adelicBox F)) ξ N S Ψ (rightConv F ψ f) :=
      { smoothCusp := ⟨⟨haut', hcusp'⟩, hKf'⟩
        continuous := hcontc
        level_invariant := hlev'
        hecke_eigen := hhecke'
        central_eigen := hce }
    exact hiso'.mem_isotypicCuspSubmodule

  refine Submodule.span_induction (p := fun ψ _ => rightConv F ψ f ∈ isotypicCuspSubmodule F (productionPinsOf F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂)
        (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F) (fun v => heckeGen (𝓞 F) F v)
        (adelicBox F)) ξ N S Ψ)
    ?_ ?_ ?_ ?_ hiso
  · exact fun ψ hψ => hgen ψ hψ
  · have : rightConv F (0 : AdelicGL2 (𝓞 F) F → ℂ) f = 0 := by
      funext g; rw [hRC]; simp
    show rightConv F 0 f ∈ _
    rw [this]
    exact Submodule.zero_mem _
  · intro a b ha hb hpa hpb
    show rightConv F (a + b) f ∈ _
    have hac : Continuous a := continuous_of_mem_isotypicCuspSubmodule ha
    have hbc : Continuous b := continuous_of_mem_isotypicCuspSubmodule hb
    have : rightConv F (a + b) f = rightConv F a f + rightConv F b f := by
      funext g
      rw [Pi.add_apply, hRC, hRC, hRC, ← integral_add (hint a hac g) (hint b hbc g)]
      refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
      show (a + b) (g * x) * f x = a (g * x) * f x + b (g * x) * f x
      rw [Pi.add_apply, add_mul]
    rw [this]
    exact Submodule.add_mem _ hpa hpb
  · intro r a ha hpa
    show rightConv F (r • a) f ∈ _
    have : rightConv F (r • a) f = r • rightConv F a f := by
      funext g
      rw [Pi.smul_apply, hRC, hRC, smul_eq_mul, ← integral_const_mul]
      refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
      show (r • a) (g * x) * f x = r * (a (g * x) * f x)
      rw [Pi.smul_apply, smul_eq_mul, mul_assoc]
    rw [this]
    exact Submodule.smul_mem _ r hpa

end S_AutomorphicForm_CuspidalConstituent_rightConv_mem_isotypicCuspSubmodule_inf_archCutSubmodule
end P2MW
export P2MW.S_AutomorphicForm_CuspidalConstituent_rightConv_mem_isotypicCuspSubmodule_inf_archCutSubmodule (solution)
