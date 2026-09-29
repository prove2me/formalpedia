-- Prove2me | solution 1 for AutomorphicForm.exists_unipotentAverage_rightConv_sPart_zetaIntegrand_entire_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.961684+00:00
-- url     : https://prove2.me/submissions/8891101b-e701-50d6-8af2-0e6ae005f072

import Definitions.Def_AutomorphicForm_RightConvolution
import Definitions.Def_AutomorphicForm_FactorizableTestFn
import Definitions.Def_AutomorphicForm_BoundedGenuineCuspRealization
import Definitions.Def_NumberField_IdeleProductMeasure
import Definitions.Def_UnramifiedWhittaker_HeckeRecursion
import Definitions.Def_NumberField_AdelicFourier
import Theorems.Thm_AutomorphicForm_addChar_eq_one_on_integers_off_of_whittakerCoefficient_ne_zero
import Theorems.Thm_AutomorphicForm_rightConv_translate_package_of_isCuspAutomorphicFnAt
import Theorems.Thm_AutomorphicForm_zetaIntegrand_whittakerCoefficient_unipotentAverage_eq_mul
import Theorems.Thm_UnramifiedWhittaker_integrable_and_differentiable_integral_mul_zetaIntegrand_sPartMeasure_of_bounded
import Theorems.Thm_UnramifiedWhittaker_integral_mul_zetaIntegrand_sPartMeasure_ne_zero_of_nonneg_of_le_re
import Theorems.Thm_NumberField_AdelicFourier_exists_mem_schwartzBruhat_isFactorizableStandardOutside_integral_eq_nonneg
import Theorems.Thm_AutomorphicForm_exists_nhd_whittakerCoefficient_diagOne_sPartMeasure_lt_top
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_exists_unipotentAverage_rightConv_sPart_zetaIntegrand_entire_ne_zero
p2m_attr_erase "instance" "instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions instCountableOfNumberField_definitions RestrictedProduct.SecondCountableTopology_of_principal instCountableElemSetSetsCofinite_definitions IsDedekindDomain.HeightOneSpectrum.Extension.instAlgebraSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnder IsDedekindDomain.HeightOneSpectrum.Extension.instAlgebraSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnder_1 IsDedekindDomain.HeightOneSpectrum.instMulActionHomClassAlgHomTensorProductAdicCompletionForallValEqUnder_definitions IsDedekindDomain.HeightOneSpectrum.Extension.instAlgebraAdicCompletionValEqUnder IsDedekindDomain.HeightOneSpectrum.adicCompletion.instFiniteForallValEqUnderOfFiniteDimensional_definitions IsDedekindDomain.HeightOneSpectrum.instIsBiscalarSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersTensorProductCoeAlgHomTensorAdicCompletionIntegersTo IsDedekindDomain.HeightOneSpectrum.Extension.instContinuousSMulAdicCompletionValEqUnder IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsModuleTopology IsDedekindDomain.HeightOneSpectrum.Extension.instFiniteSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnderOfFiniteDimensional IsDedekindDomain.HeightOneSpectrum.adicCompletion.instFiniteValEqUnderOfFiniteDimensional_definitions instIsBiscalarTensorProductCoeAlgHomBaseChange_of_algebraMap IsDedekindDomain.HeightOneSpectrum.instIsScalarTowerSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnder_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsModuleTopologyPi Submodule.instIsTopologicalModuleSubtypeMem Pi.instTopologicalModule IsTopologicalModule.toContinuousSMul IsTopologicalModule.toContinuousAdd instFunLike SemialgHomClass.toSemilinearMapClass instCoeTCSemialgHom SemialgHomClass.toRingHomClass SemialgHomClass.instSemialgHom"
p2m_attr_erase "simp" "M4aHerbrand.IdeleGaloisDescent.mk.sizeOf_spec M4aHerbrand.IdeleGaloisDescent.mk.injEq ContinuousAddEquiv.restrictedProductPi_apply RestrictedProduct.flatten_homeomorph_apply RestrictedProduct.flatten_homeomorph'_symm_apply ContinuousMulEquiv.restrictedProductPi_symm_apply RestrictedProduct.flatten_homeomorph'_apply RestrictedProduct.flatten_homeomorph_symm_apply ContinuousMulEquiv.restrictedProductPi_apply ContinuousAddEquiv.restrictedProductPi_symm_apply RingEquiv.restrictedProductCongr_symm_apply RingEquiv.restrictedProductCongrRight_apply MulEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductProd_symm_apply_coe Equiv.restrictedProductCongrRight_apply AddEquiv.restrictedProductCongr_apply Equiv.restrictedProductCongrLeft'_symm_apply_apply Equiv.restrictedProductCongr_apply_apply Equiv.restrictedProductCongrLeft_apply_apply RestrictedProduct.flatten_equiv'_apply AddEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductCongr_symm_apply Equiv.restrictedProductCongrRight_symm_apply RestrictedProduct.flatten_equiv'_symm_apply AddEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductCongrLeft'_apply RestrictedProduct.flatten_apply RingEquiv.restrictedProductCongr_apply_apply RingEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductProd_apply RestrictedProduct.flatten_equiv_apply RestrictedProduct.flatten_equiv_symm_apply LinearEquiv.restrictedProductCongrLeft'_apply RestrictedProduct.not_mem_support RestrictedProduct.mem_structureSubring_iff RestrictedProduct.not_mem_mulSupport RestrictedProduct.support_neg RestrictedProduct.mem_indexSupport_iff RestrictedProduct.mulSupport_inv RestrictedProduct.mapAlongLinearMap_apply"
p2m_attr_erase "simp" "LanglandsTunnell.TateLocal.charExt_coe_units LanglandsTunnell.TateLocal.modulus_one LanglandsTunnell.TateLocal.modulus_zero LanglandsTunnell.TateLocal.modulus_coe_units LanglandsTunnell.TateLocal.charExt_zero LanglandsTunnell.TateLocal.conductorExponentAt_one SemialgHom.baseChange_of_algebraMap_tmul_left SemialgHom.baseChangeRightOfAlgebraMap_apply Pi.semialgHomPi_apply Pi.semialgHom_apply Module.Basis.rightBaseChange_apply LinearEquiv.coe_mulLeft LinearEquiv.coe_mulRight WithVal.semialgebraMap_toFun_ofVal Module.Basis.rightBaseChange_repr IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers.tensorCoe_tmul IsDedekindDomain.HeightOneSpectrum.tensorAdicCompletionIntegersTo_tmul SemialgHom.baseChangeRightOfAlgebraMap_coe IsDedekindDomain.HeightOneSpectrum.adicCompletion.integerBaseChangeLinearEquiv_tmul_apply SemialgHom.baseChange_of_algebraMap_tmul_right IsLocalization.map_moduleTensorEquiv_symm_tmul IsLocalization.leftModuleTensorEquiv_apply IsLocalization.moduleLid_symm_apply IsLocalization.leftModuleTensorEquiv_symm_apply IsLocalization.map_moduleTensorEquiv_tmul IsModuleTopology.continuousLinearEquiv_apply AlgEquiv.extendScalars_symm_apply IsModuleTopology.Module.Basis.equivFun_homeo_symm_apply IsModuleTopology.Module.Basis.equivFun_homeo_apply IsModuleTopology.continuousAlgEquivOfIsBiscalar_apply AlgEquiv.extendScalars_apply IsModuleTopology.continuousLinearEquiv_symm_apply SemialgHom.restrictScalars_toFun SemialgHom.mk.sizeOf_spec SemialgHom.mk.injEq SemialgHom.coe_coe coe_mk TensorProduct.RightActions.smul_def TensorProduct.RightActions.Module.TensorProduct.comm_symm_apply_tmul TensorProduct.RightActions.LinearMap.baseChange_id"
p2m_attr_erase "simp" "TensorProduct.RightActions.algebraMap_eval TensorProduct.RightActions.Module.TensorProduct.comm_apply_tmul TensorProduct.RightActions.Algebra.TensorProduct.comm_symm_apply_tmul TensorProduct.RightActions.Algebra.TensorProduct.comm_apply_tmul"

set_option autoImplicit false

open NumberField NumberField.AdelicLevel NumberField.AdelicBox NumberField.AdelicHaar MeasureTheory
open AutomorphicForm AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering
open IsDedekindDomain NumberField.TateGlobal
open UnramifiedWhittaker
open NumberField.Idele

attribute [local instance] NumberField.Idele.ideleBorel NumberField.Idele.borelSpace_ideleBorel

theorem solution
    (F : Type) [Field F] [NumberField F]
    (c u d₁ d₂ : ℝ) (T : Finset (AdelicGL2 (𝓞 F) F))
    (hd : d₁ < d₂)
    (hcov : CoversModCentre F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂))
    (ξ : (productionPinsOf F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂)
        (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F) (fun v => heckeGen (𝓞 F) F v)
        (adelicBox F)).Z →* ℂˣ)
    (φ : AdelicGL2 (𝓞 F) F → ℂ)
    (hφ : IsCuspAutomorphicFnAt F
      (productionPinsOf F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂)
        (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F) (fun v => heckeGen (𝓞 F) F v)
        (adelicBox F)) ξ φ)
    (hcont : Continuous φ)
    (f : AdelicGL2 (𝓞 F) F → ℂ) (hf : IsFactorizableTestFn F f)
    (ψ : AddChar (AdeleRing (𝓞 F) F) ℂ) (hψ : IsGlobalAddChar F ψ)
    (χ : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ) (hχ : IsIdeleClassChar (𝓞 F) F χ) (hχc : Continuous χ)
    (S : Finset (HeightOneSpectrum (𝓞 F)))
    (hKS : ∀ v : HeightOneSpectrum (𝓞 F), v ∉ S →
      ∀ (kv : GL (Fin 2) (v.adicCompletionIntegers F)) (g : AdelicGL2 (𝓞 F) F),
        rightConv F φ f (g * placeEmbed F v
          (Matrix.GeneralLinearGroup.map
            (algebraMap (v.adicCompletionIntegers F) (v.adicCompletion F)) kv)) = rightConv F φ f g)
    (g₀ : AdelicGL2 (𝓞 F) F)
    (hg₀ : ∀ v : HeightOneSpectrum (𝓞 F), v ∉ S → ∀ i j : Fin 2,
      ((g₀ : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)) i j).2 v =
        ((1 : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)) i j).2 v)
    (a₀ : (AdeleRing (𝓞 F) F)ˣ)
    (ha₀ : ∀ v : HeightOneSpectrum (𝓞 F), v ∉ S → ((a₀ : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F).2 v = 1)
    (hW : whittakerCoefficient F
        (productionPinsOf F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂)
        (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F) (fun v => heckeGen (𝓞 F) F v)
        (adelicBox F)) ψ (rightConv F φ f) 1 (diagOne a₀ * g₀) ≠ 0)
    (s₁ : ℂ) :
    ∃ (B : AdeleRing (𝓞 F) F → ℂ) (Φ : AdelicGL2 (𝓞 F) F → ℂ),
      B ∈ NumberField.AdelicFourier.schwartzBruhat F ∧
      (∃ (Bi : (w : InfinitePlace F) → w.Completion → ℂ) (Bf : (v : HeightOneSpectrum (𝓞 F)) → v.adicCompletion F → ℂ),
        IsFactorizableStandardOutside B S Bi Bf) ∧
      (∀ h : AdelicGL2 (𝓞 F) F, Φ h = (letI := adeleBorel (𝓞 F) F
        ∫ x, B x * rightConv F φ (fun y => f (g₀⁻¹ * y)) (h * unipotentGL2 x) ∂(adelicAddHaar (𝓞 F) F))) ∧
      (∀ s : ℂ, Integrable (zetaIntegrand
          (fun g => whittakerCoefficient F
              (productionPinsOf F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂)
        (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F) (fun v => heckeGen (𝓞 F) F v)
        (adelicBox F)) ψ Φ 1 g) χ s) (NumberField.Idele.sPartMeasure F S)) ∧
      Differentiable ℂ (fun s : ℂ => ∫ a, zetaIntegrand
          (fun g => whittakerCoefficient F
              (productionPinsOf F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂)
        (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F) (fun v => heckeGen (𝓞 F) F v)
        (adelicBox F)) ψ Φ 1 g) χ s a ∂(NumberField.Idele.sPartMeasure F S)) ∧
      (∫ a, zetaIntegrand
          (fun g => whittakerCoefficient F
              (productionPinsOf F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂)
        (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F) (fun v => heckeGen (𝓞 F) F v)
        (adelicBox F)) ψ Φ 1 g) χ s₁ a ∂(NumberField.Idele.sPartMeasure F S)) ≠ 0 := by

  obtain ⟨hGc, hMG, hGleft, hGtr, hGW, -⟩ :=
    AutomorphicForm.rightConv_translate_package_of_isCuspAutomorphicFnAt F c u d₁ d₂ T hd hcov ξ φ hφ hcont f hf ψ g₀
  set G := rightConv F φ (fun y => f (g₀⁻¹ * y)) with hGdef
  have hW' : whittakerCoefficient F (productionPinsOf F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂)
        (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F) (fun v => heckeGen (𝓞 F) F v)
        (adelicBox F)) ψ G 1 (diagOne a₀) ≠ 0 := by
    rw [hGW]; exact hW

  obtain ⟨Ω, K, N, r, R, M₁, X, hΩm, hKm, hΩ, hK, hr, hNo, ha₀N, hNK, hZmeas, hKb, hZ₀, hNre, hΩiff⟩ :=
    AutomorphicForm.exists_nhd_whittakerCoefficient_diagOne_sPartMeasure_lt_top F _ ψ hψ G hGc hMG χ hχ hχc S a₀ ha₀ s₁ hW'

  have hleft0 : ∀ (β : F) (h : AdelicGL2 (𝓞 F) F),
      rightConv F φ f (unipotentGL2 (algebraMap F (AdeleRing (𝓞 F) F) β) * h) = rightConv F φ f h := by
    intro β h
    have e1 := hGtr (unipotentGL2 (algebraMap F (AdeleRing (𝓞 F) F) β) * (h * g₀⁻¹))
    have e2 := hGtr (h * g₀⁻¹)
    rw [inv_mul_cancel_right] at e2
    rw [mul_assoc, inv_mul_cancel_right] at e1
    rw [← e1, hGleft, e2]
  have hψS := AutomorphicForm.addChar_eq_one_on_integers_off_of_whittakerCoefficient_ne_zero F _ (rightConv F φ f) hleft0 ψ hψ S hKS g₀ hg₀ a₀ ha₀ hW

  obtain ⟨B, μ, hBSB, hstd, hμeq, hμm, hμ0, ⟨M₀, hμM⟩, hμsupp, hμint, hμpos⟩ :=
    NumberField.AdelicFourier.exists_mem_schwartzBruhat_isFactorizableStandardOutside_integral_eq_nonneg F ψ hψ S hψS a₀ ha₀ N hNo ha₀N

  letI : MeasurableSpace (AdeleRing (𝓞 F) F) := adeleBorel (𝓞 F) F
  let Φ : AdelicGL2 (𝓞 F) F → ℂ := fun h => ∫ x, B x * G (h * unipotentGL2 x) ∂(adelicAddHaar (𝓞 F) F)
  have hΦ : ∀ h, Φ h = (letI := adeleBorel (𝓞 F) F
      ∫ x, B x * G (h * unipotentGL2 x) ∂(adelicAddHaar (𝓞 F) F)) := fun h => rfl

  have hC : ∀ s : ℂ, zetaIntegrand (fun g => whittakerCoefficient F
      (productionPinsOf F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂)
        (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F) (fun v => heckeGen (𝓞 F) F v)
        (adelicBox F)) ψ Φ 1 g) χ s =
      fun a => (μ a : ℂ) * zetaIntegrand (fun g => whittakerCoefficient F
      (productionPinsOf F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂)
        (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F) (fun v => heckeGen (𝓞 F) F v)
        (adelicBox F)) ψ G 1 g) χ s a := by
    intro s; funext a
    rw [AutomorphicForm.zetaIntegrand_whittakerCoefficient_unipotentAverage_eq_mul F _ ψ hψ G hGc hMG hGleft B hBSB Φ hΦ χ s a, hμeq a]

  have hμabs : ∀ a, |μ a| ≤ M₀ := fun a => by rw [abs_of_nonneg (hμ0 a)]; exact hμM a
  have hsuppK : ∀ a ∈ Ω, a ∉ K → μ a = 0 := fun a ha haK =>
    hμsupp a ((hΩiff a).2 ha) (fun haN => haK (hNK haN))
  have hmeas : ∀ s : ℂ, Measurable fun a => (μ a : ℂ) * zetaIntegrand (fun g => whittakerCoefficient F
      (productionPinsOf F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂)
        (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F) (fun v => heckeGen (𝓞 F) F v)
        (adelicBox F)) ψ G 1 g) χ s a :=
    fun s => (Complex.measurable_ofReal.comp hμm).mul (hZmeas s)
  obtain ⟨hint, hdiff⟩ := UnramifiedWhittaker.integrable_and_differentiable_integral_mul_zetaIntegrand_sPartMeasure_of_bounded F S _ χ μ Ω K hΩm hKm hΩ hK
    M₀ M₁ X r R hr hmeas hμabs hsuppK hKb

  have hsuppN : ∀ a ∈ Ω, a ∉ N → μ a = 0 := fun a ha haN => hμsupp a ((hΩiff a).2 ha) haN
  have hne := UnramifiedWhittaker.integral_mul_zetaIntegrand_sPartMeasure_ne_zero_of_nonneg_of_le_re F S _ χ s₁ μ hμ0 (hint s₁) hμint Ω N hΩm hΩ
    a₀ hZ₀ hNre hsuppN hμpos
  refine ⟨B, Φ, hBSB, hstd, fun h => rfl, fun s => ?_, ?_, ?_⟩
  · rw [hC s]; exact hint s
  · simp_rw [hC]; exact hdiff
  · rw [hC s₁]; exact hne

end S_AutomorphicForm_exists_unipotentAverage_rightConv_sPart_zetaIntegrand_entire_ne_zero
end P2MW
export P2MW.S_AutomorphicForm_exists_unipotentAverage_rightConv_sPart_zetaIntegrand_entire_ne_zero (solution)
