-- Prove2me | solution 1 for AutomorphicForm.integral_maximalCompactHaar_rightConv_mul_conj_eq_integral_mul_conj_rightConv_star_of_isInducedSection_axis
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.340288+00:00
-- url     : https://prove2.me/submissions/275ecac5-af36-5cb6-9c81-94893cfa4c70

import Definitions.Def_AutomorphicForm_TwistedOrbital
import Definitions.Def_NumberField_PrincipalLevel
import Definitions.Def_NumberField_TateGlobalZeta
import Definitions.Def_LanglandsTunnell_ConverseData
import Definitions.Def_LocalLanglands_HeckeCosetLocal
import Definitions.Def_AutomorphicForm_AdelicKernel
import Definitions.Def_AutomorphicForm_CanonicalTruncationDomain
import Definitions.Def_AutomorphicForm_GeometricRemainder
import Definitions.Def_AutomorphicForm_InducedSection
import Definitions.Def_AutomorphicForm_EtaFamily
import Definitions.Def_AutomorphicForm_WeylIntertwining
import Definitions.Def_AutomorphicForm_SlabProfile
import Definitions.Def_AutomorphicForm_TruncationOperator
import Definitions.Def_AutomorphicForm_CarrierPins
import Definitions.Def_NumberField_AdelicHeight
import Definitions.Def_AutomorphicForm_AdelicMaximalCompact
import Definitions.Def_AutomorphicForm_ArchKFinite
import Definitions.Def_AutomorphicForm_SmoothAutomorphicFnAt
import Definitions.Def_NumberField_AdelicHaar
import Definitions.Def_NumberField_AdelicBox
import Definitions.Def_AutomorphicForm_RightConvolution
import Definitions.Def_AutomorphicForm_AutomorphicFnAt
import Definitions.Def_AutomorphicForm_ResidualSpan
import Theorems.Thm_AutomorphicForm_integral_maximalCompactHaar_mul_apply_mul_conj_eq_of_isInducedSection_axis_of_isUnitaryChar
import Theorems.Thm_NumberField_AdelicHaar_isMulRightInvariant_adelicGLHaar
import Theorems.Thm_MeasureTheory_Measure_isInvInvariant_of_isMulRightInvariant
import Theorems.Thm_NumberField_AdeleRing_secondCountableTopology_generalLinearGroup_finTwo
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_integral_maximalCompactHaar_rightConv_mul_conj_eq_integral_mul_conj_rightConv_star_of_isInducedSection_axis
p2m_attr_erase "instance" "instCountableOfNumberField_definitions RestrictedProduct.SecondCountableTopology_of_principal instCountableElemSetSetsCofinite_definitions instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions"
p2m_attr_erase "simp" "UnramifiedWhittaker.ProductMeasureData.mk.injEq UnramifiedWhittaker.ProductMeasureData.mk.sizeOf_spec AdelicDock.coe_finEmbed AdelicDock.splice_apply_self AdelicDock.coe_localEmbed NumberField.AdeleRing.val_finiteUnitsComponent IsDedekindDomain.FiniteAdeleRing.val_unitsComponent NumberField.AdeleRing.val_finitePartUnits NumberField.AdeleRing.val_infiniteUnitsComponent ContinuousAddEquiv.restrictedProductPi_apply RestrictedProduct.flatten_homeomorph_apply RestrictedProduct.flatten_homeomorph'_symm_apply ContinuousMulEquiv.restrictedProductPi_symm_apply RestrictedProduct.flatten_homeomorph'_apply RestrictedProduct.flatten_homeomorph_symm_apply ContinuousMulEquiv.restrictedProductPi_apply ContinuousAddEquiv.restrictedProductPi_symm_apply RingEquiv.restrictedProductCongr_symm_apply RingEquiv.restrictedProductCongrRight_apply MulEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductProd_symm_apply_coe Equiv.restrictedProductCongrRight_apply AddEquiv.restrictedProductCongr_apply Equiv.restrictedProductCongrLeft'_symm_apply_apply Equiv.restrictedProductCongr_apply_apply Equiv.restrictedProductCongrLeft_apply_apply RestrictedProduct.flatten_equiv'_apply AddEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductCongr_symm_apply Equiv.restrictedProductCongrRight_symm_apply RestrictedProduct.flatten_equiv'_symm_apply AddEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductCongrLeft'_apply RestrictedProduct.flatten_apply RingEquiv.restrictedProductCongr_apply_apply RingEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductProd_apply RestrictedProduct.flatten_equiv_apply RestrictedProduct.flatten_equiv_symm_apply LinearEquiv.restrictedProductCongrLeft'_apply"
p2m_attr_erase "simp" "RestrictedProduct.not_mem_support RestrictedProduct.mem_structureSubring_iff RestrictedProduct.not_mem_mulSupport RestrictedProduct.support_neg RestrictedProduct.mem_indexSupport_iff RestrictedProduct.mulSupport_inv RestrictedProduct.mapAlongLinearMap_apply"

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicLevel NumberField.AdelicBox NumberField.AdelicHaar
open AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering
open IsDedekindDomain
open scoped ComplexConjugate NNReal

attribute [local instance] NumberField.AdelicHaar.glBorel

attribute [local instance] NumberField.AdelicHaar.borelSpace_glBorel

open scoped ENNReal
open AutomorphicForm

open AutomorphicForm in
theorem solution
    (K : Type) [Field K] [NumberField K] :
    let αm : (AdeleRing (𝓞 K) K)ˣ →* ℝˣ :=
      ((NNReal.toRealHom : ℝ≥0 →+* ℝ).toMonoidHom.comp
        (distribHaarChar (AdeleRing (𝓞 K) K))).toHomUnits
    letI := adeleBorel (𝓞 K) K
    ∀ (hαm : ∀ x, 0 < ((αm x : ℝˣ) : ℝ))
      (μ ν : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ)
      (_hμ : IsUnitaryChar (𝓞 K) K μ) (_hν : IsUnitaryChar (𝓞 K) K ν)
      (t : ℝ) (Ψ χ : AdelicGL2 (𝓞 K) K → ℂ)
      (_hΨ : IsInducedSection (𝓞 K) K (etaFst μ αm hαm ((t : ℂ) * Complex.I)) (etaSnd ν αm hαm ((t : ℂ) * Complex.I)) Ψ)
      (_hχ : IsInducedSection (𝓞 K) K (etaFst μ αm hαm ((t : ℂ) * Complex.I)) (etaSnd ν αm hαm ((t : ℂ) * Complex.I)) χ)
      (_hΨc : Continuous Ψ) (_hχc : Continuous χ)
      (f : AdelicGL2 (𝓞 K) K → ℂ) (_hf : Continuous f) (_hfc : HasCompactSupport f),
    ∫ k, rightConv K Ψ f (k : AdelicGL2 (𝓞 K) K) * conj (χ (k : AdelicGL2 (𝓞 K) K)) ∂(maximalCompactHaar K) =
      ∫ k, Ψ (k : AdelicGL2 (𝓞 K) K) * conj (rightConv K χ (fun y => conj (f y⁻¹)) (k : AdelicGL2 (𝓞 K) K)) ∂(maximalCompactHaar K) := by
  intro αm
  intro hαm μ ν hμ hν t Ψ χ hΨ hχ hΨc hχc f hf hfc
  haveI := NumberField.AdelicHaar.isHaarMeasure_adelicGLHaar (Fin 2) (𝓞 K) K
  haveI := NumberField.AdelicHaar.isMulRightInvariant_adelicGLHaar K
  haveI : SecondCountableTopology (AdelicGL2 (𝓞 K) K) :=
    NumberField.AdeleRing.secondCountableTopology_generalLinearGroup_finTwo K
  haveI : (adelicGLHaar (Fin 2) (𝓞 K) K).IsInvInvariant :=
    MeasureTheory.Measure.isInvInvariant_of_isMulRightInvariant (adelicGLHaar (Fin 2) (𝓞 K) K)
  set μG : Measure (AdelicGL2 (𝓞 K) K) := adelicGLHaar (Fin 2) (𝓞 K) K with hμG
  set μK := maximalCompactHaar K with hμK

  have hU : ∀ y : AdelicGL2 (𝓞 K) K,
      ∫ k, Ψ ((k : AdelicGL2 (𝓞 K) K) * y) * conj (χ (k : AdelicGL2 (𝓞 K) K)) ∂μK =
        ∫ k, Ψ (k : AdelicGL2 (𝓞 K) K) * conj (χ ((k : AdelicGL2 (𝓞 K) K) * y⁻¹)) ∂μK := by
    intro y
    have hχy : IsInducedSection (𝓞 K) K (etaFst μ αm hαm ((t : ℂ) * Complex.I)) (etaSnd ν αm hαm ((t : ℂ) * Complex.I))
        (fun x => χ (x * y⁻¹)) := hχ.rightTranslate y⁻¹
    have hχyc : Continuous (fun x => χ (x * y⁻¹)) := hχc.comp (continuous_id.mul continuous_const)
    have h := AutomorphicForm.integral_maximalCompactHaar_mul_apply_mul_conj_eq_of_isInducedSection_axis_of_isUnitaryChar
      K hαm μ ν hμ hν t Ψ (fun x => χ (x * y⁻¹)) hΨ hχy hΨc hχyc y
    simp only [mul_assoc, mul_inv_cancel, mul_one] at h
    simpa only [hμK] using h

  set F₁ : adelicMaximalCompact K × AdelicGL2 (𝓞 K) K → ℂ :=
    fun p => Ψ ((p.1 : AdelicGL2 (𝓞 K) K) * p.2) * f p.2 * conj (χ (p.1 : AdelicGL2 (𝓞 K) K)) with hF₁
  set F₂ : adelicMaximalCompact K × AdelicGL2 (𝓞 K) K → ℂ :=
    fun p => Ψ (p.1 : AdelicGL2 (𝓞 K) K) * (conj (χ ((p.1 : AdelicGL2 (𝓞 K) K) * p.2)) * f p.2⁻¹) with hF₂
  have hval : Continuous (fun p : adelicMaximalCompact K × AdelicGL2 (𝓞 K) K => (p.1 : AdelicGL2 (𝓞 K) K)) :=
    continuous_subtype_val.comp continuous_fst
  have hF₁c : Continuous F₁ :=
    ((hΨc.comp (hval.mul continuous_snd)).mul (hf.comp continuous_snd)).mul
      (Complex.continuous_conj.comp (hχc.comp hval))
  have hF₂c : Continuous F₂ :=
    (hΨc.comp hval).mul ((Complex.continuous_conj.comp (hχc.comp (hval.mul continuous_snd))).mul
      (hf.comp (continuous_inv.comp continuous_snd)))
  have hfic : HasCompactSupport (fun y : AdelicGL2 (𝓞 K) K => f y⁻¹) :=
    hfc.comp_homeomorph (Homeomorph.inv (AdelicGL2 (𝓞 K) K))
  have hF₁s : HasCompactSupport F₁ := by
    refine HasCompactSupport.intro (isCompact_univ.prod hfc) ?_
    rintro ⟨k, y⟩ hp
    have hy : y ∉ tsupport f := fun h => hp ⟨Set.mem_univ _, h⟩
    simp only [hF₁, image_eq_zero_of_notMem_tsupport hy, mul_zero, zero_mul]
  have hF₂s : HasCompactSupport F₂ := by
    refine HasCompactSupport.intro (isCompact_univ.prod hfic) ?_
    rintro ⟨k, y⟩ hp
    have hy : y ∉ tsupport (fun y : AdelicGL2 (𝓞 K) K => f y⁻¹) := fun h => hp ⟨Set.mem_univ _, h⟩
    have h0 : f y⁻¹ = 0 := image_eq_zero_of_notMem_tsupport (f := fun y : AdelicGL2 (𝓞 K) K => f y⁻¹) hy
    simp only [hF₂, h0, mul_zero]
  have hI₁ : Integrable F₁ (μK.prod μG) := hF₁c.integrable_of_hasCompactSupport hF₁s
  have hI₂ : Integrable F₂ (μK.prod μG) := hF₂c.integrable_of_hasCompactSupport hF₂s

  have L : ∫ k, rightConv K Ψ f (k : AdelicGL2 (𝓞 K) K) * conj (χ (k : AdelicGL2 (𝓞 K) K)) ∂μK =
      ∫ y, f y * ∫ k, Ψ ((k : AdelicGL2 (𝓞 K) K) * y) * conj (χ (k : AdelicGL2 (𝓞 K) K)) ∂μK ∂μG := by
    have e1 : ∀ k : adelicMaximalCompact K,
        rightConv K Ψ f (k : AdelicGL2 (𝓞 K) K) * conj (χ (k : AdelicGL2 (𝓞 K) K)) = ∫ y, F₁ (k, y) ∂μG := by
      intro k
      rw [rightConv_apply, ← integral_mul_const]
    have e2 : ∀ y : AdelicGL2 (𝓞 K) K,
        f y * ∫ k, Ψ ((k : AdelicGL2 (𝓞 K) K) * y) * conj (χ (k : AdelicGL2 (𝓞 K) K)) ∂μK = ∫ k, F₁ (k, y) ∂μK := by
      intro y
      rw [← integral_const_mul]
      refine integral_congr_ae (Filter.Eventually.of_forall fun k => ?_)
      simp only [hF₁]
      ring
    simp_rw [e1, e2]
    exact integral_integral_swap (f := fun k y => F₁ (k, y)) hI₁

  have R : ∫ k, Ψ (k : AdelicGL2 (𝓞 K) K) * conj (rightConv K χ (fun y => conj (f y⁻¹)) (k : AdelicGL2 (𝓞 K) K)) ∂μK =
      ∫ y, f y⁻¹ * ∫ k, Ψ (k : AdelicGL2 (𝓞 K) K) * conj (χ ((k : AdelicGL2 (𝓞 K) K) * y)) ∂μK ∂μG := by
    have e1 : ∀ k : adelicMaximalCompact K,
        Ψ (k : AdelicGL2 (𝓞 K) K) * conj (rightConv K χ (fun y => conj (f y⁻¹)) (k : AdelicGL2 (𝓞 K) K)) =
          ∫ y, F₂ (k, y) ∂μG := by
      intro k
      rw [rightConv_apply, ← integral_conj, ← integral_const_mul]
      refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
      simp only [hF₂, map_mul, Complex.conj_conj]
    have e2 : ∀ y : AdelicGL2 (𝓞 K) K,
        f y⁻¹ * ∫ k, Ψ (k : AdelicGL2 (𝓞 K) K) * conj (χ ((k : AdelicGL2 (𝓞 K) K) * y)) ∂μK = ∫ k, F₂ (k, y) ∂μK := by
      intro y
      rw [← integral_const_mul]
      refine integral_congr_ae (Filter.Eventually.of_forall fun k => ?_)
      simp only [hF₂]
      ring
    simp_rw [e1, e2]
    exact integral_integral_swap (f := fun k y => F₂ (k, y)) hI₂
  rw [L, R]

  rw [← integral_inv_eq_self (fun y => f y⁻¹ * ∫ k, Ψ (k : AdelicGL2 (𝓞 K) K) * conj (χ ((k : AdelicGL2 (𝓞 K) K) * y)) ∂μK) μG]
  refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
  dsimp only
  rw [inv_inv, hU y]

end S_AutomorphicForm_integral_maximalCompactHaar_rightConv_mul_conj_eq_integral_mul_conj_rightConv_star_of_isInducedSection_axis
end P2MW
export P2MW.S_AutomorphicForm_integral_maximalCompactHaar_rightConv_mul_conj_eq_integral_mul_conj_rightConv_star_of_isInducedSection_axis (solution)
