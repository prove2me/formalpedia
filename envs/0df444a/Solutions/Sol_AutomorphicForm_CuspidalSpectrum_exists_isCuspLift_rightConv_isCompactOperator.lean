-- Prove2me | solution 1 for AutomorphicForm.CuspidalSpectrum.exists_isCuspLift_rightConv_isCompactOperator
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.553648+00:00
-- url     : https://prove2.me/submissions/00013cd9-4a52-56f9-a417-4f2b7684d390

import Definitions.Def_AutomorphicForm_CuspidalSpectrumSubrep
import Theorems.Thm_AutomorphicForm_CuspidalSpectrum_exists_isLift_rightConv
import Theorems.Thm_AutomorphicForm_CuspidalSpectrum_apply_mem_cuspSubcarrier_of_isLift_rightConv
import Theorems.Thm_AutomorphicForm_CuspidalSpectrum_isCompactOperator_lift_rightConv_comp_cuspSubcarrier
import Theorems.Thm_AutomorphicForm_continuous_and_hasCompactSupport_of_isFactorizableTestFn
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_CuspidalSpectrum_exists_isCuspLift_rightConv_isCompactOperator
p2m_attr_erase "instance" "RestrictedProduct.SecondCountableTopology_of_principal instCountableElemSetSetsCofinite_definitions instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions instCountableOfNumberField_definitions"
p2m_attr_erase "simp" "ContinuousAddEquiv.restrictedProductPi_apply RestrictedProduct.flatten_homeomorph_apply RestrictedProduct.flatten_homeomorph'_symm_apply ContinuousMulEquiv.restrictedProductPi_symm_apply RestrictedProduct.flatten_homeomorph'_apply RestrictedProduct.flatten_homeomorph_symm_apply ContinuousMulEquiv.restrictedProductPi_apply ContinuousAddEquiv.restrictedProductPi_symm_apply RingEquiv.restrictedProductCongr_symm_apply RingEquiv.restrictedProductCongrRight_apply MulEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductProd_symm_apply_coe Equiv.restrictedProductCongrRight_apply AddEquiv.restrictedProductCongr_apply Equiv.restrictedProductCongrLeft'_symm_apply_apply Equiv.restrictedProductCongr_apply_apply Equiv.restrictedProductCongrLeft_apply_apply RestrictedProduct.flatten_equiv'_apply AddEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductCongr_symm_apply Equiv.restrictedProductCongrRight_symm_apply RestrictedProduct.flatten_equiv'_symm_apply AddEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductCongrLeft'_apply RestrictedProduct.flatten_apply RingEquiv.restrictedProductCongr_apply_apply RingEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductProd_apply RestrictedProduct.flatten_equiv_apply RestrictedProduct.flatten_equiv_symm_apply LinearEquiv.restrictedProductCongrLeft'_apply RestrictedProduct.not_mem_support RestrictedProduct.mem_structureSubring_iff RestrictedProduct.not_mem_mulSupport RestrictedProduct.support_neg RestrictedProduct.mem_indexSupport_iff RestrictedProduct.mulSupport_inv RestrictedProduct.mapAlongLinearMap_apply AutomorphicForm.fnTwist_zero AutomorphicForm.fnTwist_apply"
p2m_attr_erase "simp" "AutomorphicForm.whittakerCoefficient_zero NumberField.StandardAddChar.ratArchLine_apply NumberField.StandardAddChar.AdelicTraceData.mk.sizeOf_spec NumberField.StandardAddChar.AdelicTraceData.mk.injEq NumberField.AdelicTrace.traceDiag_apply NumberField.AdelicTrace.diag_apply"

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicHaar NumberField.AdelicLevel NumberField.AdelicBox
open IsDedekindDomain AutomorphicForm AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering
open AutomorphicForm.CuspidalConstituent AutomorphicForm.CuspidalSpectrum
open scoped InnerProductSpace

attribute [local instance] NumberField.AdelicHaar.glBorel NumberField.AdelicHaar.borelSpace_glBorel

theorem solution
    (F : Type) [Field F] [NumberField F] {α β : ℝ} {Φ₀ : Set (AdelicGL2 (𝓞 F) F)}
    (hΦ₀ : IsSlabFundamentalDomain F α β Φ₀) (σ : ℝ)
    (ξ : (⊤ : Subgroup (AdeleRing (𝓞 F) F)ˣ) →* ℂˣ) (hσ : HasModulus F ξ σ)
    (f : AdelicGL2 (𝓞 F) F → ℂ) (hf : IsFactorizableTestFn F f) :
    ∃ Tc : ↥(cuspSubcarrier F hΦ₀ σ ξ) →L[ℂ] ↥(cuspSubcarrier F hΦ₀ σ ξ),
      IsCuspLift F hΦ₀ σ ξ (fun φ => rightConv F φ f) Tc ∧ IsCompactOperator Tc := by
  haveI : CompleteSpace ↥(cuspSubcarrier F hΦ₀ σ ξ) := by
    unfold cuspSubcarrier; exact (Submodule.isClosed_topologicalClosure _).completeSpace_coe
  obtain ⟨hgc, hgs⟩ := AutomorphicForm.continuous_and_hasCompactSupport_of_isFactorizableTestFn F f hf
  obtain ⟨T, T', hT, -, -⟩ := AutomorphicForm.CuspidalSpectrum.exists_isLift_rightConv F α β Φ₀ hΦ₀ σ ξ hσ f hgc hgs
  have hmem : ∀ v : ↥(cuspSubcarrier F hΦ₀ σ ξ), (T.comp (cuspSubcarrier F hΦ₀ σ ξ).subtypeL) v ∈ cuspSubcarrier F hΦ₀ σ ξ := fun v =>
    AutomorphicForm.CuspidalSpectrum.apply_mem_cuspSubcarrier_of_isLift_rightConv F hΦ₀ σ ξ hσ f hf T hT v v.2
  have hclosed : IsClosed ((cuspSubcarrier F hΦ₀ σ ξ : Submodule ℂ (Carrier F Φ₀ σ)) : Set (Carrier F Φ₀ σ)) := by
    unfold cuspSubcarrier; exact Submodule.isClosed_topologicalClosure _
  refine ⟨(T.comp (cuspSubcarrier F hΦ₀ σ ξ).subtypeL).codRestrict (cuspSubcarrier F hΦ₀ σ ξ) hmem, ?_, ?_⟩
  · intro φ h
    apply Subtype.ext
    show T (toCuspSubcarrier F hΦ₀ σ ξ φ : Carrier F Φ₀ σ) = (toCuspSubcarrier F hΦ₀ σ ξ ⟨rightConv F φ f, h⟩ : Carrier F Φ₀ σ)
    rw [toCuspSubcarrier_apply_coe, toCuspSubcarrier_apply_coe]
    exact hT.comm φ ⟨φ.2.1.1.1, φ.2.2⟩
  · exact (AutomorphicForm.CuspidalSpectrum.isCompactOperator_lift_rightConv_comp_cuspSubcarrier F α β Φ₀ hΦ₀ σ ξ hσ f hf T hT).codRestrict
      hmem hclosed

end S_AutomorphicForm_CuspidalSpectrum_exists_isCuspLift_rightConv_isCompactOperator
end P2MW
export P2MW.S_AutomorphicForm_CuspidalSpectrum_exists_isCuspLift_rightConv_isCompactOperator (solution)
