-- Prove2me | solution 1 for AutomorphicForm.CuspidalSpectrum.exists_isArchBiFinite_flat_isCompactOperator_lift_rightConv_apply_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.553648+00:00
-- url     : https://prove2.me/submissions/d431ef9f-cebe-5972-b1ad-6fd512c03d17

import Definitions.Def_AutomorphicForm_CuspidalSpectrumSubrep
import Definitions.Def_AutomorphicForm_ArchSpherical
import Theorems.Thm_AutomorphicForm_CuspidalSpectrum_exists_mem_archCutSubmodule_inner_toCuspSubcarrier_ne_zero_of_ne_zero
import Theorems.Thm_AutomorphicForm_CuspidalSpectrum_exists_isLevelSphericalOfType_flat_norm_toCuspSubcarrier_sub_lt_of_forall_apply_mul_eq
import Theorems.Thm_AutomorphicForm_CuspidalSpectrum_exists_isCompactOperator_isSymmetric_lift_rightConv
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_CuspidalSpectrum_exists_isArchBiFinite_flat_isCompactOperator_lift_rightConv_apply_ne_zero
p2m_attr_erase "instance" "instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions instCountableOfNumberField_definitions RestrictedProduct.SecondCountableTopology_of_principal instCountableElemSetSetsCofinite_definitions AutomorphicForm.compactSpace_maximalCompactAway AutomorphicForm.compactSpace_adelicMaximalCompact AutomorphicForm.isProbabilityMeasure_maximalCompactHaar AutomorphicForm.isHaarMeasure_maximalCompactHaar AutomorphicForm.compactSpace_maximalCompactAt AutomorphicForm.isProbabilityMeasure_maximalCompactAwayHaar AutomorphicForm.isHaarMeasure_maximalCompactAwayHaar AutomorphicForm.isProbabilityMeasure_maximalCompactAtHaar AutomorphicForm.isHaarMeasure_maximalCompactAtHaar"
p2m_attr_erase "simp" "AdelicDock.coe_finEmbed AdelicDock.splice_apply_self AdelicDock.coe_localEmbed AutomorphicForm.fnTwist_zero AutomorphicForm.fnTwist_apply ContinuousAddEquiv.restrictedProductPi_apply RestrictedProduct.flatten_homeomorph_apply RestrictedProduct.flatten_homeomorph'_symm_apply ContinuousMulEquiv.restrictedProductPi_symm_apply RestrictedProduct.flatten_homeomorph'_apply RestrictedProduct.flatten_homeomorph_symm_apply ContinuousMulEquiv.restrictedProductPi_apply ContinuousAddEquiv.restrictedProductPi_symm_apply RingEquiv.restrictedProductCongr_symm_apply RingEquiv.restrictedProductCongrRight_apply MulEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductProd_symm_apply_coe Equiv.restrictedProductCongrRight_apply AddEquiv.restrictedProductCongr_apply Equiv.restrictedProductCongrLeft'_symm_apply_apply Equiv.restrictedProductCongr_apply_apply Equiv.restrictedProductCongrLeft_apply_apply RestrictedProduct.flatten_equiv'_apply AddEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductCongr_symm_apply Equiv.restrictedProductCongrRight_symm_apply RestrictedProduct.flatten_equiv'_symm_apply AddEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductCongrLeft'_apply RestrictedProduct.flatten_apply RingEquiv.restrictedProductCongr_apply_apply RingEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductProd_apply RestrictedProduct.flatten_equiv_apply RestrictedProduct.flatten_equiv_symm_apply LinearEquiv.restrictedProductCongrLeft'_apply RestrictedProduct.not_mem_support RestrictedProduct.mem_structureSubring_iff RestrictedProduct.not_mem_mulSupport RestrictedProduct.support_neg"
p2m_attr_erase "simp" "RestrictedProduct.mem_indexSupport_iff RestrictedProduct.mulSupport_inv RestrictedProduct.mapAlongLinearMap_apply AutomorphicForm.whittakerCoefficient_zero NumberField.StandardAddChar.ratArchLine_apply NumberField.StandardAddChar.AdelicTraceData.mk.sizeOf_spec NumberField.StandardAddChar.AdelicTraceData.mk.injEq NumberField.AdelicTrace.traceDiag_apply NumberField.AdelicTrace.diag_apply"

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
    (v : ↥(cuspSubcarrier F hΦ₀ σ ξ)) (hv : v ≠ 0) :
    ∃ (tys : ArchTypeFamily F) (f : AdelicGL2 (𝓞 F) F → ℂ),
      IsFactorizableTestFn F f ∧ IsArchBiFinite F tys f ∧ flat F σ f = f ∧
      ∃ Tc : ↥(cuspSubcarrier F hΦ₀ σ ξ) →L[ℂ] ↥(cuspSubcarrier F hΦ₀ σ ξ),
        IsCompactOperator Tc ∧ (Tc : ↥(cuspSubcarrier F hΦ₀ σ ξ) →ₗ[ℂ] ↥(cuspSubcarrier F hΦ₀ σ ξ)).IsSymmetric ∧
        IsCuspLift F hΦ₀ σ ξ (fun φ => rightConv F φ f) Tc ∧ Tc v ≠ 0 := by
  obtain ⟨tys, U, hUf, hUo, hUc, hUi, ψ, hψ, hψt, hψU, hinner⟩ :=
    AutomorphicForm.CuspidalSpectrum.exists_mem_archCutSubmodule_inner_toCuspSubcarrier_ne_zero_of_ne_zero F hΦ₀ σ ξ hσ v hv
  set a : ℂ := ⟪v, toCuspSubcarrier F hΦ₀ σ ξ ⟨ψ, hψ⟩⟫_ℂ with ha
  have ha0 : 0 < ‖a‖ := norm_pos_iff.mpr hinner
  set ε : ℝ := ‖a‖ / (‖v‖ + 1) with hεdef
  have hv1 : 0 < ‖v‖ + 1 := by positivity
  have hε : 0 < ε := div_pos ha0 hv1
  obtain ⟨f, hft, hsph, hflat, hψf, hclose⟩ :=
    AutomorphicForm.CuspidalSpectrum.exists_isLevelSphericalOfType_flat_norm_toCuspSubcarrier_sub_lt_of_forall_apply_mul_eq
      F hΦ₀ σ ξ hσ U hUf hUo hUc hUi tys ψ hψ hψU hψt ε hε
  obtain ⟨fa, -, hfa_bf, -, hfa_eq⟩ := hsph
  have hfbf : IsArchBiFinite F tys f := IsArchBiFinite.of_factorization F hfa_eq hfa_bf
  obtain ⟨Tc, hcpt, hsymm, hlift⟩ :=
    AutomorphicForm.CuspidalSpectrum.exists_isCompactOperator_isSymmetric_lift_rightConv F hΦ₀ σ ξ hσ f hft hflat
  refine ⟨tys, f, hft, hfbf, hflat, Tc, hcpt, hsymm, hlift, ?_⟩

  intro h0
  have h1 : ⟪Tc v, toCuspSubcarrier F hΦ₀ σ ξ ⟨ψ, hψ⟩⟫_ℂ = ⟪v, toCuspSubcarrier F hΦ₀ σ ξ ⟨rightConv F ψ f, hψf⟩⟫_ℂ := by
    rw [← hlift ⟨ψ, hψ⟩ hψf]
    exact hsymm v _
  rw [h0, inner_zero_left] at h1

  have h2 : ⟪v, toCuspSubcarrier F hΦ₀ σ ξ ⟨rightConv F ψ f, hψf⟩⟫_ℂ =
      a - ⟪v, toCuspSubcarrier F hΦ₀ σ ξ ⟨ψ, hψ⟩ - toCuspSubcarrier F hΦ₀ σ ξ ⟨rightConv F ψ f, hψf⟩⟫_ℂ := by
    rw [inner_sub_right, ha]; ring
  have h3 : ‖⟪v, toCuspSubcarrier F hΦ₀ σ ξ ⟨ψ, hψ⟩ - toCuspSubcarrier F hΦ₀ σ ξ ⟨rightConv F ψ f, hψf⟩⟫_ℂ‖ < ‖a‖ := by
    calc _ ≤ ‖v‖ * ‖toCuspSubcarrier F hΦ₀ σ ξ ⟨ψ, hψ⟩ - toCuspSubcarrier F hΦ₀ σ ξ ⟨rightConv F ψ f, hψf⟩‖ := norm_inner_le_norm _ _
      _ ≤ ‖v‖ * ε := mul_le_mul_of_nonneg_left hclose.le (norm_nonneg _)
      _ < ‖a‖ := by
          rw [hεdef, mul_div_assoc']
          rw [div_lt_iff₀ hv1]
          nlinarith [norm_nonneg v]
  have h4 : ⟪v, toCuspSubcarrier F hΦ₀ σ ξ ⟨rightConv F ψ f, hψf⟩⟫_ℂ ≠ 0 := by
    rw [h2]
    intro hz
    rw [sub_eq_zero] at hz
    rw [← hz] at h3
    exact lt_irrefl _ h3
  exact h4 h1.symm

end S_AutomorphicForm_CuspidalSpectrum_exists_isArchBiFinite_flat_isCompactOperator_lift_rightConv_apply_ne_zero
end P2MW
export P2MW.S_AutomorphicForm_CuspidalSpectrum_exists_isArchBiFinite_flat_isCompactOperator_lift_rightConv_apply_ne_zero (solution)
