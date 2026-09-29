-- Prove2me | solution 1 for AutomorphicForm.archOccursInClassOf_archWeightChar_add_two_of_nonneg_of_coversModCentre
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.553648+00:00
-- url     : https://prove2.me/submissions/f6b0d20d-634e-50a2-b9a4-b0534272af72

import Mathlib
import Definitions.Def_AutomorphicForm_TranslateSpanOccurrence
import Definitions.Def_AutomorphicForm_ArchLoweringAnnihilated
import Theorems.Thm_AutomorphicForm_ArchOccursInClassOf_map_starRingEnd
import Theorems.Thm_AutomorphicForm_archOccursInClassOf_isArchLoweringAnnihilatedAt_of_not_archOccursInClassOf_archWeightChar_sub_two_of_coversModCentre
import Theorems.Thm_AutomorphicForm_one_le_of_archOccursInClassOf_isArchLoweringAnnihilatedAt_of_coversModCentre
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_archOccursInClassOf_archWeightChar_add_two_of_nonneg_of_coversModCentre
p2m_attr_erase "instance" "RestrictedProduct.SecondCountableTopology_of_principal instCountableElemSetSetsCofinite_definitions instCountableOfNumberField_definitions instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions"
p2m_attr_erase "simp" "AutomorphicForm.ArchDir.E.sizeOf_spec AutomorphicForm.ArchDir.H.sizeOf_spec AutomorphicForm.ArchDir.Fm.sizeOf_spec LanglandsTunnell.signShift_zero LanglandsTunnell.RealArchParam.twist_zero LanglandsTunnell.RealArchParam.discrete.sizeOf_spec LanglandsTunnell.RealArchParam.principal.injEq LanglandsTunnell.ComplexArchParam.dual_dual LanglandsTunnell.ComplexArchParam.mk.sizeOf_spec LanglandsTunnell.RealArchParam.dual_dual LanglandsTunnell.RealArchParam.discrete.injEq LanglandsTunnell.ComplexArchParam.twist_zero LanglandsTunnell.RealArchParam.principal.sizeOf_spec LanglandsTunnell.signShift_one LanglandsTunnell.ComplexArchParam.mk.injEq AutomorphicForm.whittakerCoefficient_zero NumberField.StandardAddChar.ratArchLine_apply NumberField.StandardAddChar.AdelicTraceData.mk.sizeOf_spec NumberField.StandardAddChar.AdelicTraceData.mk.injEq NumberField.AdelicTrace.traceDiag_apply NumberField.AdelicTrace.diag_apply AutomorphicForm.IsStableLinearOn.coe_toEnd_apply AutomorphicForm.ArchRepAt.mk.sizeOf_spec AutomorphicForm.IsIsotypicCuspFormAt.toRealization_toFun AutomorphicForm.ArchTypeFamily.mk.sizeOf_spec AutomorphicForm.charRep_apply AutomorphicForm.ArchRepAt.mk.injEq AutomorphicForm.ArchTypeFamily.mk.injEq M4aHerbrand.IdeleGaloisDescent.mk.sizeOf_spec M4aHerbrand.IdeleGaloisDescent.mk.injEq ContinuousAddEquiv.restrictedProductPi_apply RestrictedProduct.flatten_homeomorph_apply RestrictedProduct.flatten_homeomorph'_symm_apply ContinuousMulEquiv.restrictedProductPi_symm_apply RestrictedProduct.flatten_homeomorph'_apply RestrictedProduct.flatten_homeomorph_symm_apply ContinuousMulEquiv.restrictedProductPi_apply ContinuousAddEquiv.restrictedProductPi_symm_apply RingEquiv.restrictedProductCongr_symm_apply RingEquiv.restrictedProductCongrRight_apply"
p2m_attr_erase "simp" "MulEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductProd_symm_apply_coe Equiv.restrictedProductCongrRight_apply AddEquiv.restrictedProductCongr_apply Equiv.restrictedProductCongrLeft'_symm_apply_apply Equiv.restrictedProductCongr_apply_apply Equiv.restrictedProductCongrLeft_apply_apply RestrictedProduct.flatten_equiv'_apply AddEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductCongr_symm_apply Equiv.restrictedProductCongrRight_symm_apply RestrictedProduct.flatten_equiv'_symm_apply AddEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductCongrLeft'_apply RestrictedProduct.flatten_apply RingEquiv.restrictedProductCongr_apply_apply RingEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductProd_apply RestrictedProduct.flatten_equiv_apply RestrictedProduct.flatten_equiv_symm_apply LinearEquiv.restrictedProductCongrLeft'_apply RestrictedProduct.not_mem_support RestrictedProduct.mem_structureSubring_iff RestrictedProduct.not_mem_mulSupport RestrictedProduct.support_neg RestrictedProduct.mem_indexSupport_iff RestrictedProduct.mulSupport_inv RestrictedProduct.mapAlongLinearMap_apply AutomorphicForm.CuspidalConstituent.rightRegular_apply LanglandsTunnell.TateLocal.conductorExponentAt_one LanglandsTunnell.TateLocal.charExt_coe_units LanglandsTunnell.TateLocal.modulus_one LanglandsTunnell.TateLocal.modulus_zero LanglandsTunnell.TateLocal.modulus_coe_units LanglandsTunnell.TateLocal.charExt_zero LanglandsTunnell.signEpsilon_one LanglandsTunnell.RealArchParam.epsilonFactor_principal LanglandsTunnell.RealArchParam.epsilonFactor_discrete LanglandsTunnell.signEpsilon_zero LanglandsTunnell.LDatum.mk.sizeOf_spec"
p2m_attr_erase "simp" "LanglandsTunnell.LDatum.badFactor_zero LanglandsTunnell.LDatum.mk.injEq AutomorphicForm.rightTranslationEmbed_smul_apply AutomorphicForm.mem_inducedSectionSubmodule_iff AutomorphicForm.mem_borelSubgroup_iff AutomorphicForm.borelDiagFst_apply_val AutomorphicForm.borelDiagSnd_apply_val"

set_option autoImplicit false

p2m_open "NumberField NumberField.AdelicLevel NumberField.AdelicBox AutomorphicForm P2MW.S_AutomorphicForm_archOccursInClassOf_archWeightChar_add_two_of_nonneg_of_coversModCentre.AutomorphicForm AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering NumberField.InfinitePlace NumberField.InfinitePlace.Completion"

open scoped ComplexConjugate

noncomputable section

namespace AutomorphicForm
p2m_export "AutomorphicForm" "ArchOccursInClassOf AdelicGL2 HeckeEigensystem.map HeckeEigensystem HeckeEigensystem.mk.injEq HeckeEigensystem.mk rowIsometrySubgroup₀Map norm_ringEquivRealOfIsReal rowIsometrySubgroup₀ normSq_firstRowℂ_of_mem archWeightOneℝ archWeightCharℝ HasArchCharacterAt₀ ArchOccursInClassOf.map_starRingEnd archOccursInClassOf_isArchLoweringAnnihilatedAt_of_not_archOccursInClassOf_archWeightChar_sub_two_of_coversModCentre one_le_of_archOccursInClassOf_isArchLoweringAnnihilatedAt_of_coversModCentre"
p2m_open "AutomorphicForm"

namespace RaisingByConjugation

variable {F : Type} [Field F] [NumberField F]

theorem map_starRingEnd_map_starRingEnd (Θ : HeckeEigensystem F ℂ) :
    (Θ.map (starRingEnd ℂ)).map (starRingEnd ℂ) = Θ := by
  cases Θ with
  | mk level hlevel a b =>
    simp only [HeckeEigensystem.map, HeckeEigensystem.mk.injEq, true_and]
    constructor <;> funext v <;> exact Complex.conj_conj _

theorem normSq_archWeightOneℝ (k : rowIsometrySubgroup₀ ℝ) :
    Complex.normSq ((archWeightOneℝ k : ℂˣ) : ℂ) = 1 :=
  normSq_firstRowℂ_of_mem k.2

theorem conj_archWeightOneℝ (k : rowIsometrySubgroup₀ ℝ) :
    conj ((archWeightOneℝ k : ℂˣ) : ℂ) = ((archWeightOneℝ k : ℂˣ) : ℂ)⁻¹ := by
  rw [Complex.inv_def, normSq_archWeightOneℝ, inv_one, Complex.ofReal_one, mul_one]

theorem conj_archWeightCharℝ (m : ℤ) (k : rowIsometrySubgroup₀ ℝ) :
    conj ((archWeightCharℝ m k : ℂˣ) : ℂ) = ((archWeightCharℝ (-m) k : ℂˣ) : ℂ) := by
  simp only [archWeightCharℝ, MonoidHom.comp_apply, zpowGroupHom_apply, Units.val_zpow_eq_zpow_val]
  rw [map_zpow₀, conj_archWeightOneℝ, inv_zpow']

theorem hasArchCharacterAt₀_neg_of_conj {w : InfinitePlace F} (hw : w.IsReal) (m : ℤ)
    {φ : AdelicGL2 (𝓞 F) F → ℂ}
    (h : HasArchCharacterAt₀ F w
      ((archWeightCharℝ m).comp (rowIsometrySubgroup₀Map (ringEquivRealOfIsReal hw)
        (norm_ringEquivRealOfIsReal hw))) (fun g => conj (φ g))) :
    HasArchCharacterAt₀ F w
      ((archWeightCharℝ (-m)).comp (rowIsometrySubgroup₀Map (ringEquivRealOfIsReal hw)
        (norm_ringEquivRealOfIsReal hw))) φ := by
  intro k g
  have hk := h k g
  have hk' := congrArg conj hk
  simp only [map_mul, Complex.conj_conj, MonoidHom.comp_apply] at hk'
  rw [hk', MonoidHom.comp_apply, conj_archWeightCharℝ]

end RaisingByConjugation

end AutomorphicForm

end

open AutomorphicForm.RaisingByConjugation in
theorem solution
    (F : Type) [Field F] [NumberField F] (c u d₁ d₂ : ℝ) (T : Finset (AdelicGL2 (𝓞 F) F))
    (hd : d₁ < d₂)
    (hcov : CoversModCentre F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂))
    (Θ : HeckeEigensystem F ℂ)
    (w : InfinitePlace F) (hw : w.IsReal) (n : ℤ) (hn0 : 0 ≤ n)
    (hn :
      ArchOccursInClassOf F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂) Θ
        (fun φ => HasArchCharacterAt₀ F w
          ((archWeightCharℝ n).comp (rowIsometrySubgroup₀Map (ringEquivRealOfIsReal hw)
            (norm_ringEquivRealOfIsReal hw))) φ)) :
    ArchOccursInClassOf F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂) Θ
      (fun φ => HasArchCharacterAt₀ F w
        ((archWeightCharℝ (n + 2)).comp (rowIsometrySubgroup₀Map (ringEquivRealOfIsReal hw)
          (norm_ringEquivRealOfIsReal hw))) φ) := by

  have h1 : ArchOccursInClassOf F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂)
      (Θ.map (starRingEnd ℂ))
      (fun φ => HasArchCharacterAt₀ F w
        ((archWeightCharℝ (-n)).comp (rowIsometrySubgroup₀Map (ringEquivRealOfIsReal hw)
          (norm_ringEquivRealOfIsReal hw))) φ) :=
    (AutomorphicForm.ArchOccursInClassOf.map_starRingEnd F _ Θ _ hn).mono
      (fun φ hφ => hasArchCharacterAt₀_neg_of_conj hw n hφ)
  by_cases h2 : ArchOccursInClassOf F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂)
      (Θ.map (starRingEnd ℂ))
      (fun φ => HasArchCharacterAt₀ F w
        ((archWeightCharℝ (-n - 2)).comp (rowIsometrySubgroup₀Map (ringEquivRealOfIsReal hw)
          (norm_ringEquivRealOfIsReal hw))) φ)
  ·
    have h3 := (AutomorphicForm.ArchOccursInClassOf.map_starRingEnd F _ (Θ.map (starRingEnd ℂ)) _ h2).mono
      (fun φ hφ => hasArchCharacterAt₀_neg_of_conj hw (-n - 2) hφ)
    rw [map_starRingEnd_map_starRingEnd] at h3
    have e : -(-n - 2) = n + 2 := by ring
    rw [e] at h3
    exact h3
  ·
    exfalso
    have h4 :=
      AutomorphicForm.archOccursInClassOf_isArchLoweringAnnihilatedAt_of_not_archOccursInClassOf_archWeightChar_sub_two_of_coversModCentre
        F c u d₁ d₂ T hd hcov (Θ.map (starRingEnd ℂ)) w hw (-n) h1 h2
    have h5 :=
      AutomorphicForm.one_le_of_archOccursInClassOf_isArchLoweringAnnihilatedAt_of_coversModCentre
        F c u d₁ d₂ T hd hcov (Θ.map (starRingEnd ℂ)) w hw (-n) h4
    omega

end S_AutomorphicForm_archOccursInClassOf_archWeightChar_add_two_of_nonneg_of_coversModCentre
end P2MW
export P2MW.S_AutomorphicForm_archOccursInClassOf_archWeightChar_add_two_of_nonneg_of_coversModCentre (solution)
