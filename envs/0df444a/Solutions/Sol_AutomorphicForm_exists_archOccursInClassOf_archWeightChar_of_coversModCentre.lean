-- Prove2me | solution 1 for AutomorphicForm.exists_archOccursInClassOf_archWeightChar_of_coversModCentre
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.961684+00:00
-- url     : https://prove2.me/submissions/f0d0ad06-ce19-5747-93e6-edca55455a52

import Theorems.Thm_AutomorphicForm_not_isArithGenuineCuspRealizable_of_nonpos_of_lt_of_coversModCentre
import Theorems.Thm_AutomorphicForm_coversModCentre_and_archOccursInClassOf_iff_of_detWindow_le
import Theorems.Thm_AutomorphicForm_exists_archOccursInClassOf_archWeightChar_of_coversModCentre_of_pos
import Definitions.Def_AutomorphicForm_TranslateSpanOccurrence
import Definitions.Def_AutomorphicForm_ArchLoweringAnnihilated
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_exists_archOccursInClassOf_archWeightChar_of_coversModCentre
p2m_attr_erase "instance" "RestrictedProduct.SecondCountableTopology_of_principal instCountableElemSetSetsCofinite_definitions instCountableOfNumberField_definitions instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions"
p2m_attr_erase "simp" "ContinuousAddEquiv.restrictedProductPi_apply RestrictedProduct.flatten_homeomorph_apply RestrictedProduct.flatten_homeomorph'_symm_apply ContinuousMulEquiv.restrictedProductPi_symm_apply RestrictedProduct.flatten_homeomorph'_apply RestrictedProduct.flatten_homeomorph_symm_apply ContinuousMulEquiv.restrictedProductPi_apply ContinuousAddEquiv.restrictedProductPi_symm_apply RingEquiv.restrictedProductCongr_symm_apply RingEquiv.restrictedProductCongrRight_apply MulEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductProd_symm_apply_coe Equiv.restrictedProductCongrRight_apply AddEquiv.restrictedProductCongr_apply Equiv.restrictedProductCongrLeft'_symm_apply_apply Equiv.restrictedProductCongr_apply_apply Equiv.restrictedProductCongrLeft_apply_apply RestrictedProduct.flatten_equiv'_apply AddEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductCongr_symm_apply Equiv.restrictedProductCongrRight_symm_apply RestrictedProduct.flatten_equiv'_symm_apply AddEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductCongrLeft'_apply RestrictedProduct.flatten_apply RingEquiv.restrictedProductCongr_apply_apply RingEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductProd_apply RestrictedProduct.flatten_equiv_apply RestrictedProduct.flatten_equiv_symm_apply LinearEquiv.restrictedProductCongrLeft'_apply RestrictedProduct.not_mem_support RestrictedProduct.mem_structureSubring_iff RestrictedProduct.not_mem_mulSupport RestrictedProduct.support_neg RestrictedProduct.mem_indexSupport_iff RestrictedProduct.mulSupport_inv RestrictedProduct.mapAlongLinearMap_apply AutomorphicForm.whittakerCoefficient_zero NumberField.StandardAddChar.ratArchLine_apply"
p2m_attr_erase "simp" "NumberField.StandardAddChar.AdelicTraceData.mk.sizeOf_spec NumberField.StandardAddChar.AdelicTraceData.mk.injEq NumberField.AdelicTrace.traceDiag_apply NumberField.AdelicTrace.diag_apply M4aHerbrand.IdeleGaloisDescent.mk.sizeOf_spec M4aHerbrand.IdeleGaloisDescent.mk.injEq"

set_option autoImplicit false

open NumberField NumberField.AdelicLevel NumberField.AdelicBox AutomorphicForm AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering NumberField.InfinitePlace NumberField.InfinitePlace.Completion

namespace Ws1
namespace PWindow

variable {F : Type} [Field F] [NumberField F]

theorem detCeil_pos_of_coversModCentre {c u d₁ d₂ : ℝ} {T : Finset (AdelicGL2 (𝓞 F) F)}
    (hcov : CoversModCentre F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂)) : 0 < d₂ := by
  by_contra hd₂
  push Not at hd₂
  have hempty : centreCutSiegelSet F c u d₁ d₂ = ∅ := by
    ext g
    simp only [Set.mem_empty_iff_false, iff_false]
    intro hg
    obtain ⟨w⟩ := (inferInstance : Nonempty (InfinitePlace F))
    have h := ((mem_centreCutSiegelSet_iff.mp hg).2.2.2 w).2
    exact absurd (lt_of_lt_of_le (NumberField.AdelicVolume.archDetNorm_pos w g) (h.trans hd₂)) (lt_irrefl _)
  have hD : (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂) = ∅ := by
    simp only [hempty, Set.image_empty, Set.iUnion_empty]
  rw [hD] at hcov
  exact not_coversModCentre_empty hcov

theorem heightFloor_pos_of_archOccursInClassOf {c u d₁ d₂ : ℝ} {T : Finset (AdelicGL2 (𝓞 F) F)}
    (hd : d₁ < d₂) (hcov : CoversModCentre F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂))
    {Θ : HeckeEigensystem F ℂ} {P : (AdelicGL2 (𝓞 F) F → ℂ) → Prop}
    (h : ArchOccursInClassOf F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂) Θ P) : 0 < c := by
  by_contra hc
  push Not at hc
  obtain ⟨Θ', -, hΘ'⟩ := h.isArithGenuineCuspRealizable
  exact AutomorphicForm.not_isArithGenuineCuspRealizable_of_nonpos_of_lt_of_coversModCentre
    F c u d₁ d₂ T hc hd hcov Θ' hΘ'

theorem exists_pos_detWindow {c u d₁ d₂ : ℝ} {T : Finset (AdelicGL2 (𝓞 F) F)}
    (hd : d₁ < d₂) (hcov : CoversModCentre F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂))
    {Θ : HeckeEigensystem F ℂ} {P : (AdelicGL2 (𝓞 F) F → ℂ) → Prop}
    (h : ArchOccursInClassOf F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂) Θ P) :
    0 < c ∧ ∃ dp : ℝ, 0 < dp ∧ dp < d₂ ∧ d₁ ≤ dp ∧
      CoversModCentre F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u dp d₂) ∧
      ∀ Q : (AdelicGL2 (𝓞 F) F → ℂ) → Prop,
        ArchOccursInClassOf F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂) Θ Q ↔
          ArchOccursInClassOf F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u dp d₂) Θ Q := by
  have hc : 0 < c := heightFloor_pos_of_archOccursInClassOf hd hcov h
  have hd₂ : 0 < d₂ := detCeil_pos_of_coversModCentre hcov
  have hΘ : ArchOccursInClassOf F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂) Θ (fun _ => True) := h.mono fun _ _ => trivial
  refine ⟨hc, max d₁ (d₂ / 2), lt_max_of_lt_right (by linarith), max_lt hd (by linarith), le_max_left _ _, ?_⟩
  exact AutomorphicForm.coversModCentre_and_archOccursInClassOf_iff_of_detWindow_le F c u d₁ d₂ (max d₁ (d₂ / 2)) T
    hc (lt_max_of_lt_right (by linarith)) (max_lt hd (by linarith)) (le_max_left _ _) hcov Θ hΘ

end Ws1.PWindow

open Ws1.PWindow in
theorem solution
    (F : Type) [Field F] [NumberField F] (c u d₁ d₂ : ℝ) (T : Finset (AdelicGL2 (𝓞 F) F))
    (hd : d₁ < d₂)
    (hcov : CoversModCentre F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂))
    (Θ : HeckeEigensystem F ℂ)
    (hΘ : ArchOccursInClassOf F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂) Θ (fun _ => True))
    (w : InfinitePlace F) (hw : w.IsReal) :
    ∃ n : ℤ,
      ArchOccursInClassOf F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂) Θ
        (fun φ => HasArchCharacterAt₀ F w
          ((archWeightCharℝ n).comp (rowIsometrySubgroup₀Map (ringEquivRealOfIsReal hw)
            (norm_ringEquivRealOfIsReal hw))) φ) := by
  obtain ⟨hc, dp, hdp, hdp₂, -, hcov', hiff⟩ := exists_pos_detWindow hd hcov hΘ
  obtain ⟨n, hn⟩ :=
    AutomorphicForm.exists_archOccursInClassOf_archWeightChar_of_coversModCentre_of_pos F c u dp d₂ T hdp₂ hc hdp
      hcov' Θ ((hiff _).mp hΘ) w hw
  exact ⟨n, (hiff _).mpr hn⟩

end S_AutomorphicForm_exists_archOccursInClassOf_archWeightChar_of_coversModCentre
end P2MW
export P2MW.S_AutomorphicForm_exists_archOccursInClassOf_archWeightChar_of_coversModCentre (solution)
