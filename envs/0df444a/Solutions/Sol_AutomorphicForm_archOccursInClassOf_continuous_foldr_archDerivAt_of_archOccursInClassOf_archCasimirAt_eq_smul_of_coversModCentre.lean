-- Prove2me | solution 1 for AutomorphicForm.archOccursInClassOf_continuous_foldr_archDerivAt_of_archOccursInClassOf_archCasimirAt_eq_smul_of_coversModCentre
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.553648+00:00
-- url     : https://prove2.me/submissions/ebca3ce1-f07e-5d9b-8bb5-1fe737085fe7

import Mathlib
import Definitions.Def_AutomorphicForm_TranslateSpanOccurrence
import Definitions.Def_AutomorphicForm_ArchDerivCasimir
import Definitions.Def_NumberField_TateGlobalZeta
import Definitions.Def_AutomorphicForm_IsotypicCuspSpace
import Definitions.Def_AutomorphicForm_FactorizableTestFn
import Definitions.Def_AutomorphicForm_RightConvolution
import Theorems.Thm_AutomorphicForm_IsIsotypicCuspFormAt_exists_smoothCuspRealizationAt_toFun_eq_of_ne_bot
import Theorems.Thm_AutomorphicForm_isIsotypicCuspFormAt_of_mem_isotypicCuspSubmodule
import Theorems.Thm_AutomorphicForm_coversModCentre_and_archOccursInClassOf_iff_of_detWindow_le
import Theorems.Thm_AutomorphicForm_not_isArithGenuineCuspRealizable_of_nonpos_of_lt_of_coversModCentre
import Theorems.Thm_AutomorphicForm_SmoothCuspRealizationAt_exists_rightConv_ne_zero_mem_isotypicCuspSubmodule_mem_archCutSubmodule_hasArchCharacterAt_of_isReal
import Theorems.Thm_AutomorphicForm_archCasimirAt_rightConv_eq_smul_of_archCasimirAt_eq_smul_of_isArchSmoothAt_of_isFactorizableTestFn
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_archOccursInClassOf_continuous_foldr_archDerivAt_of_archOccursInClassOf_archCasimirAt_eq_smul_of_coversModCentre
p2m_attr_erase "instance" "RestrictedProduct.SecondCountableTopology_of_principal instCountableElemSetSetsCofinite_definitions instCountableOfNumberField_definitions instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions"
p2m_attr_erase "simp" "ContinuousAddEquiv.restrictedProductPi_apply RestrictedProduct.flatten_homeomorph_apply RestrictedProduct.flatten_homeomorph'_symm_apply ContinuousMulEquiv.restrictedProductPi_symm_apply RestrictedProduct.flatten_homeomorph'_apply RestrictedProduct.flatten_homeomorph_symm_apply ContinuousMulEquiv.restrictedProductPi_apply ContinuousAddEquiv.restrictedProductPi_symm_apply RingEquiv.restrictedProductCongr_symm_apply RingEquiv.restrictedProductCongrRight_apply MulEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductProd_symm_apply_coe Equiv.restrictedProductCongrRight_apply AddEquiv.restrictedProductCongr_apply Equiv.restrictedProductCongrLeft'_symm_apply_apply Equiv.restrictedProductCongr_apply_apply Equiv.restrictedProductCongrLeft_apply_apply RestrictedProduct.flatten_equiv'_apply AddEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductCongr_symm_apply Equiv.restrictedProductCongrRight_symm_apply RestrictedProduct.flatten_equiv'_symm_apply AddEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductCongrLeft'_apply RestrictedProduct.flatten_apply RingEquiv.restrictedProductCongr_apply_apply RingEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductProd_apply RestrictedProduct.flatten_equiv_apply RestrictedProduct.flatten_equiv_symm_apply LinearEquiv.restrictedProductCongrLeft'_apply RestrictedProduct.not_mem_support RestrictedProduct.mem_structureSubring_iff RestrictedProduct.not_mem_mulSupport RestrictedProduct.support_neg RestrictedProduct.mem_indexSupport_iff RestrictedProduct.mulSupport_inv RestrictedProduct.mapAlongLinearMap_apply AutomorphicForm.whittakerCoefficient_zero NumberField.StandardAddChar.ratArchLine_apply"
p2m_attr_erase "simp" "NumberField.StandardAddChar.AdelicTraceData.mk.sizeOf_spec NumberField.StandardAddChar.AdelicTraceData.mk.injEq NumberField.AdelicTrace.traceDiag_apply NumberField.AdelicTrace.diag_apply"

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 80000
set_option Elab.async false

p2m_open "NumberField NumberField.AdelicLevel NumberField.AdelicBox AutomorphicForm P2MW.S_AutomorphicForm_archOccursInClassOf_continuous_foldr_archDerivAt_of_archOccursInClassOf_archCasimirAt_eq_smul_of_coversModCentre.AutomorphicForm AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering NumberField.InfinitePlace NumberField.InfinitePlace.Completion"

open IsDedekindDomain NumberField.AdelicVolume

noncomputable section

namespace AutomorphicForm
p2m_export "AutomorphicForm" "TranslateSpanOccurrence.agrees_trans ArchOccursInClassOf SmoothCuspRealizationAt AdelicGL2 HeckeEigensystem rowIsometrySubgroup₀Map norm_ringEquivRealOfIsReal archWeightCharℝ HasArchCharacterAt₀ IsArchSmoothAt ArchDir archDerivAt archCasimirAt IsIsotypicCuspFormAt rightConv IsIsotypicCuspFormAt.exists_smoothCuspRealizationAt_toFun_eq_of_ne_bot isIsotypicCuspFormAt_of_mem_isotypicCuspSubmodule coversModCentre_and_archOccursInClassOf_iff_of_detWindow_le not_isArithGenuineCuspRealizable_of_nonpos_of_lt_of_coversModCentre SmoothCuspRealizationAt.exists_rightConv_ne_zero_mem_isotypicCuspSubmodule_mem_archCutSubmodule_hasArchCharacterAt_of_isReal archCasimirAt_rightConv_eq_smul_of_archCasimirAt_eq_smul_of_isArchSmoothAt_of_isFactorizableTestFn"
namespace RegUpAssembly
p2m_open "AutomorphicForm"

variable {F : Type} [Field F] [NumberField F]

theorem agrees_of_forall {Ψ Θ : HeckeEigensystem F ℂ} (ha : ∀ v, Ψ.a v = Θ.a v) (hb : ∀ v, Ψ.b v = Θ.b v) :
    Ψ.AgreesAwayFromFinite Θ :=
  ⟨∅, fun v _ => ⟨ha v, hb v⟩⟩

theorem archDetNorm_pos (w : InfinitePlace F) (g : AdelicGL2 (𝓞 F) F) : 0 < archDetNorm w g := by
  unfold archDetNorm
  rw [norm_pos_iff]
  exact ((Matrix.isUnit_iff_isUnit_det _).1 (Units.isUnit _)).ne_zero

theorem detCeiling_pos_of_coversModCentre {c u d₁ d₂ : ℝ} {T : Finset (AdelicGL2 (𝓞 F) F)}
    (hcov : CoversModCentre F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂)) (w : InfinitePlace F) : 0 < d₂ := by
  obtain ⟨γ, z, hmem⟩ := hcov 1
  simp only [Set.mem_iUnion, Set.mem_image] at hmem
  obtain ⟨x, -, s, hs, -⟩ := hmem
  have h := (hs.2.2.2 w).2
  exact lt_of_lt_of_le (archDetNorm_pos w s) h

theorem regup_pos (c u d₁ d₂ : ℝ) (T : Finset (AdelicGL2 (𝓞 F) F))
    (hc : 0 < c) (hd₁ : 0 < d₁) (hd : d₁ < d₂)
    (hcov : CoversModCentre F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂))
    (Θ : HeckeEigensystem F ℂ) (w : InfinitePlace F) (hw : w.IsReal) (n : ℤ) (lam : ℂ)
    (hocc : ArchOccursInClassOf F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂) Θ
      (fun φ => HasArchCharacterAt₀ F w ((archWeightCharℝ n).comp (rowIsometrySubgroup₀Map (ringEquivRealOfIsReal hw) (norm_ringEquivRealOfIsReal hw))) φ ∧ IsArchSmoothAt hw φ ∧ archCasimirAt hw φ = lam • φ)) :
    ArchOccursInClassOf F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂) Θ
      (fun φ => HasArchCharacterAt₀ F w ((archWeightCharℝ n).comp (rowIsometrySubgroup₀Map (ringEquivRealOfIsReal hw) (norm_ringEquivRealOfIsReal hw))) φ ∧ IsArchSmoothAt hw φ ∧
        (∀ l : List ArchDir, Continuous (l.foldr (archDerivAt hw) φ) ∧
              ∀ e₁ e₂ : ℝ, 0 < e₁ → e₁ < e₂ → ∃ B : ℝ, ∀ g : AdelicGL2 (𝓞 F) F,
                NumberField.TateGlobal.ideleNorm F (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc e₁ e₂ →
                  ‖l.foldr (archDerivAt hw) φ g‖ ≤ B) ∧
        archCasimirAt hw φ = lam • φ) := by
  obtain ⟨Θ', hΘ', R', hR', hty, hsm, hΩ⟩ := hocc

  obtain ⟨S, tys, f, hS, hf, hbi, hne, hmem, hcut, hty', hsm', hreg'⟩ :=
    AutomorphicForm.SmoothCuspRealizationAt.exists_rightConv_ne_zero_mem_isotypicCuspSubmodule_mem_archCutSubmodule_hasArchCharacterAt_of_isReal
      F c u d₁ d₂ T hc hd₁ hd hcov Θ' R' hR' w hw n hty

  have hΩ' := (AutomorphicForm.archCasimirAt_rightConv_eq_smul_of_archCasimirAt_eq_smul_of_isArchSmoothAt_of_isFactorizableTestFn
    F w hw R'.toFun hR' hsm lam hΩ f hf).2

  have hiso := AutomorphicForm.isIsotypicCuspFormAt_of_mem_isotypicCuspSubmodule F _ _ _ R'.centralChar Θ'.level S Θ'
    (rightConv F R'.toFun f) hmem hne
  obtain ⟨Ψ, R'', hlev, ha, hb, hfun, hξ, hS''⟩ :=
    AutomorphicForm.IsIsotypicCuspFormAt.exists_smoothCuspRealizationAt_toFun_eq_of_ne_bot F _ R'.centralChar Θ'.level
      Θ'.level_ne_bot S Θ' (rightConv F R'.toFun f) hiso hne
  have hagree : Ψ.AgreesAwayFromFinite Θ := TranslateSpanOccurrence.agrees_trans (agrees_of_forall ha hb) hΘ'
  have hcont : Continuous (rightConv F R'.toFun f) := (hreg' []).1
  refine ⟨Ψ, hagree, R'', ?_, ?_⟩
  · show Continuous R''.toFun
    rw [hfun]; exact hcont
  · rw [hfun]
    exact ⟨hty', hsm', hreg', hΩ'⟩

end AutomorphicForm.RegUpAssembly

end

open AutomorphicForm.RegUpAssembly in
theorem solution
    (F : Type) [Field F] [NumberField F] (c u d₁ d₂ : ℝ) (T : Finset (AdelicGL2 (𝓞 F) F))
    (hd : d₁ < d₂)
    (hcov : CoversModCentre F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂))
    (Θ : HeckeEigensystem F ℂ) (w : InfinitePlace F) (hw : w.IsReal) :
    ∀ (n : ℤ) (lam : ℂ),
      ArchOccursInClassOf F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂) Θ
          (fun φ => HasArchCharacterAt₀ F w ((archWeightCharℝ n).comp (rowIsometrySubgroup₀Map (ringEquivRealOfIsReal hw) (norm_ringEquivRealOfIsReal hw))) φ ∧
            IsArchSmoothAt hw φ ∧ archCasimirAt hw φ = lam • φ) →
        ArchOccursInClassOf F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂) Θ
          (fun φ => HasArchCharacterAt₀ F w ((archWeightCharℝ n).comp (rowIsometrySubgroup₀Map (ringEquivRealOfIsReal hw) (norm_ringEquivRealOfIsReal hw))) φ ∧
            IsArchSmoothAt hw φ ∧
            (∀ l : List ArchDir, Continuous (l.foldr (archDerivAt hw) φ) ∧
              ∀ e₁ e₂ : ℝ, 0 < e₁ → e₁ < e₂ → ∃ B : ℝ, ∀ g : AdelicGL2 (𝓞 F) F,
                NumberField.TateGlobal.ideleNorm F (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc e₁ e₂ →
                  ‖l.foldr (archDerivAt hw) φ g‖ ≤ B) ∧
            archCasimirAt hw φ = lam • φ) := by
  intro n lam hocc

  rcases le_or_gt c 0 with hc | hc
  · exfalso
    obtain ⟨Θ', -, hreal⟩ := hocc.isArithGenuineCuspRealizable
    exact AutomorphicForm.not_isArithGenuineCuspRealizable_of_nonpos_of_lt_of_coversModCentre F c u d₁ d₂ T hc hd hcov Θ'
      hreal

  have hd₂ : 0 < d₂ := detCeiling_pos_of_coversModCentre hcov w
  set dp : ℝ := if 0 < d₁ then d₁ else d₂ / 2 with hdp_def
  have hdp : 0 < dp := by
    rw [hdp_def]; split_ifs with h
    · exact h
    · linarith
  have hdp₂ : dp < d₂ := by
    rw [hdp_def]; split_ifs with h
    · exact hd
    · linarith
  have hd₁dp : d₁ ≤ dp := by
    rw [hdp_def]; split_ifs with h
    · exact le_rfl
    · linarith
  have hΘ : ArchOccursInClassOf F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂) Θ (fun _ => True) :=
    hocc.mono fun _ _ => trivial
  obtain ⟨hcov', hiff⟩ :=
    AutomorphicForm.coversModCentre_and_archOccursInClassOf_iff_of_detWindow_le F c u d₁ d₂ dp T hc hdp hdp₂ hd₁dp hcov Θ hΘ

  exact (hiff _).mpr (regup_pos c u dp d₂ T hc hdp hdp₂ hcov' Θ w hw n lam ((hiff _).mp hocc))

end S_AutomorphicForm_archOccursInClassOf_continuous_foldr_archDerivAt_of_archOccursInClassOf_archCasimirAt_eq_smul_of_coversModCentre
end P2MW
export P2MW.S_AutomorphicForm_archOccursInClassOf_continuous_foldr_archDerivAt_of_archOccursInClassOf_archCasimirAt_eq_smul_of_coversModCentre (solution)
