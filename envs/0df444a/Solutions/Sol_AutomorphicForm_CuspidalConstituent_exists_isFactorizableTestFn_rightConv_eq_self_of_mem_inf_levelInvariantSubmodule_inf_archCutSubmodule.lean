-- Prove2me | solution 1 for AutomorphicForm.CuspidalConstituent.exists_isFactorizableTestFn_rightConv_eq_self_of_mem_inf_levelInvariantSubmodule_inf_archCutSubmodule
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.553648+00:00
-- url     : https://prove2.me/submissions/ea32b4b8-5563-5dd2-a502-f137e11dab79

import Definitions.Def_AutomorphicForm_TranslateSpanOccurrence
import Definitions.Def_LanglandsTunnell_JLConverse
import Definitions.Def_LanglandsTunnell_RankinSelbergEuler
import Definitions.Def_AutomorphicForm_IsotypicCuspSpace
import Definitions.Def_NumberField_AdelicTraceFin
import Definitions.Def_AutomorphicForm_ProductionPinsGeneral
import Definitions.Def_AutomorphicForm_FormalBaseChange
import Definitions.Def_AutomorphicForm_ArchWeightCharTransport
import Definitions.Def_AutomorphicForm_FactorizableTestFn
import Definitions.Def_AutomorphicForm_WhittakerCoefficient
import Mathlib.Analysis.MellinTransform
import Definitions.Def_NumberField_StandardGlobalAddCharRat
import Definitions.Def_LanglandsTunnell_ConverseData
import Definitions.Def_LanglandsTunnell_ArchBaseChange
import Definitions.Def_LanglandsTunnell_ArchCasimirCompanion
import Definitions.Def_AutomorphicForm_WhittakerModelLocal
import Definitions.Def_AutomorphicForm_CuspidalConstituent
import Definitions.Def_AutomorphicForm_ArchDerivCasimir
import Theorems.Thm_AutomorphicForm_exists_isFactorizableTestFn_isArchBiFinite_forall_rightConv_eq_self_of_finiteDimensional_of_isCompact
import Theorems.Thm_AutomorphicForm_finiteDimensional_inf_levelInvariantSubmodule_inf_archCutSubmodule_of_isCuspConstituent
import Theorems.Thm_AutomorphicForm_CuspidalConstituent_rightConv_mem_levelInvariantSubmodule_inf_archCutSubmodule_of_isArchBiFinite
import Theorems.Thm_AutomorphicForm_isCompact_levelOne_inf_finiteAdelicGL2Subgroup
import Theorems.Thm_NumberField_AdelicLevel_exists_globalPoints_mul_mem_finiteIntegralGL2_rat
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_CuspidalConstituent_exists_isFactorizableTestFn_rightConv_eq_self_of_mem_inf_levelInvariantSubmodule_inf_archCutSubmodule
p2m_attr_erase "instance" "AutomorphicForm.compactSpace_maximalCompactAway AutomorphicForm.compactSpace_adelicMaximalCompact AutomorphicForm.isProbabilityMeasure_maximalCompactHaar AutomorphicForm.isHaarMeasure_maximalCompactHaar AutomorphicForm.compactSpace_maximalCompactAt AutomorphicForm.isProbabilityMeasure_maximalCompactAwayHaar AutomorphicForm.isHaarMeasure_maximalCompactAwayHaar AutomorphicForm.isProbabilityMeasure_maximalCompactAtHaar AutomorphicForm.isHaarMeasure_maximalCompactAtHaar instCountableOfNumberField_definitions RestrictedProduct.SecondCountableTopology_of_principal instCountableElemSetSetsCofinite_definitions instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions"
p2m_attr_erase "simp" "ContinuousAddEquiv.restrictedProductPi_apply RestrictedProduct.flatten_homeomorph_apply RestrictedProduct.flatten_homeomorph'_symm_apply ContinuousMulEquiv.restrictedProductPi_symm_apply RestrictedProduct.flatten_homeomorph'_apply RestrictedProduct.flatten_homeomorph_symm_apply ContinuousMulEquiv.restrictedProductPi_apply ContinuousAddEquiv.restrictedProductPi_symm_apply RingEquiv.restrictedProductCongr_symm_apply RingEquiv.restrictedProductCongrRight_apply MulEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductProd_symm_apply_coe Equiv.restrictedProductCongrRight_apply AddEquiv.restrictedProductCongr_apply Equiv.restrictedProductCongrLeft'_symm_apply_apply Equiv.restrictedProductCongr_apply_apply Equiv.restrictedProductCongrLeft_apply_apply RestrictedProduct.flatten_equiv'_apply AddEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductCongr_symm_apply Equiv.restrictedProductCongrRight_symm_apply RestrictedProduct.flatten_equiv'_symm_apply AddEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductCongrLeft'_apply RestrictedProduct.flatten_apply RingEquiv.restrictedProductCongr_apply_apply RingEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductProd_apply RestrictedProduct.flatten_equiv_apply RestrictedProduct.flatten_equiv_symm_apply LinearEquiv.restrictedProductCongrLeft'_apply RestrictedProduct.not_mem_support RestrictedProduct.mem_structureSubring_iff RestrictedProduct.not_mem_mulSupport RestrictedProduct.support_neg RestrictedProduct.mem_indexSupport_iff RestrictedProduct.mulSupport_inv RestrictedProduct.mapAlongLinearMap_apply AutomorphicForm.fnTwist_zero AutomorphicForm.fnTwist_apply"

set_option autoImplicit false

open IsDedekindDomain NumberField AutomorphicForm LanglandsTunnell LanglandsTunnell.Converse
open NumberField.TateGlobal NumberField.AdelicLevel NumberField.AdelicBox NumberField.InfinitePlace.Completion
open AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering NumberField.InfinitePlace LanglandsTunnell.RealArchParam
open scoped nonZeroDivisors

namespace Ws47
namespace C6

open AutomorphicForm.CuspidalConstituent

theorem continuous_of_mem_cuspKFiniteSubmodule (pins : CarrierPins ℚ) (ξ : pins.Z →* ℂˣ)
    {φ : AdelicGL2 (𝓞 ℚ) ℚ → ℂ} (h : φ ∈ cuspKFiniteSubmodule ℚ pins ξ) : Continuous φ := by
  unfold cuspKFiniteSubmodule at h
  refine Submodule.span_induction (p := fun ψ _ => Continuous ψ) ?_ ?_ ?_ ?_ h
  · rintro ψ ⟨-, hc, -⟩
    exact hc
  · exact continuous_zero
  · rintro ψ₁ ψ₂ - - h₁ h₂
    exact h₁.add h₂
  · rintro a ψ - h
    exact h.const_smul a

theorem coversModCentre_classRepSiegelSet_rat :
    CoversModCentre ℚ (classRepSiegelSet ℚ (1/2 : ℝ) 1 (1/2) 2) := by
  have hfin : FiniteIntegralCovering ℚ := fun g =>
    NumberField.AdelicLevel.exists_globalPoints_mul_mem_finiteIntegralGL2_rat g
  have h3 : (1 / 2 : ℝ) ≤ Real.sqrt 3 / 2 := by
    have h1 : (1 : ℝ) ≤ Real.sqrt 3 := by
      rw [show (1 : ℝ) = Real.sqrt 1 from Real.sqrt_one.symm]
      exact Real.sqrt_le_sqrt (by norm_num)
    linarith
  have h := coversModCentre_centreCutSiegelSet_rat hfin (c := (1/2 : ℝ)) (u := (1 : ℝ)) (d₁ := (1/2 : ℝ))
    (d₂ := (2 : ℝ)) h3 (by norm_num) (by norm_num) (by norm_num)
  exact h.mono (centreCutSiegelSet_subset_classRepSiegelSet ℚ _ _ _ _)

end Ws47.C6

open Ws47.C6 AutomorphicForm.CuspidalConstituent in
theorem solution
    (ξ : (productionPinsGeneral ℚ).Z →* ℂˣ)
    (V : Submodule ℂ (AdelicGL2 (𝓞 ℚ) ℚ → ℂ))
    (hV : CuspidalConstituent.IsCuspConstituent ℚ (productionPinsGeneral ℚ) ξ V)
    (N : Ideal (𝓞 ℚ)) (hN : N ≠ ⊥) (tys : ArchTypeFamily ℚ)
    (φ : AdelicGL2 (𝓞 ℚ) ℚ → ℂ)
    (hφ : φ ∈ V ⊓ CuspidalConstituent.levelInvariantSubmodule ℚ (productionPinsGeneral ℚ) N ⊓ archCutSubmodule ℚ tys) :
    ∃ α : AdelicGL2 (𝓞 ℚ) ℚ → ℂ, IsFactorizableTestFn ℚ α ∧ rightConv ℚ φ α = φ := by
  classical
  let U : Subgroup (AdelicGL2 (𝓞 ℚ) ℚ) := levelOne (𝓞 ℚ) ℚ N ⊓ finiteAdelicGL2Subgroup ℚ
  let Y : Submodule ℂ (AdelicGL2 (𝓞 ℚ) ℚ → ℂ) :=
    V ⊓ CuspidalConstituent.levelInvariantSubmodule ℚ (productionPinsGeneral ℚ) N ⊓ archCutSubmodule ℚ tys

  have hY : FiniteDimensional ℂ ↥Y :=
    AutomorphicForm.finiteDimensional_inf_levelInvariantSubmodule_inf_archCutSubmodule_of_isCuspConstituent
      ℚ (1/2 : ℝ) 1 (1/2) 2 (classRepTranslates ℚ) (by norm_num) coversModCentre_classRepSiegelSet_rat ξ N hN tys V hV

  have hYc : ∀ y ∈ Y, Continuous y := fun y hy =>
    continuous_of_mem_cuspKFiniteSubmodule _ ξ (hV.1.le hy.1.1)

  have hYU : ∀ y ∈ Y, ∀ g : AdelicGL2 (𝓞 ℚ) ℚ, ∀ k ∈ U, y (g * k) = y g :=
    fun y hy g k hk => hy.1.2 g k hk

  have hYt : Y ≤ archCutSubmodule ℚ tys := fun y hy => hy.2

  have hYs : ∀ f : AdelicGL2 (𝓞 ℚ) ℚ → ℂ, IsFactorizableTestFn ℚ f → IsLevelSphericalOfType ℚ tys U f →
      ∀ y ∈ Y, rightConv ℚ y f ∈ Y := by
    intro f hfT hsph y hy
    obtain ⟨fa, hfa1, hfa2, hfa3, hfac⟩ := hsph
    have hbf : IsArchBiFinite ℚ tys f := IsArchBiFinite.of_factorization ℚ hfac hfa2
    have hV' : rightConv ℚ y f ∈ V := hV.1.rightConv_mem f tys hfT hbf y hy.1.1
    have hfs : ∀ x, f x ≠ 0 → ∃ a k : AdelicGL2 (𝓞 ℚ) ℚ,
        glFin (𝓞 ℚ) ℚ a = 1 ∧ k ∈ (productionPinsGeneral ℚ).U N ∧ x = a * k := by
      intro x hx
      rw [hfac x] at hx
      have hind : Set.indicator ((glFin (𝓞 ℚ) ℚ) '' (U : Set (AdelicGL2 (𝓞 ℚ) ℚ))) (fun _ => (1 : ℂ))
          (glFin (𝓞 ℚ) ℚ x) ≠ 0 := fun h0 => hx (by rw [h0, mul_zero])
      obtain ⟨k, hkU, hk⟩ := Set.mem_of_indicator_ne_zero hind
      refine ⟨x * k⁻¹, k, ?_, hkU, (inv_mul_cancel_right x k).symm⟩
      rw [map_mul, map_inv, hk, mul_inv_cancel]
    have h2 :=
      AutomorphicForm.CuspidalConstituent.rightConv_mem_levelInvariantSubmodule_inf_archCutSubmodule_of_isArchBiFinite
        ℚ (classRepSiegelSet ℚ (1/2 : ℝ) 1 (1/2) 2) N tys f hfT hbf hfs y (hYc y hy) hy.1.2
    exact ⟨⟨hV', h2.1⟩, h2.2⟩

  obtain ⟨f, hfT, -, -, hrep⟩ :=
    AutomorphicForm.exists_isFactorizableTestFn_isArchBiFinite_forall_rightConv_eq_self_of_finiteDimensional_of_isCompact
      ℚ U (AutomorphicForm.isCompact_levelOne_inf_finiteAdelicGL2Subgroup ℚ N) (levelOne (𝓞 ℚ) ℚ N)
      (isOpen_levelOne (𝓞 ℚ) ℚ hN) rfl tys Y hY hYc hYU hYt hYs
  exact ⟨f, hfT, hrep φ hφ⟩

end S_AutomorphicForm_CuspidalConstituent_exists_isFactorizableTestFn_rightConv_eq_self_of_mem_inf_levelInvariantSubmodule_inf_archCutSubmodule
end P2MW
export P2MW.S_AutomorphicForm_CuspidalConstituent_exists_isFactorizableTestFn_rightConv_eq_self_of_mem_inf_levelInvariantSubmodule_inf_archCutSubmodule (solution)
