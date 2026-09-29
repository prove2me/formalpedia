-- Prove2me | solution 1 for AutomorphicForm.isCuspAutomorphicFnAt_comp_mul_right_and_sub_of_rightConv_eq_rat
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.340288+00:00
-- url     : https://prove2.me/submissions/0125d915-489b-585b-82c2-58c7a91656b9

import Definitions.Def_AutomorphicForm_ProductionPinsGeneral
import Definitions.Def_LanglandsTunnell_RankinSelbergEuler
import Definitions.Def_LanglandsTunnell_RS22GlobalIntegral
import Definitions.Def_AutomorphicForm_GodementSection
import Definitions.Def_LanglandsTunnell_RSCarrier
import Definitions.Def_LanglandsTunnell_RSCarrierSplit
import Definitions.Def_LanglandsTunnell_DeltaLift
import Definitions.Def_AutomorphicForm_WhittakerCoefficient
import Definitions.Def_AutomorphicForm_SiegelCoordinates
import Definitions.Def_AutomorphicForm_RowIsometryInvariance
import Definitions.Def_NumberField_StandardGlobalAddCharRat
import Definitions.Def_UnramifiedWhittaker_HeckeRecursion
import Definitions.Def_AdelicDock_LocalEmbedding
import Definitions.Def_AutomorphicForm_LocalOrbitalBase
import Mathlib.MeasureTheory.Group.FundamentalDomain
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Definitions.Def_AutomorphicForm_IsotypicCuspSpace
import Definitions.Def_AutomorphicForm_ArchWeightCharTransport
import Definitions.Def_AutomorphicForm_FactorizableTestFn
import Definitions.Def_AutomorphicForm_WhittakerModelLocal
import Definitions.Def_LanglandsTunnell_ConverseData
import Mathlib.Analysis.MellinTransform
import Definitions.Def_AutomorphicForm_RightConvolution
import Definitions.Def_AutomorphicForm_BoundedGenuineCuspRealization

import Theorems.Thm_AutomorphicForm_rightConv_translate_package_of_isCuspAutomorphicFnAt
import Theorems.Thm_AutomorphicForm_memLp_two_of_isBoundedOnSiegelWindows_of_exists_memLp_two_of_coversModCentre
import Theorems.Thm_AutomorphicForm_exists_iUnion_image_mul_centreCutSiegelSet_subset_setOf_ideleNorm_det_mem_Icc
import Theorems.Thm_AutomorphicForm_SiegelCovering_coversModCentre_productionPinsGeneral_D_rat
import Theorems.Thm_AutomorphicForm_whittakerCoefficientIntegrable_of_isCuspAutomorphicFnAt_of_rightConv_eq_rat
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_isCuspAutomorphicFnAt_comp_mul_right_and_sub_of_rightConv_eq_rat
p2m_attr_erase "instance" "instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instCountableOfNumberField_definitions RestrictedProduct.SecondCountableTopology_of_principal instCountableElemSetSetsCofinite_definitions"
p2m_attr_erase "simp" "ContinuousAddEquiv.restrictedProductPi_apply RestrictedProduct.flatten_homeomorph_apply RestrictedProduct.flatten_homeomorph'_symm_apply ContinuousMulEquiv.restrictedProductPi_symm_apply RestrictedProduct.flatten_homeomorph'_apply RestrictedProduct.flatten_homeomorph_symm_apply ContinuousMulEquiv.restrictedProductPi_apply ContinuousAddEquiv.restrictedProductPi_symm_apply RingEquiv.restrictedProductCongr_symm_apply RingEquiv.restrictedProductCongrRight_apply MulEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductProd_symm_apply_coe Equiv.restrictedProductCongrRight_apply AddEquiv.restrictedProductCongr_apply Equiv.restrictedProductCongrLeft'_symm_apply_apply Equiv.restrictedProductCongr_apply_apply Equiv.restrictedProductCongrLeft_apply_apply RestrictedProduct.flatten_equiv'_apply AddEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductCongr_symm_apply Equiv.restrictedProductCongrRight_symm_apply RestrictedProduct.flatten_equiv'_symm_apply AddEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductCongrLeft'_apply RestrictedProduct.flatten_apply RingEquiv.restrictedProductCongr_apply_apply RingEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductProd_apply RestrictedProduct.flatten_equiv_apply RestrictedProduct.flatten_equiv_symm_apply LinearEquiv.restrictedProductCongrLeft'_apply RestrictedProduct.not_mem_support RestrictedProduct.mem_structureSubring_iff RestrictedProduct.not_mem_mulSupport RestrictedProduct.support_neg RestrictedProduct.mem_indexSupport_iff RestrictedProduct.mulSupport_inv RestrictedProduct.mapAlongLinearMap_apply NumberField.AdeleRing.val_finiteUnitsComponent IsDedekindDomain.FiniteAdeleRing.val_unitsComponent"
p2m_attr_erase "simp" "NumberField.AdeleRing.val_finitePartUnits NumberField.AdeleRing.val_infiniteUnitsComponent"

set_option autoImplicit false

attribute [local instance] NumberField.AdelicHaar.glBorel NumberField.AdelicHaar.borelSpace_glBorel

open MeasureTheory NumberField NumberField.AdelicHaar NumberField.AdelicLevel NumberField.AdelicBox NumberField.AdelicFourier IsDedekindDomain
open AutomorphicForm AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering AutomorphicForm.SiegelCoordinates
open LanglandsTunnell LanglandsTunnell.RankinSelberg RSCarrier UnramifiedWhittaker

theorem solution
    (ξ : (productionPinsGeneral ℚ).Z →* ℂˣ) (φ : AdelicGL2 (𝓞 ℚ) ℚ → ℂ)
    (hφ : IsCuspAutomorphicFnAt ℚ (productionPinsGeneral ℚ) ξ φ) (hcont : Continuous φ)
    (hrep : ∃ α : AdelicGL2 (𝓞 ℚ) ℚ → ℂ, IsFactorizableTestFn ℚ α ∧ rightConv ℚ φ α = φ)
    (u : AdelicGL2 (𝓞 ℚ) ℚ) :
    IsCuspAutomorphicFnAt ℚ (productionPinsGeneral ℚ) ξ (fun g => φ (g * u)) ∧
    IsCuspAutomorphicFnAt ℚ (productionPinsGeneral ℚ) ξ (fun g => φ (g * u) - φ g) := by
  classical
  obtain ⟨α, hα, hφα⟩ := hrep
  by_cases h0 : φ = 0
  · subst h0
    simp only [Pi.zero_apply, sub_self]
    exact ⟨AutomorphicForm.isCuspAutomorphicFnAt_zero ℚ _ ξ, AutomorphicForm.isCuspAutomorphicFnAt_zero ℚ _ ξ⟩
  have hne : ∃ g, φ g ≠ 0 := Function.ne_iff.mp h0
  obtain ⟨hLs, hL2⟩ := (AutomorphicForm.lsXiMemberAt_iff _ _ _ _ _ _ _).mp hφ.1
  have hCusp := hφ.2

  have hP := AutomorphicForm.rightConv_translate_package_of_isCuspAutomorphicFnAt ℚ (1/2 : ℝ) 1 (1/2) 2
    (classRepTranslates ℚ) (by norm_num) AutomorphicForm.SiegelCovering.coversModCentre_productionPinsGeneral_D_rat
    ξ φ hφ hcont α hα NumberField.StandardAddChar.psiQ u
  have hψG : ∀ g : AdelicGL2 (𝓞 ℚ) ℚ, φ (g * u) = rightConv ℚ φ (fun y => α (u⁻¹ * y)) g := by
    intro g; rw [hP.2.2.2.1 g, hφα]

  have hLsψ : IsLsXiFunction (𝓞 ℚ) ℚ ⊤ ξ (fun g => φ (g * u)) := by
    refine ⟨fun γ g => ?_, fun z g => ?_⟩
    · show φ (globalPoints (𝓞 ℚ) ℚ γ * g * u) = φ (g * u)
      rw [mul_assoc]; exact hLs.left_invariant γ (g * u)
    · show φ (centralScalar (𝓞 ℚ) ℚ (z : (AdeleRing (𝓞 ℚ) ℚ)ˣ) * g * u) = ((ξ z : ℂˣ) : ℂ) * φ (g * u)
      rw [mul_assoc]; exact hLs.central_transform z (g * u)
  have hLsδ : IsLsXiFunction (𝓞 ℚ) ℚ ⊤ ξ (fun g => φ (g * u) - φ g) := by
    refine ⟨fun γ g => ?_, fun z g => ?_⟩
    · show φ (globalPoints (𝓞 ℚ) ℚ γ * g * u) - φ (globalPoints (𝓞 ℚ) ℚ γ * g) = φ (g * u) - φ g
      rw [mul_assoc, hLs.left_invariant γ (g * u), hLs.left_invariant γ g]
    · show φ (centralScalar (𝓞 ℚ) ℚ (z : (AdeleRing (𝓞 ℚ) ℚ)ˣ) * g * u)
          - φ (centralScalar (𝓞 ℚ) ℚ (z : (AdeleRing (𝓞 ℚ) ℚ)ˣ) * g) = ((ξ z : ℂˣ) : ℂ) * (φ (g * u) - φ g)
      rw [mul_assoc, hLs.central_transform z (g * u), hLs.central_transform z g, mul_sub]

  have hbdd : IsBoundedOnSiegelWindows ℚ (fun g => φ (g * u)) := by
    intro c' u' d₁' d₂' T' hc' hd₁'
    obtain ⟨C, M, hCM⟩ := hP.2.1
    obtain ⟨a, b, ha, hsub⟩ :=
      AutomorphicForm.exists_iUnion_image_mul_centreCutSiegelSet_subset_setOf_ideleNorm_det_mem_Icc ℚ c' u' d₁' d₂' hd₁' T'
    refine ⟨|C| * (max b a⁻¹) ^ M, fun g hg => ?_⟩
    have hN := hsub hg
    simp only [Set.mem_setOf_eq, Set.mem_Icc] at hN
    have hNpos : 0 < TateGlobal.ideleNorm ℚ (Matrix.GeneralLinearGroup.det g) := lt_of_lt_of_le ha hN.1
    have hm : max (TateGlobal.ideleNorm ℚ (Matrix.GeneralLinearGroup.det g))
        (TateGlobal.ideleNorm ℚ (Matrix.GeneralLinearGroup.det g))⁻¹ ≤ max b a⁻¹ :=
      max_le_max hN.2 (inv_anti₀ ha hN.1)
    have hm0 : 0 ≤ max (TateGlobal.ideleNorm ℚ (Matrix.GeneralLinearGroup.det g))
        (TateGlobal.ideleNorm ℚ (Matrix.GeneralLinearGroup.det g))⁻¹ := le_max_of_le_left hNpos.le
    show ‖φ (g * u)‖ ≤ _
    rw [hψG g]
    calc ‖rightConv ℚ φ (fun y => α (u⁻¹ * y)) g‖ ≤ C * _ ^ M := hCM g
      _ ≤ |C| * _ ^ M := by gcongr; exact le_abs_self C
      _ ≤ |C| * (max b a⁻¹) ^ M := by gcongr

  have hL2ψ := AutomorphicForm.memLp_two_of_isBoundedOnSiegelWindows_of_exists_memLp_two_of_coversModCentre
    ℚ (1/2 : ℝ) 1 (1/2) 2 (classRepTranslates ℚ) (by norm_num)
    AutomorphicForm.SiegelCovering.coversModCentre_productionPinsGeneral_D_rat ξ φ hLs hcont hne hL2
    (fun g => φ (g * u)) hLsψ (hcont.comp (continuous_mul_right u)) hbdd
  have hAψ : IsAutomorphicFnAt ℚ (productionPinsGeneral ℚ) ξ (fun g => φ (g * u)) :=
    (AutomorphicForm.lsXiMemberAt_iff _ _ _ _ _ _ _).mpr ⟨hLsψ, hL2ψ⟩
  have hAδ : IsAutomorphicFnAt ℚ (productionPinsGeneral ℚ) ξ (fun g => φ (g * u) - φ g) :=
    (AutomorphicForm.lsXiMemberAt_iff _ _ _ _ _ _ _).mpr ⟨hLsδ, hL2ψ.sub hL2⟩

  have hint : ∀ g' : AdelicGL2 (𝓞 ℚ) ℚ, (letI := (productionPinsGeneral ℚ).nS;
      Integrable (fun x : AdeleRing (𝓞 ℚ) ℚ => φ (unipotentGL2 x * g')) (productionPinsGeneral ℚ).ν) := by
    intro g'
    have hi := AutomorphicForm.whittakerCoefficientIntegrable_of_isCuspAutomorphicFnAt_of_rightConv_eq_rat
      ξ φ hcont hφ ⟨α, hα, hφα⟩ 0 g'
    unfold WhittakerCoefficientIntegrable at hi
    simpa only [map_zero, zero_mul, neg_zero, AddChar.map_zero_eq_one, mul_one] using hi

  have hCψ : @IsCuspidalFn _ (productionPinsGeneral ℚ).nS _ _ (productionPinsGeneral ℚ).ν unipotentGL2
      (fun g => φ (g * u)) := by
    intro g
    have h := hCusp (g * u)
    unfold constantTerm constantTermIntegrand at h ⊢
    simpa only [mul_assoc] using h
  have hCδ : @IsCuspidalFn _ (productionPinsGeneral ℚ).nS _ _ (productionPinsGeneral ℚ).ν unipotentGL2
      (fun g => φ (g * u) - φ g) := by
    intro g
    have h1 := hCusp (g * u)
    have h2 := hCusp g
    unfold constantTerm constantTermIntegrand at h1 h2 ⊢
    have hi1 : (letI := (productionPinsGeneral ℚ).nS;
        Integrable (fun x : AdeleRing (𝓞 ℚ) ℚ => φ (unipotentGL2 x * g * u)) (productionPinsGeneral ℚ).ν) := by
      simpa only [mul_assoc] using hint (g * u)
    have hi2 := hint g
    show (∫ x, (φ (unipotentGL2 x * g * u) - φ (unipotentGL2 x * g)) ∂(productionPinsGeneral ℚ).ν) = 0
    rw [integral_sub hi1 hi2, h2, sub_zero]
    simpa only [mul_assoc] using h1
  exact ⟨⟨hAψ, hCψ⟩, ⟨hAδ, hCδ⟩⟩

end S_AutomorphicForm_isCuspAutomorphicFnAt_comp_mul_right_and_sub_of_rightConv_eq_rat
end P2MW
export P2MW.S_AutomorphicForm_isCuspAutomorphicFnAt_comp_mul_right_and_sub_of_rightConv_eq_rat (solution)
