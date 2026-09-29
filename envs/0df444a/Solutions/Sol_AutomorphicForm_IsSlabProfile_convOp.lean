-- Prove2me | solution 1 for AutomorphicForm.IsSlabProfile.convOp
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.553648+00:00
-- url     : https://prove2.me/submissions/f42194e9-26c3-58fe-9027-313127269e7a

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
import Theorems.Thm_NumberField_AdelicHeight_exists_forall_mul_adelicHeight_le_adelicHeight_mul_of_isCompact
import Theorems.Thm_NumberField_TateGlobal_continuous_ideleNorm_det
import Theorems.Thm_NumberField_AdeleRing_secondCountableTopology_generalLinearGroup_finTwo
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_IsSlabProfile_convOp
p2m_attr_erase "instance" "instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instCountableOfNumberField_definitions RestrictedProduct.SecondCountableTopology_of_principal instCountableElemSetSetsCofinite_definitions"
p2m_attr_erase "simp" "ContinuousAddEquiv.restrictedProductPi_apply RestrictedProduct.flatten_homeomorph_apply RestrictedProduct.flatten_homeomorph'_symm_apply ContinuousMulEquiv.restrictedProductPi_symm_apply RestrictedProduct.flatten_homeomorph'_apply RestrictedProduct.flatten_homeomorph_symm_apply ContinuousMulEquiv.restrictedProductPi_apply ContinuousAddEquiv.restrictedProductPi_symm_apply RingEquiv.restrictedProductCongr_symm_apply RingEquiv.restrictedProductCongrRight_apply MulEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductProd_symm_apply_coe Equiv.restrictedProductCongrRight_apply AddEquiv.restrictedProductCongr_apply Equiv.restrictedProductCongrLeft'_symm_apply_apply Equiv.restrictedProductCongr_apply_apply Equiv.restrictedProductCongrLeft_apply_apply RestrictedProduct.flatten_equiv'_apply AddEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductCongr_symm_apply Equiv.restrictedProductCongrRight_symm_apply RestrictedProduct.flatten_equiv'_symm_apply AddEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductCongrLeft'_apply RestrictedProduct.flatten_apply RingEquiv.restrictedProductCongr_apply_apply RingEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductProd_apply RestrictedProduct.flatten_equiv_apply RestrictedProduct.flatten_equiv_symm_apply LinearEquiv.restrictedProductCongrLeft'_apply RestrictedProduct.not_mem_support RestrictedProduct.mem_structureSubring_iff RestrictedProduct.not_mem_mulSupport RestrictedProduct.support_neg RestrictedProduct.mem_indexSupport_iff RestrictedProduct.mulSupport_inv RestrictedProduct.mapAlongLinearMap_apply"

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicLevel NumberField.AdelicBox NumberField.AdelicHaar
open AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering
open IsDedekindDomain
open scoped ComplexConjugate NNReal

attribute [local instance] NumberField.AdelicHaar.glBorel NumberField.AdelicHaar.borelSpace_glBorel

open AutomorphicForm in

theorem solution
    (K : Type) [Field K] [NumberField K] [DecidableEq (HeightOneSpectrum (𝓞 K))]
    (ξK : (⊤ : Subgroup (AdeleRing (𝓞 K) K)ˣ) →* ℂˣ)
    (ψ : AdelicGL2 (𝓞 K) K → ℂ) (_hψ : AutomorphicForm.IsSlabProfile K (⊤ : Subgroup (AdeleRing (𝓞 K) K)ˣ) ξK ψ)
    (f : AdelicGL2 (𝓞 K) K → ℂ) (_hf : Continuous f) (_hfc : HasCompactSupport f) :
    AutomorphicForm.IsSlabProfile K (⊤ : Subgroup (AdeleRing (𝓞 K) K)ˣ) ξK (convOp K f ψ) := by
  classical
  haveI := isHaarMeasure_adelicGLHaar (Fin 2) (𝓞 K) K
  haveI : SecondCountableTopology (AdelicGL2 (𝓞 K) K) :=
    NumberField.AdeleRing.secondCountableTopology_generalLinearGroup_finTwo K
  set μH := adelicGLHaar (Fin 2) (𝓞 K) K with hμH
  set S := tsupport f with hS
  have hSc : IsCompact S := _hfc
  have hf0 : ∀ x, x ∉ S → f x = 0 := fun x hx => image_eq_zero_of_notMem_tsupport hx
  have hψm : Measurable ψ := _hψ.measurable

  have hdetc : Continuous fun x : AdelicGL2 (𝓞 K) K =>
      NumberField.TateGlobal.ideleNorm K (Matrix.GeneralLinearGroup.det x) :=
    NumberField.TateGlobal.continuous_ideleNorm_det K
  have hwindow : ∃ m M : ℝ, 0 < m ∧ ∀ x ∈ S,
      NumberField.TateGlobal.ideleNorm K (Matrix.GeneralLinearGroup.det x) ∈ Set.Icc m M := by
    by_cases hne : S.Nonempty
    · obtain ⟨x₀, hx₀, hmin⟩ := hSc.exists_isMinOn hne hdetc.continuousOn
      obtain ⟨x₁, hx₁, hmax⟩ := hSc.exists_isMaxOn hne hdetc.continuousOn
      exact ⟨_, _, NumberField.TateGlobal.ideleNorm_pos _, fun x hx => ⟨hmin hx, hmax hx⟩⟩
    · exact ⟨1, 1, one_pos, fun x hx => (hne ⟨x, hx⟩).elim⟩
  obtain ⟨m, M, hm, hmM⟩ := hwindow
  have hfn_int : Integrable (fun x => ‖f x‖) μH := _hf.norm.integrable_of_hasCompactSupport _hfc.norm

  have hR : ∀ h, convOp K f ψ h = ∫ x, ψ (h * x) * f x ∂μH := fun h => by
    rw [convOp_apply, rightConv_apply]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  ·
    have hsm : StronglyMeasurable (Function.uncurry fun (h x : AdelicGL2 (𝓞 K) K) => ψ (h * x) * f x) :=
      ((hψm.comp measurable_mul).mul (_hf.measurable.comp measurable_snd)).stronglyMeasurable
    have hm := (hsm.integral_prod_right (ν := μH)).measurable
    have hfun : convOp K f ψ = fun h => ∫ x, ψ (h * x) * f x ∂μH := funext hR
    rw [hfun]
    exact hm
  · intro x h
    rw [hR, hR]
    refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
    dsimp only
    rw [mul_assoc, _hψ.unipotent_mul]
  · intro γ hγ h
    rw [hR, hR]
    refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
    dsimp only
    rw [mul_assoc, _hψ.borel_mul γ hγ]
  · intro z h
    rw [hR, hR, ← integral_const_mul]
    refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
    dsimp only
    rw [mul_assoc, _hψ.central_transform, mul_assoc]
  ·
    intro d₁ d₂ hd₁
    obtain ⟨C, hC⟩ := _hψ.bounded_on_slab (d₁ * m) (d₂ * M) (mul_pos hd₁ hm)
    refine ⟨max C 0 * ∫ x, ‖f x‖ ∂μH, fun h hh => ?_⟩
    rw [hR]
    refine (norm_integral_le_of_norm_le (hfn_int.const_mul (max C 0))
      (Filter.Eventually.of_forall fun x => ?_)).trans (le_of_eq (integral_const_mul _ _))
    by_cases hx : x ∈ S
    · rw [norm_mul]
      refine mul_le_mul_of_nonneg_right ((hC _ ?_).trans (le_max_left _ _)) (norm_nonneg _)
      rw [map_mul, NumberField.TateGlobal.ideleNorm_mul]
      exact ⟨mul_le_mul hh.1 (hmM x hx).1 hm.le (hd₁.le.trans hh.1),
        mul_le_mul hh.2 (hmM x hx).2 (NumberField.TateGlobal.ideleNorm_pos _).le
          (hd₁.le.trans (hh.1.trans hh.2))⟩
    · rw [hf0 x hx]; simp
  ·
    obtain ⟨a, b, ha, hband⟩ := _hψ.height_band
    obtain ⟨κ, Kc, hκ, hcmp⟩ :=
      NumberField.AdelicHeight.exists_forall_mul_adelicHeight_le_adelicHeight_mul_of_isCompact K S hSc
    refine ⟨a / max Kc 1, b / κ, div_pos ha (lt_max_of_lt_right one_pos), fun h hh => ?_⟩
    have hex : ∃ x ∈ S, ψ (h * x) ≠ 0 := by
      by_contra hcon
      push Not at hcon
      apply hh
      rw [hR]
      refine integral_eq_zero_of_ae (Filter.Eventually.of_forall fun x => ?_)
      show ψ (h * x) * f x = (0 : AdelicGL2 (𝓞 K) K → ℂ) x
      by_cases hx : x ∈ S
      · rw [hcon x hx, zero_mul, Pi.zero_apply]
      · rw [hf0 x hx, mul_zero, Pi.zero_apply]
    obtain ⟨x, hx, hψx⟩ := hex
    have hhx := hband _ hψx
    obtain ⟨h1, h2⟩ := hcmp h x hx
    have hHpos := NumberField.AdelicHeight.adelicHeight_pos h
    constructor
    · rw [div_le_iff₀ (lt_max_of_lt_right one_pos)]
      calc a ≤ NumberField.AdelicHeight.adelicHeight K (h * x) := hhx.1
        _ ≤ Kc * NumberField.AdelicHeight.adelicHeight K h := h2
        _ ≤ max Kc 1 * NumberField.AdelicHeight.adelicHeight K h :=
            mul_le_mul_of_nonneg_right (le_max_left _ _) hHpos.le
        _ = NumberField.AdelicHeight.adelicHeight K h * max Kc 1 := mul_comm _ _
    · rw [le_div_iff₀ hκ]
      calc NumberField.AdelicHeight.adelicHeight K h * κ = κ * NumberField.AdelicHeight.adelicHeight K h := mul_comm _ _
        _ ≤ NumberField.AdelicHeight.adelicHeight K (h * x) := h1
        _ ≤ b := hhx.2

end S_AutomorphicForm_IsSlabProfile_convOp
end P2MW
export P2MW.S_AutomorphicForm_IsSlabProfile_convOp (solution)
