-- Prove2me | solution 1 for AutomorphicForm.exists_nhds_forall_iff_and_ratio_mul_sqrtRatio_mul_twistedWeighted_eq_of_norm_sub_le_of_areMatchingLocal
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.961684+00:00
-- url     : https://prove2.me/submissions/164c3a7d-7507-570c-9c3e-bbe7d601c6c5

import Definitions.Def_AutomorphicForm_TwistedOrbital
import Definitions.Def_AutomorphicForm_LocalWeightedOrbital
import Definitions.Def_NumberField_AdelicHaar
import Definitions.Def_NumberField_AdelicLevel
import Definitions.Def_NumberField_TateGlobalZeta
import Definitions.Def_NumberField_IdeleProductMeasure
import Definitions.Def_LocalLanglands_HeckeCosetLocal
import Definitions.Def_LocalLanglands_HeckeCosetSystem
import Definitions.Def_AutomorphicForm_LocalOrbitalBase
import Definitions.Def_AutomorphicForm_SatakeCombinationCoeff
import Definitions.Def_AutomorphicForm_WindingDatum
import Definitions.Def_LanglandsTunnell_CubicInduction_TorusValues
import Definitions.Def_AutomorphicForm_WeightedOrbitalRelation
import Definitions.Def_AutomorphicForm_BaseChangePlaces
import Definitions.Def_NumberField_AdelicHeight
import Definitions.Def_AutomorphicForm_WeylIntertwining
import Definitions.Def_UnramifiedWhittaker_ZetaIntegrand
import Definitions.Def_M4aHerbrand_GenuineDescent
import Theorems.Thm_AutomorphicForm_exists_nhds_forall_exists_normString_diagUnits2_eq_toTensorGL_iff_of_norm_sub_le
import Theorems.Thm_AutomorphicForm_exists_nhds_forall_ratio_mul_sqrtRatio_mul_twistedWeighted_eq_of_norm_sub_le_of_normString_diagUnits2_eq_of_areMatchingLocal
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_exists_nhds_forall_iff_and_ratio_mul_sqrtRatio_mul_twistedWeighted_eq_of_norm_sub_le_of_areMatchingLocal
p2m_attr_erase "instance" "instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instCountableOfNumberField_definitions"
set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicLevel NumberField.AdelicHaar IsDedekindDomain

attribute [local instance] NumberField.AdelicHaar.glBorel AutomorphicForm.centralizerBorel
  AutomorphicForm.twistedCentralizerBorel

open LanglandsTunnell.CubicInduction (diagUnits2)

open scoped TensorProduct TensorProduct.RightActions in
open scoped Classical in

theorem solution
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]
    (σ : L ≃ₐ[K] L) (hgen : ∀ τ : L ≃ₐ[K] L, τ ∈ Subgroup.zpowers σ) (hdeg : (Module.finrank K L).Prime)
    (v : HeightOneSpectrum (𝓞 K))
    (φ : GL (Fin 2) (L ⊗[K] v.adicCompletion K) → ℂ) (hφ : AutomorphicForm.IsSemiLocalTestFn K L v φ)
    (f : GL (Fin 2) (v.adicCompletion K) → ℂ) (hf : AutomorphicForm.IsLocalTestFn K v f)
    (hmatch : AutomorphicForm.AreMatchingLocal K L v σ φ f)  :
    ∃ U ∈ nhds (1 : (v.adicCompletion K)ˣ), ∃ ρ : ℝ, 0 < ρ ∧
      ∀ a a' t t' : (v.adicCompletion K)ˣ, t ∈ U →
        ‖(a' : (v.adicCompletion K)) - (a : (v.adicCompletion K))‖ ≤ ρ * ‖(a : (v.adicCompletion K))‖ →
        ‖(t' : (v.adicCompletion K)) - (t : (v.adicCompletion K))‖ ≤ ρ * ‖(1 : (v.adicCompletion K)) - (t : (v.adicCompletion K))‖ →
        t ≠ 1 → t' ≠ 1 →
        ((∃ α β : (L ⊗[K] (v.adicCompletion K))ˣ, AutomorphicForm.normString K L (v.adicCompletion K) σ (diagUnits2 α β) =
                AutomorphicForm.toTensorGL K L (v.adicCompletion K) (diagUnits2 a (a * t))) ↔
          (∃ α β : (L ⊗[K] (v.adicCompletion K))ˣ, AutomorphicForm.normString K L (v.adicCompletion K) σ (diagUnits2 α β) =
                AutomorphicForm.toTensorGL K L (v.adicCompletion K) (diagUnits2 a' (a' * t')))) ∧
        (∀ α β : (L ⊗[K] (v.adicCompletion K))ˣ,
              AutomorphicForm.normString K L (v.adicCompletion K) σ (diagUnits2 α β) =
                AutomorphicForm.toTensorGL K L (v.adicCompletion K) (diagUnits2 a (a * t)) →
            ∀ (τ' : @Measure (AutomorphicForm.twistedCentralizer K L (v.adicCompletion K) σ (diagUnits2 α β))
                (AutomorphicForm.twistedCentralizerBorel K L (v.adicCompletion K) σ (diagUnits2 α β))),
              @Measure.IsHaarMeasure _ _ _
                (AutomorphicForm.twistedCentralizerBorel K L (v.adicCompletion K) σ (diagUnits2 α β)) τ' →
              τ' {x | (x : GL (Fin 2) (L ⊗[K] (v.adicCompletion K))) ∈ AutomorphicForm.semiLocalIntegralSet K L v} = 1 →
            ∀ J' : ℂ, AutomorphicForm.IsTwistedWeightedOrbitalIntegral K L v σ (diagUnits2 α β) τ' φ J' →
              ∀ α' β' : (L ⊗[K] (v.adicCompletion K))ˣ,
              AutomorphicForm.normString K L (v.adicCompletion K) σ (diagUnits2 α' β') =
                AutomorphicForm.toTensorGL K L (v.adicCompletion K) (diagUnits2 a' (a' * t')) →
            ∀ (τ'' : @Measure (AutomorphicForm.twistedCentralizer K L (v.adicCompletion K) σ (diagUnits2 α' β'))
                (AutomorphicForm.twistedCentralizerBorel K L (v.adicCompletion K) σ (diagUnits2 α' β'))),
              @Measure.IsHaarMeasure _ _ _
                (AutomorphicForm.twistedCentralizerBorel K L (v.adicCompletion K) σ (diagUnits2 α' β')) τ'' →
              τ'' {x | (x : GL (Fin 2) (L ⊗[K] (v.adicCompletion K))) ∈ AutomorphicForm.semiLocalIntegralSet K L v} = 1 →
            ∀ J'' : ℂ, AutomorphicForm.IsTwistedWeightedOrbitalIntegral K L v σ (diagUnits2 α' β') τ'' φ J'' →
              ((AutomorphicForm.LocalWeightedOrbital.ratio (fun x : (v.adicCompletion K) => ‖x‖) a (a * t) *
                  AutomorphicForm.LocalWeightedOrbital.sqrtRatio (fun x : (v.adicCompletion K) => ‖x‖) a (a * t) : ℝ) : ℂ) * J' = ((AutomorphicForm.LocalWeightedOrbital.ratio (fun x : (v.adicCompletion K) => ‖x‖) a' (a' * t') *
                  AutomorphicForm.LocalWeightedOrbital.sqrtRatio (fun x : (v.adicCompletion K) => ‖x‖) a' (a' * t') : ℝ) : ℂ) * J'') := by
  obtain ⟨U₁, hU₁, ρ₁, hρ₁, h₁⟩ := AutomorphicForm.exists_nhds_forall_exists_normString_diagUnits2_eq_toTensorGL_iff_of_norm_sub_le K L σ hgen v
  obtain ⟨U₂, hU₂, ρ₂, hρ₂, h₂⟩ := AutomorphicForm.exists_nhds_forall_ratio_mul_sqrtRatio_mul_twistedWeighted_eq_of_norm_sub_le_of_normString_diagUnits2_eq_of_areMatchingLocal K L σ hgen hdeg v φ hφ f hf hmatch
  refine ⟨U₁ ∩ U₂, Filter.inter_mem hU₁ hU₂, min ρ₁ ρ₂, lt_min hρ₁ hρ₂, ?_⟩
  intro a a' t t' ht ha ht' ht1 ht'1
  have ha1 : ‖(a' : (v.adicCompletion K)) - (a : (v.adicCompletion K))‖ ≤ ρ₁ * ‖(a : (v.adicCompletion K))‖ := ha.trans (mul_le_mul_of_nonneg_right (min_le_left _ _) (norm_nonneg _))
  have ha2 : ‖(a' : (v.adicCompletion K)) - (a : (v.adicCompletion K))‖ ≤ ρ₂ * ‖(a : (v.adicCompletion K))‖ := ha.trans (mul_le_mul_of_nonneg_right (min_le_right _ _) (norm_nonneg _))
  have ht1' : ‖(t' : (v.adicCompletion K)) - (t : (v.adicCompletion K))‖ ≤ ρ₁ * ‖(1 : (v.adicCompletion K)) - (t : (v.adicCompletion K))‖ := ht'.trans (mul_le_mul_of_nonneg_right (min_le_left _ _) (norm_nonneg _))
  have ht2' : ‖(t' : (v.adicCompletion K)) - (t : (v.adicCompletion K))‖ ≤ ρ₂ * ‖(1 : (v.adicCompletion K)) - (t : (v.adicCompletion K))‖ := ht'.trans (mul_le_mul_of_nonneg_right (min_le_right _ _) (norm_nonneg _))
  exact ⟨h₁ a a' t t' ht.1 ha1 ht1', h₂ a a' t t' ht.2 ha2 ht2' ht1 ht'1⟩

end S_AutomorphicForm_exists_nhds_forall_iff_and_ratio_mul_sqrtRatio_mul_twistedWeighted_eq_of_norm_sub_le_of_areMatchingLocal
end P2MW
export P2MW.S_AutomorphicForm_exists_nhds_forall_iff_and_ratio_mul_sqrtRatio_mul_twistedWeighted_eq_of_norm_sub_le_of_areMatchingLocal (solution)
