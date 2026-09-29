-- Prove2me | solution 1 for AutomorphicForm.exists_forall_norm_ratio_mul_sqrtRatio_mul_twistedWeighted_add_halfWeighted_sub_le_of_areMatchingLocal
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.961684+00:00
-- url     : https://prove2.me/submissions/78d28e38-4dd0-5f9b-98b0-940340882fd4

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
import Theorems.Thm_AutomorphicForm_exists_forall_norm_halfWeighted_sub_le_of_not_exists_norm_eq_of_areMatchingLocal
import Theorems.Thm_AutomorphicForm_exists_forall_norm_ratio_mul_sqrtRatio_mul_twistedWeighted_add_halfWeighted_sub_le_of_normString_diagUnits2_eq_of_areMatchingLocal
import Theorems.Thm_AutomorphicForm_exists_normString_diagUnits2_eq_toTensorGL_diagUnits2_iff_exists_norm_eq
import Theorems.Thm_IsDedekindDomain_HeightOneSpectrum_image_pow_mem_nhds_one_units_adicCompletion
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_exists_forall_norm_ratio_mul_sqrtRatio_mul_twistedWeighted_add_halfWeighted_sub_le_of_areMatchingLocal
p2m_attr_erase "instance" "instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instCountableOfNumberField_definitions AutomorphicForm.compactSpace_maximalCompactAway AutomorphicForm.compactSpace_adelicMaximalCompact AutomorphicForm.isProbabilityMeasure_maximalCompactHaar AutomorphicForm.isHaarMeasure_maximalCompactHaar AutomorphicForm.compactSpace_maximalCompactAt AutomorphicForm.isProbabilityMeasure_maximalCompactAwayHaar AutomorphicForm.isHaarMeasure_maximalCompactAwayHaar AutomorphicForm.isProbabilityMeasure_maximalCompactAtHaar AutomorphicForm.isHaarMeasure_maximalCompactAtHaar"
p2m_attr_erase "simp" "LT.TwistedNorm.sigmaPartialNorm_zero LT.TwistedNorm.GL2.traceDetCompanion_apply_10 LT.TwistedNorm.GL2.traceDetCompanion_apply_00 LT.TwistedNorm.GL2.traceDetCompanion_apply_01 LT.TwistedNorm.GL2.traceDetCompanion_apply_11"
set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicLevel NumberField.AdelicHaar IsDedekindDomain

attribute [local instance] NumberField.AdelicHaar.glBorel AutomorphicForm.centralizerBorel
  AutomorphicForm.twistedCentralizerBorel

open LanglandsTunnell.CubicInduction (diagUnits2)

open scoped TensorProduct TensorProduct.RightActions

open scoped Classical

theorem solution
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]
    (σ : L ≃ₐ[K] L) (hgen : ∀ τ : L ≃ₐ[K] L, τ ∈ Subgroup.zpowers σ) (hdeg : (Module.finrank K L).Prime)
    (v : HeightOneSpectrum (𝓞 K))
    (φ : GL (Fin 2) (L ⊗[K] v.adicCompletion K) → ℂ) (hφ : AutomorphicForm.IsSemiLocalTestFn K L v φ)
    (f : GL (Fin 2) (v.adicCompletion K) → ℂ) (hf : AutomorphicForm.IsLocalTestFn K v f)
    (hmatch : AutomorphicForm.AreMatchingLocal K L v σ φ f)
    [MeasurableSpace (v.adicCompletion K)] [BorelSpace (v.adicCompletion K)]
    (μ : Measure (v.adicCompletion K)) [μ.IsAddHaarMeasure]
    (hμ : μ (v.adicCompletionIntegers K : Set (v.adicCompletion K)) = 1) :
    letI := AutomorphicForm.localGLBorel K v
    ∃ (Λ : (v.adicCompletion K)ˣ → ℂ) (C : ℝ), ∃ U ∈ nhds (1 : (v.adicCompletion K)ˣ),
      ∀ a t : (v.adicCompletion K)ˣ, t ≠ 1 → t ∈ U →
        (∀ α β : (L ⊗[K] (v.adicCompletion K))ˣ,
              AutomorphicForm.normString K L (v.adicCompletion K) σ (diagUnits2 α β) =
                AutomorphicForm.toTensorGL K L (v.adicCompletion K) (diagUnits2 a (a * t)) →
            ∀ (τ' : @Measure (AutomorphicForm.twistedCentralizer K L (v.adicCompletion K) σ (diagUnits2 α β))
                (AutomorphicForm.twistedCentralizerBorel K L (v.adicCompletion K) σ (diagUnits2 α β))),
              @Measure.IsHaarMeasure _ _ _
                (AutomorphicForm.twistedCentralizerBorel K L (v.adicCompletion K) σ (diagUnits2 α β)) τ' →
              τ' {x | (x : GL (Fin 2) (L ⊗[K] (v.adicCompletion K))) ∈ AutomorphicForm.semiLocalIntegralSet K L v} = 1 →
            ∀ J' : ℂ, AutomorphicForm.IsTwistedWeightedOrbitalIntegral K L v σ (diagUnits2 α β) τ' φ J' →
              ‖((AutomorphicForm.LocalWeightedOrbital.ratio (fun x : (v.adicCompletion K) => ‖x‖) a (a * t) *
                  AutomorphicForm.LocalWeightedOrbital.sqrtRatio (fun x : (v.adicCompletion K) => ‖x‖) a (a * t) : ℝ) : ℂ) * J' + 2 * (Module.finrank K L : ℂ) * AutomorphicForm.LocalWeightedOrbital.halfWeighted
          ((AutomorphicForm.localHaar K v).restrict (AutomorphicForm.localIntegralSet K v)) μ
          (fun x : (v.adicCompletion K) => ‖x‖) f a (a * t) - Λ a‖ ≤
                C * ‖(1 : (v.adicCompletion K)) - (t : (v.adicCompletion K))‖ * (1 + |Real.log ‖(1 : (v.adicCompletion K)) - (t : (v.adicCompletion K))‖|)) ∧
        ((¬ ∃ α β : (L ⊗[K] (v.adicCompletion K))ˣ, AutomorphicForm.normString K L (v.adicCompletion K) σ (diagUnits2 α β) =
                AutomorphicForm.toTensorGL K L (v.adicCompletion K) (diagUnits2 a (a * t))) →
          ‖2 * (Module.finrank K L : ℂ) * AutomorphicForm.LocalWeightedOrbital.halfWeighted
          ((AutomorphicForm.localHaar K v).restrict (AutomorphicForm.localIntegralSet K v)) μ
          (fun x : (v.adicCompletion K) => ‖x‖) f a (a * t) - Λ a‖ ≤
            C * ‖(1 : (v.adicCompletion K)) - (t : (v.adicCompletion K))‖ * (1 + |Real.log ‖(1 : (v.adicCompletion K)) - (t : (v.adicCompletion K))‖|)) := by
  classical
  letI : MeasurableSpace (GL (Fin 2) (v.adicCompletion K)) := AutomorphicForm.localGLBorel K v
  obtain ⟨Λ₀, C₀, U₀, hU₀, hA⟩ := AutomorphicForm.exists_forall_norm_halfWeighted_sub_le_of_not_exists_norm_eq_of_areMatchingLocal K L σ hgen hdeg v φ hφ f hf hmatch μ hμ
  obtain ⟨Λ₁, C₁, U₁, hU₁, hB⟩ := AutomorphicForm.exists_forall_norm_ratio_mul_sqrtRatio_mul_twistedWeighted_add_halfWeighted_sub_le_of_normString_diagUnits2_eq_of_areMatchingLocal K L σ hgen hdeg v φ hφ f hf hmatch μ hμ
  have hTL := AutomorphicForm.exists_normString_diagUnits2_eq_toTensorGL_diagUnits2_iff_exists_norm_eq K L σ hgen v

  have hℓ : 0 < Module.finrank K L := hdeg.pos
  have hP : (fun s : (v.adicCompletion K)ˣ => s ^ Module.finrank K L) '' Set.univ ∈ nhds (1 : (v.adicCompletion K)ˣ) :=
    IsDedekindDomain.HeightOneSpectrum.image_pow_mem_nhds_one_units_adicCompletion K v (Module.finrank K L) hℓ Set.univ Filter.univ_mem
  let IsN : (v.adicCompletion K)ˣ → Prop := fun a => ∃ α : (L ⊗[K] (v.adicCompletion K))ˣ, Algebra.norm (v.adicCompletion K) (α : (L ⊗[K] (v.adicCompletion K))) = (a : (v.adicCompletion K))
  refine ⟨fun a => if IsN a then Λ₁ a else Λ₀ a, max C₀ C₁,
    U₀ ∩ U₁ ∩ ((fun s : (v.adicCompletion K)ˣ => s ^ Module.finrank K L) '' Set.univ),
    Filter.inter_mem (Filter.inter_mem hU₀ hU₁) hP, fun a t ht1 htU => ⟨?_, ?_⟩⟩
  ·
    intro α β hαβ τ' hτ' hτ'1 J' hJ'
    have hN : IsN a := ((hTL a (a * t)).mp ⟨α, β, hαβ⟩).1
    simp only [hN, if_true]
    refine (hB a t ht1 htU.1.2 α β hαβ τ' hτ' hτ'1 J' hJ').trans ?_
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_max_right _ _) (norm_nonneg _)) (by positivity)
  ·
    intro hno
    have hN : ¬ IsN a := by
      intro ha
      apply hno
      obtain ⟨s, -, hs⟩ := htU.2
      refine (hTL a (a * t)).mpr ⟨ha, ?_⟩
      obtain ⟨α, hα⟩ := ha
      let sE : (L ⊗[K] (v.adicCompletion K))ˣ := Units.map (algebraMap (v.adicCompletion K) (L ⊗[K] (v.adicCompletion K)) : (v.adicCompletion K) →* (L ⊗[K] (v.adicCompletion K))) s
      refine ⟨α * sE, ?_⟩
      have hsE : (sE : (L ⊗[K] (v.adicCompletion K))) = algebraMap (v.adicCompletion K) (L ⊗[K] (v.adicCompletion K)) (s : (v.adicCompletion K)) := rfl
      rw [Units.val_mul, map_mul, hα, hsE, Algebra.norm_algebraMap, TensorProduct.finrank_rightAlgebra L,
        Units.val_mul, ← hs, Units.val_pow_eq_pow_val]
    simp only [hN, if_false]
    refine (hA a hN t ht1 htU.1.1).trans ?_
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_max_left _ _) (norm_nonneg _)) (by positivity)

end S_AutomorphicForm_exists_forall_norm_ratio_mul_sqrtRatio_mul_twistedWeighted_add_halfWeighted_sub_le_of_areMatchingLocal
end P2MW
export P2MW.S_AutomorphicForm_exists_forall_norm_ratio_mul_sqrtRatio_mul_twistedWeighted_add_halfWeighted_sub_le_of_areMatchingLocal (solution)
