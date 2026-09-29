-- Prove2me | solution 1 for AutomorphicForm.exists_nhds_forall_eq_of_norm_sub_le_and_norm_add_halfWeighted_sub_le_and_forall_ratio_mul_sqrtRatio_mul_twistedWeighted_eq_of_areMatchingLocal
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.961684+00:00
-- url     : https://prove2.me/submissions/21aa96b5-129e-54d1-b53e-b3d06b0909a4

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
import Theorems.Thm_AutomorphicForm_exists_isHaarMeasure_twistedCentralizer_and_exists_isTwistedWeightedOrbitalIntegral_of_normString_diagUnits2_eq
import Theorems.Thm_AutomorphicForm_ratio_mul_sqrtRatio_mul_twistedWeighted_eq_of_normString_diagUnits2_eq_of_areMatchingLocal
import Theorems.Thm_AutomorphicForm_exists_nhds_forall_iff_and_ratio_mul_sqrtRatio_mul_twistedWeighted_eq_of_norm_sub_le_of_areMatchingLocal
import Theorems.Thm_AutomorphicForm_exists_forall_norm_ratio_mul_sqrtRatio_mul_twistedWeighted_add_halfWeighted_sub_le_of_areMatchingLocal
import Theorems.Thm_AutomorphicForm_LocalWeightedOrbital_exists_nhds_forall_halfWeighted_mul_eq_halfWeighted_mul_of_norm_sub_le_of_isLocalTestFn
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_exists_nhds_forall_eq_of_norm_sub_le_and_norm_add_halfWeighted_sub_le_and_forall_ratio_mul_sqrtRatio_mul_twistedWeighted_eq_of_areMatchingLocal
p2m_attr_erase "instance" "instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instCountableOfNumberField_definitions AutomorphicForm.compactSpace_maximalCompactAway AutomorphicForm.compactSpace_adelicMaximalCompact AutomorphicForm.isProbabilityMeasure_maximalCompactHaar AutomorphicForm.isHaarMeasure_maximalCompactHaar AutomorphicForm.compactSpace_maximalCompactAt AutomorphicForm.isProbabilityMeasure_maximalCompactAwayHaar AutomorphicForm.isHaarMeasure_maximalCompactAwayHaar AutomorphicForm.isProbabilityMeasure_maximalCompactAtHaar AutomorphicForm.isHaarMeasure_maximalCompactAtHaar"
p2m_attr_erase "simp" "LT.TwistedNorm.sigmaPartialNorm_zero LT.TwistedNorm.GL2.traceDetCompanion_apply_10 LT.TwistedNorm.GL2.traceDetCompanion_apply_00 LT.TwistedNorm.GL2.traceDetCompanion_apply_01 LT.TwistedNorm.GL2.traceDetCompanion_apply_11"
set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicLevel NumberField.AdelicHaar IsDedekindDomain

attribute [local instance] NumberField.AdelicHaar.glBorel AutomorphicForm.centralizerBorel
  AutomorphicForm.twistedCentralizerBorel

open LanglandsTunnell.CubicInduction (diagUnits2)

open scoped TensorProduct TensorProduct.RightActions

open scoped Classical

set_option maxHeartbeats 3200000 in
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
    ∃ Ψ : (v.adicCompletion K)ˣ × (v.adicCompletion K)ˣ → ℂ, ∃ U ∈ nhds (1 : (v.adicCompletion K)ˣ), ∃ ρ : ℝ, 0 < ρ ∧
      (∀ a a' t t' : (v.adicCompletion K)ˣ, t ∈ U →
        ‖(a' : v.adicCompletion K) - (a : v.adicCompletion K)‖ ≤ ρ * ‖(a : v.adicCompletion K)‖ →
        ‖(t' : v.adicCompletion K) - (t : v.adicCompletion K)‖ ≤
            ρ * ‖(1 : v.adicCompletion K) - (t : v.adicCompletion K)‖ →
          Ψ (a', t') = Ψ (a, t)) ∧
      (∃ C : ℝ, ∀ a t : (v.adicCompletion K)ˣ,
        ‖(Ψ (a, t) + 2 * (Module.finrank K L : ℂ) * AutomorphicForm.LocalWeightedOrbital.halfWeighted
          ((AutomorphicForm.localHaar K v).restrict (AutomorphicForm.localIntegralSet K v)) μ
          (fun x : v.adicCompletion K => ‖x‖) f a (a * t)) -
          (Ψ (a, 1) + 2 * (Module.finrank K L : ℂ) * AutomorphicForm.LocalWeightedOrbital.halfWeighted
          ((AutomorphicForm.localHaar K v).restrict (AutomorphicForm.localIntegralSet K v)) μ
          (fun x : v.adicCompletion K => ‖x‖) f a (a * 1))‖ ≤
          C * ‖(1 : v.adicCompletion K) - (t : v.adicCompletion K)‖ *
          (1 + |Real.log ‖(1 : v.adicCompletion K) - (t : v.adicCompletion K)‖|)) ∧
      ∀ a t : (v.adicCompletion K)ˣ, t ≠ 1 → t ∈ U →
          ((∀ α β : (L ⊗[K] v.adicCompletion K)ˣ,
              AutomorphicForm.normString K L (v.adicCompletion K) σ (diagUnits2 α β) =
                AutomorphicForm.toTensorGL K L (v.adicCompletion K) (diagUnits2 a (a * t)) →
            ∀ (τ' : @Measure (AutomorphicForm.twistedCentralizer K L (v.adicCompletion K) σ (diagUnits2 α β))
                (AutomorphicForm.twistedCentralizerBorel K L (v.adicCompletion K) σ (diagUnits2 α β))),
              @Measure.IsHaarMeasure _ _ _
                (AutomorphicForm.twistedCentralizerBorel K L (v.adicCompletion K) σ (diagUnits2 α β)) τ' →
              τ' {x | (x : GL (Fin 2) (L ⊗[K] v.adicCompletion K)) ∈ AutomorphicForm.semiLocalIntegralSet K L v} = 1 →
            ∀ J' : ℂ, AutomorphicForm.IsTwistedWeightedOrbitalIntegral K L v σ (diagUnits2 α β) τ' φ J' →
              ((AutomorphicForm.LocalWeightedOrbital.ratio (fun x : v.adicCompletion K => ‖x‖) a (a * t) *
                  AutomorphicForm.LocalWeightedOrbital.sqrtRatio (fun x : v.adicCompletion K => ‖x‖) a (a * t) : ℝ) : ℂ) * J' = Ψ (a, t)) ∧
          ((¬ ∃ α β : (L ⊗[K] v.adicCompletion K)ˣ,
              AutomorphicForm.normString K L (v.adicCompletion K) σ (diagUnits2 α β) =
                AutomorphicForm.toTensorGL K L (v.adicCompletion K) (diagUnits2 a (a * t))) → Ψ (a, t) = 0)) := by
  classical
  letI : MeasurableSpace (GL (Fin 2) (v.adicCompletion K)) := AutomorphicForm.localGLBorel K v

  have hD0 := AutomorphicForm.exists_isHaarMeasure_twistedCentralizer_and_exists_isTwistedWeightedOrbitalIntegral_of_normString_diagUnits2_eq K L σ hgen hdeg v φ hφ f hf hmatch
  have hD1 := AutomorphicForm.ratio_mul_sqrtRatio_mul_twistedWeighted_eq_of_normString_diagUnits2_eq_of_areMatchingLocal K L σ hgen hdeg v φ hφ f hf hmatch
  obtain ⟨U₂, hU₂, ρ₂, hρ₂, hD2⟩ := AutomorphicForm.exists_nhds_forall_iff_and_ratio_mul_sqrtRatio_mul_twistedWeighted_eq_of_norm_sub_le_of_areMatchingLocal K L σ hgen hdeg v φ hφ f hf hmatch
  obtain ⟨Λ, C₃, U₃, hU₃, hD3⟩ := AutomorphicForm.exists_forall_norm_ratio_mul_sqrtRatio_mul_twistedWeighted_add_halfWeighted_sub_le_of_areMatchingLocal K L σ hgen hdeg v φ hφ f hf hmatch μ hμ
  obtain ⟨U₄, hU₄, ρ₄, hρ₄, hD4⟩ := AutomorphicForm.LocalWeightedOrbital.exists_nhds_forall_halfWeighted_mul_eq_halfWeighted_mul_of_norm_sub_le_of_isLocalTestFn K v μ f hf

  let H : (v.adicCompletion K)ˣ → (v.adicCompletion K)ˣ → ℂ := fun a b => AutomorphicForm.LocalWeightedOrbital.halfWeighted
          ((AutomorphicForm.localHaar K v).restrict (AutomorphicForm.localIntegralSet K v)) μ
          (fun x : (v.adicCompletion K) => ‖x‖) f a b
  let RS : (v.adicCompletion K)ˣ → (v.adicCompletion K)ˣ → ℂ := fun a t => ((AutomorphicForm.LocalWeightedOrbital.ratio (fun x : (v.adicCompletion K) => ‖x‖) a (a * t) *
                  AutomorphicForm.LocalWeightedOrbital.sqrtRatio (fun x : (v.adicCompletion K) => ‖x‖) a (a * t) : ℝ) : ℂ)
  let LIFT : (v.adicCompletion K)ˣ → (v.adicCompletion K)ˣ → Prop := fun a t => ∃ α β : (L ⊗[K] (v.adicCompletion K))ˣ, AutomorphicForm.normString K L (v.adicCompletion K) σ (diagUnits2 α β) =
                AutomorphicForm.toTensorGL K L (v.adicCompletion K) (diagUnits2 a (a * t))

  obtain ⟨r, hr, hball⟩ : ∃ r : ℝ, 0 < r ∧ ∀ t : (v.adicCompletion K)ˣ, ‖(t : (v.adicCompletion K)) - 1‖ < r → t ∈ U₂ ∩ U₃ ∩ U₄ := by
    have hemb := (Units.isEmbedding_val₀ (G₀ := (v.adicCompletion K)))
    have hN : U₂ ∩ U₃ ∩ U₄ ∈ nhds (1 : (v.adicCompletion K)ˣ) := Filter.inter_mem (Filter.inter_mem hU₂ hU₃) hU₄
    rw [hemb.nhds_eq_comap, Filter.mem_comap] at hN
    obtain ⟨T, hT, hTN⟩ := hN
    rw [Units.val_one] at hT
    obtain ⟨ε, hε, hb⟩ := Metric.mem_nhds_iff.mp hT
    exact ⟨ε, hε, fun c hc => hTN (hb (by rwa [Metric.mem_ball, dist_eq_norm]))⟩
  let B : Set (v.adicCompletion K)ˣ := {t | ‖(t : (v.adicCompletion K)) - 1‖ < r}
  have hBo : B ∈ nhds (1 : (v.adicCompletion K)ˣ) :=
    (isOpen_lt (continuous_norm.comp (Units.continuous_val.sub continuous_const)) continuous_const).mem_nhds (by simp [B, hr])

  let val : (v.adicCompletion K)ˣ → (v.adicCompletion K)ˣ → ℂ := fun a t =>
    if h : t ≠ 1 ∧ LIFT a t then
      RS a t * (hD0 a t h.1 h.2.choose h.2.choose_spec.choose h.2.choose_spec.choose_spec).choose_spec.2.2.choose
    else 0

  let Ψ : (v.adicCompletion K)ˣ × (v.adicCompletion K)ˣ → ℂ := fun p =>
    if p.2 ∈ B then (if p.2 = 1 then Λ p.1 - 2 * (Module.finrank K L : ℂ) * H p.1 p.1 else val p.1 p.2)
    else Λ p.1 - 2 * (Module.finrank K L : ℂ) * H p.1 (p.1 * p.2)

  have hval : ∀ a t : (v.adicCompletion K)ˣ, ∀ ht : t ≠ 1, ∀ α β : (L ⊗[K] (v.adicCompletion K))ˣ,
              AutomorphicForm.normString K L (v.adicCompletion K) σ (diagUnits2 α β) =
                AutomorphicForm.toTensorGL K L (v.adicCompletion K) (diagUnits2 a (a * t)) →
            ∀ (τ' : @Measure (AutomorphicForm.twistedCentralizer K L (v.adicCompletion K) σ (diagUnits2 α β))
                (AutomorphicForm.twistedCentralizerBorel K L (v.adicCompletion K) σ (diagUnits2 α β))),
              @Measure.IsHaarMeasure _ _ _
                (AutomorphicForm.twistedCentralizerBorel K L (v.adicCompletion K) σ (diagUnits2 α β)) τ' →
              τ' {x | (x : GL (Fin 2) (L ⊗[K] (v.adicCompletion K))) ∈ AutomorphicForm.semiLocalIntegralSet K L v} = 1 →
            ∀ J' : ℂ, AutomorphicForm.IsTwistedWeightedOrbitalIntegral K L v σ (diagUnits2 α β) τ' φ J' →
              val a t = RS a t * J' := by
    intro a t ht α β hαβ τ' hτ' hτ'1 J' hJ'
    have hL : LIFT a t := ⟨α, β, hαβ⟩
    have hcond : t ≠ 1 ∧ LIFT a t := ⟨ht, hL⟩
    simp only [val, dif_pos hcond]

    have hs := (hD0 a t hcond.1 hcond.2.choose hcond.2.choose_spec.choose hcond.2.choose_spec.choose_spec).choose_spec
    exact hD1 a t ht _ _ hcond.2.choose_spec.choose_spec _ hs.1 hs.2.1 _ hs.2.2.choose_spec α β hαβ τ' hτ' hτ'1 J' hJ'
  have hval0 : ∀ a t : (v.adicCompletion K)ˣ, ¬ LIFT a t → val a t = 0 := by
    intro a t h
    simp only [val]
    rw [dif_neg]
    exact fun h' => h h'.2

  have hΛ : ∀ a a' : (v.adicCompletion K)ˣ, ‖(a' : (v.adicCompletion K)) - (a : (v.adicCompletion K))‖ ≤ min ρ₂ ρ₄ * ‖(a : (v.adicCompletion K))‖ → Λ a' = Λ a := by
    intro a a' ha
    have ha2 : ‖(a' : (v.adicCompletion K)) - (a : (v.adicCompletion K))‖ ≤ ρ₂ * ‖(a : (v.adicCompletion K))‖ := ha.trans (mul_le_mul_of_nonneg_right (min_le_left _ _) (norm_nonneg _))
    have ha4 : ‖(a' : (v.adicCompletion K)) - (a : (v.adicCompletion K))‖ ≤ ρ₄ * ‖(a : (v.adicCompletion K))‖ := ha.trans (mul_le_mul_of_nonneg_right (min_le_right _ _) (norm_nonneg _))

    have hclose : ∀ t : (v.adicCompletion K)ˣ, t ∈ B → t ≠ 1 →
        ‖Λ a' - Λ a‖ ≤ 2 * (max C₃ 0) * (‖(1 : (v.adicCompletion K)) - (t : (v.adicCompletion K))‖ * (1 + |Real.log ‖(1 : (v.adicCompletion K)) - (t : (v.adicCompletion K))‖|)) := by
      intro t htB ht1
      obtain ⟨⟨htU2, htU3⟩, htU4⟩ := hball t htB
      set ε : ℝ := ‖(1 : (v.adicCompletion K)) - (t : (v.adicCompletion K))‖ * (1 + |Real.log ‖(1 : (v.adicCompletion K)) - (t : (v.adicCompletion K))‖|) with hε
      have hε0 : 0 ≤ ε := by positivity
      have hH : H a' (a' * t) = H a (a * t) := hD4 a a' t t htU4 ha4 (by rw [sub_self, norm_zero]; positivity)
      obtain ⟨hiff, hvals⟩ := hD2 a a' t t htU2 ha2 (by rw [sub_self, norm_zero]; positivity) ht1 ht1
      obtain ⟨hl, hn⟩ := hD3 a t ht1 htU3
      obtain ⟨hl', hn'⟩ := hD3 a' t ht1 htU3

      obtain ⟨G, hGa, hGa'⟩ : ∃ G : ℂ, ‖G - Λ a‖ ≤ C₃ * ε ∧ ‖G - Λ a'‖ ≤ C₃ * ε := by
        by_cases hL : LIFT a t
        · have hL' : LIFT a' t := hiff.mp hL
          obtain ⟨α, β, hαβ⟩ := hL
          obtain ⟨α', β', hαβ'⟩ := hL'
          obtain ⟨τ', hτ', h1, J', hJ'⟩ := hD0 a t ht1 α β hαβ
          obtain ⟨τ'', hτ'', h1', J'', hJ''⟩ := hD0 a' t ht1 α' β' hαβ'
          have hv := hvals α β hαβ τ' hτ' h1 J' hJ' α' β' hαβ' τ'' hτ'' h1' J'' hJ''
          refine ⟨RS a t * J' + 2 * (Module.finrank K L : ℂ) * H a (a * t), ?_, ?_⟩
          · simpa only [hε, mul_assoc] using hl α β hαβ τ' hτ' h1 J' hJ'
          · rw [hv, ← hH]
            simpa only [hε, mul_assoc] using hl' α' β' hαβ' τ'' hτ'' h1' J'' hJ''
        · have hL' : ¬ LIFT a' t := fun h => hL (hiff.mpr h)
          refine ⟨2 * (Module.finrank K L : ℂ) * H a (a * t), ?_, ?_⟩
          · simpa only [hε, mul_assoc] using hn hL
          · rw [← hH]; simpa only [hε, mul_assoc] using hn' hL'
      have hC : C₃ * ε ≤ max C₃ 0 * ε := mul_le_mul_of_nonneg_right (le_max_left _ _) hε0
      calc ‖Λ a' - Λ a‖ = ‖(G - Λ a) - (G - Λ a')‖ := by congr 1; ring
        _ ≤ ‖G - Λ a‖ + ‖G - Λ a'‖ := norm_sub_le _ _
        _ ≤ max C₃ 0 * ε + max C₃ 0 * ε := add_le_add (hGa.trans hC) (hGa'.trans hC)
        _ = 2 * max C₃ 0 * ε := by ring

    refine eq_of_sub_eq_zero (norm_le_zero_iff.mp (le_of_forall_pos_le_add fun η hη => ?_))
    rw [zero_add]
    set C' : ℝ := max C₃ 0 + 1 with hC'
    have hC'0 : 0 < C' := by positivity
    obtain ⟨x, hx0, hxlt⟩ : ∃ x : (v.adicCompletion K), 0 < ‖x‖ ∧ ‖x‖ < min (min r 1) ((η / (6 * C')) ^ 2) := by
      have hδ : 0 < min (min r 1) ((η / (6 * C')) ^ 2) :=
        lt_min (lt_min hr one_pos) (pow_pos (div_pos hη (by positivity)) 2)
      set ϖ : (v.adicCompletion K) := (uniformizerUnit K v : (v.adicCompletion K)) with hϖ
      have hϖ1 : ‖ϖ‖ < 1 := by
        refine Valued.toNormedField.norm_lt_one_iff.mpr ?_
        rw [hϖ, valued_uniformizerUnit, ← WithZero.exp_zero, WithZero.exp_lt_exp]; norm_num
      have hϖ0 : 0 < ‖ϖ‖ := norm_pos_iff.mpr (uniformizerUnit K v).ne_zero
      obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one hδ hϖ1
      refine ⟨ϖ ^ (n + 1), by rw [norm_pow]; exact pow_pos hϖ0 _, ?_⟩
      rw [norm_pow, pow_succ]
      exact lt_of_le_of_lt (mul_le_of_le_one_right (pow_nonneg hϖ0.le n) hϖ1.le) hn
    have hxr : ‖x‖ < r := hxlt.trans_le ((min_le_left _ _).trans (min_le_left _ _))
    have hx1 : ‖x‖ < 1 := hxlt.trans_le ((min_le_left _ _).trans (min_le_right _ _))
    have hxη : ‖x‖ < (η / (6 * C')) ^ 2 := hxlt.trans_le (min_le_right _ _)
    have hxne : x ≠ 0 := norm_pos_iff.mp hx0
    have h1x : ‖(1 : (v.adicCompletion K)) + x‖ = 1 := by
      have h : ‖(1 : (v.adicCompletion K))‖ ≠ ‖x‖ := by rw [norm_one]; exact (ne_of_gt hx1)
      rw [IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm h, norm_one, max_eq_left hx1.le]
    have h1x0 : (1 : (v.adicCompletion K)) + x ≠ 0 := by intro h; rw [h, norm_zero] at h1x; exact one_ne_zero h1x.symm
    set t : (v.adicCompletion K)ˣ := Units.mk0 _ h1x0 with htdef
    have htv : (t : (v.adicCompletion K)) = 1 + x := rfl
    have htB : t ∈ B := by show ‖(t : (v.adicCompletion K)) - 1‖ < r; rw [htv, add_sub_cancel_left]; exact hxr
    have ht1 : t ≠ 1 := by
      intro h; apply hxne
      have : (t : (v.adicCompletion K)) = 1 := by rw [h, Units.val_one]
      rwa [htv, add_eq_left] at this
    have hnorm : ‖(1 : (v.adicCompletion K)) - (t : (v.adicCompletion K))‖ = ‖x‖ := by rw [htv, sub_add_cancel_left, norm_neg]
    have hb := hclose t htB ht1
    rw [hnorm] at hb

    set s : ℝ := ‖x‖ with hs
    have hs0 : 0 < s := hx0
    have hsq0 : 0 < Real.sqrt s := Real.sqrt_pos.mpr hs0
    have hlog : s * |Real.log s| ≤ 2 * Real.sqrt s := by
      have hls : Real.log s = 2 * Real.log (Real.sqrt s) := by
        rw [Real.log_sqrt hs0.le]; ring
      have hneg : Real.log s ≤ 0 := Real.log_nonpos hs0.le hx1.le
      rw [abs_of_nonpos hneg, hls]
      have h1 : -Real.log (Real.sqrt s) = Real.log ((Real.sqrt s)⁻¹) := by rw [Real.log_inv]
      have h2 : Real.log ((Real.sqrt s)⁻¹) ≤ (Real.sqrt s)⁻¹ - 1 := Real.log_le_sub_one_of_pos (inv_pos.mpr hsq0)
      have h3 : s * (Real.sqrt s)⁻¹ = Real.sqrt s := by
        rw [← div_eq_mul_inv, Real.div_sqrt]
      nlinarith [h2, h3, hs0, hsq0, mul_nonneg hs0.le (inv_pos.mpr hsq0).le]
    have hsle : s ≤ Real.sqrt s := by
      have := Real.sqrt_le_sqrt hx1.le
      rw [Real.sqrt_one] at this
      calc s = Real.sqrt s * Real.sqrt s := (Real.mul_self_sqrt hs0.le).symm
        _ ≤ Real.sqrt s * 1 := mul_le_mul_of_nonneg_left this hsq0.le
        _ = Real.sqrt s := mul_one _
    have hε3 : s * (1 + |Real.log s|) ≤ 3 * Real.sqrt s := by nlinarith [hlog, hsle]
    have hsqrt : Real.sqrt s < η / (6 * C') := by
      rw [Real.sqrt_lt' (div_pos hη (by positivity))]
      exact hxη
    calc ‖Λ a' - Λ a‖ ≤ 2 * max C₃ 0 * (s * (1 + |Real.log s|)) := hb
      _ ≤ 2 * max C₃ 0 * (3 * Real.sqrt s) := mul_le_mul_of_nonneg_left hε3 (by positivity)
      _ ≤ 2 * C' * (3 * Real.sqrt s) := by gcongr; linarith [le_max_right C₃ 0]
      _ = (6 * C') * Real.sqrt s := by ring
      _ ≤ (6 * C') * (η / (6 * C')) := mul_le_mul_of_nonneg_left hsqrt.le (by positivity)
      _ = η := by field_simp
  set ρ : ℝ := min (min ρ₂ ρ₄) (1 / 2) with hρdef
  have hρ2 : ρ ≤ ρ₂ := (min_le_left _ _).trans (min_le_left _ _)
  have hρ4 : ρ ≤ ρ₄ := (min_le_left _ _).trans (min_le_right _ _)
  have hρm : ρ ≤ min ρ₂ ρ₄ := min_le_left _ _
  have hρh : ρ ≤ 1 / 2 := min_le_right _ _
  have hρ0 : 0 < ρ := lt_min (lt_min hρ₂ hρ₄) (by norm_num)
  have h1B : (1 : (v.adicCompletion K)ˣ) ∈ B := by simp [B, hr]
  have hBU : ∀ t ∈ B, t ∈ U₂ ∧ t ∈ U₃ ∧ t ∈ U₄ := fun t ht => by
    obtain ⟨⟨h2, h3⟩, h4⟩ := hball t ht; exact ⟨h2, h3, h4⟩
  refine ⟨Ψ, B, hBo, ρ, hρ0, ?_, ?_, ?_⟩
  ·
    intro a a' t t' htB ha ht'
    obtain ⟨htU2, htU3, htU4⟩ := hBU t htB
    have ha2 : ‖(a' : (v.adicCompletion K)) - (a : (v.adicCompletion K))‖ ≤ ρ₂ * ‖(a : (v.adicCompletion K))‖ := ha.trans (mul_le_mul_of_nonneg_right hρ2 (norm_nonneg _))
    have ha4 : ‖(a' : (v.adicCompletion K)) - (a : (v.adicCompletion K))‖ ≤ ρ₄ * ‖(a : (v.adicCompletion K))‖ := ha.trans (mul_le_mul_of_nonneg_right hρ4 (norm_nonneg _))
    have ham : ‖(a' : (v.adicCompletion K)) - (a : (v.adicCompletion K))‖ ≤ min ρ₂ ρ₄ * ‖(a : (v.adicCompletion K))‖ := ha.trans (mul_le_mul_of_nonneg_right hρm (norm_nonneg _))
    have ht2 : ‖(t' : (v.adicCompletion K)) - (t : (v.adicCompletion K))‖ ≤ ρ₂ * ‖(1 : (v.adicCompletion K)) - (t : (v.adicCompletion K))‖ := ht'.trans (mul_le_mul_of_nonneg_right hρ2 (norm_nonneg _))
    by_cases ht1 : t = 1
    ·
      subst ht1
      have ht'1 : t' = 1 := by
        have h := ht'; rw [Units.val_one, sub_self, norm_zero, mul_zero] at h
        exact Units.ext (sub_eq_zero.mp (norm_le_zero_iff.mp h))
      subst ht'1
      show Ψ (a', 1) = Ψ (a, 1)
      simp only [Ψ, h1B, if_true]
      have hH := hD4 a a' 1 1 (mem_of_mem_nhds hU₄) ha4 (by simp)
      simp only [mul_one] at hH
      rw [hΛ a a' ham]
      show Λ a - 2 * (Module.finrank K L : ℂ) * H a' a' = Λ a - 2 * (Module.finrank K L : ℂ) * H a a
      simp only [H]; rw [hH]
    ·
      have h1t0 : 0 < ‖(1 : (v.adicCompletion K)) - (t : (v.adicCompletion K))‖ := by
        rw [norm_pos_iff, sub_ne_zero]; intro h; exact ht1 (Units.ext h.symm)
      have hlt : ‖(t' : (v.adicCompletion K)) - (t : (v.adicCompletion K))‖ < ‖(1 : (v.adicCompletion K)) - (t : (v.adicCompletion K))‖ :=
        ht'.trans_lt (by nlinarith)
      have h1t' : ‖(1 : (v.adicCompletion K)) - (t' : (v.adicCompletion K))‖ = ‖(1 : (v.adicCompletion K)) - (t : (v.adicCompletion K))‖ := by
        have hlt' : ‖(t : (v.adicCompletion K)) - (t' : (v.adicCompletion K))‖ < ‖(1 : (v.adicCompletion K)) - (t : (v.adicCompletion K))‖ := by rw [← norm_neg, neg_sub]; exact hlt
        have := IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm (ne_of_gt hlt')
        rw [show (1 : (v.adicCompletion K)) - (t : (v.adicCompletion K)) + ((t : (v.adicCompletion K)) - (t' : (v.adicCompletion K))) = 1 - (t' : (v.adicCompletion K)) by ring, max_eq_left hlt'.le] at this
        exact this
      have ht'1 : t' ≠ 1 := by
        intro h; rw [h, Units.val_one, sub_self, norm_zero] at h1t'; exact h1t0.ne' h1t'.symm
      have ht'B : t' ∈ B := by
        show ‖(t' : (v.adicCompletion K)) - 1‖ < r
        rw [← norm_neg, neg_sub, h1t', ← norm_neg, neg_sub]; exact htB
      show Ψ (a', t') = Ψ (a, t)
      simp only [Ψ, htB, ht'B, if_true, ht1, ht'1, if_false]
      obtain ⟨hiff, hvals⟩ := hD2 a a' t t' htU2 ha2 ht2 ht1 ht'1
      by_cases hL : LIFT a t
      · have hL' : LIFT a' t' := hiff.mp hL
        have hc : t ≠ 1 ∧ LIFT a t := ⟨ht1, hL⟩
        have hc' : t' ≠ 1 ∧ LIFT a' t' := ⟨ht'1, hL'⟩
        simp only [val, dif_pos hc, dif_pos hc']
        have hs := (hD0 a t hc.1 hc.2.choose hc.2.choose_spec.choose hc.2.choose_spec.choose_spec).choose_spec
        have hs' := (hD0 a' t' hc'.1 hc'.2.choose hc'.2.choose_spec.choose hc'.2.choose_spec.choose_spec).choose_spec
        exact (hvals _ _ hc.2.choose_spec.choose_spec _ hs.1 hs.2.1 _ hs.2.2.choose_spec
          _ _ hc'.2.choose_spec.choose_spec _ hs'.1 hs'.2.1 _ hs'.2.2.choose_spec).symm
      · have hL' : ¬ LIFT a' t' := fun h => hL (hiff.mpr h)
        rw [hval0 a t hL, hval0 a' t' hL']
  ·
    refine ⟨max C₃ 0, fun a t => ?_⟩
    have hRHS : 0 ≤ max C₃ 0 * ‖(1 : (v.adicCompletion K)) - (t : (v.adicCompletion K))‖ * (1 + |Real.log ‖(1 : (v.adicCompletion K)) - (t : (v.adicCompletion K))‖|) := by positivity
    have hΨ1 : Ψ (a, 1) = Λ a - 2 * (Module.finrank K L : ℂ) * H a a := by simp only [Ψ, h1B, if_true]
    rw [hΨ1]
    simp only [mul_one]
    by_cases htB : t ∈ B
    · by_cases ht1 : t = 1
      · subst ht1
        rw [hΨ1]
        simp only [mul_one, Units.val_one]
        show ‖Λ a - 2 * (Module.finrank K L : ℂ) * H a a + 2 * (Module.finrank K L : ℂ) * H a a -
          (Λ a - 2 * (Module.finrank K L : ℂ) * H a a + 2 * (Module.finrank K L : ℂ) * H a a)‖ ≤ _
        rw [sub_self, norm_zero]; exact hRHS
      · obtain ⟨htU2, htU3, htU4⟩ := hBU t htB
        obtain ⟨hlift, hnolift⟩ := hD3 a t ht1 htU3
        have hΨt : Ψ (a, t) = val a t := by simp only [Ψ, htB, if_true, ht1, if_false]
        rw [hΨt]
        have hring : ∀ X Y Z : ℂ, X + Y - (Z - (2 * (Module.finrank K L : ℂ) * H a a) + 2 * (Module.finrank K L : ℂ) * H a a) = X + Y - Z := fun X Y Z => by ring
        show ‖val a t + 2 * (Module.finrank K L : ℂ) * H a (a * t) - (Λ a - 2 * (Module.finrank K L : ℂ) * H a a + 2 * (Module.finrank K L : ℂ) * H a a)‖ ≤ _
        rw [hring]
        by_cases hL : LIFT a t
        · have hc : t ≠ 1 ∧ LIFT a t := ⟨ht1, hL⟩
          simp only [val, dif_pos hc]
          have hs := (hD0 a t hc.1 hc.2.choose hc.2.choose_spec.choose hc.2.choose_spec.choose_spec).choose_spec
          refine (hlift _ _ hc.2.choose_spec.choose_spec _ hs.1 hs.2.1 _ hs.2.2.choose_spec).trans ?_
          exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_max_left _ _) (norm_nonneg _)) (by positivity)
        · rw [hval0 a t hL, zero_add]
          refine (hnolift hL).trans ?_
          exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_max_left _ _) (norm_nonneg _)) (by positivity)
    · have hΨt : Ψ (a, t) = Λ a - 2 * (Module.finrank K L : ℂ) * H a (a * t) := by simp only [Ψ, htB, if_false]
      rw [hΨt]
      show ‖Λ a - 2 * (Module.finrank K L : ℂ) * H a (a * t) + 2 * (Module.finrank K L : ℂ) * H a (a * t) -
        (Λ a - 2 * (Module.finrank K L : ℂ) * H a a + 2 * (Module.finrank K L : ℂ) * H a a)‖ ≤ _
      rw [show Λ a - 2 * (Module.finrank K L : ℂ) * H a (a * t) + 2 * (Module.finrank K L : ℂ) * H a (a * t) -
        (Λ a - 2 * (Module.finrank K L : ℂ) * H a a + 2 * (Module.finrank K L : ℂ) * H a a) = 0 by ring, norm_zero]
      exact hRHS
  ·
    intro a t ht1 htB
    refine ⟨fun α β hαβ τ' hτ' hτ'1 J' hJ' => ?_, fun hno => ?_⟩
    · show _ = Ψ (a, t)
      simp only [Ψ, htB, if_true, ht1, if_false]
      exact (hval a t ht1 α β hαβ τ' hτ' hτ'1 J' hJ').symm
    · show Ψ (a, t) = 0
      simp only [Ψ, htB, if_true, ht1, if_false]
      exact hval0 a t hno

end S_AutomorphicForm_exists_nhds_forall_eq_of_norm_sub_le_and_norm_add_halfWeighted_sub_le_and_forall_ratio_mul_sqrtRatio_mul_twistedWeighted_eq_of_areMatchingLocal
end P2MW
export P2MW.S_AutomorphicForm_exists_nhds_forall_eq_of_norm_sub_le_and_norm_add_halfWeighted_sub_le_and_forall_ratio_mul_sqrtRatio_mul_twistedWeighted_eq_of_areMatchingLocal (solution)
