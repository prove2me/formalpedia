-- Prove2me | solution 1 for AccountingRules.Threshold.case_2_1_first_best
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-01T04:13:34.4552+00:00
-- url     : https://prove2.me/submissions/30d85f82-f50f-4984-9d55-8b3f6e1af256

import Mathlib
import Definitions.Def_AccountingRules_Threshold_Model

set_option linter.style.haveILetI false
set_option linter.unusedVariables false
set_option linter.deprecated false

open MeasureTheory ProbabilityTheory Set

namespace AccProp2Sol

open AccountingRules.Threshold

lemma ae_mem (P : Measure ℝ) (θlo θhi M B : ℝ) (hS : Standing P θlo θhi M B) :
    ∀ᵐ θ ∂P, θ ∈ Icc θlo θhi := by
  rw [ae_iff]
  simpa [compl_def] using hS.supp_sub

lemma integrable_of_supp (μ : Measure ℝ) [IsFiniteMeasure μ] (a b : ℝ)
    (h : μ (Icc a b)ᶜ = 0) : Integrable (fun θ : ℝ => θ) μ := by
  have hae : ∀ᵐ θ ∂μ, θ ∈ Icc a b := by
    rw [ae_iff]; simpa [compl_def] using h
  refine Integrable.mono' (integrable_const (|a| + |b|)) measurable_id.aestronglyMeasurable ?_
  filter_upwards [hae] with θ hθ
  rw [Real.norm_eq_abs, abs_le]
  constructor
  · have := hθ.1; have := neg_abs_le a; have := abs_nonneg b; linarith
  · have := hθ.2; have := le_abs_self b; have := abs_nonneg a; linarith

lemma integrable_id (P : Measure ℝ) (θlo θhi M B : ℝ) (hS : Standing P θlo θhi M B) :
    Integrable (fun θ : ℝ => θ) P := by
  have := hS.prob
  exact integrable_of_supp P θlo θhi hS.supp_sub

lemma noAtoms (P : Measure ℝ) (θlo θhi M B : ℝ) (hS : Standing P θlo θhi M B) :
    NullSingletonClass P := ⟨fun x => hS.density (Real.volume_singleton)⟩

lemma pos_Iio (P : Measure ℝ) (θlo θhi M B : ℝ) (hS : Standing P θlo θhi M B) (t : ℝ)
    (ht : θlo < t) (hlohi : θlo < θhi) : 0 < P (Iio t) := by
  have h := hS.supp_full θlo (min t θhi) le_rfl (lt_min ht hlohi) (min_le_right _ _)
  exact lt_of_lt_of_le h (measure_mono (fun x hx => lt_of_lt_of_le hx.2 (min_le_left _ _)))

lemma pos_Iic (P : Measure ℝ) (θlo θhi M B : ℝ) (hS : Standing P θlo θhi M B) (t : ℝ)
    (ht : θlo < t) (hlohi : θlo < θhi) : 0 < P (Iic t) :=
  lt_of_lt_of_le (pos_Iio P θlo θhi M B hS t ht hlohi) (measure_mono Iio_subset_Iic_self)

lemma pos_Ioi (P : Measure ℝ) (θlo θhi M B : ℝ) (hS : Standing P θlo θhi M B) (t : ℝ)
    (ht : t < θhi) (hlohi : θlo < θhi) : 0 < P (Ioi t) := by
  have h := hS.supp_full (max t θlo) θhi (le_max_right _ _) (max_lt ht hlohi) le_rfl
  exact lt_of_lt_of_le h (measure_mono (fun x hx => lt_of_le_of_lt (le_max_left _ _) hx.1))

/-- `G k t = ∫_{θ ≤ t} (θ - k) dP`. -/
noncomputable def G (P : Measure ℝ) (k t : ℝ) : ℝ := ∫ θ in Iic t, (θ - k) ∂P

lemma G_eq (P : Measure ℝ) (θlo θhi M B : ℝ) (hS : Standing P θlo θhi M B) (k t : ℝ) :
    G P k t = (∫ θ in Iic t, θ ∂P) - k * (P (Iic t)).toReal := by
  have := hS.prob
  have hi := integrable_id P θlo θhi M B hS
  unfold G
  rw [integral_sub hi.integrableOn (integrable_const k).integrableOn, setIntegral_const,
    smul_eq_mul, measureReal_def, mul_comm]

lemma condMean_id (P : Measure ℝ) (S : Set ℝ) :
    condMean P id S = (∫ θ in S, θ ∂P) / (P S).toReal := rfl

lemma condMean_eq_iff (P : Measure ℝ) (θlo θhi M B : ℝ) (hS : Standing P θlo θhi M B) (k t : ℝ)
    (hpos : 0 < P (Iic t)) : condMean P id (Iic t) = k ↔ G P k t = 0 := by
  have := hS.prob
  have hF : 0 < (P (Iic t)).toReal := ENNReal.toReal_pos hpos.ne' (measure_ne_top _ _)
  rw [condMean_id, G_eq P θlo θhi M B hS, div_eq_iff hF.ne', sub_eq_zero]

lemma condMean_le_iff (P : Measure ℝ) (θlo θhi M B : ℝ) (hS : Standing P θlo θhi M B) (k t : ℝ)
    (hpos : 0 < P (Iic t)) : condMean P id (Iic t) ≤ k ↔ G P k t ≤ 0 := by
  have := hS.prob
  have hF : 0 < (P (Iic t)).toReal := ENNReal.toReal_pos hpos.ne' (measure_ne_top _ _)
  rw [condMean_id, G_eq P θlo θhi M B hS, div_le_iff₀ hF, sub_nonpos]

lemma condMean_sub (P : Measure ℝ) (θlo θhi M B : ℝ) (hS : Standing P θlo θhi M B) (t : ℝ)
    (hpos : 0 < P (Iic t)) :
    condMean P (fun θ => M - θ) (Iic t) = M - condMean P id (Iic t) := by
  have := hS.prob
  have hi := integrable_id P θlo θhi M B hS
  have hF : 0 < (P (Iic t)).toReal := ENNReal.toReal_pos hpos.ne' (measure_ne_top _ _)
  unfold condMean
  rw [integral_sub (integrable_const M).integrableOn hi.integrableOn, setIntegral_const,
    smul_eq_mul, measureReal_def]
  simp only [id]
  field_simp

/-- Strictly below the lower end: `G k k < 0` when `θlo < k`. -/
lemma G_self_neg (P : Measure ℝ) (θlo θhi M B : ℝ) (hS : Standing P θlo θhi M B) (k : ℝ)
    (hk : θlo < k) (hlohi : θlo < θhi) : G P k k < 0 := by
  have := hS.prob
  have hi := integrable_id P θlo θhi M B hS
  have hint : IntegrableOn (fun θ => k - θ) (Iic k) P :=
    ((integrable_const k).sub hi).integrableOn
  have hpos : 0 < ∫ θ in Iic k, (k - θ) ∂P := by
    rw [setIntegral_pos_iff_support_of_nonneg_ae _ hint]
    · refine lt_of_lt_of_le (pos_Iio P θlo θhi M B hS k hk hlohi) (measure_mono ?_)
      intro x hx
      refine ⟨?_, (show x < k from hx).le⟩
      simp only [Function.mem_support]
      have : x < k := hx
      linarith
    · filter_upwards [ae_restrict_mem measurableSet_Iic] with x hx
      simp only [Pi.zero_apply]
      have : x ≤ k := hx
      linarith
  have : G P k k = - ∫ θ in Iic k, (k - θ) ∂P := by
    unfold G
    rw [← integral_neg]
    congr 1; ext θ; ring
  linarith

/-- Strict monotonicity of `G k` on `[k, θhi]`. -/
lemma G_strictMono (P : Measure ℝ) (θlo θhi M B : ℝ) (hS : Standing P θlo θhi M B) (k : ℝ)
    (hk : θlo < k) (s t : ℝ) (hks : k ≤ s) (hst : s < t) (hth : t ≤ θhi) :
    G P k s < G P k t := by
  have := hS.prob
  have hi := integrable_id P θlo θhi M B hS
  have hfi : Integrable (fun θ => θ - k) P := hi.sub (integrable_const k)
  have hsplit : G P k t = G P k s + ∫ θ in Ioc s t, (θ - k) ∂P := by
    unfold G
    rw [← Iic_union_Ioc_eq_Iic hst.le, setIntegral_union (Iic_disjoint_Ioc le_rfl)
      measurableSet_Ioc hfi.integrableOn hfi.integrableOn]
  have hpos : 0 < ∫ θ in Ioc s t, (θ - k) ∂P := by
    rw [setIntegral_pos_iff_support_of_nonneg_ae _ hfi.integrableOn]
    · have h := hS.supp_full s t (by linarith) hst hth
      refine lt_of_lt_of_le h (measure_mono ?_)
      intro x hx
      refine ⟨?_, hx.1, hx.2.le⟩
      simp only [Function.mem_support]
      have := hx.1
      linarith
    · filter_upwards [ae_restrict_mem measurableSet_Ioc] with x hx
      simp only [Pi.zero_apply]
      have := hx.1
      linarith
  linarith

lemma G_continuous (P : Measure ℝ) (θlo θhi M B : ℝ) (hS : Standing P θlo θhi M B) (k : ℝ) :
    Continuous (G P k) := by
  have := hS.prob
  have := noAtoms P θlo θhi M B hS
  have hi := integrable_id P θlo θhi M B hS
  have hfi : Integrable (fun θ => θ - k) P := hi.sub (integrable_const k)
  have heq : G P k = fun t => G P k 0 + ∫ θ in (0:ℝ)..t, (θ - k) ∂P := by
    funext t
    unfold G
    rw [← intervalIntegral.integral_Iic_sub_Iic hfi.integrableOn hfi.integrableOn]
    ring
  rw [heq]
  exact continuous_const.add (hfi.continuous_primitive 0)


lemma rule_int (P : Measure ℝ) [IsFiniteMeasure P] (hi : Integrable (fun θ : ℝ => θ) P)
    (m : ℝ → ℝ) (hm : IsRule m) :
    Integrable m P ∧ Integrable (fun θ => θ * m θ) P := by
  have hb : ∀ᵐ θ ∂P, ‖m θ‖ ≤ 1 := Filter.Eventually.of_forall (fun θ => by
    rw [Real.norm_eq_abs, abs_le]; constructor <;> linarith [(hm.2 θ).1, (hm.2 θ).2])
  refine ⟨Integrable.mono' (integrable_const 1) hm.1.aestronglyMeasurable hb, ?_⟩
  have := hi.bdd_mul hm.1.aestronglyMeasurable hb
  simpa [mul_comm] using this

/-- The Lagrangian identity for the binary program. -/
lemma lagr_eq (P : Measure ℝ) [IsProbabilityMeasure P] (hi : Integrable (fun θ : ℝ => θ) P)
    (M k lam : ℝ) (m : ℝ → ℝ) (hm : IsRule m) :
    objective P M m + lam * (k * ∫ θ, (1 - m θ) ∂P - ∫ θ, θ * (1 - m θ) ∂P) =
      M + ∫ θ, ((θ - M) * m θ + lam * (k - θ) * (1 - m θ)) ∂P := by
  obtain ⟨hmi, hθm⟩ := rule_int P hi m hm
  have h1 : ∫ θ, (1 - m θ) ∂P = 1 - ∫ θ, m θ ∂P := by
    rw [integral_sub (integrable_const 1) hmi]; simp
  have h2 : ∫ θ, θ * (1 - m θ) ∂P = (∫ θ, θ ∂P) - ∫ θ, θ * m θ ∂P := by
    rw [← integral_sub hi hθm]; congr 1; ext θ; ring
  have h3 : ∫ θ, ((θ - M) * m θ + lam * (k - θ) * (1 - m θ)) ∂P =
      ∫ θ, (((1 + lam) * (θ * m θ) - (M + lam * k) * m θ) + (lam * k - lam * θ)) ∂P := by
    congr 1; ext θ; ring
  have i1 : Integrable (fun θ => (1 + lam) * (θ * m θ) - (M + lam * k) * m θ) P :=
    (hθm.const_mul _).sub (hmi.const_mul _)
  have i2 : Integrable (fun θ => lam * k - lam * θ) P := (integrable_const _).sub (hi.const_mul _)
  rw [h3, integral_add i1 i2,
    integral_sub (hθm.const_mul _) (hmi.const_mul _),
    integral_sub (integrable_const _) (hi.const_mul _),
    integral_const, h1, h2]
  unfold objective
  simp only [integral_const_mul, probReal_univ, smul_eq_mul, one_mul]
  have h4 : (∫ a : ℝ, lam * a ∂P) = lam * ∫ θ, θ ∂P := integral_const_mul lam _
  erw [h4]
  ring

lemma ind_rule (t : ℝ) : IsRule ((Ioi t).indicator (fun _ => (1 : ℝ))) := by
  refine ⟨measurable_const.indicator measurableSet_Ioi, fun θ => ?_⟩
  by_cases h : θ ∈ Ioi t <;> simp [indicator, h]

lemma pointwise_lagr (M k t lam : ℝ) (hlam : 0 ≤ lam) (hrel : M + lam * k = (1 + lam) * t)
    (m : ℝ → ℝ) (hm : IsRule m) (θ : ℝ) :
    (θ - M) * m θ + lam * (k - θ) * (1 - m θ) ≤
      (θ - M) * (Ioi t).indicator (fun _ => (1 : ℝ)) θ +
        lam * (k - θ) * (1 - (Ioi t).indicator (fun _ => (1 : ℝ)) θ) := by
  have h0 := (hm.2 θ).1
  have h1 := (hm.2 θ).2
  by_cases h : t < θ
  · have hi : (Ioi t).indicator (fun _ => (1 : ℝ)) θ = 1 := by simp [indicator, h]
    rw [hi]
    have : 0 ≤ (1 + lam) * (θ - t) := mul_nonneg (by linarith) (by linarith)
    have : 0 ≤ (1 - m θ) * ((θ - M) - lam * (k - θ)) := mul_nonneg (by linarith) (by nlinarith)
    nlinarith
  · have hi : (Ioi t).indicator (fun _ => (1 : ℝ)) θ = 0 := by simp [indicator, h]
    rw [hi]
    push_neg at h
    have : 0 ≤ (1 + lam) * (t - θ) := mul_nonneg (by linarith) (by linarith)
    have : 0 ≤ m θ * (lam * (k - θ) - (θ - M)) := mul_nonneg h0 (by nlinarith)
    nlinarith

lemma obj_le (P : Measure ℝ) [IsProbabilityMeasure P] (hi : Integrable (fun θ : ℝ => θ) P)
    (M k t lam : ℝ) (hlam : 0 ≤ lam) (hrel : M + lam * k = (1 + lam) * t)
    (m : ℝ → ℝ) (hm : IsRule m) :
    objective P M m + lam * (k * ∫ θ, (1 - m θ) ∂P - ∫ θ, θ * (1 - m θ) ∂P) ≤
      objective P M ((Ioi t).indicator (fun _ => (1 : ℝ))) +
        lam * (k * ∫ θ, (1 - (Ioi t).indicator (fun _ => (1 : ℝ)) θ) ∂P -
          ∫ θ, θ * (1 - (Ioi t).indicator (fun _ => (1 : ℝ)) θ) ∂P) := by
  rw [lagr_eq P hi M k lam m hm, lagr_eq P hi M k lam _ (ind_rule t)]
  have hint : ∀ m' : ℝ → ℝ, IsRule m' →
      Integrable (fun θ => (θ - M) * m' θ + lam * (k - θ) * (1 - m' θ)) P := by
    intro m' hm'
    obtain ⟨hmi, hθm⟩ := rule_int P hi m' hm'
    have : (fun θ => (θ - M) * m' θ + lam * (k - θ) * (1 - m' θ)) =
        fun θ => (((1 + lam) * (θ * m' θ) - (M + lam * k) * m' θ) + (lam * k - lam * θ)) := by
      ext θ; ring
    rw [this]
    exact ((hθm.const_mul _).sub (hmi.const_mul _)).add ((integrable_const _).sub (hi.const_mul _))
  have := integral_mono (hint m hm) (hint _ (ind_rule t))
    (fun θ => pointwise_lagr M k t lam hlam hrel m hm θ)
  linarith

lemma int_one_sub_ind (P : Measure ℝ) [IsFiniteMeasure P] (t : ℝ) :
    ∫ θ, (1 - (Ioi t).indicator (fun _ => (1 : ℝ)) θ) ∂P = (P (Iic t)).toReal := by
  have : (fun θ => 1 - (Ioi t).indicator (fun _ => (1 : ℝ)) θ) =
      (Iic t).indicator (fun _ => (1 : ℝ)) := by
    ext θ; by_cases h : t < θ
    · simp [indicator, h, not_le.mpr h]
    · simp [indicator, h, not_lt.mp h]
  rw [this, integral_indicator measurableSet_Iic, setIntegral_const, smul_eq_mul, mul_one,
    measureReal_def]

lemma int_θ_one_sub_ind (P : Measure ℝ) (t : ℝ) :
    ∫ θ, θ * (1 - (Ioi t).indicator (fun _ => (1 : ℝ)) θ) ∂P = ∫ θ in Iic t, θ ∂P := by
  have : (fun θ => θ * (1 - (Ioi t).indicator (fun _ => (1 : ℝ)) θ)) =
      (Iic t).indicator (fun θ => θ) := by
    ext θ; by_cases h : t < θ
    · simp [indicator, h, not_le.mpr h]
    · simp [indicator, h, not_lt.mp h]
  rw [this, integral_indicator measurableSet_Iic]

lemma int_ind (P : Measure ℝ) [IsFiniteMeasure P] (t : ℝ) :
    ∫ θ, (Ioi t).indicator (fun _ => (1 : ℝ)) θ ∂P = (P (Ioi t)).toReal := by
  rw [integral_indicator measurableSet_Ioi, setIntegral_const, smul_eq_mul, mul_one,
    measureReal_def]

lemma int_θ_ind (P : Measure ℝ) (t : ℝ) :
    ∫ θ, θ * (Ioi t).indicator (fun _ => (1 : ℝ)) θ ∂P = ∫ θ in Ioi t, θ ∂P := by
  have : (fun θ => θ * (Ioi t).indicator (fun _ => (1 : ℝ)) θ) =
      (Ioi t).indicator (fun θ => θ) := by
    ext θ; by_cases h : t < θ <;> simp [indicator, h]
  rw [this, integral_indicator measurableSet_Ioi]

lemma A2_ind (P : Measure ℝ) (θlo θhi M B : ℝ) (hS : Standing P θlo θhi M B) (t : ℝ)
    (ht : M - B ≤ t) : A2 P M B ((Ioi t).indicator (fun _ => (1 : ℝ))) := by
  have := hS.prob
  have hi := integrable_id P θlo θhi M B hS
  unfold A2
  rw [int_ind, int_θ_ind]
  have h := setIntegral_mono_on (integrable_const (M - B)).integrableOn hi.integrableOn
    measurableSet_Ioi (fun θ (hθ : θ ∈ Ioi t) => by have : t < θ := hθ; linarith)
  rw [setIntegral_const, smul_eq_mul, measureReal_def] at h
  linarith

lemma A1_ind_iff (P : Measure ℝ) (θlo θhi M B : ℝ) (hS : Standing P θlo θhi M B) (t : ℝ) :
    A1 P M B ((Ioi t).indicator (fun _ => (1 : ℝ))) ↔ G P (M - B) t ≤ 0 := by
  have := hS.prob
  unfold A1
  rw [int_one_sub_ind, int_θ_one_sub_ind, G_eq P θlo θhi M B hS]
  constructor <;> intro h <;> linarith

lemma G_le_of_condMean (P : Measure ℝ) (θlo θhi M B : ℝ) (hS : Standing P θlo θhi M B) (k t : ℝ)
    (hk : 0 ≤ k) (h : condMean P id (Iic t) ≤ k) : G P k t ≤ 0 := by
  have := hS.prob
  rcases eq_zero_or_pos (P (Iic t)) with h0 | hpos
  · rw [G_eq P θlo θhi M B hS, setIntegral_measure_zero _ h0, h0]
    simp
  · exact (condMean_le_iff P θlo θhi M B hS k t hpos).mp h

end AccProp2Sol

open AccountingRules.Threshold AccProp2Sol

theorem solution (P : Measure ℝ) (θlo θhi M B : ℝ)
    (hS : Standing P θlo θhi M B)
    (hcond : condMean P id (Iic M) ≤ M - B) :
    let mstar : ℝ → ℝ := (Ioi M).indicator (fun _ => (1 : ℝ))
    A1 P M B mstar ∧ A2 P M B mstar ∧
      ∀ m : ℝ → ℝ, IsRule m → objective P M m ≤ objective P M mstar := by
  intro mstar
  have := hS.prob
  have hi := integrable_id P θlo θhi M B hS
  have hk : 0 ≤ M - B := by linarith [hS.B_le_M]
  refine ⟨(A1_ind_iff P θlo θhi M B hS M).mpr
      (G_le_of_condMean P θlo θhi M B hS (M - B) M hk hcond),
    A2_ind P θlo θhi M B hS M (by linarith [hS.B_nonneg]), fun m hm => ?_⟩
  have := obj_le P hi M (M - B) M 0 le_rfl (by ring) m hm
  simpa using this
