-- Prove2me | solution 1 for AccountingRules.Threshold.lagrangian_threshold_maximizer
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-26T02:40:52.301095+00:00
-- url     : https://prove2.me/submissions/f3d68cc0-8343-4928-ab80-afcf9b5309fe

import Mathlib
import Definitions.Def_AccountingRules_Threshold_Model

open MeasureTheory ProbabilityTheory Set

namespace Aux_AccRulesW31
open AccountingRules.Threshold

lemma ae_mem {P : Measure ℝ} {θlo θhi M B : ℝ} (hS : Standing P θlo θhi M B) :
    ∀ᵐ θ ∂P, θ ∈ Icc θlo θhi := mem_ae_iff.mpr hS.supp_sub

lemma int_id {P : Measure ℝ} {θlo θhi M B : ℝ} (hS : Standing P θlo θhi M B) :
    Integrable (fun θ : ℝ => θ) P := by
  haveI := hS.prob
  refine Integrable.of_bound measurable_id.aestronglyMeasurable (|θlo| + |θhi|) ?_
  filter_upwards [ae_mem hS] with θ hθ
  rw [Real.norm_eq_abs, abs_le]
  constructor <;> cases abs_nonneg θlo |>.lt_or_eq <;> cases abs_nonneg θhi |>.lt_or_eq <;>
    nlinarith [hθ.1, hθ.2, le_abs_self θlo, le_abs_self θhi, neg_abs_le θlo, neg_abs_le θhi]

lemma int_m {P : Measure ℝ} {θlo θhi M B : ℝ} (hS : Standing P θlo θhi M B) {m : ℝ → ℝ}
    (hm : IsRule m) : Integrable m P := by
  haveI := hS.prob
  refine Integrable.of_bound hm.1.aestronglyMeasurable 1 (Filter.Eventually.of_forall fun θ => ?_)
  rw [Real.norm_eq_abs, abs_le]; constructor <;> linarith [(hm.2 θ).1, (hm.2 θ).2]

lemma int_idm {P : Measure ℝ} {θlo θhi M B : ℝ} (hS : Standing P θlo θhi M B) {m : ℝ → ℝ}
    (hm : IsRule m) : Integrable (fun θ => θ * m θ) P := by
  haveI := hS.prob
  refine Integrable.of_bound (measurable_id.mul hm.1).aestronglyMeasurable (|θlo| + |θhi|) ?_
  filter_upwards [ae_mem hS] with θ hθ
  rw [Real.norm_eq_abs, abs_mul]
  have h1 : |m θ| ≤ 1 := by rw [abs_le]; constructor <;> linarith [(hm.2 θ).1, (hm.2 θ).2]
  have h2 : |θ| ≤ |θlo| + |θhi| := by
    rw [abs_le]; constructor <;>
    nlinarith [hθ.1, hθ.2, le_abs_self θlo, le_abs_self θhi, neg_abs_le θlo, neg_abs_le θhi,
      abs_nonneg θlo, abs_nonneg θhi]
  calc |θ| * |m θ| ≤ |θ| * 1 := mul_le_mul_of_nonneg_left h1 (abs_nonneg _)
    _ ≤ _ := by linarith

lemma int_aff {P : Measure ℝ} {θlo θhi M B : ℝ} (hS : Standing P θlo θhi M B) {m : ℝ → ℝ}
    (hm : IsRule m) (c : ℝ) : Integrable (fun θ => (θ - c) * m θ) P := by
  have : (fun θ => (θ - c) * m θ) = fun θ => θ * m θ - c * m θ := by funext θ; ring
  rw [this]
  exact (int_idm hS hm).sub ((int_m hS hm).const_mul c)

lemma ind_rule (c : ℝ) : IsRule ((Ioi c).indicator (fun _ => (1 : ℝ))) := by
  refine ⟨measurable_const.indicator measurableSet_Ioi, fun θ => ?_⟩
  by_cases h : θ ∈ Ioi c
  · rw [indicator_of_mem h]; norm_num
  · rw [indicator_of_notMem h]; norm_num

end Aux_AccRulesW31

open AccountingRules.Threshold in
theorem solution (P : Measure ℝ) (θlo θhi M B lam : ℝ)
    (hS : Standing P θlo θhi M B) (hlam : 0 ≤ lam) (m : ℝ → ℝ)
    (hm : IsRule m) :
    (∫ θ, (θ - M + lam / (1 + lam) * B) * m θ ∂P) ≤
      ∫ θ, (θ - M + lam / (1 + lam) * B) *
        (Ioi (M - lam / (1 + lam) * B)).indicator (fun _ => (1 : ℝ)) θ ∂P := by
  set c := M - lam / (1 + lam) * B with hc
  have e : ∀ θ : ℝ, θ - M + lam / (1 + lam) * B = θ - c := fun θ => by rw [hc]; ring
  simp only [e]
  refine integral_mono (Aux_AccRulesW31.int_aff hS hm c)
    (Aux_AccRulesW31.int_aff hS (Aux_AccRulesW31.ind_rule c) c) (fun θ => ?_)
  have h0 := (hm.2 θ).1
  have h1 := (hm.2 θ).2
  by_cases h : θ ∈ Ioi c
  · rw [indicator_of_mem h]
    have : 0 < θ - c := sub_pos.mpr h
    nlinarith
  · rw [indicator_of_notMem h]
    have : θ - c ≤ 0 := by simp only [mem_Ioi, not_lt] at h; linarith
    nlinarith
