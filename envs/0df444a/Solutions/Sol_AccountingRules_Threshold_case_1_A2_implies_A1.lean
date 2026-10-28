-- Prove2me | solution 1 for AccountingRules.Threshold.case_1_A2_implies_A1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-26T02:37:25.681711+00:00
-- url     : https://prove2.me/submissions/39c490d8-de88-4dc4-ae26-f29eae8ebac3

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

lemma expand1 {P : Measure ℝ} {θlo θhi M B : ℝ} (hS : Standing P θlo θhi M B) {m : ℝ → ℝ}
    (hm : IsRule m) :
    ∫ θ, θ * (1 - m θ) ∂P = (∫ θ, θ ∂P) - ∫ θ, θ * m θ ∂P := by
  have : (fun θ => θ * (1 - m θ)) = fun θ => θ - θ * m θ := by funext θ; ring
  rw [this, integral_sub (int_id hS) (int_idm hS hm)]

lemma expand2 {P : Measure ℝ} {θlo θhi M B : ℝ} (hS : Standing P θlo θhi M B) {m : ℝ → ℝ}
    (hm : IsRule m) :
    ∫ θ, (1 - m θ) ∂P = 1 - ∫ θ, m θ ∂P := by
  haveI := hS.prob
  rw [integral_sub (integrable_const 1) (int_m hS hm)]
  simp

end Aux_AccRulesW31

open AccountingRules.Threshold in
theorem solution (P : Measure ℝ) (θlo θhi M B : ℝ)
    (hS : Standing P θlo θhi M B) (hmean : (∫ θ, θ ∂P) ≤ M - B)
    (m : ℝ → ℝ) (hm : IsRule m) (hA2 : A2 P M B m) : A1 P M B m := by
  unfold A1
  unfold A2 at hA2
  rw [Aux_AccRulesW31.expand1 hS hm, Aux_AccRulesW31.expand2 hS hm]
  nlinarith
