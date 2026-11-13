-- Prove2me | Definitions.Def_ProbabilityTheory_chapter_08_thm_8_6_support
-- name    : ProbabilityTheory_chapter_08_thm_8_6_support
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-12T08:04:24.096316+00:00
-- url     : https://prove2.me/theorems/a5835fe4-6aa5-4d7b-ae94-bc434dde1b6b
-- title:
--   Chapter ?, generated supplement: supporting Lean bundle F000
-- statement:
--   Supporting Lean declarations for Chapter ?, source module `generated supplement`: `thm_8_6_discrete_pmf`, `thm_8_6_discrete`, `thm_8_6_continuous`. The mathematical interpretation of this bundle needs review.
-- source:
--   Supplemental source module in importer v37; upstream repository https://github.com/wkshum/ProbabilityTheory/tree/e6387d4fd8005d627d2aec40d10f039ddb4e4b40

import Mathlib.Tactic
import Definitions.Def_ProbabilityTheory_chapter_08_def_8_5_F000
import Definitions.Def_ProbabilityTheory_common_support_tv_distance_core

open MeasureTheory Set
open TVCore

noncomputable section

theorem thm_8_6_discrete_pmf (p q : PMF ℕ) :
    totalVariationDistance p.toMeasure q.toMeasure
      = (1 / 2 : ℝ) * ∑' n, |(p n).toReal - (q n).toReal| := by
  simpa [TVCore.pmfDiff, TVCore.pmfReal] using
    TVCore.discrete_totalVariationDistance_eq_half_tsum_abs p q

theorem thm_8_6_discrete (P Q : Measure ℕ)
    [IsProbabilityMeasure P] [IsProbabilityMeasure Q] :
    totalVariationDistance P Q
      = (1 / 2 : ℝ) * ∑' n, |P.real {n} - Q.real {n}| := by
  calc
    totalVariationDistance P Q
        = totalVariationDistance P.toPMF.toMeasure Q.toPMF.toMeasure := by
            rw [Measure.toPMF_toMeasure, Measure.toPMF_toMeasure]
    _ = (1 / 2 : ℝ) * ∑' n, |((P.toPMF n).toReal - (Q.toPMF n).toReal)| := by
            exact thm_8_6_discrete_pmf P.toPMF Q.toPMF
    _ = (1 / 2 : ℝ) * ∑' n, |P.real {n} - Q.real {n}| := by
            simp [Measure.toPMF_apply, Measure.real_def]

theorem thm_8_6_continuous
    {f g : ℝ → ℝ} (hf_meas : Measurable f) (hg_meas : Measurable g)
    (hf_int : Integrable f volume) (hg_int : Integrable g volume)
    (hf_nonneg : ∀ x, 0 ≤ f x) (hg_nonneg : ∀ x, 0 ≤ g x)
    (hf_prob : ∫ x, f x = 1) (hg_prob : ∫ x, g x = 1) :
    totalVariationDistance (densityMeasure f) (densityMeasure g)
      = (1 / 2 : ℝ) * ∫ x, |densityDiff f g x| := by
  exact TVCore.continuous_totalVariationDistance_eq_half_integral_abs
    hf_meas hg_meas hf_int hg_int hf_nonneg hg_nonneg hf_prob hg_prob


