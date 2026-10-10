-- Prove2me | solution 1 for ActuarialValuation.compoundPoissonAggregatePMF_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-09T15:18:16.279612+00:00
-- url     : https://prove2.me/submissions/0508221c-c6db-4dcd-b5ab-4bd1e99598f7

import Mathlib
import Definitions.Def_actuarial_compoundPoissonAggregatePMF
import Definitions.Def_actuarial_compoundPoissonCountWeight
import Definitions.Def_actuarial_compoundPoissonSeverityPower
open ActuarialValuation

theorem solution (rate : ℝ) (f : ℕ → ℝ) (s : ℕ)
  (hr : 0 ≤ rate) (hf : ∀ k, 0 ≤ f k) :
  0 ≤ compoundPoissonAggregatePMF rate f s := by
  have hpow : ∀ m t, 0 ≤ compoundPoissonSeverityPower f m t := by
    intro m
    induction m with
    | zero => intro t; simp only [compoundPoissonSeverityPower]; split_ifs <;> norm_num
    | succ m ih =>
      intro t
      simp only [compoundPoissonSeverityPower, compoundPoissonConvolution]
      exact Finset.sum_nonneg fun j _ => mul_nonneg (hf j) (ih _)
  unfold compoundPoissonAggregatePMF
  refine Finset.sum_nonneg fun m _ => mul_nonneg ?_ (hpow m s)
  unfold compoundPoissonCountWeight
  positivity
