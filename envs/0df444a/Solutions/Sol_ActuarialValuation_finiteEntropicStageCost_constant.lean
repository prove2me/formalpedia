-- Prove2me | solution 1 for ActuarialValuation.finiteEntropicStageCost_constant
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-09T09:56:07.973626+00:00
-- url     : https://prove2.me/submissions/e9935aa4-b3c3-4179-afee-6136bab052f4

import Mathlib
import Definitions.Def_actuarial_finiteEntropicStageCost

open ActuarialValuation

theorem solution {S A : Type*} [Fintype S]
    (P : S → A → S → ℝ) (cost : S → A → S → ℝ)
    (beta gamma : ℝ) (next : S → ℝ) (s : S) (a : A) (c u : ℝ)
    (hsum : (∑ t : S, P s a t) = 1)
    (hc : ∀ t, cost s a t = c)
    (hu : ∀ t, next t = u)
    (hgamma : gamma ≠ 0) :
    finiteEntropicStageCost P cost beta gamma next s a = c + beta * u := by
  unfold finiteEntropicStageCost finiteEntropicTransitionMoment
  have hmom :
      (∑ t : S, P s a t * Real.exp (gamma * (cost s a t + beta * next t))) =
        Real.exp (gamma * (c + beta * u)) := by
    simp only [hc, hu, mul_comm (P s a _)]
    rw [← Finset.mul_sum, hsum, mul_one]
  rw [hmom, Real.log_exp, mul_div_cancel_left₀ _ hgamma]
