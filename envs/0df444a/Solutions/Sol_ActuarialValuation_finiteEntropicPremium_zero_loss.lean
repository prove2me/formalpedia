-- Prove2me | solution 1 for ActuarialValuation.finiteEntropicPremium_zero_loss
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-09T09:51:43.962984+00:00
-- url     : https://prove2.me/submissions/6c63e60b-4125-474b-83da-8ce0ff63a441

import Mathlib
import Definitions.Def_actuarial_finiteEntropicPremium
open MeasureTheory
open ActuarialValuation

theorem solution {Ω : Type*} [Fintype Ω] (w : Ω → ℝ) (gamma : ℝ)
    (hsum : (∑ ω : Ω, w ω) = 1) :
    finiteEntropicPremium w (fun _ => 0) gamma = 0 := by
  unfold finiteEntropicPremium finiteExponentialMoment
  simp only [mul_zero, Real.exp_zero, mul_one]
  rw [hsum, Real.log_one, zero_div]
