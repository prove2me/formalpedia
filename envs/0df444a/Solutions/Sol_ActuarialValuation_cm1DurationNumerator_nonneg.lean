-- Prove2me | solution 1 for ActuarialValuation.cm1DurationNumerator_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-10T07:32:34.538654+00:00
-- url     : https://prove2.me/submissions/2fdc086c-39f5-42f6-a31b-7d90680eb185

import Mathlib.Tactic
import Definitions.Def_actuarial_cm1Accum
import Definitions.Def_actuarial_cm1Discount
import Definitions.Def_actuarial_cm1DurationNumerator
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (c : ℕ → ℝ) (n : ℕ) (i : ℝ)
    (hi : -1 < i) (hc : ∀ k ∈ Finset.range n, 0 ≤ c k) :
    0 ≤ cm1DurationNumerator c n i := by
  unfold cm1DurationNumerator
  apply Finset.sum_nonneg
  intro k hk
  have hp : 0 < 1 + i := by linarith
  have hd : 0 ≤ cm1Discount i (k + 1) := by
    change 0 ≤ 1 / (1 + i) ^ (k + 1)
    exact le_of_lt (one_div_pos.mpr (pow_pos hp _))
  have hkpos : (0:ℝ) ≤ ((k + 1 : ℕ) : ℝ) := by positivity
  exact mul_nonneg (mul_nonneg hkpos (hc k hk)) hd
