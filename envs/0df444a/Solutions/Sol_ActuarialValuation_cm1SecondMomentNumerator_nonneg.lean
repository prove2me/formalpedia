-- Prove2me | solution 1 for ActuarialValuation.cm1SecondMomentNumerator_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-10T07:36:00.171991+00:00
-- url     : https://prove2.me/submissions/67b2293e-79fb-43d1-bb31-89c3123cd25d

import Mathlib.Tactic
import Definitions.Def_actuarial_cm1Accum
import Definitions.Def_actuarial_cm1Discount
import Definitions.Def_actuarial_cm1SecondMomentNumerator
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (c : ℕ → ℝ) (n : ℕ) (i : ℝ)
    (hi : -1 < i) (hc : ∀ k ∈ Finset.range n, 0 ≤ c k) :
    0 ≤ cm1SecondMomentNumerator c n i := by
  unfold cm1SecondMomentNumerator
  apply Finset.sum_nonneg
  intro k hk
  have hp : 0 < 1 + i := by linarith
  have hd : 0 ≤ cm1Discount i (k + 1) := by
    change 0 ≤ 1 / (1 + i) ^ (k + 1)
    exact le_of_lt (one_div_pos.mpr (pow_pos hp _))
  have hkpos : (0:ℝ) ≤ (((k + 1 : ℕ) : ℝ) * ((k + 2 : ℕ) : ℝ)) := by positivity
  exact mul_nonneg (mul_nonneg hkpos (hc k hk)) hd

