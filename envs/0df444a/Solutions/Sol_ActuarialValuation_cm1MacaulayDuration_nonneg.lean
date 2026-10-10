-- Prove2me | solution 1 for ActuarialValuation.cm1MacaulayDuration_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-10T07:15:55.907486+00:00
-- url     : https://prove2.me/submissions/e17878f9-98b9-4ae0-b4a1-872aecb9d2e5

import Mathlib.Tactic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_cm1Accum
import Definitions.Def_actuarial_cm1CashflowPV
import Definitions.Def_actuarial_cm1Discount
import Definitions.Def_actuarial_cm1DurationNumerator
import Definitions.Def_actuarial_cm1MacaulayDuration
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (c : ℕ → ℝ) (n : ℕ) (i : ℝ) (hi : -1 < i) (hc : ∀ k ∈ Finset.range n, 0 ≤ c k) (hV : 0 < cm1CashflowPV c n i) : 0 ≤ cm1MacaulayDuration c n i := by
  unfold cm1MacaulayDuration cm1DurationNumerator
  apply div_nonneg
  · apply Finset.sum_nonneg
    intro k hk
    have hp : 0 < 1 + i := by linarith
    have hd : 0 ≤ cm1Discount i (k+1) := by
      exact le_of_lt (show 0 < cm1Discount i (k+1) by
        simp only [cm1Discount, cm1Accum]
        exact one_div_pos.mpr (pow_pos hp (k+1)))
    exact mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (hc k hk)) hd
  · exact le_of_lt hV
