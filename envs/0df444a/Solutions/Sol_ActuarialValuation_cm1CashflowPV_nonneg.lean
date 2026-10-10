-- Prove2me | solution 1 for ActuarialValuation.cm1CashflowPV_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-10T07:15:35.464912+00:00
-- url     : https://prove2.me/submissions/6f84bfc9-71a3-4ec7-ac9e-163a803611f4

import Mathlib.Tactic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_cm1Accum
import Definitions.Def_actuarial_cm1CashflowPV
import Definitions.Def_actuarial_cm1Discount
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (c : ℕ → ℝ) (n : ℕ) (i : ℝ) (hi : -1 < i) (hc : ∀ k ∈ Finset.range n, 0 ≤ c k) : 0 ≤ cm1CashflowPV c n i := by
  unfold cm1CashflowPV
  apply Finset.sum_nonneg
  intro k hk
  have hp : 0 < 1 + i := by linarith
  have hd : 0 ≤ cm1Discount i (k + 1) := by
    exact le_of_lt (show 0 < cm1Discount i (k + 1) by
      simp only [cm1Discount, cm1Accum]
      exact one_div_pos.mpr (pow_pos hp (k + 1)))
  exact mul_nonneg (hc k hk) hd
