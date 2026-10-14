-- Prove2me | solution 1 for ActuarialValuation.tailStopLoss_zero_threshold
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-12T11:28:45.19455+00:00
-- url     : https://prove2.me/submissions/17ab3af5-41b2-4027-86fe-250be0e6d003

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Definitions.Def_actuarial_tailLossMean
import Definitions.Def_actuarial_tailStopLoss

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (p : ℕ → ℝ) (n : ℕ) :
    tailStopLoss p n 0 = tailLossMean p n := by
  unfold tailStopLoss tailLossMean
  apply Finset.sum_congr rfl
  intro k hk
  congr 1
  unfold tailExcess
  rw [sub_zero]
  exact max_eq_left (Nat.cast_nonneg k)
