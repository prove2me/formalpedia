-- Prove2me | solution 1 for ActuarialValuation.discreteStopLossTail_above_bound
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-09T16:21:20.072228+00:00
-- url     : https://prove2.me/submissions/310a3009-3ebb-4e68-9dd8-95878b9c1f94

import Mathlib
import Definitions.Def_actuarial_discreteStopLossTail

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution
  (w : ℕ → ℝ) (bound deductible : ℕ)
  (h : bound ≤ deductible) :
  discreteStopLossTail w bound deductible = 0 := by
  unfold discreteStopLossTail
  apply Finset.sum_eq_zero
  intro s hs
  have hsb : s ≤ bound := Nat.lt_succ_iff.mp (Finset.mem_range.mp hs)
  simp [Nat.not_lt.mpr (le_trans hsb h)]
