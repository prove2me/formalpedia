-- Prove2me | solution 1 for ActuarialValuation.cm1ServiceTotalExits_add_last
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-10T07:21:14.004871+00:00
-- url     : https://prove2.me/submissions/78cc06a6-adba-4b8c-9ab5-584e0ed3483d

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_cm1ServiceAnnualExit
import Definitions.Def_actuarial_cm1ServiceTotalExits
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (d : ℕ → ℕ → ℝ) (N m : ℕ) : cm1ServiceTotalExits d (N+1) m = cm1ServiceTotalExits d N m + cm1ServiceAnnualExit d N m := by
  simp [cm1ServiceTotalExits, Finset.sum_range_succ]
