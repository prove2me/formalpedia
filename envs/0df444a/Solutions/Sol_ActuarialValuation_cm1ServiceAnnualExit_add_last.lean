-- Prove2me | solution 1 for ActuarialValuation.cm1ServiceAnnualExit_add_last
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-10T07:20:34.754383+00:00
-- url     : https://prove2.me/submissions/6365e5a7-04e1-4790-b646-89fae07605c0

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_cm1ServiceAnnualExit
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (d : ℕ → ℕ → ℝ) (t m : ℕ) : cm1ServiceAnnualExit d t (m+1) = cm1ServiceAnnualExit d t m + d t m := by
  simp [cm1ServiceAnnualExit, Finset.sum_range_succ]
