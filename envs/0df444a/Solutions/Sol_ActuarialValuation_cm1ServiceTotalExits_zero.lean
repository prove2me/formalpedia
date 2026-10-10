-- Prove2me | solution 1 for ActuarialValuation.cm1ServiceTotalExits_zero
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-10T07:21:07.025113+00:00
-- url     : https://prove2.me/submissions/5b784dca-655c-4590-9a65-b7470b2b8caa

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
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

theorem solution (d : ℕ → ℕ → ℝ) (m : ℕ) : cm1ServiceTotalExits d 0 m = 0 := by
  simp [cm1ServiceTotalExits]
