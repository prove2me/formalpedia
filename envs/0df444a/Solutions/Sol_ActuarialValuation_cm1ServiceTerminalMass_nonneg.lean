-- Prove2me | solution 1 for ActuarialValuation.cm1ServiceTerminalMass_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-10T07:26:30.912361+00:00
-- url     : https://prove2.me/submissions/1ad95b8f-0bdd-41a4-840f-ce4a6ef623a5

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_cm1ServiceTerminalMass
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (l : ℕ → ℝ) (N : ℕ) (h0 : 0 < l 0) (hN : 0 ≤ l N) : 0 ≤ cm1ServiceTerminalMass l N := by
  unfold cm1ServiceTerminalMass
  exact div_nonneg hN (le_of_lt h0)
