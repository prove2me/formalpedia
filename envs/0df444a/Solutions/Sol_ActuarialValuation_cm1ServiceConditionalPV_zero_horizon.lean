-- Prove2me | solution 1 for ActuarialValuation.cm1ServiceConditionalPV_zero_horizon
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-10T07:27:01.419409+00:00
-- url     : https://prove2.me/submissions/b9219573-bc3e-4efb-9d48-4e00eb6e7e73

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_cm1ServiceConditionalPV
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (v : ℕ → ℝ) (b d : ℕ → ℕ → ℝ) (l : ℕ → ℝ) (m : ℕ) : cm1ServiceConditionalPV v b d l 0 m = 0 := by
  simp [cm1ServiceConditionalPV]
