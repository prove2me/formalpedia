-- Prove2me | solution 1 for ActuarialValuation.pen9FinalSalaryPension_succ
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-12T17:21:45.255843+00:00
-- url     : https://prove2.me/submissions/23d58480-20ba-4f8b-b352-36a4140000f2

import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Ring
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_pen9FinalSalaryPension

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (a s : ℝ) (n : ℕ) : pen9FinalSalaryPension a s (n+1) = pen9FinalSalaryPension a s n + a*s := by
  simp only [pen9FinalSalaryPension, Nat.cast_add, Nat.cast_one]
  ring
