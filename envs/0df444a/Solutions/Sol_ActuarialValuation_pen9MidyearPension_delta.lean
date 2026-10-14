-- Prove2me | solution 1 for ActuarialValuation.pen9MidyearPension_delta
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-12T17:27:37.459111+00:00
-- url     : https://prove2.me/submissions/2ffd6094-c4c7-4faa-a63a-ec9f34dece48

import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Ring
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_pen9FinalSalaryPension
import Definitions.Def_actuarial_pen9MidyearPension

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (a s : ℝ) (n : ℕ) : pen9MidyearPension a s n - pen9FinalSalaryPension a s n = a*s/2 := by
  unfold pen9MidyearPension pen9FinalSalaryPension
  ring
