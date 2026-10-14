-- Prove2me | solution 1 for ActuarialValuation.pen9PUC_equals_TUC_no_salary_growth
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-12T17:20:15.458005+00:00
-- url     : https://prove2.me/submissions/fab4a67a-ae45-4f87-bf88-ed7416bfb2c2

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_pen9PUC
import Definitions.Def_actuarial_pen9TUC

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (a salary f : ℝ) (n : ℕ) : pen9PUC a salary f n = pen9TUC a salary f n := by
  rfl
