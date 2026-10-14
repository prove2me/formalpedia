-- Prove2me | solution 1 for ActuarialValuation.whSecondDifference_const
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-13T06:27:25.942188+00:00
-- url     : https://prove2.me/submissions/789f1e64-5c51-4903-a457-ac1844be0267

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_whSecondDifference

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (value : ℝ) (i : ℕ) : whSecondDifference (fun _ => value) i = 0 := by
  simp [whSecondDifference, whFirstDifference]
