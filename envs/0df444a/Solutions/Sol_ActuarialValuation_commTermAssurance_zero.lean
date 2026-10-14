-- Prove2me | solution 1 for ActuarialValuation.commTermAssurance_zero
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-12T11:14:04.199454+00:00
-- url     : https://prove2.me/submissions/46cfc31f-41ff-4194-a86a-f2c54bb251f7

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_commTermAssurance

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (l : ℕ → ℝ) (v : ℝ) (x : ℕ) : commTermAssurance l v x 0 = 0 := by
  simp [commTermAssurance, commDeathSum]
