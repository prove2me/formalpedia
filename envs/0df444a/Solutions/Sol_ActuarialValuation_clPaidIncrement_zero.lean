-- Prove2me | solution 1 for ActuarialValuation.clPaidIncrement_zero
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-12T11:11:40.185738+00:00
-- url     : https://prove2.me/submissions/53ecf507-3ffd-4f1c-a3f8-9c68ea895dd9

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_clPaidIncrement

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (p : ℕ → ℕ → ℝ) (i j : ℕ) (h : p i (j+1) = p i j) : clPaidIncrement p i j = 0 := by
  simp [clPaidIncrement, h]
