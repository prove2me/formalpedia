-- Prove2me | solution 1 for ActuarialValuation.pen9DCFund_one_year
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-12T14:09:56.766961+00:00
-- url     : https://prove2.me/submissions/6587f824-e8be-4c2f-a2d1-9378e06888f1

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_pen9DCFund

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (c : ℝ) (s : ℕ → ℝ) (j : ℝ) : pen9DCFund c s j 1 = c*s 0 := by
  simp [pen9DCFund, pen9AccumFactor]
