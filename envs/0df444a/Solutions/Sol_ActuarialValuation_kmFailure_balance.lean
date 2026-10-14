-- Prove2me | solution 1 for ActuarialValuation.kmFailure_balance
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-12T11:10:51.826694+00:00
-- url     : https://prove2.me/submissions/f00c7425-b7db-4705-85ed-dd65adceb4c5

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_kmSurvival
import Definitions.Def_actuarial_kmFailure

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (r d : ℕ → ℝ) (n : ℕ) : kmSurvival r d n + kmFailure r d n = 1 := by
  unfold kmFailure
  rw [add_comm]
  exact sub_add_cancel _ _
