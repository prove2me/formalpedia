-- Prove2me | solution 1 for ActuarialValuation.cm1ZeroReserveFloor_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-10T07:21:26.948208+00:00
-- url     : https://prove2.me/submissions/4b5ca70e-c48a-49d4-87ff-395e0ff88c9e

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_cm1ZeroReserveFloor

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (c s g R : ℝ) : 0 ≤ cm1ZeroReserveFloor c s g R := by
  unfold cm1ZeroReserveFloor
  exact le_max_left _ _
