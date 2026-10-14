-- Prove2me | solution 1 for ActuarialValuation.cxSecondMoment_succ
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-12T14:48:30.319816+00:00
-- url     : https://prove2.me/submissions/341cda9b-9ffa-453f-87f0-f2abfa100409

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_cxSecondMoment

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (f : ℕ → ℝ) (n : ℕ) : cxSecondMoment f (n+1) = cxSecondMoment f n+(n:ℝ)^2*f n := by
  simp [cxSecondMoment, Finset.sum_range_succ]
