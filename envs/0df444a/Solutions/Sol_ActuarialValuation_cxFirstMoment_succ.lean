-- Prove2me | solution 1 for ActuarialValuation.cxFirstMoment_succ
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-12T14:47:09.992322+00:00
-- url     : https://prove2.me/submissions/5b4b1218-2d28-4bd9-8182-67dab5f8a1f9

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_cxFirstMoment

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (f : ℕ → ℝ) (n : ℕ) : cxFirstMoment f (n+1) = cxFirstMoment f n + (n:ℝ)*f n := by
  simp [cxFirstMoment, Finset.sum_range_succ]
