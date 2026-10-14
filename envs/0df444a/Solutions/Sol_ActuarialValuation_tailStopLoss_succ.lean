-- Prove2me | solution 1 for ActuarialValuation.tailStopLoss_succ
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-12T11:23:32.184357+00:00
-- url     : https://prove2.me/submissions/7c6d64a5-d85c-4636-8618-e197de747db2

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_tailExcess
import Definitions.Def_actuarial_tailStopLoss

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (p : ℕ → ℝ) (n : ℕ) (t : ℝ) :
    tailStopLoss p (n+1) t
      = tailStopLoss p n t + tailExcess ((n+1 : ℕ) : ℝ) t * p (n+1) := by
  unfold tailStopLoss
  exact Finset.sum_range_succ _ _
