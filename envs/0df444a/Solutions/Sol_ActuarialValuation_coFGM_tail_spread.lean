-- Prove2me | solution 1 for ActuarialValuation.coFGM_tail_spread
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-12T19:27:38.496035+00:00
-- url     : https://prove2.me/submissions/95d672b5-5361-4c88-ad7e-9b7bdebac8bf

import Mathlib.Tactic.Ring
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.Order.Group.MinMax
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_coFGM
import Definitions.Def_actuarial_coThresholdSpread

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (theta u v : ℝ) : coThresholdSpread (coFGM theta) u v=theta*u*v*(1-u)*(1-v) := by
  unfold coThresholdSpread coTailJoint coFGM coInd
  ring
