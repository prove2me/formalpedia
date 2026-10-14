-- Prove2me | solution 1 for ActuarialValuation.pen9ExitPV_decompose
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-12T14:21:44.182009+00:00
-- url     : https://prove2.me/submissions/1f979018-0963-4344-99f6-a7dde361e5e5

import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Ring
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_pen9ExitPV

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (v w d i r bw bd bi br : ℝ) : pen9ExitPV v w d i r bw bd bi br = v*w*bw + v*d*bd + v*i*bi + v*r*br := by
  unfold pen9ExitPV
  ring
