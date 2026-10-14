-- Prove2me | solution 1 for ActuarialValuation.ulMinimumNext_low
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-12T14:17:41.358018+00:00
-- url     : https://prove2.me/submissions/482ee8e1-116f-42e6-8afe-40b09eea0a2a

import Mathlib.Data.Real.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_ulMinimumNext

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (earned mortality floor : ℝ) (h : earned≤floor) : ulMinimumNext earned mortality floor = (earned-mortality*floor)/(1-mortality) := by
  simp [ulMinimumNext, h]
