-- Prove2me | solution 1 for ActuarialValuation.ulGuaranteedRisk_below
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-12T14:15:46.789472+00:00
-- url     : https://prove2.me/submissions/91987646-cd91-417a-97fa-27a06290b15e

import Mathlib.Data.Real.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_ulGuaranteedNetRisk

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (account floor : ℝ) (h : account≤floor) : ulGuaranteedNetRisk account floor = floor-account := by
  change max (floor - account) 0 = floor - account
  exact max_eq_left (sub_nonneg.mpr h)
