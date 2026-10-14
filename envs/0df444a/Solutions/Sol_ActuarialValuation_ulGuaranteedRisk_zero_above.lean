-- Prove2me | solution 1 for ActuarialValuation.ulGuaranteedRisk_zero_above
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-12T14:15:34.989474+00:00
-- url     : https://prove2.me/submissions/14c4d6f4-f435-460b-b86b-ac109a2b4c19

import Mathlib.Data.Real.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_ulGuaranteedNetRisk

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (account floor : ℝ) (h : floor≤account) : ulGuaranteedNetRisk account floor = 0 := by
  change max (floor - account) 0 = 0
  exact max_eq_right (sub_nonpos.mpr h)
