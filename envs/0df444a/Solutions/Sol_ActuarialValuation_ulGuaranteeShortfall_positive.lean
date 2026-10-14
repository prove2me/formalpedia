-- Prove2me | solution 1 for ActuarialValuation.ulGuaranteeShortfall_positive
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-12T14:17:15.11084+00:00
-- url     : https://prove2.me/submissions/97cb1da4-2768-428b-8171-d31f098597fa

import Mathlib.Data.Real.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_ulGuaranteeShortfall

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (account floor : ℝ) (h : account<floor) : ulGuaranteeShortfall account floor = floor-account := by
  change max (floor - account) 0 = floor - account
  exact max_eq_left (le_of_lt (sub_pos.mpr h))
