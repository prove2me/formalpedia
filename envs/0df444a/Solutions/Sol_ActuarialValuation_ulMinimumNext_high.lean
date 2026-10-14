-- Prove2me | solution 1 for ActuarialValuation.ulMinimumNext_high
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-12T14:17:28.213193+00:00
-- url     : https://prove2.me/submissions/baaa77b8-c2a3-4179-9f33-2f232cd65f7a

import Mathlib.Data.Real.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_ulMinimumNext

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (earned mortality floor : ℝ) (h : floor<earned) : ulMinimumNext earned mortality floor = earned := by
  simp [ulMinimumNext, not_le.mpr h]
