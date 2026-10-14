-- Prove2me | solution 1 for ActuarialValuation.pen9ReversionaryAnnuity_zero
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-12T14:01:22.226724+00:00
-- url     : https://prove2.me/submissions/a5e1e34f-526d-4aec-a293-60d555c5556d

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_pen9ReversionaryAnnuity

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (member spouse : ℝ) : pen9ReversionaryAnnuity member spouse 0 = member := by
  simp [pen9ReversionaryAnnuity]
