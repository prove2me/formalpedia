-- Prove2me | solution 1 for ActuarialValuation.pensionEarlyComparator_zero_death
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-10T07:11:51.066053+00:00
-- url     : https://prove2.me/submissions/2f09be82-f0b5-4f00-aabd-a2fb135010ff

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_pensionEarlyComparator

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (p v A : ℝ) :
  pensionEarlyComparator 0 p v A = p * v * A := by
  simp [pensionEarlyComparator]
