-- Prove2me | solution 1 for ActuarialValuation.cm1Accum_zero
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-10T07:11:24.76115+00:00
-- url     : https://prove2.me/submissions/1af0f298-5f85-4ab1-86c7-5a9ee0d8668c

import Mathlib.Tactic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_cm1Accum
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (i : ℝ) : cm1Accum i 0 = 1 := by
  simp [cm1Accum]
