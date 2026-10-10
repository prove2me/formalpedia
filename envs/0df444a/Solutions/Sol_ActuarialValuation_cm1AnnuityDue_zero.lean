-- Prove2me | solution 1 for ActuarialValuation.cm1AnnuityDue_zero
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-10T07:14:39.779991+00:00
-- url     : https://prove2.me/submissions/1baf07e7-e16b-478b-a69a-04d71d65a54a

import Mathlib.Tactic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_cm1AnnuityDue
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (i : ℝ) : cm1AnnuityDue i 0 = 0 := by
  simp [cm1AnnuityDue]
