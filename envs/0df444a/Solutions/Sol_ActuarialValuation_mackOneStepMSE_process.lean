-- Prove2me | solution 1 for ActuarialValuation.mackOneStepMSE_process
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-12T11:39:23.912646+00:00
-- url     : https://prove2.me/submissions/145397b7-4d70-46e2-a322-e5002cfcc18f

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_mackOneStepMSE

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (p : ℝ) : mackOneStepMSE p 0 = p := by
  simp [mackOneStepMSE]
