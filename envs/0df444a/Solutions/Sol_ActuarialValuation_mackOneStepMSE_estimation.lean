-- Prove2me | solution 1 for ActuarialValuation.mackOneStepMSE_estimation
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-12T11:39:35.552858+00:00
-- url     : https://prove2.me/submissions/b43948d8-9b77-4565-9ece-b3c73ec3ee54

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_mackOneStepMSE

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (e : ℝ) : mackOneStepMSE 0 e = e := by
  simp [mackOneStepMSE]
