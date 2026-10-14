-- Prove2me | solution 1 for ActuarialValuation.cxRelativeRisk_add
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-12T19:27:55.826357+00:00
-- url     : https://prove2.me/submissions/405f456f-0ba4-44f4-ae6f-d3897ff7b6af

import Mathlib.Data.Real.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Definitions.Def_actuarial_cxRelativeRisk

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (beta z1 z2 : ℝ) : cxRelativeRisk beta (z1+z2)=cxRelativeRisk beta z1*cxRelativeRisk beta z2 := by
  unfold cxRelativeRisk
  rw [mul_add, Real.exp_add]
