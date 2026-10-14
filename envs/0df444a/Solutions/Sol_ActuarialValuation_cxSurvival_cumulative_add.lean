-- Prove2me | solution 1 for ActuarialValuation.cxSurvival_cumulative_add
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-12T19:42:30.058859+00:00
-- url     : https://prove2.me/submissions/186b54b9-3b47-45d7-b897-dcb5913ba8e8

import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Ring
import Mathlib.Data.Fintype.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Definitions.Def_actuarial_cxSurvival

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (H1 H2 beta z : ℝ) : cxSurvival (H1+H2) beta z=cxSurvival H1 beta z*cxSurvival H2 beta z := by
  unfold cxSurvival
  have h : -((H1+H2)*cxRelativeRisk beta z) =
      -(H1*cxRelativeRisk beta z) + -(H2*cxRelativeRisk beta z) := by
    ring
  rw [h, Real.exp_add]
