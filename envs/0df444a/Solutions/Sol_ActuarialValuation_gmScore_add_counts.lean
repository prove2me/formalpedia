-- Prove2me | solution 1 for ActuarialValuation.gmScore_add_counts
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-12T20:25:34.36763+00:00
-- url     : https://prove2.me/submissions/09cebf8c-645d-4e44-a329-b94b992ae8e9

import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic.Ring
import Definitions.Def_actuarial_gmScore

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (x y exposure eta : ℝ) :
    gmScore (x + y) exposure eta = gmScore x exposure eta + y := by
  unfold gmScore
  ring
