-- Prove2me | solution 1 for ActuarialValuation.nhExit_partition
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-12T17:34:41.426599+00:00
-- url     : https://prove2.me/submissions/c48c6c68-3b09-4c47-9214-8e37942a9138

import Mathlib.Data.Real.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Definitions.Def_actuarial_nhSurvival
import Definitions.Def_actuarial_nhExitOne
import Definitions.Def_actuarial_nhExitTwo

import Mathlib.Tactic.Ring

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (a b p s t : ℝ) : nhSurvival a b s t+nhExitOne a b p s t+nhExitTwo a b p s t=1 := by
  unfold nhExitOne nhExitTwo
  ring
