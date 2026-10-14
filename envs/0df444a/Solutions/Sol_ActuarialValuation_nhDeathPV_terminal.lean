-- Prove2me | solution 1 for ActuarialValuation.nhDeathPV_terminal
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-12T17:36:16.212516+00:00
-- url     : https://prove2.me/submissions/4176338d-c4db-47dc-9395-4708dea634d3

import Mathlib.Data.Real.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Definitions.Def_actuarial_nhDeathPV

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (a b p δ B1 B2 T : ℝ) : nhDeathPV a b p δ B1 B2 T T=0 := by
  simp [nhDeathPV]
