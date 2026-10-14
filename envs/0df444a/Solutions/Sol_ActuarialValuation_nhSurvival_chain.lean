-- Prove2me | solution 1 for ActuarialValuation.nhSurvival_chain
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-12T17:32:58.70315+00:00
-- url     : https://prove2.me/submissions/0a209675-a7ed-4669-a9bc-5e64327486f4

import Mathlib.Data.Real.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Definitions.Def_actuarial_nhSurvival

import Mathlib.Tactic.Ring

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (a b s u t : ℝ) : nhSurvival a b s t=nhSurvival a b s u*nhSurvival a b u t := by
  unfold nhSurvival
  rw [← Real.exp_add]
  congr 1
  ring
