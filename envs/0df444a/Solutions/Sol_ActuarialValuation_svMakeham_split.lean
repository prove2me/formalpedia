-- Prove2me | solution 1 for ActuarialValuation.svMakeham_split
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-12T11:56:25.2044+00:00
-- url     : https://prove2.me/submissions/f3bbafa7-1e4e-4127-87b6-c8fda23b6dae

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Definitions.Def_actuarial_svMakehamCumulativeHazard
import Definitions.Def_actuarial_svGompertzCumulativeHazard

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (a b c t : ℝ) : svMakehamCumulativeHazard a b c t = a*t + svGompertzCumulativeHazard b c t := by
  rfl
