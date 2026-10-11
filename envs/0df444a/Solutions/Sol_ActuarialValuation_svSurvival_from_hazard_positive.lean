-- Prove2me | solution 1 for ActuarialValuation.svSurvival_from_hazard_positive
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-11T11:21:00.57829+00:00
-- url     : https://prove2.me/submissions/8fa0d5ac-3a5e-4682-9b17-5642ab4296a4

import Mathlib
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Definitions.Def_actuarial_svSurvivalFromCumulativeHazard
open ActuarialValuation

theorem solution(h : ℝ) : 0 < svSurvivalFromCumulativeHazard h := by
  unfold svSurvivalFromCumulativeHazard
  exact Real.exp_pos _
