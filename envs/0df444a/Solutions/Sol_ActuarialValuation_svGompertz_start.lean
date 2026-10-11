-- Prove2me | solution 1 for ActuarialValuation.svGompertz_start
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-11T08:52:15.173559+00:00
-- url     : https://prove2.me/submissions/4bc3ec2b-113b-42c5-bfb7-b95ac0b8d187

import Mathlib
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Definitions.Def_actuarial_svGompertzCumulativeHazard
open ActuarialValuation

theorem solution(b c : ℝ) : svGompertzCumulativeHazard b c 0 = 0 := by
  simp [svGompertzCumulativeHazard]
