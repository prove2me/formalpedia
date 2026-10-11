-- Prove2me | solution 1 for ActuarialValuation.svGompertz_hazard_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-11T11:21:47.607707+00:00
-- url     : https://prove2.me/submissions/91abcd2a-67e7-4b3d-b5d3-0b2c4f820df6

import Mathlib
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Definitions.Def_actuarial_svGompertzHazard
open ActuarialValuation

theorem solution(b c t : ℝ) (hb : 0 ≤ b) : 0 ≤ svGompertzHazard b c t := by
  unfold svGompertzHazard
  exact mul_nonneg hb (Real.exp_pos _).le
