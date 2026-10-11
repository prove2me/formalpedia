-- Prove2me | solution 1 for ActuarialValuation.lcRateRatio_positive
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-11T07:00:42.545988+00:00
-- url     : https://prove2.me/submissions/2a719311-e523-4fff-a94f-9f3513b4e327

import Mathlib
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Definitions.Def_actuarial_lcRateRatio
open ActuarialValuation

theorem solution(b k1 k2 : ℝ) : 0 < lcRateRatio b k1 k2 := by
  unfold lcRateRatio
  exact Real.exp_pos _
