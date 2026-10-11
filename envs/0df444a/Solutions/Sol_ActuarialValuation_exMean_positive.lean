-- Prove2me | solution 1 for ActuarialValuation.exMean_positive
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-11T11:19:04.492036+00:00
-- url     : https://prove2.me/submissions/f5aa2867-73b1-4ba4-acbc-310c1b3cf6e6

import Mathlib
import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Definitions.Def_actuarial_exMean
open ActuarialValuation

theorem solution(xi sigma : ℝ) (hxi : xi < 1) (hs : 0 < sigma) : 0 < exMean xi sigma := by
  unfold exMean
  exact div_pos hs (by linarith)
