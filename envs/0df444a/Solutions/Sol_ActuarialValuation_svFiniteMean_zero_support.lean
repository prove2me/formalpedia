-- Prove2me | solution 1 for ActuarialValuation.svFiniteMean_zero_support
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-11T08:44:47.600297+00:00
-- url     : https://prove2.me/submissions/73776eb2-4c33-4281-a94c-c658b2de9ad3

import Mathlib
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Definitions.Def_actuarial_svFiniteMassMean
open ActuarialValuation

theorem solution(p : ℕ → ℝ) : svFiniteMassMean p 0 = 0 := by
  simp [svFiniteMassMean]
