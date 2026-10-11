-- Prove2me | solution 1 for ActuarialValuation.svTail_at_end
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-11T08:08:23.156123+00:00
-- url     : https://prove2.me/submissions/37257053-24c9-494a-b753-7b63f8b90847

import Mathlib
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Definitions.Def_actuarial_svFiniteTailMass
open ActuarialValuation

theorem solution(p : ℕ → ℝ) (n : ℕ) : svFiniteTailMass p n n = 0 := by
  simp [svFiniteTailMass]
