-- Prove2me | solution 1 for ActuarialValuation.srWaitingTotal_zero
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-11T11:35:14.632928+00:00
-- url     : https://prove2.me/submissions/1549f4f8-fa47-4b6c-b912-9f4ed9a48711

import Mathlib
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Definitions.Def_actuarial_srWaitingTotal
open ActuarialValuation

theorem solution{Ω : Type*} (W : ℕ → Ω → ℝ) (ω : Ω) : srWaitingTotal W 0 ω=0 := by
  simp [srWaitingTotal]
