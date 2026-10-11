-- Prove2me | solution 1 for ActuarialValuation.srClaimTotal_zero
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-11T10:59:20.010988+00:00
-- url     : https://prove2.me/submissions/1ac97c76-4c5a-436e-8b6e-4787d8f4acd7

import Mathlib
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Definitions.Def_actuarial_srClaimTotal
open ActuarialValuation

theorem solution{Ω : Type*} (Y : ℕ → Ω → ℝ) (ω : Ω) : srClaimTotal Y 0 ω=0 := by
  simp [srClaimTotal]
