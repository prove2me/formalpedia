-- Prove2me | solution 1 for ActuarialValuation.srClaimTotal_succ
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-12T19:04:37.057387+00:00
-- url     : https://prove2.me/submissions/4910b2fa-a4b8-4746-ae28-8ac175e28bb3

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Definitions.Def_actuarial_srClaimTotal

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution {Ω : Type*} (Y : ℕ → Ω → ℝ) (n : ℕ) (ω : Ω) : srClaimTotal Y (n+1) ω=srClaimTotal Y n ω+Y n ω := by
  simp only [srClaimTotal, Finset.sum_range_succ]
