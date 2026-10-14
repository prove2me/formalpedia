-- Prove2me | solution 1 for ActuarialValuation.srNetLoss_succ
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-12T19:09:57.755365+00:00
-- url     : https://prove2.me/submissions/6baae480-4d61-4d21-9ec2-9372e6323ba7

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Definitions.Def_actuarial_srNetLoss

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution {Ω : Type*} (c : ℝ) (W Y : ℕ → Ω → ℝ) (n : ℕ) (ω : Ω) : srNetLoss c W Y (n+1) ω=srNetLoss c W Y n ω+Y n ω-c*W n ω := by
  simp only [srNetLoss, srClaimTotal, srWaitingTotal, Finset.sum_range_succ]
  ring
