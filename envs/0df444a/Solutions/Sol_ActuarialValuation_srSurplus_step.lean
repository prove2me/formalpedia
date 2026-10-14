-- Prove2me | solution 1 for ActuarialValuation.srSurplus_step
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-12T19:42:56.206669+00:00
-- url     : https://prove2.me/submissions/46ee5a19-7a79-4e65-927e-20bd726807bb

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Tactic.Ring
import Definitions.Def_actuarial_srSurplus

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution {Ω : Type*} (u c : ℝ) (W Y : ℕ → Ω → ℝ) (n : ℕ) (ω : Ω) : srSurplus u c W Y (n+1) ω=srSurplus u c W Y n ω+c*W n ω-Y n ω := by
  simp only [srSurplus, srNetLoss, srClaimTotal, srWaitingTotal,
    Finset.sum_range_succ]
  ring
  -- Replace the marker above with a complete proof before lint-submit.
