-- Prove2me | solution 1 for ActuarialValuation.srWaitingTotal_succ
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-12T19:05:52.843395+00:00
-- url     : https://prove2.me/submissions/3c34fd1f-7010-4720-9191-c27fcce5734d

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Definitions.Def_actuarial_srWaitingTotal

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution {Ω : Type*} (W : ℕ → Ω → ℝ) (n : ℕ) (ω : Ω) : srWaitingTotal W (n+1) ω=srWaitingTotal W n ω+W n ω := by
  simp only [srWaitingTotal, Finset.sum_range_succ]
