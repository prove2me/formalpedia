-- Prove2me | solution 1 for ActuarialValuation.srSurplus_inception
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-12T19:06:50.638625+00:00
-- url     : https://prove2.me/submissions/5b57a213-33e0-415d-97c9-583951c20b11

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Definitions.Def_actuarial_srSurplus

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution {Ω : Type*} (u c : ℝ) (W Y : ℕ → Ω → ℝ) (ω : Ω) : srSurplus u c W Y 0 ω=u := by
  simp [srSurplus, srNetLoss, srWaitingTotal, srClaimTotal]
