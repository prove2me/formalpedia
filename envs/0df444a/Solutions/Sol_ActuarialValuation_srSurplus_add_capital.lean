-- Prove2me | solution 1 for ActuarialValuation.srSurplus_add_capital
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-12T19:09:57.310371+00:00
-- url     : https://prove2.me/submissions/e6e2eb20-4ecf-4f2e-abc7-db2037ef8553

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

theorem solution {Ω : Type*} (u v c : ℝ) (W Y : ℕ → Ω → ℝ) (n : ℕ) (ω : Ω) : srSurplus (u+v) c W Y n ω=srSurplus u c W Y n ω+v := by
  simp only [srSurplus]
  ring
