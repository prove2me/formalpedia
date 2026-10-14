-- Prove2me | solution 1 for ActuarialValuation.srRuinAt_capital_antitone
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-12T19:25:30.835402+00:00
-- url     : https://prove2.me/submissions/ce70b310-e72f-4198-810e-ac2480c11328

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Definitions.Def_actuarial_srRuinAt

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution {Ω : Type*} (u v c : ℝ) (W Y : ℕ → Ω → ℝ) (n : ℕ) (ω : Ω) (h : u≤v) : srRuinAt v c W Y n ω → srRuinAt u c W Y n ω := by
  intro hv
  change srSurplus v c W Y n ω < 0 at hv
  change srSurplus u c W Y n ω < 0
  have hh : srSurplus u c W Y n ω ≤ srSurplus v c W Y n ω := by
    unfold srSurplus
    exact sub_le_sub_right h _
  exact lt_of_le_of_lt hh hv
