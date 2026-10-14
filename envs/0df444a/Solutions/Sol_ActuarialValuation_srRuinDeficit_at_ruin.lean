-- Prove2me | solution 1 for ActuarialValuation.srRuinDeficit_at_ruin
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-12T19:34:14.876013+00:00
-- url     : https://prove2.me/submissions/ef7358b0-241d-4f60-9b03-c354f1ca4fa3

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Definitions.Def_actuarial_srSurplus
import Definitions.Def_actuarial_srRuinAt
import Definitions.Def_actuarial_srRuinDeficit

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution {Ω : Type*} (u c : ℝ) (W Y : ℕ → Ω → ℝ) (n : ℕ) (ω : Ω) (h : srRuinAt u c W Y n ω) : srRuinDeficit u c W Y n ω= -srSurplus u c W Y n ω := by
  change srSurplus u c W Y n ω < 0 at h
  have hpos : 0 ≤ -srSurplus u c W Y n ω := neg_nonneg.mpr (le_of_lt h)
  simpa [srRuinDeficit, hpos]
  -- Replace the marker above with a complete proof before lint-submit.
