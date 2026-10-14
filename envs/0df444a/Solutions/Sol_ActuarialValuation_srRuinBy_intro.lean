-- Prove2me | solution 1 for ActuarialValuation.srRuinBy_intro
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-12T19:29:32.482287+00:00
-- url     : https://prove2.me/submissions/236a0306-ef29-408b-9d30-66936feb33ff

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Definitions.Def_actuarial_srRuinAt
import Definitions.Def_actuarial_srRuinBy

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution {Ω : Type*} (u c : ℝ) (W Y : ℕ → Ω → ℝ) (n N : ℕ) (ω : Ω) (hn : n≤N) (hr : srRuinAt u c W Y n ω) : srRuinBy u c W Y N ω := by
  exact ⟨n, hn, hr⟩
