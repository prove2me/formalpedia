-- Prove2me | solution 1 for ActuarialValuation.srRuinBy_monotone
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-12T19:30:07.844503+00:00
-- url     : https://prove2.me/submissions/90fd235f-e50e-46da-8041-0246d79d5f03

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Definitions.Def_actuarial_srRuinBy

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution {Ω : Type*} (u c : ℝ) (W Y : ℕ → Ω → ℝ) (N M : ℕ) (h : N≤M) (ω : Ω) : srRuinBy u c W Y N ω → srRuinBy u c W Y M ω := by
  rintro ⟨n, hn, hr⟩
  exact ⟨n, le_trans hn h, hr⟩
