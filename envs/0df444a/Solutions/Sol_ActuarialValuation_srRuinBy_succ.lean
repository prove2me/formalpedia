-- Prove2me | solution 1 for ActuarialValuation.srRuinBy_succ
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-12T19:32:07.40752+00:00
-- url     : https://prove2.me/submissions/22a57e46-c074-40c1-b65a-36db5c320627

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

theorem solution {Ω : Type*} (u c : ℝ) (W Y : ℕ → Ω → ℝ) (N : ℕ) (ω : Ω) : srRuinBy u c W Y N ω → srRuinBy u c W Y (N+1) ω := by
  rintro ⟨n, hn, hr⟩
  exact ⟨n, Nat.le_trans hn (Nat.le_succ N), hr⟩
