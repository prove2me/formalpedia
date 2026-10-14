-- Prove2me | solution 1 for ActuarialValuation.srFirstHit_is_ruin
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-12T19:23:52.354064+00:00
-- url     : https://prove2.me/submissions/664331a5-5ec9-481f-b2e8-2ee2bd6688b7

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Definitions.Def_actuarial_srRuinAt
import Definitions.Def_actuarial_srFirstHit

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution {Ω : Type*} (u c : ℝ) (W Y : ℕ → Ω → ℝ) (n : ℕ) (ω : Ω) : srFirstHit u c W Y n ω → srRuinAt u c W Y n ω := by
  intro h
  exact h.1
