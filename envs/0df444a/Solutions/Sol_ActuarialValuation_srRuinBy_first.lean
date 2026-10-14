-- Prove2me | solution 1 for ActuarialValuation.srRuinBy_first
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-12T19:26:49.245675+00:00
-- url     : https://prove2.me/submissions/ec8f968d-0eb6-4369-91dc-aa63495dc616

import Mathlib.Data.Real.Basic
import Mathlib.Data.Nat.Find
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Definitions.Def_actuarial_srRuinBy
import Definitions.Def_actuarial_srFirstHit

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution {Ω : Type*} (u c : ℝ) (W Y : ℕ → Ω → ℝ) (N : ℕ) (ω : Ω) : srRuinBy u c W Y N ω ↔ ∃ n : ℕ, n≤N ∧ srFirstHit u c W Y n ω := by
  classical
  constructor
  · rintro ⟨n, hN, hn⟩
    let hex : ∃ j : ℕ, srRuinAt u c W Y j ω := ⟨n, hn⟩
    have hle : Nat.find hex ≤ n := by
      by_contra hnot
      exact Nat.find_min hex (lt_of_not_ge hnot) hn
    refine ⟨Nat.find hex, le_trans hle hN, ?_⟩
    constructor
    · exact Nat.find_spec hex
    · intro j hj
      exact Nat.find_min hex hj
  · rintro ⟨n, hN, hn⟩
    exact ⟨n, hN, hn.1⟩
