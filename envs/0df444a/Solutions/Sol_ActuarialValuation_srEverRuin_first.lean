-- Prove2me | solution 1 for ActuarialValuation.srEverRuin_first
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-12T19:16:17.636045+00:00
-- url     : https://prove2.me/submissions/3255ffc5-dd66-4a8b-b901-bb19e8316382

import Mathlib.Data.Real.Basic
import Mathlib.Data.Nat.Find
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Definitions.Def_actuarial_srFirstHit
import Definitions.Def_actuarial_srEverRuin

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution {Ω : Type*} (u c : ℝ) (W Y : ℕ → Ω → ℝ) (ω : Ω) : srEverRuin u c W Y ω ↔ ∃ n : ℕ, srFirstHit u c W Y n ω := by
  classical
  constructor
  · rintro ⟨n, hn⟩
    let hex : ∃ k : ℕ, srRuinAt u c W Y k ω := ⟨n, hn⟩
    refine ⟨Nat.find hex, ?_⟩
    constructor
    · exact Nat.find_spec hex
    · intro j hj
      exact Nat.find_min hex hj
  · rintro ⟨n, hn⟩
    exact ⟨n, hn.1⟩
