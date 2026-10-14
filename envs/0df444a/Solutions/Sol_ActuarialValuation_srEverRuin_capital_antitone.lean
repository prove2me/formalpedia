-- Prove2me | solution 1 for ActuarialValuation.srEverRuin_capital_antitone
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-12T19:12:00.204982+00:00
-- url     : https://prove2.me/submissions/2bfe6791-4d6f-4a2b-8b61-e57efb9e2e2c

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Definitions.Def_actuarial_srEverRuin

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution {Ω : Type*} (u v c : ℝ) (W Y : ℕ → Ω → ℝ) (ω : Ω) (h : u≤v) : srEverRuin v c W Y ω → srEverRuin u c W Y ω := by
  rintro ⟨n, hn⟩
  refine ⟨n, ?_⟩
  change srSurplus v c W Y n ω < 0 at hn
  change srSurplus u c W Y n ω < 0
  have hh : srSurplus u c W Y n ω ≤ srSurplus v c W Y n ω := by
    unfold srSurplus
    exact sub_le_sub_right h _
  exact lt_of_le_of_lt hh hn
