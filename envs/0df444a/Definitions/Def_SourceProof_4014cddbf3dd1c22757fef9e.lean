-- Prove2me | Definitions.Def_SourceProof_4014cddbf3dd1c22757fef9e
-- name    : SourceProof_4014cddbf3dd1c22757fef9e
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-18T22:31:44.659032+00:00
-- url     : https://prove2.me/theorems/142bfdbe-8603-4365-b189-3e197e62e29f
-- title:
--   LevyStochCalc source proof: LevyStochCalc.Probability.ProgressivelyMeasurable.stopped
-- statement:
--   Auxiliary theorem proved in the original LevyStochCalc source. Its proof and dependencies are retained verbatim from the certified extraction.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Probability_StoppedProgressive_F000
import Definitions.Def_SourceProof_0efef36d22ac9421e0560dc4

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# Stopping a progressively measurable process

Cutting a process off at a stopping time keeps it progressively measurable: before a time `t` the
region `{(ω, s) : s ≤ t, s ≤ τ ω}` is the complement, inside `Ω × (-∞, t]`, of a countable union
of rectangles `{τ ≤ q} × (q, t]` over the rationals, each measurable for the σ-algebra at `t`.
-/

open MeasureTheory

namespace LevyStochCalc.Probability

variable {Ω : Type*} {mΩ : MeasurableSpace Ω}


theorem _root_.Prove2MeSourceProof.h_4014cddbf3dd1c22757fef9e {ℱ : Filtration ℝ mΩ} {τ : Ω → WithTop ℝ}
    (hτ : MeasureTheory.IsStoppingTime ℱ τ) {H : Ω → ℝ → ℝ}
    (hH : ProgressivelyMeasurable ℱ H) :
    ProgressivelyMeasurable ℱ (LevyStochCalc.Probability.stopped τ H) := by
  intro t
  letI : MeasurableSpace Ω := ℱ t
  have key : (fun p : Ω × ℝ =>
        (Set.Iic t).indicator (LevyStochCalc.Probability.stopped τ H p.1) p.2)
      = Set.indicator (LevyStochCalc.Probability.stoppedRegion τ t)
        (fun p : Ω × ℝ => (Set.Iic t).indicator (H p.1) p.2) := by
    funext p
    by_cases h1 : p ∈ LevyStochCalc.Probability.stoppedRegion τ t
    · obtain ⟨h1a, h1b⟩ := h1
      rw [Set.indicator_of_mem (show p ∈ LevyStochCalc.Probability.stoppedRegion τ t from ⟨h1a, h1b⟩),
        Set.indicator_of_mem (show p.2 ∈ Set.Iic t from h1a),
        Set.indicator_of_mem (show p.2 ∈ Set.Iic t from h1a),
        LevyStochCalc.Probability.stopped, if_pos h1b]
    · rw [Set.indicator_of_notMem h1]
      by_cases h2 : p.2 ∈ Set.Iic t
      · have h3 : ¬ ((p.2 : ℝ) : WithTop ℝ) ≤ τ p.1 := fun hc => h1 ⟨h2, hc⟩
        rw [Set.indicator_of_mem h2, LevyStochCalc.Probability.stopped, if_neg h3]
      · rw [Set.indicator_of_notMem h2]
  rw [key]
  exact (hH t).indicator (_root_.Prove2MeSourceProof.h_0efef36d22ac9421e0560dc4 hτ t)
end LevyStochCalc.Probability


