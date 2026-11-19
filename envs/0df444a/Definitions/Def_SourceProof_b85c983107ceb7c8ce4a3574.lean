-- Prove2me | Definitions.Def_SourceProof_b85c983107ceb7c8ce4a3574
-- name    : SourceProof_b85c983107ceb7c8ce4a3574
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-18T23:30:57.763313+00:00
-- url     : https://prove2.me/theorems/479584ac-a23f-417b-937c-e26fb055a398
-- title:
--   LevyStochCalc source proof: LevyStochCalc.Probability.measurableSet_stoppedSet
-- statement:
--   Auxiliary theorem proved in the original LevyStochCalc source. Its proof and dependencies are retained verbatim from the certified extraction.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Probability_StoppedProgressive_F001

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

theorem _root_.Prove2MeSourceProof.h_b85c983107ceb7c8ce4a3574 {ℱ : Filtration ℝ mΩ} {τ : Ω → WithTop ℝ}
    (hτ : MeasureTheory.IsStoppingTime ℱ τ) : MeasurableSet (stoppedSet τ) := by
  have hcompl : (LevyStochCalc.Probability.stoppedSet τ)ᶜ
      = ⋃ q : ℚ, {ω : Ω | τ ω ≤ ((q : ℝ) : WithTop ℝ)} ×ˢ Set.Ioi (q : ℝ) := by
    ext p
    simp only [LevyStochCalc.Probability.stoppedSet, Set.mem_compl_iff, Set.mem_setOf_eq, not_le, Set.mem_iUnion,
      Set.mem_prod, Set.mem_Ioi]
    constructor
    · intro hlt
      have hne : τ p.1 ≠ ⊤ := by
        intro h
        rw [h] at hlt
        exact absurd hlt (by simp)
      obtain ⟨r, hr⟩ := WithTop.ne_top_iff_exists.mp hne
      rw [← hr] at hlt
      have hrlt : r < p.2 := by exact_mod_cast hlt
      obtain ⟨q, hq1, hq2⟩ := exists_rat_btwn hrlt
      refine ⟨q, ?_, hq2⟩
      rw [← hr]
      exact_mod_cast hq1.le
    · rintro ⟨q, hq1, hq2⟩
      calc τ p.1 ≤ ((q : ℝ) : WithTop ℝ) := hq1
        _ < ((p.2 : ℝ) : WithTop ℝ) := by exact_mod_cast hq2
  have hmc : MeasurableSet (LevyStochCalc.Probability.stoppedSet τ)ᶜ := by
    rw [hcompl]
    exact MeasurableSet.iUnion fun q =>
      ((ℱ.le (q : ℝ)) _ (hτ (q : ℝ))).prod measurableSet_Ioi
  simpa using hmc.compl
end LevyStochCalc.Probability


