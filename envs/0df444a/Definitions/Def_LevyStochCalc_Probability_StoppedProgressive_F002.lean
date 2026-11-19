-- Prove2me | Definitions.Def_LevyStochCalc_Probability_StoppedProgressive_F002
-- name    : LevyStochCalc_Probability_StoppedProgressive_F002
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-18T23:31:32.169267+00:00
-- url     : https://prove2.me/theorems/daf2c435-a997-4702-999e-da61fc6b74e9
-- title:
--   Source declarations: LevyStochCalc.Probability.StoppedProgressive
-- statement:
--   Source-preserving extracted declarations from LevyStochCalc.Probability.StoppedProgressive. Existing definitions, lemmas, instances, proofs and elaboration context are retained; generated import closure remains under review.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Probability_StoppedProgressive_F000
import Definitions.Def_LevyStochCalc_Probability_StoppedProgressive_F001
import Definitions.Def_SourceProof_b85c983107ceb7c8ce4a3574

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

/-- **Cutting off at a stopping time preserves joint measurability.** -/
theorem measurable_uncurry_stopped {ℱ : Filtration ℝ mΩ} {τ : Ω → WithTop ℝ}
    (hτ : MeasureTheory.IsStoppingTime ℱ τ) {H : Ω → ℝ → ℝ}
    (hH : Measurable (Function.uncurry H)) :
    Measurable (Function.uncurry (LevyStochCalc.Probability.stopped τ H)) := by
  have hfun : Function.uncurry (LevyStochCalc.Probability.stopped τ H)
      = Set.indicator (stoppedSet τ) (Function.uncurry H) := by
    funext p
    by_cases hp : p ∈ stoppedSet τ
    · rw [Set.indicator_of_mem hp]
      exact if_pos hp
    · rw [Set.indicator_of_notMem hp]
      exact if_neg hp
  rw [hfun]
  exact hH.indicator (_root_.Prove2MeSourceProof.h_b85c983107ceb7c8ce4a3574 hτ)
end LevyStochCalc.Probability


