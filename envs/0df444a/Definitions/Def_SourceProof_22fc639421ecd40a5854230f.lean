-- Prove2me | Definitions.Def_SourceProof_22fc639421ecd40a5854230f
-- name    : SourceProof_22fc639421ecd40a5854230f
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-24T23:20:58.623577+00:00
-- url     : https://prove2.me/theorems/e44c9b84-a158-4584-95c0-456e9c9fd104
-- title:
--   StochLean source theorem: ProbabilityTheory.denseWindowOscillation_le_of_bound

import Definitions.Def_StochLean_Probability_Process_Path_CadlagWindowOscillation_F000

/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/

/-! # Measurable two-time short-window oscillations

The envelope uses two points of the existing clipped dense grid and an actual
order and strict-width guard. Countability makes it measurable. Two right-side
approximating sequences recover every strict window of a right-continuous
path; doubling a positive width also covers a closed-width window. Cadlag
compact boundedness proves finiteness before the real-valued bridge is used.
-/

@[expose] public section

open Set Filter MeasureTheory
open scoped NNReal ENNReal Topology

namespace ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω}

theorem _root_.Prove2MeSourceProof.h_22fc639421ecd40a5854230f {X : ℝ≥0 → Ω → ℝ}
    {T δ : ℝ≥0} {ω : Ω} {K : ℝ}
    (hK : ∀ r s : ℝ≥0, r ≤ s → s ≤ T → s < r + δ → ‖X s ω - X r ω‖ ≤ K) :
    denseWindowOscillation X T δ ω ≤ ENNReal.ofReal K := by
  apply iSup_le
  intro i
  apply iSup_le
  intro j
  by_cases h : ProbabilityTheory.denseTimeUpTo T i ≤ ProbabilityTheory.denseTimeUpTo T j ∧
      ProbabilityTheory.denseTimeUpTo T j < ProbabilityTheory.denseTimeUpTo T i + δ
  · rw [if_pos h]
    exact ENNReal.ofReal_le_ofReal (hK _ _ h.1 (min_le_left _ _) h.2)
  · rw [if_neg h]
    exact bot_le
end ProbabilityTheory


