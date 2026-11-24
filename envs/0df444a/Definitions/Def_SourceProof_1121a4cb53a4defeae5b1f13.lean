-- Prove2me | Definitions.Def_SourceProof_1121a4cb53a4defeae5b1f13
-- name    : SourceProof_1121a4cb53a4defeae5b1f13
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-24T23:19:48.378137+00:00
-- url     : https://prove2.me/theorems/a933ae0f-e51d-4684-b2dd-870bed0106b4
-- title:
--   StochLean source theorem: ProbabilityTheory.ofReal_norm_sub_le_denseWindowOscillation_grid

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

theorem _root_.Prove2MeSourceProof.h_1121a4cb53a4defeae5b1f13 {X : ℝ≥0 → Ω → ℝ}
    {T δ : ℝ≥0} {i j : ℕ} (hij : denseTimeUpTo T i ≤ denseTimeUpTo T j)
    (hwidth : denseTimeUpTo T j < denseTimeUpTo T i + δ) (ω : Ω) :
    ENNReal.ofReal ‖X (denseTimeUpTo T j) ω - X (denseTimeUpTo T i) ω‖ ≤
      denseWindowOscillation X T δ ω := by
  apply le_iSup_of_le i
  apply le_iSup_of_le j
  have hguard : ProbabilityTheory.denseTimeUpTo T i ≤ ProbabilityTheory.denseTimeUpTo T j ∧
      ProbabilityTheory.denseTimeUpTo T j < ProbabilityTheory.denseTimeUpTo T i + δ := ⟨hij, hwidth⟩
  rw [if_pos hguard]
end ProbabilityTheory


