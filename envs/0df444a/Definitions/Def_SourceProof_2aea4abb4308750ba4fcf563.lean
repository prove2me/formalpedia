-- Prove2me | Definitions.Def_SourceProof_2aea4abb4308750ba4fcf563
-- name    : SourceProof_2aea4abb4308750ba4fcf563
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-25T18:06:26.482797+00:00
-- url     : https://prove2.me/theorems/327e45a7-0d07-4243-9e08-27ca1d027de4
-- title:
--   StochLean source theorem: ProbabilityTheory.ofReal_norm_sub_le_denseWindowOscillation_double_width

import Definitions.Def_StochLean_Probability_Process_Path_CadlagWindowOscillation_F000
import Definitions.Def_SourceProof_f52e0f0d3a3e8c96b04f0727

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

theorem _root_.Prove2MeSourceProof.h_2aea4abb4308750ba4fcf563
    {X : ℝ≥0 → Ω → ℝ} {ω : Ω} (hX : IsRightContinuousPath (X · ω))
    {T δ r s : ℝ≥0} (hδ : 0 < δ) (hrs : r ≤ s) (hsT : s ≤ T)
    (hwidth : s ≤ r + δ) :
    ENNReal.ofReal ‖X s ω - X r ω‖ ≤ denseWindowOscillation X T (2 * δ) ω := by
  apply _root_.Prove2MeSourceProof.h_f52e0f0d3a3e8c96b04f0727 hX hrs hsT
  have hd : δ < 2 * δ := by
    rw [two_mul]
    exact lt_add_of_pos_right δ hδ
  have hsum : r + δ < r + 2 * δ := by gcongr
  exact hwidth.trans_lt hsum
end ProbabilityTheory


