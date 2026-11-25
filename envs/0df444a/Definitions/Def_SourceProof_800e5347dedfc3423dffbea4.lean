-- Prove2me | Definitions.Def_SourceProof_800e5347dedfc3423dffbea4
-- name    : SourceProof_800e5347dedfc3423dffbea4
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-25T18:16:54.627363+00:00
-- url     : https://prove2.me/theorems/a870d8be-2817-4146-8675-449eef8b1530
-- title:
--   StochLean source theorem: ProbabilityTheory.norm_sub_le_toReal_denseWindowOscillation_double_width

import Definitions.Def_SourceProof_2aea4abb4308750ba4fcf563
import Definitions.Def_SourceProof_aac25b083b3a0e2c8f7bfc38

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

theorem _root_.Prove2MeSourceProof.h_800e5347dedfc3423dffbea4
    {X : ℝ≥0 → Ω → ℝ} {ω : Ω} (hX : IsCadlagPath (X · ω))
    {T δ r s : ℝ≥0} (hδ : 0 < δ) (hrs : r ≤ s) (hsT : s ≤ T)
    (hwidth : s ≤ r + δ) :
    ‖X s ω - X r ω‖ ≤ (denseWindowOscillation X T (2 * δ) ω).toReal :=
  (ENNReal.ofReal_le_iff_le_toReal (_root_.Prove2MeSourceProof.h_aac25b083b3a0e2c8f7bfc38 hX T _)).mp
    (_root_.Prove2MeSourceProof.h_2aea4abb4308750ba4fcf563 hX.1 hδ hrs hsT hwidth)
end ProbabilityTheory


