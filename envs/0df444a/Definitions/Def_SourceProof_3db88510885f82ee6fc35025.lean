-- Prove2me | Definitions.Def_SourceProof_3db88510885f82ee6fc35025
-- name    : SourceProof_3db88510885f82ee6fc35025
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-24T23:21:14.113383+00:00
-- url     : https://prove2.me/theorems/db3cd3f2-ead0-43d3-a2f3-40b75cbbfe20
-- title:
--   StochLean source theorem: ProbabilityTheory.cappedDenseWindowOscillation_nonneg

import Definitions.Def_StochLean_Probability_Process_Path_CadlagWindowMoments_F000

/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/

/-! # Fixed-cap second moments of short cadlag windows

On a measurable good event with jumps bounded by `b`, the positive excess of
the squared capped window envelope over `b²` tends to zero. A fixed cap gives
integrable domination without any moment assumption on a jump count. The
result bounds the asymptotic second moment, but does not presume convergence
of the envelope itself or control a cap that varies with the width.
-/

@[expose] public section

open Set Filter MeasureTheory
open scoped NNReal ENNReal Topology

namespace ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω}

theorem _root_.Prove2MeSourceProof.h_3db88510885f82ee6fc35025 (X : ℝ≥0 → Ω → ℝ)
    (T δ : ℝ≥0) {C : ℝ} (hC : 0 ≤ C) (ω : Ω) :
    0 ≤ cappedDenseWindowOscillation X T δ C ω :=
  le_min hC ENNReal.toReal_nonneg
end ProbabilityTheory


