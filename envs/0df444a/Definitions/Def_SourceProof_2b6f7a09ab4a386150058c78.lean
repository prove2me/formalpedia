-- Prove2me | Definitions.Def_SourceProof_2b6f7a09ab4a386150058c78
-- name    : SourceProof_2b6f7a09ab4a386150058c78
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-24T22:15:30.41674+00:00
-- url     : https://prove2.me/theorems/b740a735-c7bd-4a54-86dd-ed10fd7ed643
-- title:
--   StochLean source theorem: ProbabilityTheory.cappedDenseWindowOscillation_le_cap

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

theorem _root_.Prove2MeSourceProof.h_2b6f7a09ab4a386150058c78 (X : ℝ≥0 → Ω → ℝ)
    (T δ : ℝ≥0) (C : ℝ) (ω : Ω) :
    cappedDenseWindowOscillation X T δ C ω ≤ C := min_le_left _ _
end ProbabilityTheory


