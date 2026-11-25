-- Prove2me | Definitions.Def_SourceProof_f5d660a305e198c9103ff597
-- name    : SourceProof_f5d660a305e198c9103ff597
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-25T17:56:36.344796+00:00
-- url     : https://prove2.me/theorems/b5f73648-b620-4e33-82fa-535125d91cfd
-- title:
--   StochLean source theorem: ProbabilityTheory.measurable_cappedDenseWindowOscillation

import Definitions.Def_StochLean_Probability_Process_Path_CadlagWindowMoments_F000
import Definitions.Def_SourceProof_2ea59af0c9ba6765e1c4dab1

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

theorem _root_.Prove2MeSourceProof.h_f5d660a305e198c9103ff597 {X : ℝ≥0 → Ω → ℝ}
    (hX : ∀ t, Measurable (X t)) (T δ : ℝ≥0) (C : ℝ) :
    Measurable (cappedDenseWindowOscillation X T δ C) :=
  measurable_const.min (_root_.Prove2MeSourceProof.h_2ea59af0c9ba6765e1c4dab1 hX T δ).ennreal_toReal
end ProbabilityTheory


