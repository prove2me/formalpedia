-- Prove2me | Definitions.Def_StochLean_Probability_Process_Path_CadlagWindowMoments_F000
-- name    : StochLean_Probability_Process_Path_CadlagWindowMoments_F000
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-24T22:07:34.431805+00:00
-- url     : https://prove2.me/theorems/ba9d81df-d792-4ce6-9d6e-2c7611d83eb7
-- title:
--   StochLean: Probability.Process.Path.CadlagWindowMoments F000

import Definitions.Def_StochLean_Probability_Process_Path_CadlagWindowOscillation_F000
import Definitions.Def_StochLean_Probability_Process_Path_CadlagWindowOscillation_F001
import Mathlib.MeasureTheory.Integral.DominatedConvergence

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

/-- A fixed real cap on the existing countable short-window envelope. On the
cadlag domain the extended envelope is finite, so `toReal` is its actual value. -/
noncomputable def cappedDenseWindowOscillation (X : ℝ≥0 → Ω → ℝ)
    (T δ : ℝ≥0) (C : ℝ) (ω : Ω) : ℝ :=
  min C (denseWindowOscillation X T δ ω).toReal
end ProbabilityTheory


