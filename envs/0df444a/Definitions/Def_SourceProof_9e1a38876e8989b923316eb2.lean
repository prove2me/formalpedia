-- Prove2me | Definitions.Def_SourceProof_9e1a38876e8989b923316eb2
-- name    : SourceProof_9e1a38876e8989b923316eb2
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-24T21:47:33.788784+00:00
-- url     : https://prove2.me/theorems/a00f0bea-8057-455b-8695-183ebfa5d113
-- title:
--   StochLean source theorem: ProbabilityTheory.HasFiniteVariationPaths.congr

import Definitions.Def_StochLean_Probability_Process_Path_FiniteVariation_F000

/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/

/-! # Finite variation on one common path event

The deterministic owners remain Mathlib's bounded and locally bounded variation.
Local finite variation and finite total variation on the half-line are distinct.
Cadlag paths and adaptedness are separate hypotheses, not implicit fields.
-/

@[expose] public section

open MeasureTheory Filter Set
open scoped NNReal ENNReal

namespace ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω}

variable {X Y : ℝ≥0 → Ω → ℝ} {P : Measure Ω}

namespace HasFiniteVariationPaths
theorem _root_.Prove2MeSourceProof.h_9e1a38876e8989b923316eb2 (hXY : Indistinguishable X Y P)
    (hX : HasFiniteVariationPaths X P) : HasFiniteVariationPaths Y P := by
  filter_upwards [hXY, hX] with ω hω hfv
  simpa only [hω] using hfv
end HasFiniteVariationPaths

end ProbabilityTheory


