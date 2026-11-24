-- Prove2me | Definitions.Def_SourceProof_6ed3c177b9234dc2ab8ed747
-- name    : SourceProof_6ed3c177b9234dc2ab8ed747
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-24T21:46:31.153382+00:00
-- url     : https://prove2.me/theorems/ab76e5dc-22d6-45aa-9c9a-0c7a7a4abb1d
-- title:
--   StochLean source theorem: ProbabilityTheory.HasMonotonePaths.hasFiniteVariationPaths

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

namespace HasMonotonePaths
theorem _root_.Prove2MeSourceProof.h_6ed3c177b9234dc2ab8ed747 (hX : HasMonotonePaths X P) :
    HasFiniteVariationPaths X P :=
  hX.mono fun _ hω ↦ (hω.monotoneOn univ).locallyBoundedVariationOn
end HasMonotonePaths

end ProbabilityTheory


