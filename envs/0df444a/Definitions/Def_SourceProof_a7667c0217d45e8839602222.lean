-- Prove2me | Definitions.Def_SourceProof_a7667c0217d45e8839602222
-- name    : SourceProof_a7667c0217d45e8839602222
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-25T00:45:42.064718+00:00
-- url     : https://prove2.me/theorems/26eebdc8-9a63-4ab7-b03d-e52be841166b
-- title:
--   StochLean source theorem: ProbabilityTheory.FiniteStoppingTime.stoppedValue_eq

import Definitions.Def_StochLean_Probability_Process_Stopping_Finite_F000

/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/

/-! # Everywhere finite stopping times

These are witness data for Protter simple predictable representations, not a
replacement for Mathlib's `IsStoppingTime`. A source endpoint is finite at every
sample, which is stronger than almost-sure finiteness. Evaluation is ordinary
function application and never uses the totalized value at infinity.
-/

@[expose] public section

open MeasureTheory
open scoped NNReal

namespace ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω}

namespace FiniteStoppingTime

variable {F : Filtration ℝ≥0 mΩ}

theorem _root_.Prove2MeSourceProof.h_a7667c0217d45e8839602222 {E : Type*} (X : ℝ≥0 → Ω → E) (τ : FiniteStoppingTime F) :
    stoppedValue X τ.withTop = fun ω ↦ X (τ ω) ω := rfl
end FiniteStoppingTime
end ProbabilityTheory


