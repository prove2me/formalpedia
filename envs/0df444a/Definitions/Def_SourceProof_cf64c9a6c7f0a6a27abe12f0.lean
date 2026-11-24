-- Prove2me | Definitions.Def_SourceProof_cf64c9a6c7f0a6a27abe12f0
-- name    : SourceProof_cf64c9a6c7f0a6a27abe12f0
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-24T18:57:19.603156+00:00
-- url     : https://prove2.me/theorems/247f5812-2c53-4623-9e8f-608053691fce
-- title:
--   StochLean source theorem: ProbabilityTheory.FiniteStoppingTime.max_apply

import Definitions.Def_StochLean_Probability_Process_Stopping_Finite_F003

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

@[simp] theorem _root_.Prove2MeSourceProof.h_cf64c9a6c7f0a6a27abe12f0 (τ σ : FiniteStoppingTime F) (ω : Ω) :
    τ.max σ ω = Max.max (τ ω) (σ ω) := rfl
end FiniteStoppingTime
end ProbabilityTheory


