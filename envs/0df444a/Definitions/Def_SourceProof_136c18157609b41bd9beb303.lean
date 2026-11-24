-- Prove2me | Definitions.Def_SourceProof_136c18157609b41bd9beb303
-- name    : SourceProof_136c18157609b41bd9beb303
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-24T18:57:29.128269+00:00
-- url     : https://prove2.me/theorems/2633fec6-d54f-4b2a-bca5-b9aeeaa82977
-- title:
--   StochLean source theorem: ProbabilityTheory.FiniteStoppingTime.min_apply

import Definitions.Def_StochLean_Probability_Process_Stopping_Finite_F002

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

@[simp] theorem _root_.Prove2MeSourceProof.h_136c18157609b41bd9beb303 (τ σ : FiniteStoppingTime F) (ω : Ω) :
    τ.min σ ω = Min.min (τ ω) (σ ω) := rfl
end FiniteStoppingTime
end ProbabilityTheory


