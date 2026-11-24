-- Prove2me | Definitions.Def_SourceProof_7ed134b1bc2c6d08d6fe0b39
-- name    : SourceProof_7ed134b1bc2c6d08d6fe0b39
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-24T23:45:18.838844+00:00
-- url     : https://prove2.me/theorems/1dc3f4a9-d3ce-467c-8d04-527d6ccf633e
-- title:
--   StochLean source theorem: ProbabilityTheory.FiniteStoppingTime.withTop_ne_top

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

@[simp] theorem _root_.Prove2MeSourceProof.h_7ed134b1bc2c6d08d6fe0b39 (τ : FiniteStoppingTime F) (ω : Ω) : τ.withTop ω ≠ ⊤ :=
  WithTop.coe_ne_top
end FiniteStoppingTime
end ProbabilityTheory


