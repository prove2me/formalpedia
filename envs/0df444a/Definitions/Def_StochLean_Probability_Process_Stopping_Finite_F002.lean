-- Prove2me | Definitions.Def_StochLean_Probability_Process_Stopping_Finite_F002
-- name    : StochLean_Probability_Process_Stopping_Finite_F002
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-24T18:14:21.771374+00:00
-- url     : https://prove2.me/theorems/20a542c9-0b7d-401a-a756-06a8d49012b3
-- title:
--   StochLean: Probability.Process.Stopping.Finite F002

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

def min (τ σ : FiniteStoppingTime F) : FiniteStoppingTime F :=
  ⟨fun ω ↦ Min.min (τ ω) (σ ω), by
    simpa only [WithTop.coe_min] using τ.isStoppingTime.min σ.isStoppingTime⟩
end FiniteStoppingTime
end ProbabilityTheory


