-- Prove2me | Definitions.Def_StochLean_Probability_Process_Stopping_Finite_F003
-- name    : StochLean_Probability_Process_Stopping_Finite_F003
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-24T18:14:18.790124+00:00
-- url     : https://prove2.me/theorems/28bc9c4d-2a7b-4c17-8e5a-94ee34b687bc
-- title:
--   StochLean: Probability.Process.Stopping.Finite F003

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

def max (τ σ : FiniteStoppingTime F) : FiniteStoppingTime F :=
  ⟨fun ω ↦ Max.max (τ ω) (σ ω), by
    simpa only [WithTop.coe_max] using τ.isStoppingTime.max σ.isStoppingTime⟩
end FiniteStoppingTime
end ProbabilityTheory


