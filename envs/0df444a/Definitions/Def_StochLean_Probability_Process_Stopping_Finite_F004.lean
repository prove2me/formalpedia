-- Prove2me | Definitions.Def_StochLean_Probability_Process_Stopping_Finite_F004
-- name    : StochLean_Probability_Process_Stopping_Finite_F004
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-24T18:14:22.172683+00:00
-- url     : https://prove2.me/theorems/1ceb4511-22a5-471f-a5b1-ac1c58a45664
-- title:
--   StochLean: Probability.Process.Stopping.Finite F004

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

/-- The canonical sigma-algebra at this stopping time. -/
@[instance_reducible] def measurableSpace (τ : FiniteStoppingTime F) : MeasurableSpace Ω :=
  τ.isStoppingTime.measurableSpace
end FiniteStoppingTime
end ProbabilityTheory


