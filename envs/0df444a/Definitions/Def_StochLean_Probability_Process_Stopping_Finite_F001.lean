-- Prove2me | Definitions.Def_StochLean_Probability_Process_Stopping_Finite_F001
-- name    : StochLean_Probability_Process_Stopping_Finite_F001
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-24T18:14:12.642816+00:00
-- url     : https://prove2.me/theorems/b1494eae-5c46-4c1f-b027-26d70c881f72
-- title:
--   StochLean: Probability.Process.Stopping.Finite F001

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

def const (F : Filtration ℝ≥0 mΩ) (t : ℝ≥0) : FiniteStoppingTime F :=
  ⟨fun _ ↦ t, isStoppingTime_const F t⟩
end FiniteStoppingTime
end ProbabilityTheory


