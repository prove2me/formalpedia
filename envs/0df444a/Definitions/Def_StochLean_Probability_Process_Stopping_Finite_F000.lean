-- Prove2me | Definitions.Def_StochLean_Probability_Process_Stopping_Finite_F000
-- name    : StochLean_Probability_Process_Stopping_Finite_F000
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-24T16:06:51.643556+00:00
-- url     : https://prove2.me/theorems/09c6d7a1-6912-4331-905a-1f4eb8ae2117
-- title:
--   Everywhere finite stopping times
-- statement:
--   A finite stopping time consists of a nonnegative real-valued random time whose inclusion into the extended time set satisfies the stopping-time property.

import Mathlib.Probability.Process.Stopping

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

structure FiniteStoppingTime (F : Filtration ℝ≥0 mΩ) where
  toFun : Ω → ℝ≥0
  isStoppingTime : IsStoppingTime F (fun ω ↦ (toFun ω : WithTop ℝ≥0))
namespace FiniteStoppingTime

variable {F : Filtration ℝ≥0 mΩ}

instance : CoeFun (FiniteStoppingTime F) (fun _ ↦ Ω → ℝ≥0) := ⟨toFun⟩
def withTop (τ : FiniteStoppingTime F) : Ω → WithTop ℝ≥0 := fun ω ↦ τ ω
end FiniteStoppingTime
end ProbabilityTheory


