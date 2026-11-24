-- Prove2me | Definitions.Def_StochLean_Probability_Process_Stopping_Finite_F006
-- name    : StochLean_Probability_Process_Stopping_Finite_F006
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-24T19:15:55.509796+00:00
-- url     : https://prove2.me/theorems/479e22b2-1d92-4f38-87c8-faad95ad9693
-- title:
--   StochLean: Probability.Process.Stopping.Finite F006

import Definitions.Def_StochLean_Probability_Process_Stopping_Finite_F005

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

/-- A possibly infinite stopping time capped at a deterministic finite time. -/
noncomputable def truncate {τ : Ω → WithTop ℝ≥0} (hτ : IsStoppingTime F τ)
    (t : ℝ≥0) : FiniteStoppingTime F :=
  ofNotTop ((isStoppingTime_const F t).min hτ)
    (fun _ ↦ ne_top_of_le_ne_top WithTop.coe_ne_top (min_le_left _ _))
end FiniteStoppingTime
end ProbabilityTheory


