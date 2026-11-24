-- Prove2me | Definitions.Def_SourceProof_faea1308e58b2b1b6deb90cf
-- name    : SourceProof_faea1308e58b2b1b6deb90cf
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-24T18:57:10.529255+00:00
-- url     : https://prove2.me/theorems/d6dca54d-0b83-44bf-b4a4-a57f98b77331
-- title:
--   StochLean source theorem: ProbabilityTheory.FiniteStoppingTime.stoppedProcess_eq

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

theorem _root_.Prove2MeSourceProof.h_faea1308e58b2b1b6deb90cf {E : Type*} (X : ℝ≥0 → Ω → E) (τ : FiniteStoppingTime F) :
    stoppedProcess X τ.withTop = fun t ω ↦ X (Min.min t (τ ω)) ω := by
  ext t ω
  change X (WithTop.untopA (Min.min (t : WithTop ℝ≥0) (τ ω))) ω = _
  rw [← WithTop.coe_min]
  rfl
end FiniteStoppingTime
end ProbabilityTheory


