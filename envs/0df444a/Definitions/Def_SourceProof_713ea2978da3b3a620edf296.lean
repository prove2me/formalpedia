-- Prove2me | Definitions.Def_SourceProof_713ea2978da3b3a620edf296
-- name    : SourceProof_713ea2978da3b3a620edf296
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-24T21:47:49.434264+00:00
-- url     : https://prove2.me/theorems/d18c5cbe-f230-4c02-85a7-4095345e03c2
-- title:
--   StochLean source theorem: ProbabilityTheory.FiniteStoppingTime.withTop_truncate

import Definitions.Def_StochLean_Probability_Process_Stopping_Finite_F006
import Definitions.Def_SourceProof_c3c7921df94e85b3cc715c88

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

@[simp] theorem _root_.Prove2MeSourceProof.h_713ea2978da3b3a620edf296 {τ : Ω → WithTop ℝ≥0} (hτ : IsStoppingTime F τ)
    (t : ℝ≥0) : (truncate hτ t).withTop = fun ω ↦ Min.min (t : WithTop ℝ≥0) (τ ω) :=
  _root_.Prove2MeSourceProof.h_c3c7921df94e85b3cc715c88 _ _
end FiniteStoppingTime
end ProbabilityTheory


