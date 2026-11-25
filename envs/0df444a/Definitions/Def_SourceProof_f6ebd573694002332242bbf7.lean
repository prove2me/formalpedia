-- Prove2me | Definitions.Def_SourceProof_f6ebd573694002332242bbf7
-- name    : SourceProof_f6ebd573694002332242bbf7
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-25T17:56:40.149207+00:00
-- url     : https://prove2.me/theorems/e0baad23-665c-4cf8-a52a-d5a8bd979600
-- title:
--   StochLean source theorem: ProbabilityTheory.FiniteStoppingTime.measurableSpace_ofNotTop

import Definitions.Def_StochLean_Probability_Process_Stopping_Finite_F004
import Definitions.Def_StochLean_Probability_Process_Stopping_Finite_F005
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

@[simp] theorem _root_.Prove2MeSourceProof.h_f6ebd573694002332242bbf7 {τ : Ω → WithTop ℝ≥0}
    (hτ : IsStoppingTime F τ) (hne : ∀ ω, τ ω ≠ ⊤) :
    (ofNotTop hτ hne).measurableSpace = hτ.measurableSpace := by
  have heq := _root_.Prove2MeSourceProof.h_c3c7921df94e85b3cc715c88 hτ hne
  unfold ProbabilityTheory.FiniteStoppingTime.measurableSpace
  congr 1
end FiniteStoppingTime
end ProbabilityTheory


