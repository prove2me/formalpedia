-- Prove2me | Definitions.Def_SourceProof_c3c7921df94e85b3cc715c88
-- name    : SourceProof_c3c7921df94e85b3cc715c88
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-24T19:16:49.711911+00:00
-- url     : https://prove2.me/theorems/bdc92e2f-df30-48b1-b695-36754638b149
-- title:
--   StochLean source theorem: ProbabilityTheory.FiniteStoppingTime.withTop_ofNotTop

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

@[simp] theorem _root_.Prove2MeSourceProof.h_c3c7921df94e85b3cc715c88 {τ : Ω → WithTop ℝ≥0} (hτ : IsStoppingTime F τ)
    (hne : ∀ ω, τ ω ≠ ⊤) : (ofNotTop hτ hne).withTop = τ := by
  funext ω
  change ((τ ω).untopA : WithTop ℝ≥0) = τ ω
  rw [WithTop.untopA_eq_untop (hne ω), WithTop.coe_untop]
end FiniteStoppingTime
end ProbabilityTheory


