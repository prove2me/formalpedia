-- Prove2me | Definitions.Def_StochLean_Probability_Process_Stopping_Finite_F005
-- name    : StochLean_Probability_Process_Stopping_Finite_F005
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-24T18:57:30.508294+00:00
-- url     : https://prove2.me/theorems/b0bfe4f7-c400-44eb-93e0-ba72230c1666
-- title:
--   StochLean: Probability.Process.Stopping.Finite F005

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

/-- Forget the top point only after an everywhere-finiteness proof. -/
noncomputable def ofNotTop {τ : Ω → WithTop ℝ≥0} (hτ : IsStoppingTime F τ)
    (hne : ∀ ω, τ ω ≠ ⊤) : FiniteStoppingTime F :=
  ⟨fun ω ↦ (τ ω).untopA, by
    have heq (ω) : ((τ ω).untopA : WithTop ℝ≥0) = τ ω := by
      rw [WithTop.untopA_eq_untop (hne ω), WithTop.coe_untop]
    simpa only [heq] using hτ⟩
end FiniteStoppingTime
end ProbabilityTheory


