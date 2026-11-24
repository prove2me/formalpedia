-- Prove2me | Definitions.Def_StochLean_Probability_Martingale_QuadraticVariation_F002
-- name    : StochLean_Probability_Martingale_QuadraticVariation_F002
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-24T18:57:07.210443+00:00
-- url     : https://prove2.me/theorems/3fffb202-a150-4c4c-82eb-09c0e0af7da9
-- title:
--   StochLean: Probability.Martingale.QuadraticVariation F002

import Definitions.Def_StochLean_Probability_Martingale_QuadraticVariation_F000

/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/

/-!
# Quadratic variation and predictable bracket in discrete time

The pathwise quadratic variation `[M]` and the predictable bracket `⟨M⟩` are deliberately
different definitions.  The latter is the Doob predictable part (compensator) of the former.
-/

@[expose] public section

open scoped BigOperators ProbabilityTheory

namespace MeasureTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω}

/-- The square of a process minus its pathwise quadratic variation. Its increments are the
martingale-transform terms `2 Mₙ (Mₙ₊₁ - Mₙ)`. -/
def squareMinusPathwiseQuadraticVariation (M : ℕ → Ω → ℝ) : ℕ → Ω → ℝ :=
  fun n => M n ^ 2 - pathwiseQuadraticVariation M n
end MeasureTheory


