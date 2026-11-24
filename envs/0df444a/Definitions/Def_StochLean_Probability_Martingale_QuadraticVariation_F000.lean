-- Prove2me | Definitions.Def_StochLean_Probability_Martingale_QuadraticVariation_F000
-- name    : StochLean_Probability_Martingale_QuadraticVariation_F000
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-24T16:06:42.750044+00:00
-- url     : https://prove2.me/theorems/61e50b29-4885-4ace-98b6-a06e86d131b6
-- title:
--   StochLean: Probability.Martingale.QuadraticVariation F000

import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.Probability.Martingale.Centering
import Mathlib.Probability.Moments.Variance

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

/-- Pathwise quadratic variation of a real-valued discrete process. -/
def pathwiseQuadraticVariation (M : ℕ → Ω → ℝ) (n : ℕ) (ω : Ω) : ℝ :=
  ∑ k ∈ Finset.range n, (M (k + 1) ω - M k ω) ^ 2
end MeasureTheory


