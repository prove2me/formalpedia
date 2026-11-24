-- Prove2me | Definitions.Def_SourceProof_83bfe2ab7b5ac3b55345c1e4
-- name    : SourceProof_83bfe2ab7b5ac3b55345c1e4
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-24T18:57:55.924109+00:00
-- url     : https://prove2.me/theorems/f96422ad-d73b-4866-946b-1cb1d4f9f621
-- title:
--   StochLean source theorem: MeasureTheory.pathwiseQuadraticVariation_eq_sum

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

theorem _root_.Prove2MeSourceProof.h_83bfe2ab7b5ac3b55345c1e4 (M : ℕ → Ω → ℝ) (n : ℕ) :
    pathwiseQuadraticVariation M n =
      ∑ k ∈ Finset.range n, (M (k + 1) - M k) ^ 2 := by
  ext ω
  simp [MeasureTheory.pathwiseQuadraticVariation]
end MeasureTheory


