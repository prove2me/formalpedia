-- Prove2me | Definitions.Def_SourceProof_8ea11dc318d9dadc642df2e6
-- name    : SourceProof_8ea11dc318d9dadc642df2e6
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-24T19:16:27.414293+00:00
-- url     : https://prove2.me/theorems/a482fbac-c8cb-4003-b0c2-f6ba9885d611
-- title:
--   StochLean source theorem: MeasureTheory.integrable_pathwiseQuadraticVariation

import Definitions.Def_StochLean_Probability_Martingale_QuadraticVariation_F000
import Definitions.Def_SourceProof_83bfe2ab7b5ac3b55345c1e4

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

theorem _root_.Prove2MeSourceProof.h_8ea11dc318d9dadc642df2e6 {M : ℕ → Ω → ℝ} {μ : Measure Ω}
    (hΔ : ∀ k, Integrable ((M (k + 1) - M k) ^ 2) μ) (n : ℕ) :
    Integrable (pathwiseQuadraticVariation M n) μ := by
  rw [_root_.Prove2MeSourceProof.h_83bfe2ab7b5ac3b55345c1e4]
  exact integrable_finsetSum' _ fun k _ => hΔ k
end MeasureTheory


