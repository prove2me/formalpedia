-- Prove2me | Definitions.Def_SourceProof_ce98c22b423cb6d74f7bb08a
-- name    : SourceProof_ce98c22b423cb6d74f7bb08a
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-24T18:58:39.123226+00:00
-- url     : https://prove2.me/theorems/22e214db-2523-4241-93f1-cde0be3296ee
-- title:
--   StochLean source theorem: MeasureTheory.predictableQuadraticVariation_zero

import Definitions.Def_StochLean_Probability_Martingale_QuadraticVariation_F001

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

@[simp]
theorem _root_.Prove2MeSourceProof.h_ce98c22b423cb6d74f7bb08a (M : ℕ → Ω → ℝ)
    (𝓕 : Filtration ℕ mΩ) (μ : Measure Ω) :
    predictableQuadraticVariation M 𝓕 μ 0 = 0 := by
  simp [MeasureTheory.predictableQuadraticVariation]
end MeasureTheory


