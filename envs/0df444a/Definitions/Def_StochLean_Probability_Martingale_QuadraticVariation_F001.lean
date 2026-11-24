-- Prove2me | Definitions.Def_StochLean_Probability_Martingale_QuadraticVariation_F001
-- name    : StochLean_Probability_Martingale_QuadraticVariation_F001
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-24T18:14:24.246801+00:00
-- url     : https://prove2.me/theorems/f2cebfef-8763-4b5d-808e-9c86bba40bdb
-- title:
--   StochLean: Probability.Martingale.QuadraticVariation F001

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

/-- The predictable bracket, defined as the Doob compensator of pathwise quadratic variation. -/
noncomputable def predictableQuadraticVariation (M : ℕ → Ω → ℝ)
    (𝓕 : Filtration ℕ mΩ) (μ : Measure Ω) : ℕ → Ω → ℝ :=
  predictablePart (pathwiseQuadraticVariation M) 𝓕 μ
end MeasureTheory


