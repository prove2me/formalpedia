-- Prove2me | Definitions.Def_SourceProof_dff4282bdbe72b40f691dd9d
-- name    : SourceProof_dff4282bdbe72b40f691dd9d
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-24T19:17:26.792869+00:00
-- url     : https://prove2.me/theorems/544ade54-9831-4b6d-8f0f-1a92cb2c9100
-- title:
--   StochLean source theorem: MeasureTheory.integrable_predictableQuadraticVariation

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

theorem _root_.Prove2MeSourceProof.h_dff4282bdbe72b40f691dd9d {M : ℕ → Ω → ℝ}
    {𝓕 : Filtration ℕ mΩ} {μ : Measure Ω}
    (_hΔ : ∀ k, Integrable ((M (k + 1) - M k) ^ 2) μ) (n : ℕ) :
    Integrable (predictableQuadraticVariation M 𝓕 μ n) μ := by
  unfold MeasureTheory.predictableQuadraticVariation predictablePart
  exact integrable_finsetSum' _ fun k _ => integrable_condExp
end MeasureTheory


