-- Prove2me | Definitions.Def_SourceProof_c0dcc82fc3fd86f95355f3d8
-- name    : SourceProof_c0dcc82fc3fd86f95355f3d8
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-24T21:47:35.727593+00:00
-- url     : https://prove2.me/theorems/8cadced5-8df3-4778-aeb3-9047f610820a
-- title:
--   StochLean source theorem: MeasureTheory.martingale_pathwiseQuadraticVariation_sub_predictableQuadraticVariation

import Definitions.Def_StochLean_Probability_Martingale_QuadraticVariation_F001
import Definitions.Def_SourceProof_8ea11dc318d9dadc642df2e6
import Definitions.Def_SourceProof_91c2eb3fbe16e1a7fcad5287

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


theorem _root_.Prove2MeSourceProof.h_c0dcc82fc3fd86f95355f3d8
    {M : ℕ → Ω → ℝ} {𝓕 : Filtration ℕ mΩ} {μ : Measure Ω}
    [SigmaFiniteFiltration μ 𝓕] (hM : StronglyAdapted 𝓕 M)
    (hΔ : ∀ k, Integrable ((M (k + 1) - M k) ^ 2) μ) :
    Martingale (pathwiseQuadraticVariation M - predictableQuadraticVariation M 𝓕 μ) 𝓕 μ := by
  change Martingale (martingalePart (MeasureTheory.pathwiseQuadraticVariation M) 𝓕 μ) 𝓕 μ
  exact martingale_martingalePart (_root_.Prove2MeSourceProof.h_91c2eb3fbe16e1a7fcad5287 hM)
    (_root_.Prove2MeSourceProof.h_8ea11dc318d9dadc642df2e6 hΔ)
end MeasureTheory


