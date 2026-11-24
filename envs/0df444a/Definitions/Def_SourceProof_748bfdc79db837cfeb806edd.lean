-- Prove2me | Definitions.Def_SourceProof_748bfdc79db837cfeb806edd
-- name    : SourceProof_748bfdc79db837cfeb806edd
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-24T23:45:24.412453+00:00
-- url     : https://prove2.me/theorems/6edde6f8-4940-48ff-8cbb-9508f3cd4fb6
-- title:
--   StochLean source theorem: MeasureTheory.Martingale.square_sub_predictableQuadraticVariation

import Definitions.Def_StochLean_Probability_Martingale_QuadraticVariation_F001
import Definitions.Def_SourceProof_549506abde5375992c159de2
import Definitions.Def_SourceProof_c0dcc82fc3fd86f95355f3d8

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

namespace Martingale

theorem _root_.Prove2MeSourceProof.h_748bfdc79db837cfeb806edd
    {M : ℕ → Ω → ℝ} {𝓕 : Filtration ℕ mΩ} {μ : Measure Ω}
    [IsFiniteMeasure μ] [SigmaFiniteFiltration μ 𝓕]
    (hM : Martingale M 𝓕 μ) (hM_two : ∀ n, MemLp (M n) 2 μ) :
    Martingale (fun n => M n ^ 2 - predictableQuadraticVariation M 𝓕 μ n) 𝓕 μ := by
  have hΔ_sq : ∀ n, Integrable ((M (n + 1) - M n) ^ 2) μ :=
    fun n => ((hM_two (n + 1)).sub (hM_two n)).integrable_sq
  have hsum := (_root_.Prove2MeSourceProof.h_549506abde5375992c159de2 hM) hM_two |>.add
    (_root_.Prove2MeSourceProof.h_c0dcc82fc3fd86f95355f3d8
      hM.stronglyAdapted hΔ_sq)
  have heq : (fun n => M n ^ 2 - MeasureTheory.predictableQuadraticVariation M 𝓕 μ n) =
      MeasureTheory.squareMinusPathwiseQuadraticVariation M +
        (MeasureTheory.pathwiseQuadraticVariation M - MeasureTheory.predictableQuadraticVariation M 𝓕 μ) := by
    ext n ω
    simp [MeasureTheory.squareMinusPathwiseQuadraticVariation]
  rw [heq]
  exact hsum
end Martingale

end MeasureTheory


