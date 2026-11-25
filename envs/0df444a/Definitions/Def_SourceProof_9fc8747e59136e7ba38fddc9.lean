-- Prove2me | Definitions.Def_SourceProof_9fc8747e59136e7ba38fddc9
-- name    : SourceProof_9fc8747e59136e7ba38fddc9
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-25T00:45:40.621802+00:00
-- url     : https://prove2.me/theorems/ee647ac2-28cc-4ccc-83c1-1f0d2050e8a8
-- title:
--   StochLean source theorem: MeasureTheory.Martingale.integral_sub_initial_sq_eq_integral_predictableQuadraticVariation

import Definitions.Def_SourceProof_872696e532e82d1580222069

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

theorem _root_.Prove2MeSourceProof.h_9fc8747e59136e7ba38fddc9
    {M : ℕ → Ω → ℝ} {𝓕 : Filtration ℕ mΩ} {μ : Measure Ω}
    [IsFiniteMeasure μ] [SigmaFiniteFiltration μ 𝓕]
    (hM : Martingale M 𝓕 μ) (hM_two : ∀ n, MemLp (M n) 2 μ) (n : ℕ) :
    ∫ ω, (M n ω - M 0 ω) ^ 2 ∂μ =
      ∫ ω, predictableQuadraticVariation M 𝓕 μ n ω ∂μ := by
  let N : ℕ → Ω → ℝ := fun k => M k - M 0
  have hconst : Martingale (fun _ : ℕ => M 0) 𝓕 μ :=
    martingale_const_fun 𝓕 μ (hM.stronglyMeasurable 0) (hM.integrable 0)
  have hN : Martingale N 𝓕 μ := by
    change Martingale (M - fun _ : ℕ => M 0) 𝓕 μ
    exact hM.sub hconst
  have hN_two : ∀ k, MemLp (N k) 2 μ := fun k => (hM_two k).sub (hM_two 0)
  have hN_zero : N 0 = 0 := by
    ext ω
    simp [N]
  have hqv : MeasureTheory.pathwiseQuadraticVariation N = MeasureTheory.pathwiseQuadraticVariation M := by
    ext k ω
    simp only [MeasureTheory.pathwiseQuadraticVariation, N]
    apply Finset.sum_congr rfl
    intro j hj
    congr 1
    change (M (j + 1) ω - M 0 ω) - (M j ω - M 0 ω) =
      M (j + 1) ω - M j ω
    ring
  have hbr : MeasureTheory.predictableQuadraticVariation N 𝓕 μ =
      MeasureTheory.predictableQuadraticVariation M 𝓕 μ := by
    simp only [MeasureTheory.predictableQuadraticVariation, hqv]
  have h := (_root_.Prove2MeSourceProof.h_872696e532e82d1580222069 hN) hN_two hN_zero n
  rw [hbr] at h
  simpa only [N, Pi.sub_apply] using h
end Martingale

end MeasureTheory


