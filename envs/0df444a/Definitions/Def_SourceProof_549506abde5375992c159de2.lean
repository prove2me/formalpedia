-- Prove2me | Definitions.Def_SourceProof_549506abde5375992c159de2
-- name    : SourceProof_549506abde5375992c159de2
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-24T21:47:40.030405+00:00
-- url     : https://prove2.me/theorems/c8d78338-47d9-4ec5-b1f8-29308f6d28ae
-- title:
--   StochLean source theorem: MeasureTheory.Martingale.square_sub_pathwiseQuadraticVariation

import Definitions.Def_StochLean_Probability_Martingale_QuadraticVariation_F002
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

namespace Martingale

theorem _root_.Prove2MeSourceProof.h_549506abde5375992c159de2
    {M : ℕ → Ω → ℝ} {𝓕 : Filtration ℕ mΩ} {μ : Measure Ω}
    [IsFiniteMeasure μ] (hM : Martingale M 𝓕 μ) (hM_two : ∀ n, MemLp (M n) 2 μ) :
    Martingale (squareMinusPathwiseQuadraticVariation M) 𝓕 μ := by
  have hΔ_two : ∀ n, MemLp (M (n + 1) - M n) 2 μ :=
    fun n => (hM_two (n + 1)).sub (hM_two n)
  have hΔ_sq : ∀ n, Integrable ((M (n + 1) - M n) ^ 2) μ :=
    fun n => (hΔ_two n).integrable_sq
  have hadp : StronglyAdapted 𝓕 (MeasureTheory.squareMinusPathwiseQuadraticVariation M) := by
    intro n
    exact (hM.stronglyMeasurable n).pow 2 |>.sub
      (_root_.Prove2MeSourceProof.h_91c2eb3fbe16e1a7fcad5287 hM.stronglyAdapted n)
  have hint : ∀ n, Integrable (MeasureTheory.squareMinusPathwiseQuadraticVariation M n) μ := by
    intro n
    exact (hM_two n).integrable_sq.sub (_root_.Prove2MeSourceProof.h_8ea11dc318d9dadc642df2e6 hΔ_sq n)
  refine martingale_of_condExp_sub_eq_zero_nat hadp hint fun n => ?_
  have hdiff : MeasureTheory.squareMinusPathwiseQuadraticVariation M (n + 1) -
      MeasureTheory.squareMinusPathwiseQuadraticVariation M n =
        (2 : ℝ) • (M n * (M (n + 1) - M n)) := by
    ext ω
    simp [MeasureTheory.squareMinusPathwiseQuadraticVariation, MeasureTheory.pathwiseQuadraticVariation,
      Finset.sum_range_succ, smul_eq_mul]
    ring
  rw [hdiff]
  calc
    μ[(2 : ℝ) • (M n * (M (n + 1) - M n)) | 𝓕 n] =ᵐ[μ]
        (2 : ℝ) • μ[M n * (M (n + 1) - M n) | 𝓕 n] :=
      condExp_smul (2 : ℝ) _ _
    _ =ᵐ[μ] (2 : ℝ) • (M n * μ[M (n + 1) - M n | 𝓕 n]) := by
      have hpull := condExp_mul_of_stronglyMeasurable_left (hM.stronglyMeasurable n)
        ((hM_two n).integrable_mul (hΔ_two n))
        ((hM.integrable (n + 1)).sub (hM.integrable n))
      filter_upwards [hpull] with ω hω
      simp [smul_eq_mul, hω]
    _ =ᵐ[μ] 0 := by
      have hzero : μ[M (n + 1) - M n | 𝓕 n] =ᵐ[μ] 0 := by
        calc
          μ[M (n + 1) - M n | 𝓕 n] =ᵐ[μ]
              μ[M (n + 1) | 𝓕 n] - μ[M n | 𝓕 n] :=
            condExp_sub (hM.integrable (n + 1)) (hM.integrable n) _
          _ =ᵐ[μ] M n - M n :=
            (hM.condExp_ae_eq n.le_succ).sub (hM.condExp_ae_eq le_rfl)
          _ =ᵐ[μ] 0 := by simp
      filter_upwards [hzero] with ω hω
      simp [hω]
end Martingale

end MeasureTheory


