-- Prove2me | Definitions.Def_SourceProof_711d7a58a27af1d1b25e8dc9
-- name    : SourceProof_711d7a58a27af1d1b25e8dc9
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-20T18:28:22.870098+00:00
-- url     : https://prove2.me/theorems/8d06eea8-dc16-4587-9caf-04cbe70e824a
-- title:
--   LevyStochCalc source module: SourceProof_711d7a58a27af1d1b25e8dc9
-- statement:
--   The original source theorem `LevyStochCalc.Brownian.Ito.tendsto_lintegral_nnnorm_sq_of_eLpNorm` comes from the `LevyStochCalc.Brownian.ItoL2CompletionApi` module. The staged Lean declaration includes its source proof and dependency references.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Brownian_ItoL2CompletionQuadVar_F000
import Definitions.Def_LevyStochCalc_Brownian_ItoL2CompletionQuadVar_F001
import Definitions.Def_LevyStochCalc_Brownian_ItoL2CompletionQuadVar_F002

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# Brownian Itô integral: the `stochasticIntegral` API

The martingale property of the compensated square for the right-continuation `ℱ₊` of `ℱ`,
the unified existence theorem `itoIsometry_brownian_unified_existence` combining the
martingale, quadratic-variation and isometry conclusions, the isometry for differences of
integrands, and the `stochasticIntegral` interface with `itoIsometry`,
`quadVar_stochasticIntegral` and `martingale_stochasticIntegral`.
-/

namespace LevyStochCalc.Brownian.Ito

open MeasureTheory
open scoped NNReal ENNReal

universe u
variable {Ω : Type u} [MeasurableSpace Ω]

section MasterSequence

variable
    {P : MeasureTheory.Measure Ω} [MeasureTheory.IsProbabilityMeasure P]
    (W : LevyStochCalc.Brownian.BrownianMotion P)
    (ℱ : Filtration ℝ ‹MeasurableSpace Ω›) (hℱ : IsBrownianFiltration W ℱ)
    (H : Ω → ℝ → ℝ) (h_meas : Measurable (Function.uncurry H))
    (h_progMeas : Probability.ProgressivelyMeasurable ℱ H)
    (h_sq_int_global : ∀ T, 0 < T →
      ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
        (‖H ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)

end MasterSequence


theorem _root_.Prove2MeSourceProof.h_711d7a58a27af1d1b25e8dc9
    {β : Type*} [MeasurableSpace β] {μ : MeasureTheory.Measure β}
    {ι : Type*} {l : Filter ι} {gₙ : ι → β → ℝ} {g : β → ℝ}
    (hgₙ : ∀ n, MeasureTheory.AEStronglyMeasurable (gₙ n) μ)
    (hg : MeasureTheory.AEStronglyMeasurable g μ)
    (hgfin : MeasureTheory.eLpNorm g 2 μ ≠ ⊤)
    (htend : Filter.Tendsto (fun n => MeasureTheory.eLpNorm (gₙ n - g) 2 μ) l (nhds 0)) :
    Filter.Tendsto (fun n => ∫⁻ x, (‖gₙ n x‖₊ : ℝ≥0∞) ^ 2 ∂μ) l
      (nhds (∫⁻ x, (‖g x‖₊ : ℝ≥0∞) ^ 2 ∂μ)) := by
  -- `eLpNorm gₙ 2 → eLpNorm g 2` by the two-sided triangle bound.
  have hnorm : Filter.Tendsto (fun n => MeasureTheory.eLpNorm (gₙ n) 2 μ) l
      (nhds (MeasureTheory.eLpNorm g 2 μ)) := by
    have hlo : Filter.Tendsto (fun n => MeasureTheory.eLpNorm g 2 μ
        - MeasureTheory.eLpNorm (gₙ n - g) 2 μ) l (nhds (MeasureTheory.eLpNorm g 2 μ)) := by
      have := ENNReal.Tendsto.sub (tendsto_const_nhds (x := MeasureTheory.eLpNorm g 2 μ))
        htend (Or.inl hgfin)
      simpa using this
    have hhi : Filter.Tendsto (fun n => MeasureTheory.eLpNorm (gₙ n - g) 2 μ
        + MeasureTheory.eLpNorm g 2 μ) l (nhds (MeasureTheory.eLpNorm g 2 μ)) := by
      have := htend.add (tendsto_const_nhds (x := MeasureTheory.eLpNorm g 2 μ))
      simpa using this
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hlo hhi
      (Filter.Eventually.of_forall (fun n => ?_)) (Filter.Eventually.of_forall (fun n => ?_))
    · refine tsub_le_iff_left.mpr ?_
      calc MeasureTheory.eLpNorm g 2 μ
          = MeasureTheory.eLpNorm (gₙ n - (gₙ n - g)) 2 μ := by
            refine MeasureTheory.eLpNorm_congr_ae (Filter.Eventually.of_forall (fun x => ?_))
            simp only [Pi.sub_apply]; ring
        _ ≤ MeasureTheory.eLpNorm (gₙ n - g) 2 μ + MeasureTheory.eLpNorm (gₙ n) 2 μ := by
            refine le_trans (MeasureTheory.eLpNorm_sub_le (hgₙ n)
              ((hgₙ n).sub hg) (by norm_num)) ?_
            rw [add_comm]
    · calc MeasureTheory.eLpNorm (gₙ n) 2 μ
          = MeasureTheory.eLpNorm ((gₙ n - g) + g) 2 μ := by
            refine MeasureTheory.eLpNorm_congr_ae (Filter.Eventually.of_forall (fun x => ?_))
            simp only [Pi.add_apply, Pi.sub_apply]; ring
        _ ≤ MeasureTheory.eLpNorm (gₙ n - g) 2 μ + MeasureTheory.eLpNorm g 2 μ :=
            MeasureTheory.eLpNorm_add_le ((hgₙ n).sub hg) hg (by norm_num)
  have hconv : ∀ x : β → ℝ,
      MeasureTheory.eLpNorm x 2 μ * MeasureTheory.eLpNorm x 2 μ
        = ∫⁻ y, (‖x y‖₊ : ℝ≥0∞) ^ 2 ∂μ := by
    intro x
    rw [← LevyStochCalc.Brownian.Ito.eLpNorm_sq_eq_lintegral_nnnorm_sq,
      show (2 : ℝ) = ((2 : ℕ) : ℝ) from by norm_num, ENNReal.rpow_natCast, pow_two]
  simp_rw [← hconv]
  exact ENNReal.Tendsto.mul hnorm (Or.inr hgfin) hnorm (Or.inr hgfin)
end LevyStochCalc.Brownian.Ito


