-- Prove2me | Definitions.Def_SourceProof_585438f7fe1537e8a461ed92
-- name    : SourceProof_585438f7fe1537e8a461ed92
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-19T15:11:28.17739+00:00
-- url     : https://prove2.me/theorems/496d1833-4a50-4390-999d-62cf77a87cc4
-- title:
--   LevyStochCalc source module: SourceProof_585438f7fe1537e8a461ed92
-- statement:
--   The original source theorem `LevyStochCalc.Poisson.Compensated.SimplePredictable.lintegral_eval_sq_outer` comes from the `LevyStochCalc.Poisson.CompensatedSimple` module. The staged Lean declaration includes its source proof and dependency references.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Poisson_CompensatedSimple_F003

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# Compensated Poisson integral: simple predictable integrands

The simple predictable integrands `φ = ∑_i ξ_i · 1_{(t_i, t_{i+1}] × A_i}` and
their integral `simpleIntegral` against the compensated Poisson measure
`Ñ(dt, de) := N(dt, de) − ν(de) dt`, with the indicator/rectangle bookkeeping
lemmas. The moment identities are in `Poisson/CompensatedMoments.lean`; the
L²-isometry in `Poisson/CompensatedIsometry.lean`.
-/

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace LevyStochCalc.Poisson.Compensated

universe u v

variable {Ω : Type u} [MeasurableSpace Ω]
variable {E : Type v} [MeasurableSpace E]


theorem _root_.Prove2MeSourceProof.h_585438f7fe1537e8a461ed92
    {P : Measure Ω} [IsProbabilityMeasure P]
    {ν : Measure E} [SigmaFinite ν] {T : ℝ}
    (φ : SimplePredictable Ω E ν T) :
    ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, ∫⁻ e,
        (‖φ.eval s e ω‖₊ : ℝ≥0∞) ^ 2 ∂ν ∂volume ∂P
      = ∑ i : Fin φ.N,
        LevyStochCalc.Poisson.referenceIntensity ν (φ.fullRect i) *
        ∫⁻ ω, (‖φ.ξ i ω‖₊ : ℝ≥0∞) ^ 2 ∂P := by
  -- Step 1: rewrite inner double-lintegral via lintegral_eval_sq.
  rw [show (fun ω : Ω => ∫⁻ s in Set.Icc (0 : ℝ) T, ∫⁻ e,
              (‖φ.eval s e ω‖₊ : ℝ≥0∞) ^ 2 ∂ν ∂volume)
        = (fun ω : Ω => ∑ i : Fin φ.N,
            (‖φ.ξ i ω‖₊ : ℝ≥0∞) ^ 2 *
            LevyStochCalc.Poisson.referenceIntensity ν (φ.fullRect i)) from
    funext (fun ω => LevyStochCalc.Poisson.Compensated.SimplePredictable.lintegral_eval_sq φ ω)]
  -- Step 2: pull outer sum out via lintegral_finset_sum.
  have h_sq_meas : ∀ i : Fin φ.N,
      Measurable (fun ω : Ω => (‖φ.ξ i ω‖₊ : ℝ≥0∞) ^ 2) := by
    intro i
    refine Measurable.pow_const ?_ 2
    exact ENNReal.continuous_coe.measurable.comp (φ.ξ_measurable i).nnnorm
  rw [MeasureTheory.lintegral_finsetSum]
  · refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [MeasureTheory.lintegral_mul_const _ (h_sq_meas i)]
    ring
  · intro i _
    exact (h_sq_meas i).mul_const _
end LevyStochCalc.Poisson.Compensated


