-- Prove2me | Definitions.Def_SourceProof_186e21643bf26d9e554362b3
-- name    : SourceProof_186e21643bf26d9e554362b3
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-20T18:04:49.913877+00:00
-- url     : https://prove2.me/theorems/ce1c3383-6647-464e-864c-68102e37a9ea
-- title:
--   LevyStochCalc source module: SourceProof_186e21643bf26d9e554362b3
-- statement:
--   The original source theorem `LevyStochCalc.Brownian.Ito.eval_lintegral_sq_finite` comes from the `LevyStochCalc.Brownian.ItoL2CompletionConvergence` module. The staged Lean declaration includes its source proof and dependency references.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Brownian_ItoL2CompletionConvergence_F002

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# Brownian Itô integral: `L¹`/`L²` convergence and adapted approximation

Transfer of the martingale property along `L¹`-limits, criteria for `L¹`
convergence of squares from `L²` bounds, the endpoint `L²` bound for differences of
simple integrals, and the existence of an adapted `SimplePredictable` integrand
within a prescribed `L²([0, T] × Ω)` tolerance of a progressively measurable
square-integrable integrand, together with the norm and increment identities they
use.
-/

namespace LevyStochCalc.Brownian.Ito

open MeasureTheory
open scoped NNReal ENNReal

universe u
variable {Ω : Type u} [MeasurableSpace Ω]


theorem _root_.Prove2MeSourceProof.h_186e21643bf26d9e554362b3
    {P : MeasureTheory.Measure Ω} [MeasureTheory.IsProbabilityMeasure P]
    {T' : ℝ} (H : SimplePredictable Ω T') (T : ℝ) :
    ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
      (‖H.eval s ω‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤ := by
  set C : ℝ := ∑ i : Fin H.N, (H.ξ_bounded i).choose with hC
  have hbound : ∀ ω s, (‖H.eval s ω‖₊ : ℝ≥0∞) ^ 2 ≤ ENNReal.ofReal (C ^ 2) := by
    intro ω s
    rw [show (‖H.eval s ω‖₊ : ℝ≥0∞) = ENNReal.ofReal ‖H.eval s ω‖
          from (ofReal_norm _).symm, ← ENNReal.ofReal_pow (norm_nonneg _)]
    refine ENNReal.ofReal_le_ofReal ?_
    have h1 : ‖H.eval s ω‖ ≤ C := by
      rw [Real.norm_eq_abs]; exact LevyStochCalc.Brownian.Ito.eval_abs_le_sum_bounds H s ω
    nlinarith [h1, norm_nonneg (H.eval s ω)]
  refine lt_of_le_of_lt (MeasureTheory.lintegral_mono (fun ω =>
    le_trans (MeasureTheory.lintegral_mono (fun s => hbound ω s))
      (le_of_eq (MeasureTheory.setLIntegral_const _ _)))) ?_
  rw [MeasureTheory.lintegral_const]
  exact ENNReal.mul_lt_top
    (ENNReal.mul_lt_top ENNReal.ofReal_lt_top measure_Icc_lt_top) (measure_lt_top _ _)
end LevyStochCalc.Brownian.Ito


