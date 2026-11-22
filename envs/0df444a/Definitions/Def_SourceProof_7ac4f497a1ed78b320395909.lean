-- Prove2me | Definitions.Def_SourceProof_7ac4f497a1ed78b320395909
-- name    : SourceProof_7ac4f497a1ed78b320395909
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-21T10:18:00.261669+00:00
-- url     : https://prove2.me/theorems/c2b6a51c-d404-4fa2-ad58-6e9f76a7fc5f
-- title:
--   LevyStochCalc source module: SourceProof_7ac4f497a1ed78b320395909
-- statement:
--   The original source theorem `LevyStochCalc.Ito.JumpFormula.lintegral_window_mark_sq_le_of_abs_le` comes from the `LevyStochCalc.Ito.ItoLevyMixedBounds` module. The staged Lean declaration includes its source proof and dependency references.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Ito_ItoLevyMixedBounds_F000

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# Bounds and admissibility of the mixed integrands

Energy bounds on a bounded window for integrands dominated by finitely many square-integrable
ones, the bounds on the four mixed integrands through the bounded derivatives of the state
function, their continuity in the state, and the progressive measurability of a marked integrand
read at a progressively measurable state.

## Main statements

* `LevyStochCalc.Ito.JumpFormula.lintegral_window_sq_le_of_abs_le`,
  `LevyStochCalc.Ito.JumpFormula.lintegral_window_mark_sq_le_of_abs_le` — energy bounds for
  dominated integrands.
* `LevyStochCalc.Ito.JumpFormula.abs_mixedDriftIntegrand_le`,
  `LevyStochCalc.Ito.JumpFormula.abs_mixedJumpIncrement_le` — bounds on the mixed integrands.
* `LevyStochCalc.Ito.JumpFormula.markedProgressivelyMeasurable_time_state_jump` — the triple of
  the time, a progressively measurable state and the jump coefficient along a path is marked
  progressively measurable.
-/

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal
open LevyStochCalc.Ito.Setting LevyStochCalc.Poisson.Compensated LevyStochCalc.Probability

namespace LevyStochCalc.Ito.JumpFormula

universe u v

section Norms

end Norms

section Energies

variable {Ω : Type u} [MeasurableSpace Ω] {E : Type v} [MeasurableSpace E]
  {P : Measure Ω} [IsProbabilityMeasure P] {ν : Measure E} [SigmaFinite ν]

omit [IsProbabilityMeasure P] in

theorem _root_.Prove2MeSourceProof.h_7ac4f497a1ed78b320395909 {n : ℕ} {φ : Ω → ℝ → E → ℝ}
    {a : Fin n → Ω → ℝ → E → ℝ} {c : ℝ}
    (ha : ∀ i, Measurable fun p : Ω × ℝ × E => a i p.1 p.2.1 p.2.2)
    (h : ∀ ω s e, |φ ω s e| ≤ c * ∑ i, |a i ω s e|) (T : ℝ)
    (hq : ∀ i, ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, ∫⁻ e,
      (‖a i ω s e‖₊ : ℝ≥0∞) ^ 2 ∂ν ∂volume ∂P < ⊤) :
    ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, ∫⁻ e, (‖φ ω s e‖₊ : ℝ≥0∞) ^ 2 ∂ν ∂volume ∂P < ⊤ := by
  have hpt : ∀ ω s e, (‖φ ω s e‖₊ : ℝ≥0∞) ^ 2
      ≤ ENNReal.ofReal (c ^ 2 * n) * ∑ i, (‖a i ω s e‖₊ : ℝ≥0∞) ^ 2 :=
    fun ω s e => LevyStochCalc.Ito.JumpFormula.enorm_sq_le_of_abs_le_mul_sum (h ω s e)
  refine lt_of_le_of_lt
    (lintegral_mono fun ω => lintegral_mono fun s => lintegral_mono fun e => hpt ω s e) ?_
  have hm : ∀ i, Measurable fun p : Ω × ℝ × E => (‖a i p.1 p.2.1 p.2.2‖₊ : ℝ≥0∞) ^ 2 :=
    fun i => ((ha i).nnnorm.coe_nnreal_ennreal).pow_const 2
  have hC : ENNReal.ofReal (c ^ 2 * n) ≠ ⊤ := ENNReal.ofReal_ne_top
  simp_rw [lintegral_const_mul' _ _ hC]
  rw [LevyStochCalc.Ito.JumpFormula.lintegral_window_mark_sum (f := fun i ω s e => (‖a i ω s e‖₊ : ℝ≥0∞) ^ 2) hm T]
  exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top (ENNReal.sum_lt_top.mpr fun i _ => hq i)
end Energies

section MixedBounds

variable {n d : ℕ} {E : Type v} {u : ℝ → (Fin n → ℝ) → ℝ}

end MixedBounds

section MixedContinuity

variable {n d : ℕ} {E : Type v} {u : ℝ → (Fin n → ℝ) → ℝ} {z : ℕ → Fin n → ℝ} {w : Fin n → ℝ}

end MixedContinuity

section Progressive

variable {Ω : Type u} [MeasurableSpace Ω] {E : Type v} [MeasurableSpace E]

end Progressive

end LevyStochCalc.Ito.JumpFormula


