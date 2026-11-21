-- Prove2me | Definitions.Def_LevyStochCalc_Ito_CompensatedLocalityCutoff_F001
-- name    : LevyStochCalc_Ito_CompensatedLocalityCutoff_F001
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-20T19:48:34.456971+00:00
-- url     : https://prove2.me/theorems/503965fe-2996-4f57-a39a-d0621ed7906e
-- title:
--   Source declarations: LevyStochCalc.Ito.CompensatedLocalityCutoff
-- statement:
--   Source-preserving extracted declarations from LevyStochCalc.Ito.CompensatedLocalityCutoff. Existing definitions, lemmas, instances, proofs and elaboration context are retained; generated import closure remains under review.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Ito_CompensatedLocalityCutoff_F000

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# The marked integrand cut off at a stopping time

The marked process `markedStopped τ φ`, which agrees with `φ` at the times a stopping time `τ`
has not passed and vanishes afterwards, is dominated pointwise by `φ` and inherits from it joint
measurability, marked progressive measurability and finite energy; those three admissibility
properties transport along an equality of marked integrands and are stable under differences.

## Main definitions

* `markedStopped τ φ` — the marked process `φ` cut off at the stopping time `τ`.
-/

open MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal Topology

namespace LevyStochCalc.Poisson.Compensated

universe u v

variable {Ω : Type u} [MeasurableSpace Ω] {E : Type v} [MeasurableSpace E]
  {P : Measure Ω} [IsProbabilityMeasure P] {ν : Measure E} [SigmaFinite ν]
  {ℱ : Filtration ℝ ‹MeasurableSpace Ω›}

section MarkedStopped

variable (τ : Ω → WithTop ℝ) (φ : Ω → ℝ → E → ℝ)

variable {τ φ}

omit [IsProbabilityMeasure P] [SigmaFinite ν] in
/-- A marked integrand dominated pointwise by one of finite energy has finite energy. -/
theorem sq_int_global_of_abs_le {ψ : Ω → ℝ → E → ℝ}
    (h : ∀ ω s e, |ψ ω s e| ≤ |φ ω s e|)
    (hq : ∀ T : ℝ, 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, ∫⁻ e,
      (‖φ ω s e‖₊ : ℝ≥0∞) ^ 2 ∂ν ∂volume ∂P < ⊤) :
    ∀ T : ℝ, 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, ∫⁻ e,
      (‖ψ ω s e‖₊ : ℝ≥0∞) ^ 2 ∂ν ∂volume ∂P < ⊤ := by
  intro T hT
  refine lt_of_le_of_lt (lintegral_mono fun ω => lintegral_mono fun s => lintegral_mono
    fun e => ?_) (hq T hT)
  have hle : (‖ψ ω s e‖₊ : ℝ≥0∞) ≤ (‖φ ω s e‖₊ : ℝ≥0∞) := by
    refine ENNReal.coe_le_coe.mpr ?_
    rw [← NNReal.coe_le_coe]
    simpa [Real.norm_eq_abs] using h ω s e
  gcongr
omit [IsProbabilityMeasure P] [SigmaFinite ν] in
/-- The cut-off integrand has finite energy. -/
theorem sq_int_global_markedStopped
    (hq : ∀ T : ℝ, 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, ∫⁻ e,
      (‖φ ω s e‖₊ : ℝ≥0∞) ^ 2 ∂ν ∂volume ∂P < ⊤) :
    ∀ T : ℝ, 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, ∫⁻ e,
      (‖markedStopped τ φ ω s e‖₊ : ℝ≥0∞) ^ 2 ∂ν ∂volume ∂P < ⊤ :=
  sq_int_global_of_abs_le (fun ω s e => abs_markedStopped_le τ φ ω s e) hq
end MarkedStopped

section Transport

variable {φ ψ : Ω → ℝ → E → ℝ}

omit [MeasurableSpace Ω] [MeasurableSpace E] in
/-- Joint measurability transported along an equality of marked integrands. -/
theorem measurable_uncurry_congr [MeasurableSpace Ω] [MeasurableSpace E] (h : φ = ψ)
    (hm : Measurable fun p : Ω × ℝ × E => φ p.1 p.2.1 p.2.2) :
    Measurable fun p : Ω × ℝ × E => ψ p.1 p.2.1 p.2.2 := by
  subst h
  exact hm
/-- Progressive measurability transported along an equality of marked integrands. -/
theorem markedProgressivelyMeasurable_congr (h : φ = ψ)
    (hp : LevyStochCalc.Probability.MarkedProgressivelyMeasurable ℱ φ) :
    LevyStochCalc.Probability.MarkedProgressivelyMeasurable ℱ ψ := by
  subst h
  exact hp
omit [IsProbabilityMeasure P] [SigmaFinite ν] in
/-- Finite energy transported along an equality of marked integrands. -/
theorem sq_int_global_congr (h : φ = ψ)
    (hq : ∀ T : ℝ, 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, ∫⁻ e,
      (‖φ ω s e‖₊ : ℝ≥0∞) ^ 2 ∂ν ∂volume ∂P < ⊤) :
    ∀ T : ℝ, 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, ∫⁻ e,
      (‖ψ ω s e‖₊ : ℝ≥0∞) ^ 2 ∂ν ∂volume ∂P < ⊤ := by
  subst h
  exact hq
/-- Differences of progressively measurable marked processes are progressively measurable. -/
theorem markedProgressivelyMeasurable_sub
    (h₁ : LevyStochCalc.Probability.MarkedProgressivelyMeasurable ℱ φ)
    (h₂ : LevyStochCalc.Probability.MarkedProgressivelyMeasurable ℱ ψ) :
    LevyStochCalc.Probability.MarkedProgressivelyMeasurable ℱ
      fun ω s e => φ ω s e - ψ ω s e := by
  refine markedProgressivelyMeasurable_congr ?_
    (_root_.Prove2MeSourceProof.h_67a5d0b973066b3e65d99ba2 h₁
      (markedProgressivelyMeasurable_const_mul h₂ (-1 : ℝ)))
  funext ω s e
  ring
end Transport

end LevyStochCalc.Poisson.Compensated


