-- Prove2me | Definitions.Def_SourceProof_6cdc47526d2ae213604fd2f4
-- name    : SourceProof_6cdc47526d2ae213604fd2f4
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-20T19:55:55.158803+00:00
-- url     : https://prove2.me/theorems/8af9eb06-8ae4-421c-88d2-8b91e28bfa18
-- title:
--   LevyStochCalc source module: SourceProof_6cdc47526d2ae213604fd2f4
-- statement:
--   The original source theorem `LevyStochCalc.Poisson.Compensated.stochasticIntegral_sub` comes from the `LevyStochCalc.Ito.CompensatedLocalityWindow` module. The staged Lean declaration includes its source proof and dependency references.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Ito_CompensatedLocalityWindow_F001

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# The compensated integral over a time window

Restricting a marked integrand to a window `(c, t]` preserves admissibility and yields the
increment of the compensated integral across that window; an integrand vanishing after a
positive time `c` has an integral that no longer moves after `c`, the hit indicator of a
stopping time at `c` factors out of the integral over `(c, t]`, and the integral is additive in
the integrand, over differences and over finite sums.

## Main statements

* `stochasticIntegral_ae_eq_of_vanishing_gt` — the integral of an integrand vanishing after a
  time `c` does not move after `c`.
* `stochasticIntegral_indicator_Ioc` — restricting the integrand to `(c, t]` gives the increment
  of the integral over `(c, t]`.
-/

open MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal Topology

namespace LevyStochCalc.Poisson.Compensated

open LevyStochCalc.Brownian.Ito (indIoc indIoc_le_one measurable_uncurry_indIoc hitInd
  abs_hitInd_le_one stronglyMeasurable_hitInd sq_nnnorm_add_le_two_mul)

universe u v

variable {Ω : Type u} [MeasurableSpace Ω] {E : Type v} [MeasurableSpace E]
  {P : Measure Ω} [IsProbabilityMeasure P] {ν : Measure E} [SigmaFinite ν]
  {ℱ : Filtration ℝ ‹MeasurableSpace Ω›}

section Window

variable (N : PoissonRandomMeasure P ν) (hℱ : IsPoissonFiltration N ℱ)
  {φ : Ω → ℝ → E → ℝ}
  (hm : Measurable fun p : Ω × ℝ × E => φ p.1 p.2.1 p.2.2)
  (hp : LevyStochCalc.Probability.MarkedProgressivelyMeasurable ℱ φ)
  (hq : ∀ T : ℝ, 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, ∫⁻ e,
    (‖φ ω s e‖₊ : ℝ≥0∞) ^ 2 ∂ν ∂volume ∂P < ⊤)

end Window

section Linear

variable (N : PoissonRandomMeasure P ν) (hℱ : IsPoissonFiltration N ℱ)

include hℱ in

theorem _root_.Prove2MeSourceProof.h_6cdc47526d2ae213604fd2f4 {φ₁ φ₂ : Ω → ℝ → E → ℝ}
    (hm₁ : Measurable fun p : Ω × ℝ × E => φ₁ p.1 p.2.1 p.2.2)
    (hm₂ : Measurable fun p : Ω × ℝ × E => φ₂ p.1 p.2.1 p.2.2)
    (hp₁ : LevyStochCalc.Probability.MarkedProgressivelyMeasurable ℱ φ₁)
    (hp₂ : LevyStochCalc.Probability.MarkedProgressivelyMeasurable ℱ φ₂)
    (hq₁ : ∀ T : ℝ, 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, ∫⁻ e,
      (‖φ₁ ω s e‖₊ : ℝ≥0∞) ^ 2 ∂ν ∂volume ∂P < ⊤)
    (hq₂ : ∀ T : ℝ, 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, ∫⁻ e,
      (‖φ₂ ω s e‖₊ : ℝ≥0∞) ^ 2 ∂ν ∂volume ∂P < ⊤)
    (hms : Measurable fun p : Ω × ℝ × E => φ₁ p.1 p.2.1 p.2.2 - φ₂ p.1 p.2.1 p.2.2)
    (hps : LevyStochCalc.Probability.MarkedProgressivelyMeasurable ℱ
      fun ω s e => φ₁ ω s e - φ₂ ω s e)
    (hqs : ∀ T : ℝ, 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, ∫⁻ e,
      (‖φ₁ ω s e - φ₂ ω s e‖₊ : ℝ≥0∞) ^ 2 ∂ν ∂volume ∂P < ⊤)
    {T : ℝ} (hT : 0 < T) :
    stochasticIntegral N ℱ hℱ (fun ω s e => φ₁ ω s e - φ₂ ω s e) hms hps hqs T
      =ᵐ[P] fun ω => stochasticIntegral N ℱ hℱ φ₁ hm₁ hp₁ hq₁ T ω
        - stochasticIntegral N ℱ hℱ φ₂ hm₂ hp₂ hq₂ T ω := by
  have hsubfun : (fun ω s e => φ₁ ω s e - φ₂ ω s e)
      = fun ω s e => φ₁ ω s e + (-1 : ℝ) * φ₂ ω s e := by
    funext ω s e
    ring
  have hmn : Measurable fun p : Ω × ℝ × E => (-1 : ℝ) * φ₂ p.1 p.2.1 p.2.2 :=
    measurable_const.mul hm₂
  have hpn := LevyStochCalc.Poisson.Compensated.markedProgressivelyMeasurable_const_mul hp₂ (-1 : ℝ)
  have hqn : ∀ T' : ℝ, 0 < T' → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T', ∫⁻ e,
      (‖(-1 : ℝ) * φ₂ ω s e‖₊ : ℝ≥0∞) ^ 2 ∂ν ∂volume ∂P < ⊤ :=
    fun T' hT' =>
    lt_top_iff_ne_top.mpr (LevyStochCalc.Poisson.Compensated.markedEnergy_const_mul_ne_top hm₂ (hq₂ T' hT').ne (-1 : ℝ))
  have hma := LevyStochCalc.Poisson.Compensated.measurable_uncurry_congr hsubfun hms
  have hpa := LevyStochCalc.Poisson.Compensated.markedProgressivelyMeasurable_congr hsubfun hps
  have hqa := LevyStochCalc.Poisson.Compensated.sq_int_global_congr hsubfun hqs
  rw [LevyStochCalc.Poisson.Compensated.stochasticIntegral_congr_fun N hℱ (φ := fun ω s e => φ₁ ω s e - φ₂ ω s e)
    hms hps hqs hsubfun hma hpa hqa T]
  filter_upwards [_root_.Prove2MeSourceProof.h_79a6cde54e31b0f9d920e0b6 N ℱ hℱ hm₁ hmn hp₁ hpn hq₁ hqn hma hpa hqa hT,
    _root_.Prove2MeSourceProof.h_607da3f21f7f718eec49c956 N ℱ hℱ hm₂ hp₂ hq₂ (-1 : ℝ) hmn hpn hqn hT]
    with ω hadd hneg
  rw [hadd, hneg]
  ring
end Linear

end LevyStochCalc.Poisson.Compensated


