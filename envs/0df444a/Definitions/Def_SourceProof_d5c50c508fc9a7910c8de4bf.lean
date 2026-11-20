-- Prove2me | Definitions.Def_SourceProof_d5c50c508fc9a7910c8de4bf
-- name    : SourceProof_d5c50c508fc9a7910c8de4bf
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-19T19:12:57.211479+00:00
-- url     : https://prove2.me/theorems/aa0b827f-4b9c-48ac-ac4a-0581b0c9c758
-- title:
--   LevyStochCalc source module: SourceProof_d5c50c508fc9a7910c8de4bf
-- statement:
--   The original source theorem `LevyStochCalc.Poisson.tendsto_lintegral_enorm_pathwise` comes from the `LevyStochCalc.Poisson.CompensatorL1` module. The staged Lean declaration includes its source proof and dependency references.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Poisson_CompensatorL1_F002
import Definitions.Def_SourceProof_cee30bfb9b70a700a473aa9b

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# From energy to the mean pathwise integral

The compensator identity turns the mean of the absolute integral against the random measure into
the mean against the reference intensity, and on a window of finite intensity the latter is
controlled by the energy through the comparison of `L¹` with `L²`. So an energy-null sequence of
predictable marked integrands has pathwise compensated integrals tending to zero in mean.
-/

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal Topology

namespace LevyStochCalc.Poisson

universe u v

variable {Ω : Type u} [MeasurableSpace Ω] {E : Type v} [MeasurableSpace E]
  {P : Measure Ω} [IsProbabilityMeasure P] {ν : Measure E} [SigmaFinite ν]

section Bound

variable {A : Set E} {T : ℝ}

end Bound

section Pathwise

variable (N : PoissonRandomMeasure P ν) {ℱ : Filtration ℝ ‹MeasurableSpace Ω›}
  {A : Set E} {T : ℝ}


theorem _root_.Prove2MeSourceProof.h_d5c50c508fc9a7910c8de4bf (hℱ : IsPoissonFiltration N ℱ) (hA : MeasurableSet A)
    (hAν : ν A ≠ ⊤) (T : ℝ) {η : ℕ → Ω → ℝ → E → ℝ}
    (hη : ∀ n, Probability.MarkedPredictable ℱ ν (η n))
    (hηm : ∀ n, Measurable fun p : Ω × ℝ × E => η n p.1 p.2.1 p.2.2)
    (hen : Tendsto (fun n => ∫⁻ ω, ∫⁻ q in Set.Ioc (0 : ℝ) T ×ˢ A,
      ‖η n ω q.1 q.2‖ₑ ^ 2 ∂(referenceIntensity ν) ∂P) atTop (𝓝 0)) :
    Tendsto (fun n => ∫⁻ ω, ‖(∫ q in Set.Ioc (0 : ℝ) T ×ˢ A, η n ω q.1 q.2 ∂(N.N ω))
      - ∫ q in Set.Ioc (0 : ℝ) T ×ˢ A,
          η n ω q.1 q.2 ∂(referenceIntensity ν)‖ₑ ∂P) atTop (𝓝 0) := by
  have hRfin : LevyStochCalc.Poisson.referenceIntensity ν (Set.Ioc (0 : ℝ) T ×ˢ A) ≠ ⊤ :=
    LevyStochCalc.Poisson.referenceIntensity_Ioc_prod_ne_top hAν T
  have hlim : Tendsto (fun n => 2 * ((∫⁻ ω, ∫⁻ q in Set.Ioc (0 : ℝ) T ×ˢ A,
      ‖η n ω q.1 q.2‖ₑ ^ 2 ∂(LevyStochCalc.Poisson.referenceIntensity ν) ∂P) ^ (2 : ℝ)⁻¹
      * LevyStochCalc.Poisson.referenceIntensity ν (Set.Ioc (0 : ℝ) T ×ˢ A) ^ (2 : ℝ)⁻¹)) atTop (𝓝 0) := by
    have hrpow : Tendsto (fun n => (∫⁻ ω, ∫⁻ q in Set.Ioc (0 : ℝ) T ×ˢ A,
        ‖η n ω q.1 q.2‖ₑ ^ 2 ∂(LevyStochCalc.Poisson.referenceIntensity ν) ∂P) ^ (2 : ℝ)⁻¹) atTop (𝓝 0) := by
      have := (ENNReal.continuous_rpow_const (y := (2 : ℝ)⁻¹)).tendsto 0
      have h0 : ((0 : ℝ≥0∞)) ^ (2 : ℝ)⁻¹ = 0 := ENNReal.zero_rpow_of_pos (by norm_num)
      rw [h0] at this
      exact this.comp hen
    have hmtop : LevyStochCalc.Poisson.referenceIntensity ν (Set.Ioc (0 : ℝ) T ×ˢ A) ^ (2 : ℝ)⁻¹ ≠ ⊤ :=
      ENNReal.rpow_ne_top_of_nonneg (by norm_num) hRfin
    have hmul := ENNReal.Tendsto.mul_const hrpow (Or.inr hmtop)
    rw [zero_mul] at hmul
    have hfin : Tendsto (fun n => (2 : ℝ≥0∞) * ((∫⁻ ω, ∫⁻ q in Set.Ioc (0 : ℝ) T ×ˢ A,
        ‖η n ω q.1 q.2‖ₑ ^ 2 ∂(LevyStochCalc.Poisson.referenceIntensity ν) ∂P) ^ (2 : ℝ)⁻¹
        * LevyStochCalc.Poisson.referenceIntensity ν (Set.Ioc (0 : ℝ) T ×ˢ A) ^ (2 : ℝ)⁻¹))
        atTop (𝓝 ((2 : ℝ≥0∞) * 0)) :=
      ENNReal.Tendsto.const_mul hmul (Or.inr (by norm_num))
    rwa [mul_zero] at hfin
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hlim
    (fun n => bot_le) (fun n => ?_)
  refine (LevyStochCalc.Poisson.lintegral_enorm_pathwise_le N hℱ hA hAν T (hη n)).trans ?_
  gcongr
  exact _root_.Prove2MeSourceProof.h_cee30bfb9b70a700a473aa9b hRfin (hηm n)
end Pathwise

end LevyStochCalc.Poisson


