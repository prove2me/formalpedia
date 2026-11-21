-- Prove2me | Definitions.Def_SourceProof_ba87322c9970bc59472f4ba2
-- name    : SourceProof_ba87322c9970bc59472f4ba2
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-20T19:14:50.220497+00:00
-- url     : https://prove2.me/theorems/56b1d688-f45b-4316-a3a7-aa401fd01b6a
-- title:
--   LevyStochCalc source module: SourceProof_ba87322c9970bc59472f4ba2
-- statement:
--   The original source theorem `LevyStochCalc.Poisson.Compensated.stochasticIntegral_congr_ae` comes from the `LevyStochCalc.Poisson.CompensatedCongr` module. The staged Lean declaration includes its source proof and dependency references.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Poisson_CompensatedLinear_F001
import Definitions.Def_LevyStochCalc_Poisson_CompensatedLinear_F002

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# The compensated integral depends only on the class of its integrand

Two admissible marked integrands that agree almost everywhere for the product of the sample
measure, Lebesgue measure on the horizon and the mark measure have almost surely equal
compensated integrals: the energy of their difference vanishes, and the difference isometry
turns that into an almost sure identity.
-/

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology

namespace LevyStochCalc.Poisson.Compensated

universe u v

variable {Ω : Type u} [MeasurableSpace Ω] {E : Type v} [MeasurableSpace E]
  {P : Measure Ω} [IsProbabilityMeasure P] {ν : Measure E} [SigmaFinite ν]
  {ℱ : Filtration ℝ ‹MeasurableSpace Ω›}


theorem _root_.Prove2MeSourceProof.h_ba87322c9970bc59472f4ba2 (N : LevyStochCalc.Poisson.PoissonRandomMeasure P ν)
    (hℱ : LevyStochCalc.Poisson.IsPoissonFiltration N ℱ) (φ ψ : Ω → ℝ → E → ℝ)
    (hφm : Measurable fun p : Ω × ℝ × E => φ p.1 p.2.1 p.2.2)
    (hψm : Measurable fun p : Ω × ℝ × E => ψ p.1 p.2.1 p.2.2)
    (hφp : Probability.MarkedProgressivelyMeasurable ℱ φ)
    (hψp : Probability.MarkedProgressivelyMeasurable ℱ ψ)
    (hφq : ∀ T' : ℝ, 0 < T' → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T', ∫⁻ e,
      (‖φ ω s e‖₊ : ℝ≥0∞) ^ 2 ∂ν ∂volume ∂P < ⊤)
    (hψq : ∀ T' : ℝ, 0 < T' → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T', ∫⁻ e,
      (‖ψ ω s e‖₊ : ℝ≥0∞) ^ 2 ∂ν ∂volume ∂P < ⊤)
    {T : ℝ} (hT : 0 < T)
    (h : (fun p : Ω × ℝ × E => φ p.1 p.2.1 p.2.2)
      =ᵐ[markedEnergyMeasure P ν T] fun p : Ω × ℝ × E => ψ p.1 p.2.1 p.2.2) :
    stochasticIntegral N ℱ hℱ φ hφm hφp hφq T
      =ᵐ[P] stochasticIntegral N ℱ hℱ ψ hψm hψp hψq T := by
  have hzero : ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, ∫⁻ e,
      (‖φ ω s e - ψ ω s e‖₊ : ℝ≥0∞) ^ 2 ∂ν ∂volume ∂P = 0 := by
    have hdiff : (fun p : Ω × ℝ × E => φ p.1 p.2.1 p.2.2 - ψ p.1 p.2.1 p.2.2)
        =ᵐ[LevyStochCalc.Poisson.Compensated.markedEnergyMeasure P ν T] fun _ => (0 : ℝ) := by
      filter_upwards [h] with p hp
      rw [hp, sub_self]
    have hE : LevyStochCalc.Poisson.Compensated.markedEnergy P ν T (fun ω s e => φ ω s e - ψ ω s e)
        = eLpNorm (fun p : Ω × ℝ × E => φ p.1 p.2.1 p.2.2 - ψ p.1 p.2.1 p.2.2) 2
          (LevyStochCalc.Poisson.Compensated.markedEnergyMeasure P ν T) ^ 2 :=
      LevyStochCalc.Poisson.Compensated.markedEnergy_eq_eLpNorm_sq (hφm.sub hψm) T
    have hz : LevyStochCalc.Poisson.Compensated.markedEnergy P ν T (fun ω s e => φ ω s e - ψ ω s e) = 0 := by
      rw [hE, eLpNorm_congr_ae hdiff]
      simp
    exact hz
  have hiso := LevyStochCalc.Poisson.Compensated.itoIsometry_diff_compensated N ℱ hℱ φ ψ hφm hψm hφp hψp hφq hψq T hT
  rw [hzero] at hiso
  have hL1 : MemLp (LevyStochCalc.Poisson.Compensated.stochasticIntegral N ℱ hℱ φ hφm hφp hφq T) 2 P :=
    LevyStochCalc.Poisson.Compensated.stochasticIntegral_memLp N ℱ hℱ φ hφm hφp hφq T
  have hL2 : MemLp (LevyStochCalc.Poisson.Compensated.stochasticIntegral N ℱ hℱ ψ hψm hψp hψq T) 2 P :=
    LevyStochCalc.Poisson.Compensated.stochasticIntegral_memLp N ℱ hℱ ψ hψm hψp hψq T
  have hae : AEMeasurable (fun ω => (‖LevyStochCalc.Poisson.Compensated.stochasticIntegral N ℱ hℱ φ hφm hφp hφq T ω
      - LevyStochCalc.Poisson.Compensated.stochasticIntegral N ℱ hℱ ψ hψm hψp hψq T ω‖₊ : ℝ≥0∞) ^ 2) P :=
    (((hL1.sub hL2).aestronglyMeasurable.aemeasurable).nnnorm).coe_nnreal_ennreal.pow_const 2
  filter_upwards [(lintegral_eq_zero_iff' hae).mp hiso] with ω hω
  have h2 : (‖LevyStochCalc.Poisson.Compensated.stochasticIntegral N ℱ hℱ φ hφm hφp hφq T ω
      - LevyStochCalc.Poisson.Compensated.stochasticIntegral N ℱ hℱ ψ hψm hψp hψq T ω‖₊ : ℝ≥0∞) = 0 :=
    (pow_eq_zero_iff (n := 2) (by norm_num)).mp hω
  have h3 : LevyStochCalc.Poisson.Compensated.stochasticIntegral N ℱ hℱ φ hφm hφp hφq T ω
      - LevyStochCalc.Poisson.Compensated.stochasticIntegral N ℱ hℱ ψ hψm hψp hψq T ω = 0 := by simpa using h2
  linarith
end LevyStochCalc.Poisson.Compensated


