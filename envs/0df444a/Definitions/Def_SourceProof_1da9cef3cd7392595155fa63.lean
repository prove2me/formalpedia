-- Prove2me | Definitions.Def_SourceProof_1da9cef3cd7392595155fa63
-- name    : SourceProof_1da9cef3cd7392595155fa63
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-20T19:32:12.915783+00:00
-- url     : https://prove2.me/theorems/1523ae59-0c62-42ea-a637-5977df506ec9
-- title:
--   LevyStochCalc source module: SourceProof_1da9cef3cd7392595155fa63
-- statement:
--   The original source theorem `LevyStochCalc.Poisson.Compensated.stochasticIntegral_ae_zero_of_vanishing` comes from the `LevyStochCalc.Poisson.CompensatedPullOut` module. The staged Lean declaration includes its source proof and dependency references.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Poisson_CompensatedRange_F002
import Definitions.Def_LevyStochCalc_Poisson_CompensatedRange_F003

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# Pulling a past weight inside a compensated integral

A bounded weight measurable at time `a` times the compensated integral of a marked integrand
vanishing up to `a` is the compensated integral of the weighted integrand. The identity is proved
in `L²`: the squared distance between the two sides expands, through the Itô–Lévy isometry and
the quadratic-variation martingale started at `a`, into a combination of weighted compensators
that cancels.
-/

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal

namespace LevyStochCalc.Poisson.Compensated

universe u v

variable {Ω : Type u} [MeasurableSpace Ω] {E : Type v} [MeasurableSpace E]
  {P : Measure Ω} [IsProbabilityMeasure P] {ν : Measure E} [SigmaFinite ν]
  {ℱ : Filtration ℝ ‹MeasurableSpace Ω›}

section Vanishing

variable (N : PoissonRandomMeasure P ν) (hℱ : IsPoissonFiltration N ℱ) (φ : Ω → ℝ → E → ℝ)
  (hm : Measurable fun p : Ω × ℝ × E => φ p.1 p.2.1 p.2.2)
  (hp : Probability.MarkedProgressivelyMeasurable ℱ φ)
  (hq : ∀ T : ℝ, 0 < T → markedEnergy P ν T φ < ⊤)

include hℱ in

theorem _root_.Prove2MeSourceProof.h_1da9cef3cd7392595155fa63 {a : ℝ} (ha : 0 ≤ a)
    (hφa : ∀ ω s e, s ≤ a → φ ω s e = 0) :
    stochasticIntegral N ℱ hℱ φ hm hp hq a =ᵐ[P] 0 := by
  have hiso := LevyStochCalc.Poisson.Compensated.process_lintegral_sq' N ℱ hℱ φ hm hp hq ha
  have h0 : (∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) a, ∫⁻ e, (‖φ ω s e‖₊ : ℝ≥0∞) ^ 2 ∂ν ∂volume ∂P)
      = 0 := by
    have hin : ∀ ω,
        ∫⁻ s in Set.Icc (0 : ℝ) a, ∫⁻ e, (‖φ ω s e‖₊ : ℝ≥0∞) ^ 2 ∂ν ∂volume = 0 := by
      intro ω
      rw [setLIntegral_congr_fun measurableSet_Icc (g := fun _ => (0 : ℝ≥0∞))
        (fun s hs => by
          have h := fun e => hφa ω s e hs.2
          simp [h])]
      simp
    simp [hin]
  have hzero : ∫⁻ ω, (‖LevyStochCalc.Poisson.Compensated.process N ℱ hℱ φ hm hp hq a ω‖₊ : ℝ≥0∞) ^ 2 ∂P = 0 := hiso.trans h0
  have hae : AEMeasurable (fun ω => (‖LevyStochCalc.Poisson.Compensated.process N ℱ hℱ φ hm hp hq a ω‖₊ : ℝ≥0∞) ^ 2) P :=
    ((((LevyStochCalc.Poisson.Compensated.process_memLp N ℱ hℱ φ hm hp hq a).aestronglyMeasurable.aemeasurable).nnnorm
      ).coe_nnreal_ennreal).pow_const 2
  have hproc : LevyStochCalc.Poisson.Compensated.process N ℱ hℱ φ hm hp hq a =ᵐ[P] 0 := by
    filter_upwards [(lintegral_eq_zero_iff' hae).mp hzero] with ω hω
    have h2 : (‖LevyStochCalc.Poisson.Compensated.process N ℱ hℱ φ hm hp hq a ω‖₊ : ℝ≥0∞) ^ 2 = 0 := hω
    have h3 : (‖LevyStochCalc.Poisson.Compensated.process N ℱ hℱ φ hm hp hq a ω‖₊ : ℝ≥0∞) = 0 :=
      (pow_eq_zero_iff (n := 2) (by norm_num)).mp h2
    simpa using h3
  exact (LevyStochCalc.Poisson.Compensated.stochasticIntegral_ae_eq_process N ℱ hℱ φ hm hp hq a).trans hproc
end Vanishing

section Weighted

namespace MarkedHorizonIntegrand

variable {T : ℝ}

variable (N : PoissonRandomMeasure P ν) (hℱ : IsPoissonFiltration N ℱ)

end MarkedHorizonIntegrand

end Weighted

end LevyStochCalc.Poisson.Compensated


