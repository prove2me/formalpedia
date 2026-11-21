-- Prove2me | Definitions.Def_SourceProof_ec4d5d34845b027c60491406
-- name    : SourceProof_ec4d5d34845b027c60491406
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-20T19:31:49.466021+00:00
-- url     : https://prove2.me/theorems/792ec43d-ee4f-4ec3-b9fa-4b89c3123939
-- title:
--   LevyStochCalc source module: SourceProof_ec4d5d34845b027c60491406
-- statement:
--   The original source theorem `LevyStochCalc.Poisson.Compensated.markedProgressivelyMeasurable_mul_of_vanishing` comes from the `LevyStochCalc.Poisson.CompensatedPullOut` module. The staged Lean declaration includes its source proof and dependency references.
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

end Vanishing

section Weighted


theorem _root_.Prove2MeSourceProof.h_ec4d5d34845b027c60491406 {φ : Ω → ℝ → E → ℝ}
    (hp : Probability.MarkedProgressivelyMeasurable ℱ φ) {a : ℝ}
    (hφa : ∀ ω s e, s ≤ a → φ ω s e = 0) {V : Ω → ℝ} (hVm : StronglyMeasurable[ℱ a] V) :
    Probability.MarkedProgressivelyMeasurable ℱ fun ω s e => V ω * φ ω s e := by
  intro t
  change @StronglyMeasurable (Ω × ℝ × E) ℝ _
    (@Prod.instMeasurableSpace Ω (ℝ × E) (ℱ t) inferInstance)
    fun p : Ω × ℝ × E => (Set.Iic t).indicator (fun s => V p.1 * φ p.1 s p.2.2) p.2.1
  rcases lt_or_ge t a with hta | hat
  · have h0 : (fun p : Ω × ℝ × E =>
        (Set.Iic t).indicator (fun s => V p.1 * φ p.1 s p.2.2) p.2.1) = fun _ => 0 := by
      funext p
      by_cases hs : p.2.1 ∈ Set.Iic t
      · rw [Set.indicator_of_mem hs, hφa _ _ _ (le_trans hs hta.le), mul_zero]
      · rw [Set.indicator_of_notMem hs]
    rw [h0]
    exact stronglyMeasurable_const
  · have h1 : @StronglyMeasurable (Ω × ℝ × E) ℝ _
        (@Prod.instMeasurableSpace Ω (ℝ × E) (ℱ t) inferInstance) fun p => V p.1 :=
      (hVm.mono (ℱ.mono hat)).comp_measurable (@measurable_fst Ω (ℝ × E) (ℱ t) _)
    have h2 := hp t
    have h3 : (fun p : Ω × ℝ × E =>
        (Set.Iic t).indicator (fun s => V p.1 * φ p.1 s p.2.2) p.2.1)
        = fun p => V p.1 * (Set.Iic t).indicator (fun s => φ p.1 s p.2.2) p.2.1 := by
      funext p
      exact Set.indicator_const_mul _ _ _ _
    rw [h3]
    exact h1.mul h2
namespace MarkedHorizonIntegrand

variable {T : ℝ}

variable (N : PoissonRandomMeasure P ν) (hℱ : IsPoissonFiltration N ℱ)

end MarkedHorizonIntegrand

end Weighted

end LevyStochCalc.Poisson.Compensated


