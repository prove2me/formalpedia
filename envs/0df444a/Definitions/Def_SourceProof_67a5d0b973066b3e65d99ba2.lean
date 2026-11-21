-- Prove2me | Definitions.Def_SourceProof_67a5d0b973066b3e65d99ba2
-- name    : SourceProof_67a5d0b973066b3e65d99ba2
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-20T19:16:24.136189+00:00
-- url     : https://prove2.me/theorems/67572d5b-9fd5-4491-9fbf-c5248a7aaea8
-- title:
--   LevyStochCalc source module: SourceProof_67a5d0b973066b3e65d99ba2
-- statement:
--   The original source theorem `LevyStochCalc.Poisson.Compensated.markedProgressivelyMeasurable_add` comes from the `LevyStochCalc.Poisson.CompensatedRange` module. The staged Lean declaration includes its source proof and dependency references.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Brownian_ItoRange_F001
import Definitions.Def_LevyStochCalc_Brownian_ItoRange_F002
import Definitions.Def_LevyStochCalc_Poisson_CompensatedLinear_F001
import Definitions.Def_LevyStochCalc_Poisson_CompensatedLinear_F002

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# The range of the compensated Poisson integral on a horizon

A marked integrand supported in `[0, T]`, jointly and progressively measurable and of finite
energy, is admissible for the compensated integral up to `T`. Such integrands are closed under
sums and scalar multiples, and the integral is additive and homogeneous on them, so their
integrals form a submodule of `L²`. The isometry of differences carries an energy-Cauchy sequence
of integrands to an `L²`-Cauchy sequence of integrals, so that submodule is closed.
-/

namespace LevyStochCalc.Poisson.Compensated

open MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal Topology

universe u v

variable {Ω : Type u} [MeasurableSpace Ω] {E : Type v} [MeasurableSpace E]
  {P : Measure Ω} [IsProbabilityMeasure P] {ν : Measure E} [SigmaFinite ν]

section Progressive

variable {ℱ : Filtration ℝ ‹MeasurableSpace Ω›}


theorem _root_.Prove2MeSourceProof.h_67a5d0b973066b3e65d99ba2 {φ₁ φ₂ : Ω → ℝ → E → ℝ}
    (h₁ : Probability.MarkedProgressivelyMeasurable ℱ φ₁)
    (h₂ : Probability.MarkedProgressivelyMeasurable ℱ φ₂) :
    Probability.MarkedProgressivelyMeasurable ℱ fun ω s e => φ₁ ω s e + φ₂ ω s e := by
  intro t
  have hrw : (fun p : Ω × ℝ × E =>
        (Set.Iic t).indicator (fun s => φ₁ p.1 s p.2.2 + φ₂ p.1 s p.2.2) p.2.1)
      = fun p : Ω × ℝ × E => (Set.Iic t).indicator (fun s => φ₁ p.1 s p.2.2) p.2.1
        + (Set.Iic t).indicator (fun s => φ₂ p.1 s p.2.2) p.2.1 := by
    funext p
    by_cases hp : p.2.1 ∈ Set.Iic t
    · simp [Set.indicator_of_mem hp]
    · simp [Set.indicator_of_notMem hp]
  rw [hrw]
  exact (h₁ t).add (h₂ t)
end Progressive

namespace MarkedHorizonIntegrand

variable {ℱ : Filtration ℝ ‹MeasurableSpace Ω›} {T : ℝ}

section Integral

variable {ℱ : Filtration ℝ ‹MeasurableSpace Ω›} {T : ℝ}
  (N : LevyStochCalc.Poisson.PoissonRandomMeasure P ν) (hℱ : IsPoissonFiltration N ℱ)

end Integral

end MarkedHorizonIntegrand

section Range

variable {ℱ : Filtration ℝ ‹MeasurableSpace Ω›} {T : ℝ}
  (N : LevyStochCalc.Poisson.PoissonRandomMeasure P ν) (hℱ : IsPoissonFiltration N ℱ)

end Range

section Representation

variable {ℱ : Filtration ℝ ‹MeasurableSpace Ω›} {T : ℝ}
  (N : LevyStochCalc.Poisson.PoissonRandomMeasure P ν) (hℱ : IsPoissonFiltration N ℱ)

end Representation

end LevyStochCalc.Poisson.Compensated


