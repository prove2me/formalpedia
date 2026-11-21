-- Prove2me | Definitions.Def_LevyStochCalc_Poisson_CompensatedRange_F003
-- name    : LevyStochCalc_Poisson_CompensatedRange_F003
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-20T19:26:48.426967+00:00
-- url     : https://prove2.me/theorems/2acc3b9c-cad1-466c-a5f8-9f9a7a928fe9
-- title:
--   Source declarations: LevyStochCalc.Poisson.CompensatedRange
-- statement:
--   Source-preserving extracted declarations from LevyStochCalc.Poisson.CompensatedRange. Existing definitions, lemmas, instances, proofs and elaboration context are retained; generated import closure remains under review.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Poisson_CompensatedRange_F001

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

/-- The compensated integral over the horizon is measurable before `T`. -/
theorem MarkedHorizonIntegrand.aestronglyMeasurable (G : MarkedHorizonIntegrand P ν ℱ T) :
    AEStronglyMeasurable[ℱ T] (G.integral N hℱ) P :=
  ((process_stronglyAdapted N ℱ hℱ G.toFun G.measurable_uncurry G.progressive
    G.sq_int_global T).aestronglyMeasurable).congr
    (stochasticIntegral_ae_eq_process N ℱ hℱ G.toFun G.measurable_uncurry G.progressive
      G.sq_int_global T).symm
end Representation

end LevyStochCalc.Poisson.Compensated


