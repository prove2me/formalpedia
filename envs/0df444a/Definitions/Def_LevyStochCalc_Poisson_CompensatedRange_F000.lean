-- Prove2me | Definitions.Def_LevyStochCalc_Poisson_CompensatedRange_F000
-- name    : LevyStochCalc_Poisson_CompensatedRange_F000
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-20T19:18:36.450961+00:00
-- url     : https://prove2.me/theorems/aecb3198-1d4d-4d32-bf42-269fe3d285c8
-- title:
--   Source declarations: LevyStochCalc.Poisson.CompensatedRange
-- statement:
--   Source-preserving extracted declarations from LevyStochCalc.Poisson.CompensatedRange. Existing definitions, lemmas, instances, proofs and elaboration context are retained; generated import closure remains under review.
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

/-- The zero marked process is progressively measurable. -/
theorem markedProgressivelyMeasurable_zero (ℱ : Filtration ℝ ‹MeasurableSpace Ω›) :
    Probability.MarkedProgressivelyMeasurable (E := E) ℱ
      fun (_ : Ω) (_ : ℝ) (_ : E) => (0 : ℝ) := by
  intro t
  have hrw : (fun p : Ω × ℝ × E => (Set.Iic t).indicator (fun _ => (0 : ℝ)) p.2.1)
      = fun _ : Ω × ℝ × E => (0 : ℝ) := by
    funext p
    simp
  rw [hrw]
  exact stronglyMeasurable_const
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


