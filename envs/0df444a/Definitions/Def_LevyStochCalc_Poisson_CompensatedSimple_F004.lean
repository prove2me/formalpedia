-- Prove2me | Definitions.Def_LevyStochCalc_Poisson_CompensatedSimple_F004
-- name    : LevyStochCalc_Poisson_CompensatedSimple_F004
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-19T00:24:42.343005+00:00
-- url     : https://prove2.me/theorems/1e7e4170-1aca-490a-8ba4-d0cd8b1640c3
-- title:
--   LevyStochCalc source module: LevyStochCalc.Poisson.CompensatedSimple
-- statement:
--   Exact source-faithful declarations from LevyStochCalc.Poisson.CompensatedSimple in the pinned LevyStochCalc project.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Poisson_CompensatedSimple_F000

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# Compensated Poisson integral: simple predictable integrands

The simple predictable integrands `φ = ∑_i ξ_i · 1_{(t_i, t_{i+1}] × A_i}` and
their integral `simpleIntegral` against the compensated Poisson measure
`Ñ(dt, de) := N(dt, de) − ν(de) dt`, with the indicator/rectangle bookkeeping
lemmas. The moment identities are in `Poisson/CompensatedMoments.lean`; the
L²-isometry in `Poisson/CompensatedIsometry.lean`.
-/

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace LevyStochCalc.Poisson.Compensated

universe u v

variable {Ω : Type u} [MeasurableSpace Ω]
variable {E : Type v} [MeasurableSpace E]

/-- Integral of a simple predictable integrand against the compensated
Poisson random measure:

  `∑_i ξ_i · [N((t_i ∧ t, t_{i+1} ∧ t] × A_i)`
  `      − ((t_{i+1} ∧ t − t_i ∧ t)·ν(A_i))]`

Using the `compensated` field of the time-aware `PoissonRandomMeasure`. -/
noncomputable def simpleIntegral
    {P : Measure Ω} [IsProbabilityMeasure P]
    {ν : Measure E} [SigmaFinite ν]
    (N : LevyStochCalc.Poisson.PoissonRandomMeasure P ν)
    {T : ℝ} (φ : SimplePredictable Ω E ν T) (t : ℝ) (ω : Ω) : ℝ :=
  ∑ i : Fin φ.N,
    φ.ξ i ω * N.compensated (φ.timeRect i t) ω
end LevyStochCalc.Poisson.Compensated


