-- Prove2me | Definitions.Def_LevyStochCalc_Poisson_CompensatedIsometryL2_F002
-- name    : LevyStochCalc_Poisson_CompensatedIsometryL2_F002
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-19T00:26:26.034872+00:00
-- url     : https://prove2.me/theorems/4b72bcee-8465-4263-987f-4f0e2b7d81fe
-- title:
--   Source declarations: LevyStochCalc.Poisson.CompensatedIsometryL2
-- statement:
--   Source-preserving extracted declarations from LevyStochCalc.Poisson.CompensatedIsometryL2. Existing definitions, lemmas, instances, proofs and elaboration context are retained; generated import closure remains under review.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Poisson_CompensatedSimple_F004
import Mathlib.MeasureTheory.Group.Arithmetic
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.MeasurableSpace.Constructions
import Mathlib.MeasureTheory.Measure.HasOuterApproxClosed
import Mathlib.Probability.Process.Filtration

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# L²-isometry of the simple compensated-Poisson integral

Expansion of `(∑_i ξ_i · Ñ(B_i))²` into its diagonal and off-diagonal terms, the resulting
isometry `∫⁻ ‖simpleIntegral N φ T‖² ∂P = ∫⁻ ∫⁻ ∫⁻ ‖φ.eval‖² ∂ν ∂volume ∂P` together with
its Bochner sum form `∑_i ν̂(fullRect i).toReal · ∫ ξ_i² ∂P`, the finiteness of the
`L²`-norm and the membership `MemLp (simpleIntegral N φ T) 2 P`.
-/

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace LevyStochCalc.Poisson.Compensated

universe u v

variable {Ω : Type u} [MeasurableSpace Ω]
variable {E : Type v} [MeasurableSpace E]

/-! ## Square integrability of the simple compensated integral

The simple integral `simpleIntegral N φ T` of an adapted simple integrand has finite second
moment and lies in `L²(P)`; the Brownian counterpart is the lift
`LevyStochCalc.Brownian.Ito.simpleIntegralLp_brownian` to `Lp ℝ 2 P`. -/

/-- **B1: Simple integral against compensated Poisson `Ñ` (renamed alias).**

This is the standard `simpleIntegral` in this namespace, exposed under the
roadmap's explicit name `simpleIntegral_compensatedPoisson`. Mathematical
content:
`∫ g dÑ := ∑_i ξ_i · Ñ((t_i, t_{i+1}] × A_i)`
where `Ñ(B) := N(B) − ν̂(B)` is the compensated random measure
(`PoissonRandomMeasure.compensated`); equivalently
`∫ g dÑ = ∫ g dN − ∫ g(z) ν(dz) dt` for simple `g`. -/
@[reducible] noncomputable def simpleIntegral_compensatedPoisson
    {P : Measure Ω} [IsProbabilityMeasure P]
    {ν : Measure E} [SigmaFinite ν]
    (N : LevyStochCalc.Poisson.PoissonRandomMeasure P ν)
    {T : ℝ} (φ : SimplePredictable Ω E ν T) (t : ℝ) (ω : Ω) : ℝ :=
  simpleIntegral N φ t ω
end LevyStochCalc.Poisson.Compensated


