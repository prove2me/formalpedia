-- Prove2me | Definitions.Def_LevyStochCalc_Poisson_CompensatedMartingaleQuadratic_F001
-- name    : LevyStochCalc_Poisson_CompensatedMartingaleQuadratic_F001
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-19T17:10:34.921185+00:00
-- url     : https://prove2.me/theorems/d49d0957-7451-43cc-8469-be97bf08a1ec
-- title:
--   Source declarations: LevyStochCalc.Poisson.CompensatedMartingaleQuadratic
-- statement:
--   Source-preserving extracted declarations from LevyStochCalc.Poisson.CompensatedMartingaleQuadratic. Existing definitions, lemmas, instances, proofs and elaboration context are retained; generated import closure remains under review.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Poisson_CompensatedMartingaleIncrement_F000
import Definitions.Def_LevyStochCalc_Poisson_CompensatedMartingaleIncrement_F001

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# Quadratic-variation martingale of the compensated simple integral

The set-level weighted isometry `∫ g·(Iₜ − Iₛ)² = ∑_i ν̂(Rᵢ).toReal · ∫ g·ξᵢ²` over the
increment boxes `Rᵢ = timeRect i t \ timeRect i s`, membership of `simpleIntegral N φ t` in
`L²(P)` at every running time, its vanishing at nonpositive times, and the resulting
martingale property of the compensated square
`t ↦ (simpleIntegral N φ t)² − ∫₀ᵗ ∫_E |φ(s,e)|² ν(de) ds` with respect to a Poisson
filtration; also the joint measurability of the simple integrand `eval` in `(s, e, ω)`.
-/

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace LevyStochCalc.Poisson.Compensated

universe u v

variable {Ω : Type u} [MeasurableSpace Ω]
variable {E : Type v} [MeasurableSpace E]

/-- **Joint measurability of the simple integrand `eval`** in `(s, e, ω)`. A finite
sum of indicators of the measurable time-mark rectangles, with measurable coefficients.
Needed for the `L²(P ⊗ ds ⊗ ν)` norm computations of the density layer. -/
lemma SimplePredictable.eval_jointly_measurable
    {ν : Measure E} [SigmaFinite ν] {T : ℝ} (φ : SimplePredictable Ω E ν T) :
    Measurable (fun p : ℝ × E × Ω => φ.eval p.1 p.2.1 p.2.2) := by
  unfold SimplePredictable.eval
  refine Finset.measurable_sum _ (fun i _ => ?_)
  refine Measurable.ite ?_ ((φ.ξ_measurable i).comp (measurable_snd.comp measurable_snd))
    measurable_const
  exact MeasurableSet.inter (measurable_fst measurableSet_Ioi)
    (MeasurableSet.inter (measurable_fst measurableSet_Iic)
      ((measurable_fst.comp measurable_snd) (φ.A_measurable i)))
end LevyStochCalc.Poisson.Compensated


