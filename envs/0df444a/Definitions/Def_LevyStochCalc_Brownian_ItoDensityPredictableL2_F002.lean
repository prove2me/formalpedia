-- Prove2me | Definitions.Def_LevyStochCalc_Brownian_ItoDensityPredictableL2_F002
-- name    : LevyStochCalc_Brownian_ItoDensityPredictableL2_F002
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-20T12:21:57.437881+00:00
-- url     : https://prove2.me/theorems/e8acf5a4-28d6-4a9d-9abc-8616fde8335a
-- title:
--   Source declarations: LevyStochCalc.Brownian.ItoDensityPredictableL2
-- statement:
--   Source-preserving extracted declarations from LevyStochCalc.Brownian.ItoDensityPredictableL2. Existing definitions, lemmas, instances, proofs and elaboration context are retained; generated import closure remains under review.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Brownian_ItoDensityPointwise_F000

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# `L²` convergence of the predictable dyadic approximations

For a bounded jointly measurable integrand the left-shifted dyadic simple processes
converge to it in `L²(Ω × [0,T])`, giving density of the simple predictable processes and
of the adapted simple processes in the bounded case, joint measurability of the evaluation
map and the `L²` Cauchy property of the approximating sequence.
-/

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal
-- `open Classical` is avoided at file scope; explicit decidability is used.

namespace LevyStochCalc.Brownian.Ito

universe u

variable {Ω : Type u} [MeasurableSpace Ω]

/-- **Generic joint measurability of `SimplePredictable.eval`.** For any
`SimplePredictable Ω T`, the function `(p : Ω × ℝ) ↦ H.eval p.2 p.1` is measurable.

Proof: `eval` is a finite sum of indicator-times-coefficient terms, each measurable
since the indicator's set is `{p | partition i.castSucc < p.2 ≤ partition i.succ}`
(measurable in `snd`) and the coefficient is `H.ξ i ∘ fst` (measurable since
`H.ξ_measurable i`). -/
lemma SimplePredictable.eval_jointly_measurable
    {T : ℝ} (H : SimplePredictable Ω T) :
    Measurable (fun (p : Ω × ℝ) => H.eval p.2 p.1) := by
  unfold SimplePredictable.eval
  refine Finset.measurable_sum _ ?_
  intro i _
  refine Measurable.ite ?_ ?_ measurable_const
  · refine MeasurableSet.inter ?_ ?_
    · exact measurable_snd (measurableSet_Ioi (a := H.partition i.castSucc))
    · exact measurable_snd (measurableSet_Iic (a := H.partition i.succ))
  · exact (H.ξ_measurable i).comp measurable_fst
-- maxHeartbeats: triangle-inequality lift through nested lintegrals + Tonelli.

end LevyStochCalc.Brownian.Ito


