-- Prove2me | Definitions.Def_SourceProof_4d8cba1d4063b809a3d381bd
-- name    : SourceProof_4d8cba1d4063b809a3d381bd
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-20T15:11:24.73435+00:00
-- url     : https://prove2.me/theorems/234c0273-c925-4887-ad1c-da2c70a081c9
-- title:
--   LevyStochCalc source module: SourceProof_4d8cba1d4063b809a3d381bd
-- statement:
--   The original source theorem `LevyStochCalc.Brownian.Ito.predictableDyadicSimple_brownian_eval_jointly_measurable` comes from the `LevyStochCalc.Brownian.ItoDensityPredictableL2` module. The staged Lean declaration includes its source proof and dependency references.
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


theorem _root_.Prove2MeSourceProof.h_4d8cba1d4063b809a3d381bd
    {T : ℝ} (hT : 0 < T) (g : Ω → ℝ → ℝ)
    (h_meas : Measurable (Function.uncurry g))
    (M : ℝ) (h_bound : ∀ ω s, |g ω s| ≤ M) (n : ℕ) :
    Measurable (fun (p : Ω × ℝ) =>
      (predictableDyadicSimple_brownian hT g h_meas M h_bound n).eval p.2 p.1) := by
  unfold LevyStochCalc.Brownian.Ito.SimplePredictable.eval
  refine Finset.measurable_sum _ ?_
  intro i _
  refine Measurable.ite ?_ ?_ measurable_const
  · refine MeasurableSet.inter ?_ ?_
    · exact measurable_snd (measurableSet_Ioi
        (a := (LevyStochCalc.Brownian.Ito.predictableDyadicSimple_brownian hT g h_meas M h_bound n).partition
          i.castSucc))
    · exact measurable_snd (measurableSet_Iic
        (a := (LevyStochCalc.Brownian.Ito.predictableDyadicSimple_brownian hT g h_meas M h_bound n).partition
          i.succ))
  · exact (LevyStochCalc.Brownian.Ito.dyadicAvg_shifted_brownian_measurable T g h_meas n i).comp measurable_fst
-- maxHeartbeats: triangle-inequality lift through nested lintegrals + Tonelli.

end LevyStochCalc.Brownian.Ito


