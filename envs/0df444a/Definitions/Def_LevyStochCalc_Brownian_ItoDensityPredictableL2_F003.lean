-- Prove2me | Definitions.Def_LevyStochCalc_Brownian_ItoDensityPredictableL2_F003
-- name    : LevyStochCalc_Brownian_ItoDensityPredictableL2_F003
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-20T15:43:25.014361+00:00
-- url     : https://prove2.me/theorems/1d92415f-bd60-4baa-895b-f08f88152bc0
-- title:
--   Source declarations: LevyStochCalc.Brownian.ItoDensityPredictableL2
-- statement:
--   Source-preserving extracted declarations from LevyStochCalc.Brownian.ItoDensityPredictableL2. Existing definitions, lemmas, instances, proofs and elaboration context are retained; generated import closure remains under review.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Brownian_ItoDensityPointwise_F000
import Definitions.Def_SourceProof_4d8cba1d4063b809a3d381bd
import Definitions.Def_SourceProof_5731c142c22a48f56440eba3
import Definitions.Def_SourceProof_6f312b3c41a43c93c4f0c9a1

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

-- maxHeartbeats: triangle-inequality lift through nested lintegrals + Tonelli.

/-- **L²-Cauchy of `predictableDyadicSimple_brownian` evals.** Direct corollary of
`predictableDyadicSimple_brownian_L2_converges` + `L2_cauchy_of_L2_tendsto_brownian`. -/
lemma predictableDyadicSimple_brownian_L2_cauchy
    {P : Measure Ω} [IsProbabilityMeasure P]
    {T : ℝ} (hT : 0 < T)
    (g : Ω → ℝ → ℝ)
    (h_meas : Measurable (Function.uncurry g))
    (M : ℝ) (h_bound : ∀ ω s, |g ω s| ≤ M) :
    ∀ ε : ℝ≥0∞, 0 < ε → ∃ N : ℕ, ∀ n m : ℕ, N ≤ n → N ≤ m →
      ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
        (‖(predictableDyadicSimple_brownian hT g h_meas M h_bound n).eval s ω -
          (predictableDyadicSimple_brownian hT g h_meas M h_bound m).eval s ω‖₊
          : ℝ≥0∞) ^ 2
          ∂volume ∂P < ε :=
  _root_.Prove2MeSourceProof.h_6f312b3c41a43c93c4f0c9a1
    (fun n => predictableDyadicSimple_brownian hT g h_meas M h_bound n) g
    (fun n => _root_.Prove2MeSourceProof.h_4d8cba1d4063b809a3d381bd hT g h_meas M
      h_bound n)
    h_meas
    (_root_.Prove2MeSourceProof.h_5731c142c22a48f56440eba3 hT g h_meas M h_bound)
end LevyStochCalc.Brownian.Ito


