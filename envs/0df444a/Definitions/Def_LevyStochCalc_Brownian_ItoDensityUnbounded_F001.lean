-- Prove2me | Definitions.Def_LevyStochCalc_Brownian_ItoDensityUnbounded_F001
-- name    : LevyStochCalc_Brownian_ItoDensityUnbounded_F001
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-20T16:11:47.313796+00:00
-- url     : https://prove2.me/theorems/1b5b4b70-ea1e-4b4d-8fe1-cbac1a512a2b
-- title:
--   Source declarations: LevyStochCalc.Brownian.ItoDensityUnbounded
-- statement:
--   Source-preserving extracted declarations from LevyStochCalc.Brownian.ItoDensityUnbounded. Existing definitions, lemmas, instances, proofs and elaboration context are retained; generated import closure remains under review.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Brownian_ItoDensityPredictableL2_F000
import Definitions.Def_LevyStochCalc_Brownian_ItoDensityPredictableL2_F001
import Definitions.Def_LevyStochCalc_Brownian_ItoDensityPredictableL2_F002
import Definitions.Def_LevyStochCalc_Brownian_ItoDensityPredictableL2_F003
import Definitions.Def_SourceProof_cd0c957e24cb795d7143dc2e

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# Density of the simple predictable processes in `L²`

Removal of the boundedness restriction by truncation: the `eLpNorm`/`lintegral`
dictionary on the product measure, and the density results `simplePredictable_dense_L2`
and `adaptedSimple_dense_L2_brownian` for an arbitrary square-integrable integrand.
-/

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal
-- `open Classical` is avoided at file scope; explicit decidability is used.

namespace LevyStochCalc.Brownian.Ito

universe u

variable {Ω : Type u} [MeasurableSpace Ω]

/-- **Bounded dyadic eval lintegral_sq tendsto.** Specialization of
`lintegral_sq_eval_tendsto_of_diff_tendsto_zero_brownian` to the
`predictableDyadicSimple_brownian` sequence (bounded `g` case). -/
lemma predictableDyadicSimple_brownian_eval_norm_tendsto_bounded
    {P : Measure Ω} [IsProbabilityMeasure P]
    {T : ℝ} (hT : 0 < T)
    (g : Ω → ℝ → ℝ)
    (h_meas : Measurable (Function.uncurry g))
    (M : ℝ) (h_bound : ∀ ω s, |g ω s| ≤ M) :
    Filter.Tendsto
      (fun n => ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
        (‖(predictableDyadicSimple_brownian hT g h_meas M h_bound n).eval s ω‖₊
          : ℝ≥0∞) ^ 2 ∂volume ∂P)
      Filter.atTop
      (nhds (∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
        (‖g ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P)) :=
  _root_.Prove2MeSourceProof.h_cd0c957e24cb795d7143dc2e (μ := P) (T := T) g h_meas
    (fun n => (predictableDyadicSimple_brownian hT g h_meas M h_bound n).eval)
    (fun n => _root_.Prove2MeSourceProof.h_4d8cba1d4063b809a3d381bd hT g h_meas
      M h_bound n)
    (_root_.Prove2MeSourceProof.h_5731c142c22a48f56440eba3 (P := P) hT g h_meas M h_bound)
-- maxHeartbeats: triangle-inequality lift through nested lintegrals + Tonelli.

-- maxHeartbeats: triangle-inequality lift through nested lintegrals + Tonelli.

end LevyStochCalc.Brownian.Ito


