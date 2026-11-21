-- Prove2me | Definitions.Def_LevyStochCalc_Brownian_ItoMartingale_F001
-- name    : LevyStochCalc_Brownian_ItoMartingale_F001
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-20T16:14:31.118095+00:00
-- url     : https://prove2.me/theorems/8ad419fc-c705-468f-93fa-a904221f3605
-- title:
--   Source declarations: LevyStochCalc.Brownian.ItoMartingale
-- statement:
--   Source-preserving extracted declarations from LevyStochCalc.Brownian.ItoMartingale. Existing definitions, lemmas, instances, proofs and elaboration context are retained; generated import closure remains under review.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Brownian_ItoDensityUnbounded_F000
import Definitions.Def_LevyStochCalc_Brownian_ItoDensityUnbounded_F001
import Definitions.Def_SourceProof_1199f50b2446ab81aa9b8339

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# Martingale property of the simple Brownian integral

`simpleIntegral W H` is a martingale w.r.t. any filtration `ℱ` for which `W` is a
Brownian motion and `H` is adapted (`martingale_simpleIntegral_brownian`), via the
conditional-expectation identity for `W`. Builds on `Brownian/ItoSimple.lean` and
`Brownian/ItoDensity.lean`.
-/

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal
-- `open Classical` is avoided at file scope; explicit decidability is used.

namespace LevyStochCalc.Brownian.Ito

universe u

variable {Ω : Type u} [MeasurableSpace Ω]

/-- **C0a: Density of simple Brownian-predictable processes in `L²(Ω × [0, T])`.**
For every `H ∈ L²(Ω × [0, T], dP ⊗ ds)`, there exists a sequence of
`SimplePredictable` integrands whose `eval`s converge to `H` in
`L²(P ⊗ ds)`-norm. Public re-export of the existing
`simplePredictable_dense_L2` under the roadmap's name. -/
theorem simplePredictable_dense_Lp_brownian
    {P : Measure Ω} [IsProbabilityMeasure P]
    {T : ℝ} (hT : 0 < T)
    (H : Ω → ℝ → ℝ) (h_meas : Measurable (Function.uncurry H))
    (h_sq_int : ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
      (‖H ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤) :
    ∃ Hn : ℕ → SimplePredictable Ω T,
      Filter.Tendsto
        (fun n => ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
          (‖H ω s - (Hn n).eval s ω‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P)
        Filter.atTop (nhds 0) :=
  _root_.Prove2MeSourceProof.h_1199f50b2446ab81aa9b8339 hT H h_meas h_sq_int
end LevyStochCalc.Brownian.Ito


