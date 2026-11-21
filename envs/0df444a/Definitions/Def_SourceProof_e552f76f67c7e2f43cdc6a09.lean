-- Prove2me | Definitions.Def_SourceProof_e552f76f67c7e2f43cdc6a09
-- name    : SourceProof_e552f76f67c7e2f43cdc6a09
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-20T19:39:19.000609+00:00
-- url     : https://prove2.me/theorems/60865016-5bb0-4704-bbf4-cf22f4c82e1c
-- title:
--   LevyStochCalc source module: SourceProof_e552f76f67c7e2f43cdc6a09
-- statement:
--   The original source theorem `LevyStochCalc.Brownian.Ito.integral_mul_stochasticIntegral_eq_zero` comes from the `LevyStochCalc.Brownian.PRPPerpBridge` module. The staged Lean declaration includes its source proof and dependency references.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_SourceProof_21680fbb00c3cbdc68b476b2

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# From horizon orthogonality to orthogonality against every Itô integral

A weight orthogonal to the Itô integrals of integrands supported in `[0, T]` is orthogonal to
`∫_0^t K dW` for every admissible `K` and every `t > 0`. For `t ≤ T` this is because `K` clipped
to `(0, t]` is such an integrand and its integral over the horizon is `∫_0^t K dW`; for `t > T`
the remaining increment is a martingale increment after `T`, which a weight measurable before `T`
does not see.
-/

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace LevyStochCalc.Brownian.Ito

universe u

variable {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {ℱ : Filtration ℝ ‹MeasurableSpace Ω›}


theorem _root_.Prove2MeSourceProof.h_e552f76f67c7e2f43cdc6a09 (V : LevyStochCalc.Brownian.BrownianMotion P)
    (hℱ : IsBrownianFiltration V ℱ) {T : ℝ} (hT : 0 < T) {z : Ω → ℝ} (hz2 : MemLp z 2 P)
    (hzm : AEStronglyMeasurable[ℱ T] z P)
    (hperp : ∀ G : HorizonIntegrand P ℱ T, ∫ ω, z ω * G.integral V hℱ ω ∂P = 0)
    (K : Ω → ℝ → ℝ) (hm : Measurable (Function.uncurry K))
    (hp : Probability.ProgressivelyMeasurable ℱ K)
    (hq : ∀ T' : ℝ, 0 < T' → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T',
      (‖K ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
    {t : ℝ} (ht : 0 < t) :
    ∫ ω, z ω * stochasticIntegralBrownian V ℱ hℱ K hm hp hq t ω ∂P = 0 := by
  have hclip : ∀ {u : ℝ}, 0 < u → u ≤ T →
      ∫ ω, z ω * LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian V ℱ hℱ K hm hp hq u ω ∂P = 0 := by
    intro u hu huT
    have h := hperp (LevyStochCalc.Brownian.Ito.clipHorizonIntegrand K hm hp hq hu huT)
    rw [← h]
    refine integral_congr_ae ?_
    filter_upwards [LevyStochCalc.Brownian.Ito.integral_clipHorizonIntegrand V hℱ K hm hp hq hu huT] with ω e
    rw [e]
  rcases le_or_gt t T with htT | hTt
  · exact hclip ht htT
  · have hMLp : ∀ u : ℝ, MemLp (LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian V ℱ hℱ K hm hp hq u) 2 P := fun u =>
      LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian_memLp V ℱ hℱ K hm hp hq u
    have h2 := _root_.Prove2MeSourceProof.h_21680fbb00c3cbdc68b476b2 V hℱ K hm hp hq hz2 hzm hTt.le (t := t)
    have hint1 : Integrable
        (fun ω => z ω * LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian V ℱ hℱ K hm hp hq T ω) P :=
      LevyStochCalc.Brownian.Ito.integrable_mul_of_memLp_two hz2 (hMLp T)
    have hint2 : Integrable (fun ω => z ω * (LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian V ℱ hℱ K hm hp hq t ω
        - LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian V ℱ hℱ K hm hp hq T ω)) P :=
      LevyStochCalc.Brownian.Ito.integrable_mul_of_memLp_two hz2 ((hMLp t).sub (hMLp T))
    have hrw : (fun ω => z ω * LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian V ℱ hℱ K hm hp hq t ω)
        = fun ω => z ω * LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian V ℱ hℱ K hm hp hq T ω
          + z ω * (LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian V ℱ hℱ K hm hp hq t ω
            - LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian V ℱ hℱ K hm hp hq T ω) := by
      funext ω; ring
    rw [show (∫ ω, z ω * LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian V ℱ hℱ K hm hp hq t ω ∂P)
        = ∫ ω, (z ω * LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian V ℱ hℱ K hm hp hq T ω
          + z ω * (LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian V ℱ hℱ K hm hp hq t ω
            - LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian V ℱ hℱ K hm hp hq T ω)) ∂P from by rw [hrw],
      integral_add hint1 hint2, hclip hT (le_refl T), h2, add_zero]
end LevyStochCalc.Brownian.Ito


