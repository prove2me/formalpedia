-- Prove2me | Definitions.Def_LevyStochCalc_Brownian_PRPPerpBridge_F000
-- name    : LevyStochCalc_Brownian_PRPPerpBridge_F000
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-20T19:31:59.641412+00:00
-- url     : https://prove2.me/theorems/e95ebc60-e185-4b8b-ac11-25f4a68e2c7e
-- title:
--   Source declarations: LevyStochCalc.Brownian.PRPPerpBridge
-- statement:
--   Source-preserving extracted declarations from LevyStochCalc.Brownian.PRPPerpBridge. Existing definitions, lemmas, instances, proofs and elaboration context are retained; generated import closure remains under review.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Brownian_ItoIncrementMomentBounds_F001
import Definitions.Def_LevyStochCalc_Brownian_ItoIncrementMomentBounds_F002
import Definitions.Def_LevyStochCalc_Brownian_PRPMultidimRange_F000
import Definitions.Def_SourceProof_371bbffaec7b2a5d68568212
import Definitions.Def_SourceProof_39285c9e8cb91346b858af97

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

/-- An admissible integrand clipped to `(0, t]`, as an integrand over the horizon `[0, T]`. -/
noncomputable def clipHorizonIntegrand (K : Ω → ℝ → ℝ)
    (hm : Measurable (Function.uncurry K))
    (hp : Probability.ProgressivelyMeasurable ℱ K)
    (hq : ∀ T' : ℝ, 0 < T' → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T',
      (‖K ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
    {t T : ℝ} (ht : 0 < t) (htT : t ≤ T) : HorizonIntegrand P ℱ T where
  toFun := fun ω s => (Set.Ioc (0 : ℝ) t).indicator (fun _ => (1 : ℝ)) s * K ω s
  measurable_uncurry := measurable_uncurry_indicator_Ioc_mul K hm 0 t
  progressive := progressivelyMeasurable_indicator_Ioc_mul ℱ K hp 0 t
  vanishing := by
    intro ω s hs
    have hns : s ∉ Set.Ioc (0 : ℝ) t := fun h => hs ⟨h.1.le, h.2.trans htT⟩
    rw [Set.indicator_of_notMem hns, zero_mul]
  energy_ne_top := by
    exact (lintegral_sq_indicator_Ioc_mul_lt_top K hq 0 t T (ht.trans_le htT)).ne
/-- The clipped integrand's integral over the horizon is the integral up to the clipping time. -/
theorem integral_clipHorizonIntegrand (V : LevyStochCalc.Brownian.BrownianMotion P)
    (hℱ : IsBrownianFiltration V ℱ) (K : Ω → ℝ → ℝ) (hm : Measurable (Function.uncurry K))
    (hp : Probability.ProgressivelyMeasurable ℱ K)
    (hq : ∀ T' : ℝ, 0 < T' → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T',
      (‖K ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
    {t T : ℝ} (ht : 0 < t) (htT : t ≤ T) :
    (clipHorizonIntegrand K hm hp hq ht htT).integral V hℱ
      =ᵐ[P] stochasticIntegralBrownian V ℱ hℱ K hm hp hq t := by
  have hT : (0 : ℝ) < T := ht.trans_le htT
  have hcoe : (clipHorizonIntegrand K hm hp hq ht htT).integral V hℱ
      = stochasticIntegralBrownian V ℱ hℱ
        (fun ω s => (Set.Ioc (0 : ℝ) t).indicator (fun _ => (1 : ℝ)) s * K ω s)
        (measurable_uncurry_indicator_Ioc_mul K hm 0 t)
        (progressivelyMeasurable_indicator_Ioc_mul ℱ K hp 0 t)
        (lintegral_sq_indicator_Ioc_mul_lt_top K hq 0 t) T := rfl
  have hind := _root_.Prove2MeSourceProof.h_371bbffaec7b2a5d68568212 V ℱ hℱ K hm hp hq (le_refl (0 : ℝ)) ht
    (measurable_uncurry_indicator_Ioc_mul K hm 0 t)
    (progressivelyMeasurable_indicator_Ioc_mul ℱ K hp 0 t)
    (lintegral_sq_indicator_Ioc_mul_lt_top K hq 0 t) hT
  have hz := _root_.Prove2MeSourceProof.h_39285c9e8cb91346b858af97 V ℱ hℱ K hm hp hq (le_refl (0 : ℝ))
  rw [hcoe]
  filter_upwards [hind, hz] with ω e1 e2
  rw [e1, min_eq_left htT, min_eq_left hT.le, e2, Pi.zero_apply, sub_zero]
omit [IsProbabilityMeasure P] in
/-- A product of two square-integrable functions is integrable. -/
lemma integrable_mul_of_memLp_two {f g : Ω → ℝ} (hf : MemLp f 2 P) (hg : MemLp g 2 P) :
    Integrable (fun ω => f ω * g ω) P := by
  have hdom : Integrable (fun ω => 1 / 2 * f ω ^ 2 + 1 / 2 * g ω ^ 2) P :=
    (hf.integrable_sq.const_mul (1 / 2 : ℝ)).add (hg.integrable_sq.const_mul (1 / 2 : ℝ))
  refine Integrable.mono' hdom (hf.1.mul hg.1) ?_
  filter_upwards with ω
  rw [Real.norm_eq_abs, abs_mul]
  nlinarith [sq_abs (f ω), sq_abs (g ω), sq_nonneg (|f ω| - |g ω|)]
end LevyStochCalc.Brownian.Ito


