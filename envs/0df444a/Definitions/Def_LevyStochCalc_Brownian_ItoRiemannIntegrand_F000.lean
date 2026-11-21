-- Prove2me | Definitions.Def_LevyStochCalc_Brownian_ItoRiemannIntegrand_F000
-- name    : LevyStochCalc_Brownian_ItoRiemannIntegrand_F000
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-20T19:15:06.928187+00:00
-- url     : https://prove2.me/theorems/e11ca94d-5fd4-4536-9e53-010b756c7c96
-- title:
--   Source declarations: LevyStochCalc.Brownian.ItoRiemannIntegrand
-- statement:
--   Source-preserving extracted declarations from LevyStochCalc.Brownian.ItoRiemannIntegrand. Existing definitions, lemmas, instances, proofs and elaboration context are retained; generated import closure remains under review.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Brownian_ItoIncrementMomentBounds_F000
import Definitions.Def_LevyStochCalc_Brownian_ItoIncrementMomentBounds_F001
import Definitions.Def_LevyStochCalc_Brownian_ItoIncrementMomentBounds_F002
import Definitions.Def_LevyStochCalc_Brownian_ItoIncrementMomentRestrict_F000
import Definitions.Def_LevyStochCalc_Brownian_ItoIncrementMomentRestrict_F001
import Definitions.Def_SourceProof_f7873a967b51c0099c698616

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# Riemann sums of the Itô integral against a step weight

Summing the increments of the `L²` Itô integral of `H` across the cells of a partition, weighted
by coefficients frozen at the left endpoints, gives the `L²` Itô integral of the product of the
step weight with `H`; and replacing the step weight by a general integrand costs, in `L²`, the
`L²` distance between them times the bound on `H`.

## Main statements

* `LevyStochCalc.Brownian.Ito.SimplePredictable.integralAgainst_eq_sum` — past the last
  partition point the elementary integral against a process is the plain weighted sum of its
  increments.
* `LevyStochCalc.Brownian.Ito.sum_xi_mul_stochasticIntegral_sub_ae` — that sum is the `L²` Itô
  integral of the product.
* `LevyStochCalc.Brownian.Ito.lintegral_sq_stochasticIntegral_mul_sub_le` — the `L²` distance
  between the two products is controlled by the `L²` distance between the weights.
-/

namespace LevyStochCalc.Brownian.Ito

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

universe u

variable {Ω : Type u} [MeasurableSpace Ω]

/-- Past the last partition point, the elementary integral of a simple integrand against a
process is the weighted sum of the process's increments across the cells. -/
theorem SimplePredictable.integralAgainst_eq_sum {T : ℝ} (G : SimplePredictable Ω T)
    (M : ℝ → Ω → ℝ) {t : ℝ} (ht : G.partition (Fin.last G.N) ≤ t) (ω : Ω) :
    G.integralAgainst M t ω
      = ∑ i : Fin G.N, G.ξ i ω
        * (M (G.partition i.succ) ω - M (G.partition i.castSucc) ω) := by
  unfold SimplePredictable.integralAgainst
  refine Finset.sum_congr rfl fun i _ => ?_
  have h1 : G.partition i.succ ≤ t :=
    le_trans (G.partition_strictMono.monotone (Fin.le_last _)) ht
  have h2 : G.partition i.castSucc ≤ t :=
    le_of_lt ((G.partition_strictMono Fin.castSucc_lt_succ).trans_le h1)
  rw [min_eq_left h1, min_eq_left h2]
section Riemann

variable {P : Measure Ω} [IsProbabilityMeasure P] (W : LevyStochCalc.Brownian.BrownianMotion P)
  (ℱ : Filtration ℝ ‹MeasurableSpace Ω›) (hℱ : IsBrownianFiltration W ℱ)
  {T₀ : ℝ} (G : SimplePredictable Ω T₀)
  (h_adapt : ∀ i : Fin G.N, @MeasureTheory.StronglyMeasurable Ω ℝ _
    (ℱ (G.partition i.castSucc)) (G.ξ i))
  (H : Ω → ℝ → ℝ) (hm : Measurable (Function.uncurry H))
  (hp : Probability.ProgressivelyMeasurable ℱ H)
  (hq : ∀ T, 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
    (‖H ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
  (hmm : Measurable (Function.uncurry fun ω s => G.eval s ω * H ω s))
  (hmp : Probability.ProgressivelyMeasurable ℱ fun ω s => G.eval s ω * H ω s)
  (hmq : ∀ T, 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
    (‖G.eval s ω * H ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)

include hℱ h_adapt in
/-- **The weighted sum of the Itô integral's increments is an Itô integral.** -/
theorem sum_xi_mul_stochasticIntegral_sub_ae {t : ℝ} (ht : 0 < t)
    (hlast : G.partition (Fin.last G.N) ≤ t) :
    (fun ω => ∑ i : Fin G.N, G.ξ i ω
        * (stochasticIntegralBrownian W ℱ hℱ H hm hp hq (G.partition i.succ) ω
          - stochasticIntegralBrownian W ℱ hℱ H hm hp hq (G.partition i.castSucc) ω))
      =ᵐ[P] stochasticIntegralBrownian W ℱ hℱ (fun ω s => G.eval s ω * H ω s) hmm hmp hmq t := by
  have hkey := _root_.Prove2MeSourceProof.h_f7873a967b51c0099c698616 W ℱ hℱ G h_adapt H hm hp hq
    hmm hmp hmq ht
  refine Filter.EventuallyEq.trans (Filter.Eventually.of_forall fun ω => ?_) hkey
  exact (G.integralAgainst_eq_sum (stochasticIntegralBrownian W ℱ hℱ H hm hp hq) hlast ω).symm
end Riemann

section Comparison

variable {P : Measure Ω} [IsProbabilityMeasure P] (W : LevyStochCalc.Brownian.BrownianMotion P)
  (ℱ : Filtration ℝ ‹MeasurableSpace Ω›) (hℱ : IsBrownianFiltration W ℱ)
  (H : Ω → ℝ → ℝ) (hm : Measurable (Function.uncurry H))
  (hp : Probability.ProgressivelyMeasurable ℱ H)
  (hq : ∀ T, 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
    (‖H ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)

end Comparison

end LevyStochCalc.Brownian.Ito


