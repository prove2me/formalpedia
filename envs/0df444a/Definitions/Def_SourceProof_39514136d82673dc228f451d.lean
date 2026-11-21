-- Prove2me | Definitions.Def_SourceProof_39514136d82673dc228f451d
-- name    : SourceProof_39514136d82673dc228f451d
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-20T19:16:37.815176+00:00
-- url     : https://prove2.me/theorems/ea091609-7c29-4650-b50c-7e37ff664166
-- title:
--   LevyStochCalc source module: SourceProof_39514136d82673dc228f451d
-- statement:
--   The original source theorem `LevyStochCalc.Brownian.Ito.lintegral_sq_stochasticIntegral_mul_sub_le` comes from the `LevyStochCalc.Brownian.ItoRiemannIntegrand` module. The staged Lean declaration includes its source proof and dependency references.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Brownian_ItoIncrementMomentBounds_F001
import Definitions.Def_LevyStochCalc_Brownian_ItoIncrementMomentBounds_F002
import Definitions.Def_SourceProof_9ab1096355abba8f677466b8

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

end Riemann

section Comparison

variable {P : Measure Ω} [IsProbabilityMeasure P] (W : LevyStochCalc.Brownian.BrownianMotion P)
  (ℱ : Filtration ℝ ‹MeasurableSpace Ω›) (hℱ : IsBrownianFiltration W ℱ)
  (H : Ω → ℝ → ℝ) (hm : Measurable (Function.uncurry H))
  (hp : Probability.ProgressivelyMeasurable ℱ H)
  (hq : ∀ T, 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
    (‖H ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)

include hℱ in

theorem _root_.Prove2MeSourceProof.h_39514136d82673dc228f451d
    (u v : Ω → ℝ → ℝ)
    (hmu : Measurable (Function.uncurry fun ω s => u ω s * H ω s))
    (hpu : Probability.ProgressivelyMeasurable ℱ fun ω s => u ω s * H ω s)
    (hqu : ∀ T, 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
      (‖u ω s * H ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
    (hmv : Measurable (Function.uncurry fun ω s => v ω s * H ω s))
    (hpv : Probability.ProgressivelyMeasurable ℱ fun ω s => v ω s * H ω s)
    (hqv : ∀ T, 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
      (‖v ω s * H ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
    {C : ℝ} (hC0 : 0 ≤ C) (hCH : ∀ ω s, |H ω s| ≤ C)
    {T : ℝ} (hT : 0 < T) :
    ∫⁻ ω, (‖stochasticIntegralBrownian W ℱ hℱ (fun ω s => u ω s * H ω s) hmu hpu hqu T ω
        - stochasticIntegralBrownian W ℱ hℱ (fun ω s => v ω s * H ω s) hmv hpv hqv T ω‖₊
          : ℝ≥0∞) ^ 2 ∂P
      ≤ ENNReal.ofReal (C ^ 2)
        * ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, (‖u ω s - v ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P := by
  rw [_root_.Prove2MeSourceProof.h_9ab1096355abba8f677466b8 W ℱ hℱ _ _ hmu hmv hpu hpv hqu hqv hT]
  rw [← MeasureTheory.lintegral_const_mul' _ _ (by simp : ENNReal.ofReal (C ^ 2) ≠ ⊤)]
  refine lintegral_mono fun ω => ?_
  rw [← MeasureTheory.lintegral_const_mul' _ _ (by simp : ENNReal.ofReal (C ^ 2) ≠ ⊤)]
  refine lintegral_mono fun s => ?_
  have hfac : u ω s * H ω s - v ω s * H ω s = (u ω s - v ω s) * H ω s := by ring
  rw [hfac]
  have hnn : (‖(u ω s - v ω s) * H ω s‖₊ : ℝ≥0∞) ^ 2
      = (‖u ω s - v ω s‖₊ : ℝ≥0∞) ^ 2 * (‖H ω s‖₊ : ℝ≥0∞) ^ 2 := by
    rw [nnnorm_mul, ENNReal.coe_mul, mul_pow]
  rw [hnn, mul_comm (ENNReal.ofReal (C ^ 2))]
  refine mul_le_mul_right ?_ _
  have h1 : (‖H ω s‖₊ : ℝ≥0∞) ≤ ENNReal.ofReal C := by
    rw [ENNReal.ofReal_eq_coe_nnreal hC0]
    refine ENNReal.coe_le_coe.mpr ?_
    rw [← NNReal.coe_le_coe]
    simpa [Real.norm_eq_abs] using hCH ω s
  calc (‖H ω s‖₊ : ℝ≥0∞) ^ 2 ≤ ENNReal.ofReal C ^ 2 := pow_le_pow_left' h1 2
    _ = ENNReal.ofReal (C ^ 2) := (ENNReal.ofReal_pow hC0 2).symm
end Comparison

end LevyStochCalc.Brownian.Ito


