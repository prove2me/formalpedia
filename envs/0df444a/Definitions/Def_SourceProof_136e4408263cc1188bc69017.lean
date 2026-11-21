-- Prove2me | Definitions.Def_SourceProof_136e4408263cc1188bc69017
-- name    : SourceProof_136e4408263cc1188bc69017
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-20T19:40:15.316494+00:00
-- url     : https://prove2.me/theorems/a6b82f2b-8506-46dd-899d-2ec42acbbd6c
-- title:
--   LevyStochCalc source module: SourceProof_136e4408263cc1188bc69017
-- statement:
--   The original source theorem `LevyStochCalc.Brownian.Ito.IsItoVersion.lintegral_sq_martingaleRiemann_sub_le` comes from the `LevyStochCalc.Brownian.ItoMartingaleRiemann` module. The staged Lean declaration includes its source proof and dependency references.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_SourceProof_3b3636a20b20ac59ccdbdb27

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# The martingale Riemann sum of the Itô formula

Freezing a Lipschitz function of a continuous Itô process at the left endpoints of a uniform
grid and pairing it with the Itô integral's increments gives a Riemann sum for
`∫_0^T φ(X_s)·H_s dW_s`, with an `L²` error of order `√(T/m)`.

## Main statements

* `LevyStochCalc.Brownian.Ito.lintegral_sq_bounded_mul_lt_top` — a bounded weight preserves the
  `L²` bound on an integrand.
* `LevyStochCalc.Brownian.Ito.IsItoVersion.lintegral_sq_frozen_sub_le` — the `L²` distance
  between the frozen step weight and the weight itself.
* `LevyStochCalc.Brownian.Ito.IsItoVersion.lintegral_sq_martingaleRiemann_sub_le` — the `L²`
  error of the martingale Riemann sum.
-/

namespace LevyStochCalc.Brownian.Ito

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

universe u

variable {Ω : Type u} [MeasurableSpace Ω]

section Weight

variable {P : Measure Ω} [IsProbabilityMeasure P] {H : Ω → ℝ → ℝ}

end Weight

section Frozen

variable {P : Measure Ω} [IsProbabilityMeasure P] {W : LevyStochCalc.Brownian.BrownianMotion P}
  {ℱ : Filtration ℝ ‹MeasurableSpace Ω›} {hℱ : IsBrownianFiltration W ℱ}
  {H : Ω → ℝ → ℝ} {hm : Measurable (Function.uncurry H)}
  {hp : Probability.ProgressivelyMeasurable ℱ H}
  {hq : ∀ T, 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
    (‖H ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤}
  {X₀ : Ω → ℝ} {bdrift : Ω → ℝ → ℝ} {X : ℝ → Ω → ℝ}
  {C : ℝ} (hC0 : 0 ≤ C) (hCH : ∀ ω s, |H ω s| ≤ C)

include hC0 hCH in

theorem _root_.Prove2MeSourceProof.h_136e4408263cc1188bc69017
    (h : IsItoVersion W ℱ hℱ H hm hp hq X₀ bdrift X)
    (hbm : Measurable (Function.uncurry bdrift))
    {B : ℝ} (hB0 : 0 ≤ B) (hB : ∀ (ω : Ω) (s : ℝ), |bdrift ω s| ≤ B)
    {φ : ℝ → ℝ} {Kφ : ℝ} (hφbd : ∀ x, |φ x| ≤ Kφ)
    {L : ℝ} (hL0 : 0 ≤ L) (hφlip : ∀ x y : ℝ, |φ x - φ y| ≤ L * |x - y|)
    (hmg : Measurable (Function.uncurry fun ω s => φ (X s ω) * H ω s))
    (hpg : Probability.ProgressivelyMeasurable ℱ fun ω s => φ (X s ω) * H ω s)
    (hqg : ∀ T', 0 < T' → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T',
      (‖φ (X s ω) * H ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
    {T : ℝ} (hT : 0 < T) {m : ℕ} (hm0 : m ≠ 0) :
    ∫⁻ ω, (‖(∑ i : Fin m, φ (X (unifGrid T m (i : ℕ)) ω)
          * (stochasticIntegralBrownian W ℱ hℱ H hm hp hq
              (unifGrid T m ((i : ℕ) + 1)) ω
            - stochasticIntegralBrownian W ℱ hℱ H hm hp hq (unifGrid T m (i : ℕ)) ω))
        - stochasticIntegralBrownian W ℱ hℱ (fun ω s => φ (X s ω) * H ω s)
            hmg hpg hqg T ω‖₊ : ℝ≥0∞) ^ 2 ∂P
      ≤ ENNReal.ofReal (C ^ 2) * (ENNReal.ofReal (L ^ 2)
        * ENNReal.ofReal (T * (2 * (B * (T / (m : ℝ))) ^ 2
          + 2 * (C ^ 2 * (T / (m : ℝ)))))) := by
  have hφc : Continuous φ := by
    have hlip : LipschitzWith (Real.toNNReal L) φ := by
      refine LipschitzWith.of_dist_le_mul fun x y => ?_
      rw [Real.dist_eq, Real.dist_eq, Real.coe_toNNReal L hL0]
      exact hφlip x y
    exact hlip.continuous
  set ξ : Fin m → Ω → ℝ := fun i ω => φ (X (LevyStochCalc.Brownian.Ito.unifGrid T m (i : ℕ)) ω) with hξdef
  have hbdd : ∀ i : Fin m, ∃ M : ℝ, ∀ ω : Ω, |ξ i ω| ≤ M := fun i => ⟨Kφ, fun ω => hφbd _⟩
  have hmeas : ∀ i : Fin m, Measurable (ξ i) := fun i =>
    hφc.measurable.comp (h.measurable (LevyStochCalc.Brownian.Ito.unifGrid T m (i : ℕ)))
  have hadapt : ∀ i : Fin m, @MeasureTheory.StronglyMeasurable Ω ℝ _
      (ℱ (LevyStochCalc.Brownian.Ito.unifGrid T m (i : ℕ))) (ξ i) := fun i =>
    hφc.comp_stronglyMeasurable (h.adapted (LevyStochCalc.Brownian.Ito.unifGrid T m (i : ℕ)))
  have hstep := LevyStochCalc.Brownian.Ito.sum_unifGrid_mul_sub_ae W ℱ hℱ H hm hp hq hT hm0 ξ hbdd hmeas hadapt
  have hcongr : ∫⁻ ω, (‖(∑ i : Fin m, ξ i ω
          * (LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian W ℱ hℱ H hm hp hq
              (LevyStochCalc.Brownian.Ito.unifGrid T m ((i : ℕ) + 1)) ω
            - LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian W ℱ hℱ H hm hp hq (LevyStochCalc.Brownian.Ito.unifGrid T m (i : ℕ)) ω))
        - LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian W ℱ hℱ (fun ω s => φ (X s ω) * H ω s)
            hmg hpg hqg T ω‖₊ : ℝ≥0∞) ^ 2 ∂P
      = ∫⁻ ω, (‖LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian W ℱ hℱ
          (fun ω s => (LevyStochCalc.Brownian.Ito.SimplePredictable.ofUnifGrid hT hm0 ξ hbdd hmeas).eval s ω * H ω s)
          ((LevyStochCalc.Brownian.Ito.SimplePredictable.ofUnifGrid hT hm0 ξ hbdd hmeas).measurable_uncurry_eval_mul hm)
          ((LevyStochCalc.Brownian.Ito.SimplePredictable.ofUnifGrid hT hm0 ξ hbdd hmeas).progressivelyMeasurable_eval_mul ℱ
            (LevyStochCalc.Brownian.Ito.SimplePredictable.ofUnifGrid_adapt ℱ hT hm0 ξ hbdd hmeas hadapt) hp)
          (fun T' hT' =>
            (_root_.Prove2MeSourceProof.h_ab7ca2049b8b9b3eaf1b7768 (LevyStochCalc.Brownian.Ito.SimplePredictable.ofUnifGrid hT hm0 ξ hbdd hmeas))
              hq T' hT') T ω
        - LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian W ℱ hℱ (fun ω s => φ (X s ω) * H ω s)
            hmg hpg hqg T ω‖₊ : ℝ≥0∞) ^ 2 ∂P := by
    refine lintegral_congr_ae ?_
    filter_upwards [hstep] with ω hω
    rw [hω]
  rw [hcongr]
  refine le_trans (_root_.Prove2MeSourceProof.h_39514136d82673dc228f451d W ℱ hℱ H
    (fun ω s => (LevyStochCalc.Brownian.Ito.SimplePredictable.ofUnifGrid hT hm0 ξ hbdd hmeas).eval s ω)
    (fun ω s => φ (X s ω)) _ _ _ hmg hpg hqg hC0 hCH hT) ?_
  gcongr _ * ?_
  exact (fun p2mMethodArg0 p2mMethodArg1 => _root_.Prove2MeSourceProof.h_3b3636a20b20ac59ccdbdb27 p2mMethodArg0 p2mMethodArg1 h) hC0 hCH hbm hB0 hB hL0 hφlip hT hm0 ξ hbdd hmeas
    fun i ω => rfl
end Frozen

end LevyStochCalc.Brownian.Ito


