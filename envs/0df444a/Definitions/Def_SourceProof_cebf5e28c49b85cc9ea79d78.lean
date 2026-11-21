-- Prove2me | Definitions.Def_SourceProof_cebf5e28c49b85cc9ea79d78
-- name    : SourceProof_cebf5e28c49b85cc9ea79d78
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-20T19:43:36.143598+00:00
-- url     : https://prove2.me/theorems/ef105a40-1bed-468d-9a2c-d62432bc7fbf
-- title:
--   LevyStochCalc source module: SourceProof_cebf5e28c49b85cc9ea79d78
-- statement:
--   The original source theorem `LevyStochCalc.Brownian.Ito.IsVectorItoVersion.lintegral_sq_martingaleRiemann_sub_le` comes from the `LevyStochCalc.Brownian.VectorItoMartingaleRiemann` module. The staged Lean declaration includes its source proof and dependency references.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_SourceProof_41463ec0846b1376f598d798

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# The martingale Riemann sum along a vector Itô process

Freezing a Lipschitz function of a continuous vector Itô process at the left endpoints of a
uniform grid and pairing it with the increments of an Itô integral against one Brownian
coordinate gives a Riemann sum for `∫_0^T φ(X_s)·G_s dWᵏ_s`, with an `L²` error of order
`√(T/m)`.

## Main statements

* `LevyStochCalc.Brownian.Ito.IsVectorItoVersion.lintegral_sq_frozen_sub_le` — the `L²` distance
  between the frozen step weight and the weight itself.
* `LevyStochCalc.Brownian.Ito.IsVectorItoVersion.lintegral_sq_martingaleRiemann_sub_le` — the
  `L²` error of the martingale Riemann sum.
-/

namespace LevyStochCalc.Brownian.Ito

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

universe u

section VectorFrozen

open LevyStochCalc.Brownian.Multidim

variable {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {n d : ℕ} {W : Multidim.MultidimBrownianMotion P d}
  {ℱ : Filtration ℝ ‹MeasurableSpace Ω›}
  {hcoord : ∀ k : Fin d, IsBrownianFiltration (W.W k) ℱ}
  {H : Fin n → Fin d → Ω → ℝ → ℝ}
  {hHm : ∀ m k, Measurable (Function.uncurry (H m k))}
  {hHp : ∀ m k, Probability.ProgressivelyMeasurable ℱ (H m k)}
  {hHs : ∀ (m : Fin n) (k : Fin d) (T : ℝ), 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
    (‖H m k ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤}
  {X₀ : Ω → Fin n → ℝ} {bdrift : Fin n → Ω → ℝ → ℝ} {X : ℝ → Ω → Fin n → ℝ}
  {C : ℝ} (hC0 : 0 ≤ C)
  (hCH : ∀ (m : Fin n) (k : Fin d) (ω : Ω) (s : ℝ), |H m k ω s| ≤ C)

include hC0 hCH in

theorem _root_.Prove2MeSourceProof.h_cebf5e28c49b85cc9ea79d78
    (h : IsVectorItoVersion W ℱ hcoord H hHm hHp hHs X₀ bdrift X)
    (hbm : ∀ m, Measurable (Function.uncurry (bdrift m))) {B : ℝ} (hB0 : 0 ≤ B)
    (hB : ∀ (m : Fin n) (ω : Ω) (s : ℝ), |bdrift m ω s| ≤ B)
    {φ : (Fin n → ℝ) → ℝ} {Kφ : ℝ} (hφbd : ∀ x, |φ x| ≤ Kφ)
    {L : ℝ} (hL0 : 0 ≤ L) (hφlip : ∀ x y : Fin n → ℝ, |φ x - φ y| ≤ L * ‖x - y‖)
    (k : Fin d) {G : Ω → ℝ → ℝ} (hGm : Measurable (Function.uncurry G))
    (hGp : Probability.ProgressivelyMeasurable ℱ G)
    (hGs : ∀ T', 0 < T' → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T',
      (‖G ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
    {CG : ℝ} (hCG0 : 0 ≤ CG) (hCG : ∀ ω s, |G ω s| ≤ CG)
    (hmg : Measurable (Function.uncurry fun ω s => φ (X s ω) * G ω s))
    (hpg : Probability.ProgressivelyMeasurable ℱ fun ω s => φ (X s ω) * G ω s)
    (hqg : ∀ T', 0 < T' → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T',
      (‖φ (X s ω) * G ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
    {T : ℝ} (hT : 0 < T) {m : ℕ} (hm0 : m ≠ 0) :
    ∫⁻ ω, (‖(∑ i : Fin m, φ (X (unifGrid T m (i : ℕ)) ω)
          * (stochasticIntegralBrownian (W.W k) ℱ (hcoord k) G hGm hGp hGs
              (unifGrid T m ((i : ℕ) + 1)) ω
            - stochasticIntegralBrownian (W.W k) ℱ (hcoord k) G hGm hGp hGs
              (unifGrid T m (i : ℕ)) ω))
        - stochasticIntegralBrownian (W.W k) ℱ (hcoord k) (fun ω s => φ (X s ω) * G ω s)
            hmg hpg hqg T ω‖₊ : ℝ≥0∞) ^ 2 ∂P
      ≤ ENNReal.ofReal (CG ^ 2) * (ENNReal.ofReal (L ^ 2)
        * ENNReal.ofReal (T * ((n : ℝ) * (2 * (B * (T / (m : ℝ))) ^ 2
          + 2 * ((d : ℝ) ^ 2 * (C ^ 2 * (T / (m : ℝ)))))))) := by
  have hφc : Continuous φ := by
    have hlip : LipschitzWith (Real.toNNReal L) φ := by
      refine LipschitzWith.of_dist_le_mul fun x y => ?_
      rw [Real.dist_eq, dist_eq_norm, Real.coe_toNNReal L hL0]
      exact hφlip x y
    exact hlip.continuous
  set ξ : Fin m → Ω → ℝ := fun i ω => φ (X (LevyStochCalc.Brownian.Ito.unifGrid T m (i : ℕ)) ω) with hξdef
  have hbdd : ∀ i : Fin m, ∃ M : ℝ, ∀ ω : Ω, |ξ i ω| ≤ M := fun i => ⟨Kφ, fun ω => hφbd _⟩
  have hmeas : ∀ i : Fin m, Measurable (ξ i) := fun i =>
    hφc.measurable.comp (h.measurable (LevyStochCalc.Brownian.Ito.unifGrid T m (i : ℕ)))
  have hadapt : ∀ i : Fin m, @MeasureTheory.StronglyMeasurable Ω ℝ _
      (ℱ (LevyStochCalc.Brownian.Ito.unifGrid T m (i : ℕ))) (ξ i) := fun i =>
    hφc.comp_stronglyMeasurable (h.adapted (LevyStochCalc.Brownian.Ito.unifGrid T m (i : ℕ)))
  have hstep := LevyStochCalc.Brownian.Ito.sum_unifGrid_mul_sub_ae (W.W k) ℱ (hcoord k) G hGm hGp hGs hT hm0 ξ hbdd hmeas
    hadapt
  have hcongr : ∫⁻ ω, (‖(∑ i : Fin m, ξ i ω
          * (LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian (W.W k) ℱ (hcoord k) G hGm hGp hGs
              (LevyStochCalc.Brownian.Ito.unifGrid T m ((i : ℕ) + 1)) ω
            - LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian (W.W k) ℱ (hcoord k) G hGm hGp hGs
              (LevyStochCalc.Brownian.Ito.unifGrid T m (i : ℕ)) ω))
        - LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian (W.W k) ℱ (hcoord k) (fun ω s => φ (X s ω) * G ω s)
            hmg hpg hqg T ω‖₊ : ℝ≥0∞) ^ 2 ∂P
      = ∫⁻ ω, (‖LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian (W.W k) ℱ (hcoord k)
          (fun ω s => (LevyStochCalc.Brownian.Ito.SimplePredictable.ofUnifGrid hT hm0 ξ hbdd hmeas).eval s ω * G ω s)
          ((LevyStochCalc.Brownian.Ito.SimplePredictable.ofUnifGrid hT hm0 ξ hbdd hmeas).measurable_uncurry_eval_mul hGm)
          ((LevyStochCalc.Brownian.Ito.SimplePredictable.ofUnifGrid hT hm0 ξ hbdd hmeas).progressivelyMeasurable_eval_mul ℱ
            (LevyStochCalc.Brownian.Ito.SimplePredictable.ofUnifGrid_adapt ℱ hT hm0 ξ hbdd hmeas hadapt) hGp)
          (fun T' hT' =>
            (_root_.Prove2MeSourceProof.h_ab7ca2049b8b9b3eaf1b7768 (LevyStochCalc.Brownian.Ito.SimplePredictable.ofUnifGrid hT hm0 ξ hbdd hmeas))
              hGs T' hT') T ω
        - LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian (W.W k) ℱ (hcoord k) (fun ω s => φ (X s ω) * G ω s)
            hmg hpg hqg T ω‖₊ : ℝ≥0∞) ^ 2 ∂P := by
    refine lintegral_congr_ae ?_
    filter_upwards [hstep] with ω hω
    rw [hω]
  rw [hcongr]
  refine le_trans (_root_.Prove2MeSourceProof.h_39514136d82673dc228f451d (W.W k) ℱ (hcoord k) G
    (fun ω s => (LevyStochCalc.Brownian.Ito.SimplePredictable.ofUnifGrid hT hm0 ξ hbdd hmeas).eval s ω)
    (fun ω s => φ (X s ω)) _ _ _ hmg hpg hqg hCG0 hCG hT) ?_
  gcongr _ * ?_
  exact (fun p2mMethodArg0 p2mMethodArg1 => _root_.Prove2MeSourceProof.h_41463ec0846b1376f598d798 p2mMethodArg0 p2mMethodArg1 h) hC0 hCH hbm hB0 hB hL0 hφlip hT hm0 ξ hbdd hmeas
    fun i ω => rfl
end VectorFrozen

end LevyStochCalc.Brownian.Ito


