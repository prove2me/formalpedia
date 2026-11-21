-- Prove2me | Definitions.Def_LevyStochCalc_Brownian_ItoFormula_F000
-- name    : LevyStochCalc_Brownian_ItoFormula_F000
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-20T19:32:47.533087+00:00
-- url     : https://prove2.me/theorems/dbbb1587-a7ea-40d5-b1c8-012f513d11ba
-- title:
--   Source declarations: LevyStochCalc.Brownian.ItoFormula
-- statement:
--   Source-preserving extracted declarations from LevyStochCalc.Brownian.ItoFormula. Existing definitions, lemmas, instances, proofs and elaboration context are retained; generated import closure remains under review.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Brownian_ItoFormulaGrid_F002
import Definitions.Def_LevyStochCalc_Brownian_ItoRiemannIntegrand_F000
import Definitions.Def_LevyStochCalc_Brownian_TaylorTwo_F000
import Definitions.Def_LevyStochCalc_Brownian_TaylorTwo_F001
import Definitions.Def_SourceProof_39514136d82673dc228f451d
import Definitions.Def_SourceProof_4a14e5e540e270806f2d3259
import Definitions.Def_SourceProof_ab7ca2049b8b9b3eaf1b7768

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# Grid Riemann sums of the Itô integral

The weighted sum of the Itô integral's increments across a uniform grid is itself an Itô
integral — that of the grid's step weight against the integrand — and replacing the step weight
by a general one costs the `L²` distance between them times the bound on the integrand.

## Main statements

* `LevyStochCalc.Brownian.Ito.sum_unifGrid_mul_sub_ae` — the grid-weighted sum of increments as
  an Itô integral.
* `LevyStochCalc.Brownian.Ito.lintegral_sq_sum_unifGrid_sub_le` — that sum is `L²`-close to the
  Itô integral of the weight, with the weight's modulus of continuity as the rate.
* `LevyStochCalc.Brownian.Ito.integral_abs_taylorRemainder_le` — the second-order Taylor
  remainder along a uniform grid is `O(m^{-1/2})` in `L¹`.
-/

namespace LevyStochCalc.Brownian.Ito

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

universe u

variable {Ω : Type u} [MeasurableSpace Ω]

section GridSum

variable {P : Measure Ω} [IsProbabilityMeasure P] (W : LevyStochCalc.Brownian.BrownianMotion P)
  (ℱ : Filtration ℝ ‹MeasurableSpace Ω›) (hℱ : IsBrownianFiltration W ℱ)
  (H : Ω → ℝ → ℝ) (hm : Measurable (Function.uncurry H))
  (hp : Probability.ProgressivelyMeasurable ℱ H)
  (hq : ∀ T, 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
    (‖H ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)

include hℱ in
/-- **The grid-weighted sum of the Itô integral's increments is an Itô integral.** For
coefficients `ξ i` measurable at the left endpoint of cell `i` of the uniform grid,

  `∑ᵢ ξᵢ · (M_{tᵢ₊₁} − M_{tᵢ}) = ∫_0^T G_m(s)·H_s dW_s`

almost surely, where `G_m` is the step process with value `ξ i` on `(tᵢ, tᵢ₊₁]`. -/
theorem sum_unifGrid_mul_sub_ae {T : ℝ} (hT : 0 < T) {m : ℕ} (hm0 : m ≠ 0)
    (ξ : Fin m → Ω → ℝ) (hbdd : ∀ i : Fin m, ∃ M : ℝ, ∀ ω : Ω, |ξ i ω| ≤ M)
    (hmeas : ∀ i : Fin m, Measurable (ξ i))
    (hadapt : ∀ i : Fin m, @MeasureTheory.StronglyMeasurable Ω ℝ _
      (ℱ (unifGrid T m (i : ℕ))) (ξ i)) :
    (fun ω => ∑ i : Fin m, ξ i ω
        * (stochasticIntegralBrownian W ℱ hℱ H hm hp hq (unifGrid T m ((i : ℕ) + 1)) ω
          - stochasticIntegralBrownian W ℱ hℱ H hm hp hq (unifGrid T m (i : ℕ)) ω))
      =ᵐ[P] stochasticIntegralBrownian W ℱ hℱ
        (fun ω s => (SimplePredictable.ofUnifGrid hT hm0 ξ hbdd hmeas).eval s ω * H ω s)
        ((SimplePredictable.ofUnifGrid hT hm0 ξ hbdd hmeas).measurable_uncurry_eval_mul hm)
        ((SimplePredictable.ofUnifGrid hT hm0 ξ hbdd hmeas).progressivelyMeasurable_eval_mul ℱ
          (SimplePredictable.ofUnifGrid_adapt ℱ hT hm0 ξ hbdd hmeas hadapt) hp)
        (fun T' hT' =>
          (_root_.Prove2MeSourceProof.h_ab7ca2049b8b9b3eaf1b7768 (SimplePredictable.ofUnifGrid hT hm0 ξ hbdd hmeas))
            hq T' hT') T := by
  have hlast : (SimplePredictable.ofUnifGrid hT hm0 ξ hbdd hmeas).partition
      (Fin.last (SimplePredictable.ofUnifGrid hT hm0 ξ hbdd hmeas).N) ≤ T :=
    (SimplePredictable.ofUnifGrid hT hm0 ξ hbdd hmeas).partition_le_T
  exact sum_xi_mul_stochasticIntegral_sub_ae W ℱ hℱ
    (SimplePredictable.ofUnifGrid hT hm0 ξ hbdd hmeas)
    (SimplePredictable.ofUnifGrid_adapt ℱ hT hm0 ξ hbdd hmeas hadapt) H hm hp hq _ _ _ hT hlast
include hℱ in
/-- **The martingale Riemann sum is `L²`-close to the Itô integral of the weight.** If the cell
coefficients are a weight `g` frozen at the grid's left endpoints and `g` varies by at most `ε`
over the mesh, then

  `‖∑ᵢ g(tᵢ)·ΔMᵢ − ∫_0^T g_s H_s dW_s‖_{L²}² ≤ C²·ε²·T`. -/
theorem lintegral_sq_sum_unifGrid_sub_le
    (g : Ω → ℝ → ℝ)
    (hmg : Measurable (Function.uncurry fun ω s => g ω s * H ω s))
    (hpg : Probability.ProgressivelyMeasurable ℱ fun ω s => g ω s * H ω s)
    (hqg : ∀ T', 0 < T' → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T',
      (‖g ω s * H ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
    {C : ℝ} (hC0 : 0 ≤ C) (hCH : ∀ ω s, |H ω s| ≤ C)
    {T : ℝ} (hT : 0 < T) {m : ℕ} (hm0 : m ≠ 0)
    (ξ : Fin m → Ω → ℝ) (hbdd : ∀ i : Fin m, ∃ M : ℝ, ∀ ω : Ω, |ξ i ω| ≤ M)
    (hmeas : ∀ i : Fin m, Measurable (ξ i))
    (hadapt : ∀ i : Fin m, @MeasureTheory.StronglyMeasurable Ω ℝ _
      (ℱ (unifGrid T m (i : ℕ))) (ξ i))
    (hξg : ∀ (i : Fin m) (ω : Ω), ξ i ω = g ω (unifGrid T m (i : ℕ)))
    {ε : ℝ} (hε0 : 0 ≤ ε)
    (hmod : ∀ ω : Ω, ∀ x ∈ Set.Icc (0 : ℝ) T, ∀ y ∈ Set.Icc (0 : ℝ) T,
      |x - y| ≤ T / (m : ℝ) → |g ω x - g ω y| ≤ ε) :
    ∫⁻ ω, (‖(∑ i : Fin m, ξ i ω
          * (stochasticIntegralBrownian W ℱ hℱ H hm hp hq (unifGrid T m ((i : ℕ) + 1)) ω
            - stochasticIntegralBrownian W ℱ hℱ H hm hp hq (unifGrid T m (i : ℕ)) ω))
        - stochasticIntegralBrownian W ℱ hℱ (fun ω s => g ω s * H ω s) hmg hpg hqg T ω‖₊
          : ℝ≥0∞) ^ 2 ∂P
      ≤ ENNReal.ofReal (C ^ 2) * ENNReal.ofReal (ε ^ 2 * T) := by
  have hstep := sum_unifGrid_mul_sub_ae W ℱ hℱ H hm hp hq hT hm0 ξ hbdd hmeas hadapt
  have hcongr : ∫⁻ ω, (‖(∑ i : Fin m, ξ i ω
        * (stochasticIntegralBrownian W ℱ hℱ H hm hp hq (unifGrid T m ((i : ℕ) + 1)) ω
          - stochasticIntegralBrownian W ℱ hℱ H hm hp hq (unifGrid T m (i : ℕ)) ω))
      - stochasticIntegralBrownian W ℱ hℱ (fun ω s => g ω s * H ω s) hmg hpg hqg T ω‖₊
        : ℝ≥0∞) ^ 2 ∂P
      = ∫⁻ ω, (‖stochasticIntegralBrownian W ℱ hℱ
          (fun ω s => (SimplePredictable.ofUnifGrid hT hm0 ξ hbdd hmeas).eval s ω * H ω s)
          ((SimplePredictable.ofUnifGrid hT hm0 ξ hbdd hmeas).measurable_uncurry_eval_mul hm)
          ((SimplePredictable.ofUnifGrid hT hm0 ξ hbdd hmeas).progressivelyMeasurable_eval_mul ℱ
            (SimplePredictable.ofUnifGrid_adapt ℱ hT hm0 ξ hbdd hmeas hadapt) hp)
          (fun T' hT' =>
            (_root_.Prove2MeSourceProof.h_ab7ca2049b8b9b3eaf1b7768 (SimplePredictable.ofUnifGrid hT hm0 ξ hbdd hmeas))
              hq T' hT') T ω
        - stochasticIntegralBrownian W ℱ hℱ (fun ω s => g ω s * H ω s) hmg hpg hqg T ω‖₊
          : ℝ≥0∞) ^ 2 ∂P := by
    refine lintegral_congr_ae ?_
    filter_upwards [hstep] with ω hω
    rw [hω]
  rw [hcongr]
  refine le_trans (_root_.Prove2MeSourceProof.h_39514136d82673dc228f451d W ℱ hℱ H
    (fun ω s => (SimplePredictable.ofUnifGrid hT hm0 ξ hbdd hmeas).eval s ω) g _ _ _
    hmg hpg hqg hC0 hCH hT) ?_
  refine mul_le_mul_right ?_ _
  refine _root_.Prove2MeSourceProof.h_4a14e5e540e270806f2d3259
    (fun ω s => (SimplePredictable.ofUnifGrid hT hm0 ξ hbdd hmeas).eval s ω) g hε0 ?_
  intro ω s hs
  exact abs_ofUnifGrid_eval_sub_le hT hm0 ξ hbdd hmeas g hξg hmod ω hs
end GridSum

section TaylorRemainder

variable {P : Measure Ω} [IsProbabilityMeasure P] (W : LevyStochCalc.Brownian.BrownianMotion P)
  (ℱ : Filtration ℝ ‹MeasurableSpace Ω›) (hℱ : IsBrownianFiltration W ℱ)
  (H : Ω → ℝ → ℝ) (hm : Measurable (Function.uncurry H))
  (hp : Probability.ProgressivelyMeasurable ℱ H)
  (hq : ∀ T, 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
    (‖H ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)

variable {C : ℝ} (hC0 : 0 ≤ C) (hCH : ∀ ω s, |H ω s| ≤ C)

end TaylorRemainder

end LevyStochCalc.Brownian.Ito


