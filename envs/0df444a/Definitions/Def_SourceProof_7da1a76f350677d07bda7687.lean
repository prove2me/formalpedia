-- Prove2me | Definitions.Def_SourceProof_7da1a76f350677d07bda7687
-- name    : SourceProof_7da1a76f350677d07bda7687
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-20T19:21:39.415957+00:00
-- url     : https://prove2.me/theorems/78bcaecc-86c8-4028-8e99-1a0a60763818
-- title:
--   LevyStochCalc source module: SourceProof_7da1a76f350677d07bda7687
-- statement:
--   The original source theorem `LevyStochCalc.Brownian.Ito.integral_sq_quadVarIncrement_le` comes from the `LevyStochCalc.Brownian.ItoQuadVarSum` module. The staged Lean declaration includes its source proof and dependency references.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Brownian_ItoQuadVarSum_F001

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# Compensated square increments of the Itô integral

The increment `(M_b − M_a)² − ∫_a^b H_s² ds` of the compensated square of the Itô integral is
conditionally centred at its left endpoint, so a weighted sum of such increments over a
partition is a sum of martingale differences.

## Main statements

* `LevyStochCalc.Brownian.Ito.quadVarIncrement` — the compensated square increment.
* `LevyStochCalc.Brownian.Ito.condExp_quadVarIncrement` — it is conditionally centred at the
  left endpoint.
* `LevyStochCalc.Brownian.Ito.compensator_sub_bounds` — the compensator increment across
  `(a, b]` lies between `0` and `C²(b − a)`.
* `LevyStochCalc.Brownian.Ito.integral_sq_quadVarIncrement_le` — its second moment is at most
  `(2(6 + c) + 2)·C⁴·(b − a)²`.
* `LevyStochCalc.Brownian.Ito.integral_sq_weighted_quadVarSum_le` — the second moment of a
  weighted sum over a grid is at most `D²·(2(6 + c) + 2)·C⁴·∑ᵢ (tᵢ₊₁ − tᵢ)²`.
* `LevyStochCalc.Brownian.Ito.exists_continuous_modification_stochasticIntegralBrownian` — the
  Itô integral of a bounded integrand has a modification with continuous paths.
-/

namespace LevyStochCalc.Brownian.Ito

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

universe u

variable {Ω : Type u} [MeasurableSpace Ω]

section QuadVarIncrement

variable {P : Measure Ω} [IsProbabilityMeasure P] (W : LevyStochCalc.Brownian.BrownianMotion P)
  (ℱ : Filtration ℝ ‹MeasurableSpace Ω›) (hℱ : IsBrownianFiltration W ℱ)
  (H : Ω → ℝ → ℝ) (hm : Measurable (Function.uncurry H))
  (hp : Probability.ProgressivelyMeasurable ℱ H)
  (hq : ∀ T, 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
    (‖H ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)

end QuadVarIncrement

section Bounds

variable {P : Measure Ω} [IsProbabilityMeasure P] (W : LevyStochCalc.Brownian.BrownianMotion P)
  (ℱ : Filtration ℝ ‹MeasurableSpace Ω›) (hℱ : IsBrownianFiltration W ℱ)
  (H : Ω → ℝ → ℝ) (hm : Measurable (Function.uncurry H))
  (hp : Probability.ProgressivelyMeasurable ℱ H)
  (hq : ∀ T, 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
    (‖H ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
  {C : ℝ} (hC0 : 0 ≤ C) (hCH : ∀ ω s, |H ω s| ≤ C)

end Bounds

section IncrementL2

variable {P : Measure Ω} [IsProbabilityMeasure P] (W : LevyStochCalc.Brownian.BrownianMotion P)
  (ℱ : Filtration ℝ ‹MeasurableSpace Ω›) (hℱ : IsBrownianFiltration W ℱ)
  (H : Ω → ℝ → ℝ) (hm : Measurable (Function.uncurry H))
  (hp : Probability.ProgressivelyMeasurable ℱ H)
  (hq : ∀ T, 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
    (‖H ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
  {C : ℝ} (hC0 : 0 ≤ C) (hCH : ∀ ω s, |H ω s| ≤ C)

include hℱ hC0 hCH in

theorem _root_.Prove2MeSourceProof.h_7da1a76f350677d07bda7687 {a b : ℝ} (ha : 0 ≤ a) (hab : a < b) :
    ∫ ω, (quadVarIncrement W ℱ hℱ H hm hp hq a b ω) ^ 2 ∂P
      ≤ (2 * (6 + gaussianFourthMoment) + 2) * C ^ 4 * (b - a) ^ 2 := by
  have hcg : (0 : ℝ) ≤ LevyStochCalc.Brownian.Ito.gaussianFourthMoment := LevyStochCalc.Brownian.Ito.gaussianFourthMoment_nonneg
  have hba : (0 : ℝ) ≤ b - a := by linarith
  have hXmem := LevyStochCalc.Brownian.Ito.memLp_two_sq_increment W ℱ hℱ H hm hp hq hC0 hCH ha hab
  have hYmem := LevyStochCalc.Brownian.Ito.memLp_two_compensator_sub H hm hq hC0 hCH ha hab.le
  have hXint : Integrable (fun ω => ((LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian W ℱ hℱ H hm hp hq b ω
      - LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian W ℱ hℱ H hm hp hq a ω) ^ 2) ^ 2) P := by
    have hfun : (fun ω => ((LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian W ℱ hℱ H hm hp hq b ω
          - LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian W ℱ hℱ H hm hp hq a ω) ^ 2) ^ 2)
        = (fun ω => (LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian W ℱ hℱ H hm hp hq b ω
            - LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian W ℱ hℱ H hm hp hq a ω) ^ 2)
          * (fun ω => (LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian W ℱ hℱ H hm hp hq b ω
            - LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian W ℱ hℱ H hm hp hq a ω) ^ 2) := by
      funext ω; rw [pow_two]; rfl
    rw [hfun]
    exact hXmem.integrable_mul hXmem
  have hYint : Integrable (fun ω => ((∫ u in Set.Icc (0 : ℝ) b, (H ω u) ^ 2 ∂volume)
      - ∫ u in Set.Icc (0 : ℝ) a, (H ω u) ^ 2 ∂volume) ^ 2) P := by
    have hfun : (fun ω => ((∫ u in Set.Icc (0 : ℝ) b, (H ω u) ^ 2 ∂volume)
          - ∫ u in Set.Icc (0 : ℝ) a, (H ω u) ^ 2 ∂volume) ^ 2)
        = (fun ω => (∫ u in Set.Icc (0 : ℝ) b, (H ω u) ^ 2 ∂volume)
            - ∫ u in Set.Icc (0 : ℝ) a, (H ω u) ^ 2 ∂volume)
          * (fun ω => (∫ u in Set.Icc (0 : ℝ) b, (H ω u) ^ 2 ∂volume)
            - ∫ u in Set.Icc (0 : ℝ) a, (H ω u) ^ 2 ∂volume) := by
      funext ω; rw [pow_two]; rfl
    rw [hfun]
    exact hYmem.integrable_mul hYmem
  -- the fourth moment of the increment
  have hX : ∫ ω, ((LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian W ℱ hℱ H hm hp hq b ω
        - LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian W ℱ hℱ H hm hp hq a ω) ^ 2) ^ 2 ∂P
      ≤ (6 + LevyStochCalc.Brownian.Ito.gaussianFourthMoment) * C ^ 4 * (b - a) ^ 2 := by
    have hK : (0 : ℝ) ≤ (6 + LevyStochCalc.Brownian.Ito.gaussianFourthMoment) * C ^ 4 * (b - a) ^ 2 := by positivity
    have heq : ENNReal.ofReal (∫ ω, ((LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian W ℱ hℱ H hm hp hq b ω
          - LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian W ℱ hℱ H hm hp hq a ω) ^ 2) ^ 2 ∂P)
        = ∫⁻ ω, ENNReal.ofReal (((LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian W ℱ hℱ H hm hp hq b ω
            - LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian W ℱ hℱ H hm hp hq a ω) ^ 2) ^ 2) ∂P :=
      MeasureTheory.ofReal_integral_eq_lintegral_ofReal hXint
        (Filter.Eventually.of_forall fun ω => by positivity)
    have hpt : ∀ ω : Ω, ENNReal.ofReal (((LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian W ℱ hℱ H hm hp hq b ω
          - LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian W ℱ hℱ H hm hp hq a ω) ^ 2) ^ 2)
        = (‖LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian W ℱ hℱ H hm hp hq b ω
            - LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian W ℱ hℱ H hm hp hq a ω‖₊ : ℝ≥0∞) ^ 4 := by
      have key : ∀ x : ℝ, ENNReal.ofReal ((x ^ 2) ^ 2) = (‖x‖₊ : ℝ≥0∞) ^ 4 := by
        intro x
        have h1 : (‖x‖₊ : ℝ≥0∞) = ENNReal.ofReal |x| := by
          rw [ENNReal.ofReal_eq_coe_nnreal (abs_nonneg _)]
          exact congrArg _ (NNReal.eq (by simp [Real.norm_eq_abs]))
        rw [h1, ← ENNReal.ofReal_pow (abs_nonneg _), ← abs_pow,
          abs_of_nonneg (by positivity : (0 : ℝ) ≤ x ^ 4)]
        congr 1
        ring
      exact fun ω => key _
    rw [← ENNReal.ofReal_le_ofReal_iff hK, heq]
    simp_rw [hpt]
    exact _root_.Prove2MeSourceProof.h_0895508398bff4a45b14f57f W ℱ hℱ H hm hp hq hC0 hCH ha hab
  -- the compensator increment
  have hY : ∫ ω, ((∫ u in Set.Icc (0 : ℝ) b, (H ω u) ^ 2 ∂volume)
        - ∫ u in Set.Icc (0 : ℝ) a, (H ω u) ^ 2 ∂volume) ^ 2 ∂P
      ≤ C ^ 4 * (b - a) ^ 2 := by
    have hbnd : ∀ ω : Ω, ((∫ u in Set.Icc (0 : ℝ) b, (H ω u) ^ 2 ∂volume)
        - ∫ u in Set.Icc (0 : ℝ) a, (H ω u) ^ 2 ∂volume) ^ 2 ≤ C ^ 4 * (b - a) ^ 2 := by
      intro ω
      obtain ⟨h1, h2⟩ := LevyStochCalc.Brownian.Ito.compensator_sub_bounds H hm hC0 hCH ha hab.le ω
      nlinarith [sq_nonneg C, mul_nonneg (mul_nonneg hC0 hC0) hba]
    calc ∫ ω, ((∫ u in Set.Icc (0 : ℝ) b, (H ω u) ^ 2 ∂volume)
            - ∫ u in Set.Icc (0 : ℝ) a, (H ω u) ^ 2 ∂volume) ^ 2 ∂P
        ≤ ∫ _ω : Ω, C ^ 4 * (b - a) ^ 2 ∂P :=
          MeasureTheory.integral_mono hYint (integrable_const _) hbnd
      _ = C ^ 4 * (b - a) ^ 2 := by simp
  -- combine
  have hptwise : ∀ ω : Ω, (LevyStochCalc.Brownian.Ito.quadVarIncrement W ℱ hℱ H hm hp hq a b ω) ^ 2
      ≤ 2 * (((LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian W ℱ hℱ H hm hp hq b ω
          - LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian W ℱ hℱ H hm hp hq a ω) ^ 2) ^ 2)
        + 2 * (((∫ u in Set.Icc (0 : ℝ) b, (H ω u) ^ 2 ∂volume)
          - ∫ u in Set.Icc (0 : ℝ) a, (H ω u) ^ 2 ∂volume) ^ 2) := by
    intro ω
    simp only [LevyStochCalc.Brownian.Ito.quadVarIncrement]
    nlinarith [sq_nonneg ((LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian W ℱ hℱ H hm hp hq b ω
        - LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian W ℱ hℱ H hm hp hq a ω) ^ 2
      + ((∫ u in Set.Icc (0 : ℝ) b, (H ω u) ^ 2 ∂volume)
        - ∫ u in Set.Icc (0 : ℝ) a, (H ω u) ^ 2 ∂volume))]
  have hζint : Integrable (fun ω => (LevyStochCalc.Brownian.Ito.quadVarIncrement W ℱ hℱ H hm hp hq a b ω) ^ 2) P := by
    have hmem := LevyStochCalc.Brownian.Ito.memLp_two_quadVarIncrement W ℱ hℱ H hm hp hq hC0 hCH ha hab
    have hfun : (fun ω => (LevyStochCalc.Brownian.Ito.quadVarIncrement W ℱ hℱ H hm hp hq a b ω) ^ 2)
        = LevyStochCalc.Brownian.Ito.quadVarIncrement W ℱ hℱ H hm hp hq a b * LevyStochCalc.Brownian.Ito.quadVarIncrement W ℱ hℱ H hm hp hq a b := by
      funext ω; rw [pow_two]; rfl
    rw [hfun]
    exact hmem.integrable_mul hmem
  calc ∫ ω, (LevyStochCalc.Brownian.Ito.quadVarIncrement W ℱ hℱ H hm hp hq a b ω) ^ 2 ∂P
      ≤ ∫ ω, (2 * (((LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian W ℱ hℱ H hm hp hq b ω
            - LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian W ℱ hℱ H hm hp hq a ω) ^ 2) ^ 2)
          + 2 * (((∫ u in Set.Icc (0 : ℝ) b, (H ω u) ^ 2 ∂volume)
            - ∫ u in Set.Icc (0 : ℝ) a, (H ω u) ^ 2 ∂volume) ^ 2)) ∂P :=
        MeasureTheory.integral_mono hζint ((hXint.const_mul 2).add (hYint.const_mul 2)) hptwise
    _ = 2 * (∫ ω, ((LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian W ℱ hℱ H hm hp hq b ω
            - LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian W ℱ hℱ H hm hp hq a ω) ^ 2) ^ 2 ∂P)
          + 2 * (∫ ω, ((∫ u in Set.Icc (0 : ℝ) b, (H ω u) ^ 2 ∂volume)
            - ∫ u in Set.Icc (0 : ℝ) a, (H ω u) ^ 2 ∂volume) ^ 2 ∂P) := by
        rw [MeasureTheory.integral_add (hXint.const_mul 2) (hYint.const_mul 2),
          MeasureTheory.integral_const_mul, MeasureTheory.integral_const_mul]
    _ ≤ 2 * ((6 + LevyStochCalc.Brownian.Ito.gaussianFourthMoment) * C ^ 4 * (b - a) ^ 2) + 2 * (C ^ 4 * (b - a) ^ 2) := by
        gcongr
    _ = (2 * (6 + LevyStochCalc.Brownian.Ito.gaussianFourthMoment) + 2) * C ^ 4 * (b - a) ^ 2 := by ring
end IncrementL2

section WeightedSum

variable {P : Measure Ω} [IsProbabilityMeasure P] (W : LevyStochCalc.Brownian.BrownianMotion P)
  (ℱ : Filtration ℝ ‹MeasurableSpace Ω›) (hℱ : IsBrownianFiltration W ℱ)
  (H : Ω → ℝ → ℝ) (hm : Measurable (Function.uncurry H))
  (hp : Probability.ProgressivelyMeasurable ℱ H)
  (hq : ∀ T, 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
    (‖H ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
  {C : ℝ} (hC0 : 0 ≤ C) (hCH : ∀ ω s, |H ω s| ≤ C)

end WeightedSum

section ContinuousModification

variable {P : Measure Ω} [IsProbabilityMeasure P] (W : LevyStochCalc.Brownian.BrownianMotion P)
  (ℱ : Filtration ℝ ‹MeasurableSpace Ω›) (hℱ : IsBrownianFiltration W ℱ)
  (H : Ω → ℝ → ℝ) (hm : Measurable (Function.uncurry H))
  (hp : Probability.ProgressivelyMeasurable ℱ H)
  (hq : ∀ T, 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
    (‖H ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
  {C : ℝ} (hC0 : 0 ≤ C) (hCH : ∀ ω s, |H ω s| ≤ C)

end ContinuousModification

end LevyStochCalc.Brownian.Ito


