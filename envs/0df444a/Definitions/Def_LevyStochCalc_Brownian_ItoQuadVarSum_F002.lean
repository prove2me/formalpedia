-- Prove2me | Definitions.Def_LevyStochCalc_Brownian_ItoQuadVarSum_F002
-- name    : LevyStochCalc_Brownian_ItoQuadVarSum_F002
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-20T19:17:24.977588+00:00
-- url     : https://prove2.me/theorems/c3db74de-fb85-4c73-8188-16be5e95ad2d
-- title:
--   Source declarations: LevyStochCalc.Brownian.ItoQuadVarSum
-- statement:
--   Source-preserving extracted declarations from LevyStochCalc.Brownian.ItoQuadVarSum. Existing definitions, lemmas, instances, proofs and elaboration context are retained; generated import closure remains under review.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Brownian_ItoL2CompletionQuadVar_F002
import Definitions.Def_LevyStochCalc_Brownian_ItoQuadVarSum_F000
import Definitions.Def_SourceProof_08c64b3622d7f10f8c921d88

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

end IncrementL2

section WeightedSum

variable {P : Measure Ω} [IsProbabilityMeasure P] (W : LevyStochCalc.Brownian.BrownianMotion P)
  (ℱ : Filtration ℝ ‹MeasurableSpace Ω›) (hℱ : IsBrownianFiltration W ℱ)
  (H : Ω → ℝ → ℝ) (hm : Measurable (Function.uncurry H))
  (hp : Probability.ProgressivelyMeasurable ℱ H)
  (hq : ∀ T, 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
    (‖H ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
  {C : ℝ} (hC0 : 0 ≤ C) (hCH : ∀ ω s, |H ω s| ≤ C)

include hℱ in
/-- The compensated square increment across a grid cell is measurable for the σ-algebra at the
right endpoint. -/
theorem stronglyMeasurable_quadVarIncrement {a b : ℝ} (hab : a ≤ b) :
    @MeasureTheory.StronglyMeasurable Ω ℝ _ (ℱ.rightCont b)
      (quadVarIncrement W ℱ hℱ H hm hp hq a b) := by
  have hMmart := _root_.Prove2MeSourceProof.h_08c64b3622d7f10f8c921d88 W ℱ hℱ H hm hp hq
  have hMb : @MeasureTheory.StronglyMeasurable Ω ℝ _ (ℱ.rightCont b)
      (stochasticIntegralBrownian W ℱ hℱ H hm hp hq b) := hMmart.1 b
  have hMa : @MeasureTheory.StronglyMeasurable Ω ℝ _ (ℱ.rightCont b)
      (stochasticIntegralBrownian W ℱ hℱ H hm hp hq a) :=
    (hMmart.1 a).mono (ℱ.rightCont.mono hab)
  have hAb : @MeasureTheory.StronglyMeasurable Ω ℝ _ (ℱ.rightCont b)
      (fun ω => ∫ u in Set.Icc (0 : ℝ) b, (H ω u) ^ 2 ∂volume) :=
    (compensatorH_adapted ℱ H hp b).mono (ℱ.le_rightCont b)
  have hAa : @MeasureTheory.StronglyMeasurable Ω ℝ _ (ℱ.rightCont b)
      (fun ω => ∫ u in Set.Icc (0 : ℝ) a, (H ω u) ^ 2 ∂volume) :=
    ((compensatorH_adapted ℱ H hp a).mono (ℱ.le_rightCont a)).mono (ℱ.rightCont.mono hab)
  exact ((hMb.sub hMa).measurable.pow_const 2).stronglyMeasurable.sub (hAb.sub hAa)
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


