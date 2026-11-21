-- Prove2me | Definitions.Def_SourceProof_cb15b0bd12e621847d80c2c5
-- name    : SourceProof_cb15b0bd12e621847d80c2c5
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-20T19:17:27.469176+00:00
-- url     : https://prove2.me/theorems/292d50d8-c094-4142-ba01-3dca283daea8
-- title:
--   LevyStochCalc source module: SourceProof_cb15b0bd12e621847d80c2c5
-- statement:
--   The original source theorem `LevyStochCalc.Brownian.Ito.condExp_quadVarIncrement` comes from the `LevyStochCalc.Brownian.ItoQuadVarSum` module. The staged Lean declaration includes its source proof and dependency references.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Brownian_ItoL2CompletionQuadVar_F000
import Definitions.Def_LevyStochCalc_Brownian_ItoL2CompletionQuadVar_F002
import Definitions.Def_LevyStochCalc_Brownian_ItoQuadVarSum_F000
import Definitions.Def_SourceProof_08c64b3622d7f10f8c921d88
import Definitions.Def_SourceProof_580018e2ba31f91ba73e0981

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

include hℱ in

theorem _root_.Prove2MeSourceProof.h_cb15b0bd12e621847d80c2c5 {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) :
    P[quadVarIncrement W ℱ hℱ H hm hp hq a b | ℱ.rightCont a] =ᵐ[P] 0 := by
  have hMmart := _root_.Prove2MeSourceProof.h_08c64b3622d7f10f8c921d88 W ℱ hℱ H hm hp hq
  have hQmart := _root_.Prove2MeSourceProof.h_580018e2ba31f91ba73e0981 W ℱ hℱ H hm hp hq
  have hMmem : ∀ t : ℝ, MemLp (LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian W ℱ hℱ H hm hp hq t) 2 P :=
    fun t => LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian_memLp W ℱ hℱ H hm hp hq t
  have hMint : ∀ t : ℝ, Integrable (LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian W ℱ hℱ H hm hp hq t) P :=
    fun t => (hMmem t).integrable (by norm_num)
  have hAint : ∀ t : ℝ, 0 ≤ t →
      Integrable (fun ω => ∫ u in Set.Icc (0 : ℝ) t, (H ω u) ^ 2 ∂volume) P :=
    fun t ht => LevyStochCalc.Brownian.Ito.compensatorH_integrable H hm hq ht
  have hMsq : ∀ t : ℝ,
      Integrable (fun ω => (LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian W ℱ hℱ H hm hp hq t ω) ^ 2) P := by
    intro t
    have hfun : (fun ω => (LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian W ℱ hℱ H hm hp hq t ω) ^ 2)
        = LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian W ℱ hℱ H hm hp hq t
          * LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian W ℱ hℱ H hm hp hq t := by
      funext ω; rw [pow_two]; rfl
    rw [hfun]
    exact (hMmem t).integrable_mul (hMmem t)
  have hb : (0 : ℝ) ≤ b := ha.trans hab
  -- the three pieces of the decomposition
  have hi1 : Integrable (fun ω => (LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian W ℱ hℱ H hm hp hq b ω) ^ 2
      - ∫ u in Set.Icc (0 : ℝ) b, (H ω u) ^ 2 ∂volume) P := (hMsq b).sub (hAint b hb)
  have hi2 : Integrable (fun ω => LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian W ℱ hℱ H hm hp hq a ω
      * LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian W ℱ hℱ H hm hp hq b ω) P :=
    (hMmem a).integrable_mul (hMmem b)
  have hi3 : Integrable (fun ω => (LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian W ℱ hℱ H hm hp hq a ω) ^ 2
      + ∫ u in Set.Icc (0 : ℝ) a, (H ω u) ^ 2 ∂volume) P := (hMsq a).add (hAint a ha)
  have hdecomp : LevyStochCalc.Brownian.Ito.quadVarIncrement W ℱ hℱ H hm hp hq a b
      = (fun ω => (LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian W ℱ hℱ H hm hp hq b ω) ^ 2
          - ∫ u in Set.Icc (0 : ℝ) b, (H ω u) ^ 2 ∂volume)
        + ((-2 : ℝ) • fun ω => LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian W ℱ hℱ H hm hp hq a ω
            * LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian W ℱ hℱ H hm hp hq b ω)
        + (fun ω => (LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian W ℱ hℱ H hm hp hq a ω) ^ 2
            + ∫ u in Set.Icc (0 : ℝ) a, (H ω u) ^ 2 ∂volume) := by
    funext ω
    simp only [LevyStochCalc.Brownian.Ito.quadVarIncrement, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    ring
  -- conditional expectations of the three pieces
  have h1 : P[fun ω => (LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian W ℱ hℱ H hm hp hq b ω) ^ 2
        - ∫ u in Set.Icc (0 : ℝ) b, (H ω u) ^ 2 ∂volume | ℱ.rightCont a]
      =ᵐ[P] fun ω => (LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian W ℱ hℱ H hm hp hq a ω) ^ 2
        - ∫ u in Set.Icc (0 : ℝ) a, (H ω u) ^ 2 ∂volume := hQmart.2 a b hab
  have h2 : P[fun ω => LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian W ℱ hℱ H hm hp hq a ω
        * LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian W ℱ hℱ H hm hp hq b ω | ℱ.rightCont a]
      =ᵐ[P] fun ω => (LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian W ℱ hℱ H hm hp hq a ω) ^ 2 := by
    have hMa : @MeasureTheory.StronglyMeasurable Ω ℝ _ (ℱ.rightCont a)
        (LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian W ℱ hℱ H hm hp hq a) := hMmart.1 a
    have hkey := MeasureTheory.condExp_mul_of_stronglyMeasurable_left (m := ℱ.rightCont a)
      hMa hi2 (hMint b)
    have hfun : (fun ω => LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian W ℱ hℱ H hm hp hq a ω
        * LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian W ℱ hℱ H hm hp hq b ω)
        = LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian W ℱ hℱ H hm hp hq a
          * LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian W ℱ hℱ H hm hp hq b := rfl
    rw [hfun]
    filter_upwards [hkey, hMmart.2 a b hab] with ω hω hω'
    rw [hω, Pi.mul_apply, hω', pow_two]
  have h3 : P[fun ω => (LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian W ℱ hℱ H hm hp hq a ω) ^ 2
        + ∫ u in Set.Icc (0 : ℝ) a, (H ω u) ^ 2 ∂volume | ℱ.rightCont a]
      =ᵐ[P] fun ω => (LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian W ℱ hℱ H hm hp hq a ω) ^ 2
        + ∫ u in Set.Icc (0 : ℝ) a, (H ω u) ^ 2 ∂volume := by
    refine Filter.EventuallyEq.of_eq (MeasureTheory.condExp_of_stronglyMeasurable
      (ℱ.rightCont.le a) ?_ hi3)
    have hMa : @MeasureTheory.StronglyMeasurable Ω ℝ _ (ℱ.rightCont a)
        (LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian W ℱ hℱ H hm hp hq a) := hMmart.1 a
    have hAa : @MeasureTheory.StronglyMeasurable Ω ℝ _ (ℱ.rightCont a)
        (fun ω => ∫ u in Set.Icc (0 : ℝ) a, (H ω u) ^ 2 ∂volume) :=
      (LevyStochCalc.Brownian.Ito.compensatorH_adapted ℱ H hp a).mono (ℱ.le_rightCont a)
    exact ((hMa.measurable.pow_const 2).stronglyMeasurable).add hAa
  -- assemble
  rw [hdecomp]
  have hadd1 := MeasureTheory.condExp_add hi1 (hi2.smul (-2 : ℝ)) (ℱ.rightCont a)
  have hadd2 := MeasureTheory.condExp_add (hi1.add (hi2.smul (-2 : ℝ))) hi3 (ℱ.rightCont a)
  have hsmul := MeasureTheory.condExp_smul (μ := P) (m := ℱ.rightCont a) (-2 : ℝ)
    (fun ω => LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian W ℱ hℱ H hm hp hq a ω
      * LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian W ℱ hℱ H hm hp hq b ω)
  filter_upwards [hadd2, hadd1, hsmul, h1, h2, h3] with ω e2 e1 es f1 f2 f3
  rw [e2, Pi.add_apply, e1, Pi.add_apply, es, Pi.smul_apply, f1, f2, f3, Pi.zero_apply]
  simp only [smul_eq_mul]
  ring
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


