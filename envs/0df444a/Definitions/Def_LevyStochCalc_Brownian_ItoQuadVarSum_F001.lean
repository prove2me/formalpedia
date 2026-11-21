-- Prove2me | Definitions.Def_LevyStochCalc_Brownian_ItoQuadVarSum_F001
-- name    : LevyStochCalc_Brownian_ItoQuadVarSum_F001
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-20T19:18:19.908691+00:00
-- url     : https://prove2.me/theorems/941e150d-f153-43ae-87fa-9290f51f3479
-- title:
--   Source declarations: LevyStochCalc.Brownian.ItoQuadVarSum
-- statement:
--   Source-preserving extracted declarations from LevyStochCalc.Brownian.ItoQuadVarSum. Existing definitions, lemmas, instances, proofs and elaboration context are retained; generated import closure remains under review.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Brownian_ItoL2CompletionQuadVar_F002
import Definitions.Def_LevyStochCalc_Brownian_ItoQuadVarSum_F000
import Definitions.Def_SourceProof_0895508398bff4a45b14f57f

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

/-- A square-integrable function lies in `L²`. -/
theorem memLp_two_of_lintegral_sq_lt_top {P' : Measure Ω} {f : Ω → ℝ}
    (hf : MeasureTheory.AEStronglyMeasurable f P')
    (h : ∫⁻ ω, (‖f ω‖₊ : ℝ≥0∞) ^ 2 ∂P' < ⊤) : MemLp f 2 P' := by
  refine ⟨hf, ?_⟩
  by_contra hcon
  have htop : MeasureTheory.eLpNorm f 2 P' = ⊤ := top_le_iff.mp (not_lt.mp hcon)
  rw [← eLpNorm_two_rpow_eq_lintegral_sq f, htop,
    ENNReal.top_rpow_of_pos (by norm_num : (0 : ℝ) < 2)] at h
  exact lt_irrefl _ h
section Bounds

variable {P : Measure Ω} [IsProbabilityMeasure P] (W : LevyStochCalc.Brownian.BrownianMotion P)
  (ℱ : Filtration ℝ ‹MeasurableSpace Ω›) (hℱ : IsBrownianFiltration W ℱ)
  (H : Ω → ℝ → ℝ) (hm : Measurable (Function.uncurry H))
  (hp : Probability.ProgressivelyMeasurable ℱ H)
  (hq : ∀ T, 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
    (‖H ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
  {C : ℝ} (hC0 : 0 ≤ C) (hCH : ∀ ω s, |H ω s| ≤ C)

include hm hC0 hCH in
/-- The square of a bounded integrand is integrable on every set of finite measure. -/
theorem integrableOn_sq (ω : Ω) {s : Set ℝ} (hs : volume s ≠ ⊤) :
    MeasureTheory.IntegrableOn (fun u => (H ω u) ^ 2) s volume := by
  have hmeas : Measurable fun u => (H ω u) ^ 2 :=
    ((Measurable.of_uncurry_left hm).pow_const 2)
  refine MeasureTheory.Measure.integrableOn_of_bounded (M := C ^ 2) hs
    hmeas.aestronglyMeasurable ?_
  refine Filter.Eventually.of_forall fun u => ?_
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity : (0 : ℝ) ≤ (H ω u) ^ 2)]
  nlinarith [hCH ω u, abs_nonneg (H ω u), sq_abs (H ω u)]
include hm hC0 hCH in
/-- The compensator increment across `(a, b]` is between `0` and `C²(b − a)`. -/
theorem compensator_sub_bounds {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) (ω : Ω) :
    0 ≤ (∫ u in Set.Icc (0 : ℝ) b, (H ω u) ^ 2 ∂volume)
          - ∫ u in Set.Icc (0 : ℝ) a, (H ω u) ^ 2 ∂volume
      ∧ (∫ u in Set.Icc (0 : ℝ) b, (H ω u) ^ 2 ∂volume)
          - ∫ u in Set.Icc (0 : ℝ) a, (H ω u) ^ 2 ∂volume ≤ C ^ 2 * (b - a) := by
  have hmeas : Measurable fun u => (H ω u) ^ 2 :=
    ((Measurable.of_uncurry_left hm).pow_const 2)
  have hsplit : Set.Icc (0 : ℝ) b = Set.Icc (0 : ℝ) a ∪ Set.Ioc a b := by
    rw [Set.Icc_union_Ioc_eq_Icc ha hab]
  have hdisj : Disjoint (Set.Icc (0 : ℝ) a) (Set.Ioc a b) :=
    Set.disjoint_left.mpr fun x hx hx' => absurd hx.2 (not_le.mpr hx'.1)
  have hint1 : MeasureTheory.IntegrableOn (fun u => (H ω u) ^ 2) (Set.Icc (0 : ℝ) a) volume :=
    integrableOn_sq H hm hC0 hCH ω (by simp)
  have hint2 : MeasureTheory.IntegrableOn (fun u => (H ω u) ^ 2) (Set.Ioc a b) volume :=
    integrableOn_sq H hm hC0 hCH ω (by simp)
  have hadd : (∫ u in Set.Icc (0 : ℝ) b, (H ω u) ^ 2 ∂volume)
      = (∫ u in Set.Icc (0 : ℝ) a, (H ω u) ^ 2 ∂volume)
        + ∫ u in Set.Ioc a b, (H ω u) ^ 2 ∂volume := by
    rw [hsplit]
    exact MeasureTheory.setIntegral_union hdisj measurableSet_Ioc hint1 hint2
  rw [hadd, add_sub_cancel_left]
  refine ⟨MeasureTheory.setIntegral_nonneg measurableSet_Ioc fun u _ => by positivity, ?_⟩
  have hle : ∫ u in Set.Ioc a b, (H ω u) ^ 2 ∂volume
      ≤ ∫ _u in Set.Ioc a b, C ^ 2 ∂volume := by
    refine MeasureTheory.setIntegral_mono_on hint2
      (MeasureTheory.integrableOn_const (by simp [Real.volume_Ioc])) measurableSet_Ioc
      fun u _ => ?_
    nlinarith [hCH ω u, abs_nonneg (H ω u), sq_abs (H ω u)]
  refine hle.trans ?_
  rw [MeasureTheory.setIntegral_const, Real.volume_real_Ioc_of_le hab, smul_eq_mul]
  exact le_of_eq (mul_comm _ _)
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
/-- The square of an increment of the Itô integral lies in `L²`. -/
theorem memLp_two_sq_increment {a b : ℝ} (ha : 0 ≤ a) (hab : a < b) :
    MemLp (fun ω => (stochasticIntegralBrownian W ℱ hℱ H hm hp hq b ω
      - stochasticIntegralBrownian W ℱ hℱ H hm hp hq a ω) ^ 2) 2 P := by
  have hmeas : Measurable fun ω => stochasticIntegralBrownian W ℱ hℱ H hm hp hq b ω
      - stochasticIntegralBrownian W ℱ hℱ H hm hp hq a ω :=
    (((stochasticIntegralBrownian_stronglyAdapted W ℱ hℱ H hm hp hq b).mono
        (ℱ.le b)).measurable).sub
      (((stochasticIntegralBrownian_stronglyAdapted W ℱ hℱ H hm hp hq a).mono
        (ℱ.le a)).measurable)
  refine memLp_two_of_lintegral_sq_lt_top (hmeas.pow_const 2).aestronglyMeasurable ?_
  have hpt : ∀ ω : Ω, (‖(stochasticIntegralBrownian W ℱ hℱ H hm hp hq b ω
        - stochasticIntegralBrownian W ℱ hℱ H hm hp hq a ω) ^ 2‖₊ : ℝ≥0∞) ^ 2
      = (‖stochasticIntegralBrownian W ℱ hℱ H hm hp hq b ω
        - stochasticIntegralBrownian W ℱ hℱ H hm hp hq a ω‖₊ : ℝ≥0∞) ^ 4 := by
    intro ω
    rw [nnnorm_pow, ENNReal.coe_pow, ← pow_mul]
  simp_rw [hpt]
  exact lt_of_le_of_lt
    (_root_.Prove2MeSourceProof.h_0895508398bff4a45b14f57f W ℱ hℱ H hm hp hq hC0 hCH ha hab)
    (by simp)
include hm hq hC0 hCH in
/-- The compensator increment lies in `L²`. -/
theorem memLp_two_compensator_sub {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) :
    MemLp (fun ω => (∫ u in Set.Icc (0 : ℝ) b, (H ω u) ^ 2 ∂volume)
      - ∫ u in Set.Icc (0 : ℝ) a, (H ω u) ^ 2 ∂volume) 2 P := by
  have hint := ((compensatorH_integrable H hm hq (ha.trans hab)).sub
    (compensatorH_integrable H hm hq ha))
  refine MeasureTheory.MemLp.of_bound hint.aestronglyMeasurable (C ^ 2 * (b - a)) ?_
  refine Filter.Eventually.of_forall fun ω => ?_
  obtain ⟨h1, h2⟩ := compensator_sub_bounds H hm hC0 hCH ha hab ω
  rw [Real.norm_eq_abs, abs_of_nonneg h1]
  exact h2
include hℱ hC0 hCH in
/-- The compensated square increment lies in `L²`. -/
theorem memLp_two_quadVarIncrement {a b : ℝ} (ha : 0 ≤ a) (hab : a < b) :
    MemLp (quadVarIncrement W ℱ hℱ H hm hp hq a b) 2 P :=
  (memLp_two_sq_increment W ℱ hℱ H hm hp hq hC0 hCH ha hab).sub
    (memLp_two_compensator_sub H hm hq hC0 hCH ha hab.le)
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


