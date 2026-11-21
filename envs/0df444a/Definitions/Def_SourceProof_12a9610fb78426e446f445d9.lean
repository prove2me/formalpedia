-- Prove2me | Definitions.Def_SourceProof_12a9610fb78426e446f445d9
-- name    : SourceProof_12a9610fb78426e446f445d9
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-20T19:25:04.601332+00:00
-- url     : https://prove2.me/theorems/799f6ff8-552a-4f74-bcc7-24674bdcce13
-- title:
--   LevyStochCalc source module: SourceProof_12a9610fb78426e446f445d9
-- statement:
--   The original source theorem `LevyStochCalc.Brownian.Ito.integral_sq_weighted_quadVarSum_le` comes from the `LevyStochCalc.Brownian.ItoQuadVarSum` module. The staged Lean declaration includes its source proof and dependency references.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Brownian_ItoQuadVarSum_F002
import Definitions.Def_SourceProof_7da1a76f350677d07bda7687
import Definitions.Def_SourceProof_cb15b0bd12e621847d80c2c5
import Definitions.Def_SourceProof_d03d1ce2f6914927fb902784

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

include hℱ hC0 hCH in

theorem _root_.Prove2MeSourceProof.h_12a9610fb78426e446f445d9
    (t : ℕ → ℝ) (h0 : 0 ≤ t 0) (ht : ∀ k, t k < t (k + 1))
    (g : ℕ → Ω → ℝ)
    (hg : ∀ k, @MeasureTheory.StronglyMeasurable Ω ℝ _ (ℱ.rightCont (t k)) (g k))
    {D : ℝ} (hD0 : 0 ≤ D) (hgD : ∀ (k : ℕ) (ω : Ω), |g k ω| ≤ D) (n : ℕ) :
    ∫ ω, (∑ i ∈ Finset.range n,
        g i ω * quadVarIncrement W ℱ hℱ H hm hp hq (t i) (t (i + 1)) ω) ^ 2 ∂P
      ≤ D ^ 2 * ((2 * (6 + gaussianFourthMoment) + 2) * C ^ 4)
        * ∑ i ∈ Finset.range n, (t (i + 1) - t i) ^ 2 := by
  have htmono : StrictMono t := strictMono_nat_of_lt_succ ht
  have ht0 : ∀ k, 0 ≤ t k := fun k => h0.trans (htmono.monotone (Nat.zero_le k))
  -- the martingale-difference data
  set 𝒢 : ℕ → MeasurableSpace Ω := fun k => ℱ.rightCont (t k) with h𝒢
  have h𝒢le : ∀ k, 𝒢 k ≤ ‹MeasurableSpace Ω› := fun k => ℱ.rightCont.le (t k)
  have h𝒢mono : Monotone 𝒢 := fun i j hij => ℱ.rightCont.mono (htmono.monotone hij)
  set Y : ℕ → Ω → ℝ := fun k ω =>
    g k ω * LevyStochCalc.Brownian.Ito.quadVarIncrement W ℱ hℱ H hm hp hq (t k) (t (k + 1)) ω with hY
  have hζmem : ∀ k, MemLp (LevyStochCalc.Brownian.Ito.quadVarIncrement W ℱ hℱ H hm hp hq (t k) (t (k + 1))) 2 P :=
    fun k => LevyStochCalc.Brownian.Ito.memLp_two_quadVarIncrement W ℱ hℱ H hm hp hq hC0 hCH (ht0 k) (ht k)
  have hgmeas : ∀ k, Measurable (g k) := fun k => ((hg k).mono (h𝒢le k)).measurable
  have hYmem : ∀ k, MemLp (Y k) 2 P := by
    intro k
    refine MeasureTheory.MemLp.mono ((hζmem k).const_mul D)
      ((hgmeas k).aestronglyMeasurable.mul (hζmem k).aestronglyMeasurable)
      (Filter.Eventually.of_forall fun ω => ?_)
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_mul, abs_mul, abs_of_nonneg hD0]
    exact mul_le_mul_of_nonneg_right (hgD k ω) (abs_nonneg _)
  have hYmeas : ∀ k, @MeasureTheory.StronglyMeasurable Ω ℝ _ (𝒢 (k + 1)) (Y k) := by
    intro k
    exact ((hg k).mono (h𝒢mono (Nat.le_succ k))).mul
      (LevyStochCalc.Brownian.Ito.stronglyMeasurable_quadVarIncrement W ℱ hℱ H hm hp hq (ht k).le)
  have hYcond : ∀ k, P[Y k | 𝒢 k] =ᵐ[P] 0 := by
    intro k
    have hprod : Integrable (g k * LevyStochCalc.Brownian.Ito.quadVarIncrement W ℱ hℱ H hm hp hq (t k) (t (k + 1))) P :=
      (hYmem k).integrable (by norm_num)
    have hkey := MeasureTheory.condExp_mul_of_stronglyMeasurable_left (m := 𝒢 k) (hg k)
      hprod ((hζmem k).integrable (by norm_num))
    have hfun : Y k = g k * LevyStochCalc.Brownian.Ito.quadVarIncrement W ℱ hℱ H hm hp hq (t k) (t (k + 1)) := rfl
    rw [hfun]
    filter_upwards [hkey,
      _root_.Prove2MeSourceProof.h_cb15b0bd12e621847d80c2c5 W ℱ hℱ H hm hp hq (ht0 k) (ht k).le] with ω hω hω'
    rw [hω, Pi.mul_apply, hω', Pi.zero_apply, mul_zero]
  -- orthogonality
  rw [_root_.Prove2MeSourceProof.h_d03d1ce2f6914927fb902784 𝒢 h𝒢le h𝒢mono Y hYmem
    hYmeas hYcond n]
  -- termwise bound
  have hterm : ∀ i ∈ Finset.range n, ∫ ω, (Y i ω) ^ 2 ∂P
      ≤ D ^ 2 * ((2 * (6 + LevyStochCalc.Brownian.Ito.gaussianFourthMoment) + 2) * C ^ 4) * (t (i + 1) - t i) ^ 2 := by
    intro i _
    have hζint : Integrable
        (fun ω => (LevyStochCalc.Brownian.Ito.quadVarIncrement W ℱ hℱ H hm hp hq (t i) (t (i + 1)) ω) ^ 2) P := by
      have hfun : (fun ω => (LevyStochCalc.Brownian.Ito.quadVarIncrement W ℱ hℱ H hm hp hq (t i) (t (i + 1)) ω) ^ 2)
          = LevyStochCalc.Brownian.Ito.quadVarIncrement W ℱ hℱ H hm hp hq (t i) (t (i + 1))
            * LevyStochCalc.Brownian.Ito.quadVarIncrement W ℱ hℱ H hm hp hq (t i) (t (i + 1)) := by
        funext ω; rw [pow_two]; rfl
      rw [hfun]
      exact (hζmem i).integrable_mul (hζmem i)
    have hYint : Integrable (fun ω => (Y i ω) ^ 2) P := by
      have hfun : (fun ω => (Y i ω) ^ 2) = Y i * Y i := by funext ω; rw [pow_two]; rfl
      rw [hfun]
      exact (hYmem i).integrable_mul (hYmem i)
    have hstep : ∫ ω, (Y i ω) ^ 2 ∂P
        ≤ D ^ 2 * ∫ ω, (LevyStochCalc.Brownian.Ito.quadVarIncrement W ℱ hℱ H hm hp hq (t i) (t (i + 1)) ω) ^ 2 ∂P := by
      have hle : ∫ ω, (Y i ω) ^ 2 ∂P
          ≤ ∫ ω, D ^ 2 * (LevyStochCalc.Brownian.Ito.quadVarIncrement W ℱ hℱ H hm hp hq (t i) (t (i + 1)) ω) ^ 2 ∂P := by
        refine MeasureTheory.integral_mono hYint (hζint.const_mul _) fun ω => ?_
        have hgi : (g i ω) ^ 2 ≤ D ^ 2 := by
          have h := pow_le_pow_left₀ (abs_nonneg (g i ω)) (hgD i ω) 2
          rwa [← abs_pow, abs_of_nonneg (sq_nonneg (g i ω))] at h
        have : (Y i ω) ^ 2 = (g i ω) ^ 2
            * (LevyStochCalc.Brownian.Ito.quadVarIncrement W ℱ hℱ H hm hp hq (t i) (t (i + 1)) ω) ^ 2 := by
          simp only [hY]; ring
        rw [this]
        exact mul_le_mul_of_nonneg_right hgi (sq_nonneg _)
      rwa [MeasureTheory.integral_const_mul] at hle
    have hbnd := _root_.Prove2MeSourceProof.h_7da1a76f350677d07bda7687 W ℱ hℱ H hm hp hq hC0 hCH (ht0 i) (ht i)
    have hD2 : (0 : ℝ) ≤ D ^ 2 := sq_nonneg D
    calc ∫ ω, (Y i ω) ^ 2 ∂P
        ≤ D ^ 2 * ∫ ω, (LevyStochCalc.Brownian.Ito.quadVarIncrement W ℱ hℱ H hm hp hq (t i) (t (i + 1)) ω) ^ 2 ∂P := hstep
      _ ≤ D ^ 2 * ((2 * (6 + LevyStochCalc.Brownian.Ito.gaussianFourthMoment) + 2) * C ^ 4 * (t (i + 1) - t i) ^ 2) :=
          mul_le_mul_of_nonneg_left hbnd hD2
      _ = D ^ 2 * ((2 * (6 + LevyStochCalc.Brownian.Ito.gaussianFourthMoment) + 2) * C ^ 4) * (t (i + 1) - t i) ^ 2 := by
          ring
  calc ∑ i ∈ Finset.range n, ∫ ω, (Y i ω) ^ 2 ∂P
      ≤ ∑ i ∈ Finset.range n,
          D ^ 2 * ((2 * (6 + LevyStochCalc.Brownian.Ito.gaussianFourthMoment) + 2) * C ^ 4) * (t (i + 1) - t i) ^ 2 :=
        Finset.sum_le_sum hterm
    _ = D ^ 2 * ((2 * (6 + LevyStochCalc.Brownian.Ito.gaussianFourthMoment) + 2) * C ^ 4)
          * ∑ i ∈ Finset.range n, (t (i + 1) - t i) ^ 2 := by
        rw [Finset.mul_sum]
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


