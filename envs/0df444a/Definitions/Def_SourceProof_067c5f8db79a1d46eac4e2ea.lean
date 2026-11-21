-- Prove2me | Definitions.Def_SourceProof_067c5f8db79a1d46eac4e2ea
-- name    : SourceProof_067c5f8db79a1d46eac4e2ea
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-20T19:36:14.209095+00:00
-- url     : https://prove2.me/theorems/19431bb4-e525-4420-8b9f-9a115f4d3817
-- title:
--   LevyStochCalc source module: SourceProof_067c5f8db79a1d46eac4e2ea
-- statement:
--   The original source theorem `LevyStochCalc.Brownian.Ito.integral_sq_weighted_crossSum_le` comes from the `LevyStochCalc.Brownian.CrossVariationSum` module. The staged Lean declaration includes its source proof and dependency references.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Brownian_CrossVariationSum_F000
import Definitions.Def_SourceProof_d03d1ce2f6914927fb902784

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# Weighted sums of cross increments

For two distinct Brownian coordinates the product of the increments of the Itô integrals across a
cell is conditionally centred at the cell's left endpoint, so a weighted sum of such products over
a partition is a sum of martingale differences whenever the weights are measurable at the left
endpoints. Its second moment is therefore the sum of the termwise second moments, and each of
those is bounded through the fourth moments of the two increments.

## Main statements

* `LevyStochCalc.Brownian.Ito.integrable_sq_mul_and_le` — the square of a product is integrable
  with second moment at most half the sum of the fourth moments.
* `LevyStochCalc.Brownian.Ito.crossIncrement` — the product of the increments of the Itô
  integrals against two coordinates across a cell.
* `LevyStochCalc.Brownian.Ito.integrable_sq_crossIncrement_and_le` — its square is integrable,
  with second moment at most `(6 + c)·(C_H⁴ + C_K⁴)/2·(b − a)²`.
* `LevyStochCalc.Brownian.Ito.integral_sq_weighted_crossSum_le` — the second moment of a weighted
  sum over a grid is at most `D²·(6 + c)·(C_H⁴ + C_K⁴)/2·∑ᵢ (tᵢ₊₁ − tᵢ)²`.
-/

namespace LevyStochCalc.Brownian.Ito

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

universe u

variable {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {ℱ : Filtration ℝ ‹MeasurableSpace Ω›}

section CrossSum

open LevyStochCalc.Brownian.Multidim

variable {d : ℕ} (W : Multidim.MultidimBrownianMotion P d)
  (hcoord : ∀ k : Fin d, IsBrownianFiltration (W.W k) ℱ)
  {H K : Ω → ℝ → ℝ} (hHm : Measurable (Function.uncurry H))
  (hHp : Probability.ProgressivelyMeasurable ℱ H)
  (hHs : ∀ T, 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
    (‖H ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
  (hKm : Measurable (Function.uncurry K))
  (hKp : Probability.ProgressivelyMeasurable ℱ K)
  (hKs : ∀ T, 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
    (‖K ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)

variable {CH CK : ℝ} (hCH0 : 0 ≤ CH) (hCH : ∀ ω s, |H ω s| ≤ CH)
  (hCK0 : 0 ≤ CK) (hCK : ∀ ω s, |K ω s| ≤ CK)

include hCH0 hCH hCK0 hCK in

theorem _root_.Prove2MeSourceProof.h_067c5f8db79a1d46eac4e2ea {i j : Fin d} (hij : i ≠ j)
    (t : ℕ → ℝ) (h0 : 0 ≤ t 0) (ht : ∀ k, t k < t (k + 1))
    (g : ℕ → Ω → ℝ) (hg : ∀ k, StronglyMeasurable[ℱ (t k)] (g k))
    {D : ℝ} (hD0 : 0 ≤ D) (hgD : ∀ (k : ℕ) (ω : Ω), |g k ω| ≤ D) (n : ℕ) :
    ∫ ω, (∑ k ∈ Finset.range n, g k ω *
        crossIncrement W hcoord hHm hHp hHs hKm hKp hKs i j (t k) (t (k + 1)) ω) ^ 2 ∂P
      ≤ D ^ 2 * ((6 + gaussianFourthMoment) * (CH ^ 4 + CK ^ 4) / 2)
        * ∑ k ∈ Finset.range n, (t (k + 1) - t k) ^ 2 := by
  have htmono : StrictMono t := strictMono_nat_of_lt_succ ht
  have ht0 : ∀ k, 0 ≤ t k := fun k => h0.trans (htmono.monotone (Nat.zero_le k))
  set 𝒢 : ℕ → MeasurableSpace Ω := fun k => ℱ (t k) with h𝒢
  have h𝒢le : ∀ k, 𝒢 k ≤ ‹MeasurableSpace Ω› := fun k => ℱ.le (t k)
  have h𝒢mono : Monotone 𝒢 := fun p q hpq => ℱ.mono (htmono.monotone hpq)
  set Y : ℕ → Ω → ℝ := fun k ω =>
    g k ω * LevyStochCalc.Brownian.Ito.crossIncrement W hcoord hHm hHp hHs hKm hKp hKs i j (t k) (t (k + 1)) ω with hY
  have hζmem : ∀ k, MemLp
      (LevyStochCalc.Brownian.Ito.crossIncrement W hcoord hHm hHp hHs hKm hKp hKs i j (t k) (t (k + 1))) 2 P :=
    fun k => LevyStochCalc.Brownian.Ito.memLp_two_crossIncrement W hcoord hHm hHp hHs hKm hKp hKs hCH0 hCH hCK0 hCK
      i j (ht0 k) (ht k)
  have hgmeas : ∀ k, Measurable (g k) := fun k => ((hg k).mono (h𝒢le k)).measurable
  have hYmem : ∀ k, MemLp (Y k) 2 P := by
    intro k
    refine MeasureTheory.MemLp.mono ((hζmem k).const_mul D)
      ((hgmeas k).aestronglyMeasurable.mul (hζmem k).aestronglyMeasurable)
      (Filter.Eventually.of_forall fun ω => ?_)
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_mul, abs_mul, abs_of_nonneg hD0]
    exact mul_le_mul_of_nonneg_right (hgD k ω) (abs_nonneg _)
  have hYmeas : ∀ k, @MeasureTheory.StronglyMeasurable Ω ℝ _ (𝒢 (k + 1)) (Y k) := fun k =>
    ((hg k).mono (h𝒢mono (Nat.le_succ k))).mul
      (LevyStochCalc.Brownian.Ito.stronglyMeasurable_crossIncrement W hcoord hHm hHp hHs hKm hKp hKs i j (ht k).le)
  have hYcond : ∀ k, P[Y k | 𝒢 k] =ᵐ[P] 0 := by
    intro k
    have hprod : Integrable
        (g k * LevyStochCalc.Brownian.Ito.crossIncrement W hcoord hHm hHp hHs hKm hKp hKs i j (t k) (t (k + 1))) P :=
      (hYmem k).integrable (by norm_num)
    have hkey := MeasureTheory.condExp_mul_of_stronglyMeasurable_left (m := 𝒢 k) (hg k)
      hprod ((hζmem k).integrable (by norm_num))
    have hfun : Y k
        = g k * LevyStochCalc.Brownian.Ito.crossIncrement W hcoord hHm hHp hHs hKm hKp hKs i j (t k) (t (k + 1)) := rfl
    rw [hfun]
    filter_upwards [hkey, LevyStochCalc.Brownian.Ito.condExp_crossIncrement W hcoord hHm hHp hHs hKm hKp hKs hij
      (ht0 k) (ht k)] with ω hω hω'
    rw [hω, Pi.mul_apply, hω', Pi.zero_apply, mul_zero]
  rw [_root_.Prove2MeSourceProof.h_d03d1ce2f6914927fb902784 𝒢 h𝒢le h𝒢mono Y hYmem
    hYmeas hYcond n]
  have hterm : ∀ k ∈ Finset.range n, ∫ ω, (Y k ω) ^ 2 ∂P
      ≤ D ^ 2 * ((6 + LevyStochCalc.Brownian.Ito.gaussianFourthMoment) * (CH ^ 4 + CK ^ 4) / 2) * (t (k + 1) - t k) ^ 2 := by
    intro k _
    obtain ⟨hζint, hζle⟩ := LevyStochCalc.Brownian.Ito.integrable_sq_crossIncrement_and_le W hcoord hHm hHp hHs hKm hKp hKs
      hCH0 hCH hCK0 hCK i j (ht0 k) (ht k)
    have hYint : Integrable (fun ω => (Y k ω) ^ 2) P := by
      have hfun : (fun ω => (Y k ω) ^ 2) = Y k * Y k := by funext ω; rw [pow_two]; rfl
      rw [hfun]
      exact (hYmem k).integrable_mul (hYmem k)
    have hstep : ∫ ω, (Y k ω) ^ 2 ∂P ≤ D ^ 2 * ∫ ω,
        (LevyStochCalc.Brownian.Ito.crossIncrement W hcoord hHm hHp hHs hKm hKp hKs i j (t k) (t (k + 1)) ω) ^ 2 ∂P := by
      have hle : ∫ ω, (Y k ω) ^ 2 ∂P ≤ ∫ ω, D ^ 2 *
          (LevyStochCalc.Brownian.Ito.crossIncrement W hcoord hHm hHp hHs hKm hKp hKs i j (t k) (t (k + 1)) ω) ^ 2 ∂P := by
        refine MeasureTheory.integral_mono hYint (hζint.const_mul _) fun ω => ?_
        have hgi : (g k ω) ^ 2 ≤ D ^ 2 := by
          have h := pow_le_pow_left₀ (abs_nonneg (g k ω)) (hgD k ω) 2
          rwa [← abs_pow, abs_of_nonneg (sq_nonneg (g k ω))] at h
        have hsq : (Y k ω) ^ 2 = (g k ω) ^ 2
            * (LevyStochCalc.Brownian.Ito.crossIncrement W hcoord hHm hHp hHs hKm hKp hKs i j (t k) (t (k + 1)) ω) ^ 2 := by
          simp only [hY]; ring
        rw [hsq]
        exact mul_le_mul_of_nonneg_right hgi (sq_nonneg _)
      rwa [MeasureTheory.integral_const_mul] at hle
    have hD2 : (0 : ℝ) ≤ D ^ 2 := sq_nonneg D
    calc ∫ ω, (Y k ω) ^ 2 ∂P
        ≤ D ^ 2 * ∫ ω,
            (LevyStochCalc.Brownian.Ito.crossIncrement W hcoord hHm hHp hHs hKm hKp hKs i j (t k) (t (k + 1)) ω) ^ 2 ∂P :=
          hstep
      _ ≤ D ^ 2 * ((6 + LevyStochCalc.Brownian.Ito.gaussianFourthMoment) * (CH ^ 4 + CK ^ 4) / 2 * (t (k + 1) - t k) ^ 2) :=
          mul_le_mul_of_nonneg_left hζle hD2
      _ = D ^ 2 * ((6 + LevyStochCalc.Brownian.Ito.gaussianFourthMoment) * (CH ^ 4 + CK ^ 4) / 2)
            * (t (k + 1) - t k) ^ 2 := by ring
  calc ∑ k ∈ Finset.range n, ∫ ω, (Y k ω) ^ 2 ∂P
      ≤ ∑ k ∈ Finset.range n,
          D ^ 2 * ((6 + LevyStochCalc.Brownian.Ito.gaussianFourthMoment) * (CH ^ 4 + CK ^ 4) / 2)
            * (t (k + 1) - t k) ^ 2 := Finset.sum_le_sum hterm
    _ = D ^ 2 * ((6 + LevyStochCalc.Brownian.Ito.gaussianFourthMoment) * (CH ^ 4 + CK ^ 4) / 2)
          * ∑ k ∈ Finset.range n, (t (k + 1) - t k) ^ 2 := by rw [Finset.mul_sum]
end CrossSum

end LevyStochCalc.Brownian.Ito


