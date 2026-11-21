-- Prove2me | Definitions.Def_SourceProof_746f2da768f1cbb4ee1d5a85
-- name    : SourceProof_746f2da768f1cbb4ee1d5a85
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-20T19:35:38.78853+00:00
-- url     : https://prove2.me/theorems/d6391e2a-51c5-44d5-9868-ae09c9632e83
-- title:
--   LevyStochCalc source module: SourceProof_746f2da768f1cbb4ee1d5a85
-- statement:
--   The original source theorem `LevyStochCalc.Brownian.Ito.sum_integral_norm_vectorItoIncrement_pow_three_le` comes from the `LevyStochCalc.Brownian.VectorItoThirdMoment` module. The staged Lean declaration includes its source proof and dependency references.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Brownian_VectorItoThirdMoment_F000

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# Third absolute moments of a vector Itô process's increments

The second-order Taylor remainder of a function with Lipschitz second derivative is cubic in the
increment, so Itô's formula in the vector setting needs the third absolute moment of `‖ΔX‖`. It
is assembled from the coordinatewise splitting: the supremum norm is controlled by the sum of the
coordinates, each coordinate by its drift part and its martingale part, and the martingale part
by the individual Itô increments.

## Main statements

* `LevyStochCalc.Brownian.Ito.integral_abs_sum_pow_three_le` — the third absolute moment of a
  finite sum.
* `LevyStochCalc.Brownian.Ito.integral_norm_pi_pow_three_le` — the third moment of the supremum
  norm from the coordinates.
* `LevyStochCalc.Brownian.Ito.integral_norm_vectorItoProcess_sub_pow_three_le` —
  `𝔼‖ΔX‖³ ≤ 4n³((BΔt)³ + d³κ Δt√(Δt))` with `κ = (C² + (6+c)C⁴)/2`.
* `LevyStochCalc.Brownian.Ito.sum_integral_norm_vectorItoIncrement_pow_three_le` — the same
  summed over a uniform grid, of order `m^{-1/2}`.
-/

namespace LevyStochCalc.Brownian.Ito

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

universe u

section GenericThird

variable {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]

end GenericThird

section VectorThird

open LevyStochCalc.Brownian.Multidim

variable {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {n d : ℕ} (W : Multidim.MultidimBrownianMotion P d)
  (ℱ : Filtration ℝ ‹MeasurableSpace Ω›)
  (hcoord : ∀ k : Fin d, IsBrownianFiltration (W.W k) ℱ)
  (H : Fin n → Fin d → Ω → ℝ → ℝ)
  (hHm : ∀ m k, Measurable (Function.uncurry (H m k)))
  (hHp : ∀ m k, Probability.ProgressivelyMeasurable ℱ (H m k))
  (hHs : ∀ (m : Fin n) (k : Fin d) (T : ℝ), 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
    (‖H m k ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
  {C : ℝ} (hC0 : 0 ≤ C)
  (hCH : ∀ (m : Fin n) (k : Fin d) (ω : Ω) (s : ℝ), |H m k ω s| ≤ C)

include hC0 hCH in

theorem _root_.Prove2MeSourceProof.h_746f2da768f1cbb4ee1d5a85 (X₀ : Ω → Fin n → ℝ)
    (bdrift : Fin n → Ω → ℝ → ℝ) (hbm : ∀ m, Measurable (Function.uncurry (bdrift m)))
    {B : ℝ} (hB0 : 0 ≤ B) (hB : ∀ (m : Fin n) (ω : Ω) (s : ℝ), |bdrift m ω s| ≤ B)
    {T : ℝ} (hT : 0 < T) {m : ℕ} (hm0 : m ≠ 0) :
    ∑ i ∈ Finset.range m, ∫ ω,
        ‖vectorItoProcess W ℱ hcoord H hHm hHp hHs X₀ bdrift (unifGrid T m (i + 1)) ω
          - vectorItoProcess W ℱ hcoord H hHm hHp hHs X₀ bdrift (unifGrid T m i) ω‖ ^ 3 ∂P
      ≤ (n : ℝ) ^ 2 * ((n : ℝ) * (4 * ((m : ℝ) * (B * (T / (m : ℝ))) ^ 3
        + (d : ℝ) ^ 2 * ((d : ℝ) * ((C ^ 2 + (6 + gaussianFourthMoment) * C ^ 4) / 2
          * (T * Real.sqrt (T / (m : ℝ)))))))) := by
  have hm' : (0 : ℝ) < (m : ℝ) := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hm0)
  have hTm : (m : ℝ) * (T / (m : ℝ)) = T := by field_simp
  have hterm : ∀ i ∈ Finset.range m, ∫ ω,
      ‖LevyStochCalc.Brownian.Ito.vectorItoProcess W ℱ hcoord H hHm hHp hHs X₀ bdrift (LevyStochCalc.Brownian.Ito.unifGrid T m (i + 1)) ω
        - LevyStochCalc.Brownian.Ito.vectorItoProcess W ℱ hcoord H hHm hHp hHs X₀ bdrift (LevyStochCalc.Brownian.Ito.unifGrid T m i) ω‖ ^ 3 ∂P
      ≤ (n : ℝ) ^ 2 * ((n : ℝ) * (4 * ((B * (T / (m : ℝ))) ^ 3
        + (d : ℝ) ^ 2 * ((d : ℝ) * ((C ^ 2 + (6 + LevyStochCalc.Brownian.Ito.gaussianFourthMoment) * C ^ 4) / 2
          * (T / (m : ℝ) * Real.sqrt (T / (m : ℝ)))))))) := by
    intro i _
    have hle := LevyStochCalc.Brownian.Ito.integral_norm_vectorItoProcess_sub_pow_three_le W ℱ hcoord H hHm hHp hHs
      hC0 hCH X₀ bdrift hbm hB0 hB (LevyStochCalc.Brownian.Ito.unifGrid_nonneg hT.le m i) (LevyStochCalc.Brownian.Ito.unifGrid_lt_succ hT hm0 i)
    rwa [LevyStochCalc.Brownian.Ito.unifGrid_succ_sub hm0 i] at hle
  refine (Finset.sum_le_sum hterm).trans ?_
  rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  have hκ0 : (0 : ℝ) ≤ (C ^ 2 + (6 + LevyStochCalc.Brownian.Ito.gaussianFourthMoment) * C ^ 4) / 2 := by
    have h1 : (0 : ℝ) ≤ (6 + LevyStochCalc.Brownian.Ito.gaussianFourthMoment) * C ^ 4 :=
      mul_nonneg (by linarith [LevyStochCalc.Brownian.Ito.gaussianFourthMoment_nonneg]) (by positivity)
    linarith [sq_nonneg C]
  have hsplit : (m : ℝ) * ((n : ℝ) ^ 2 * ((n : ℝ) * (4 * ((B * (T / (m : ℝ))) ^ 3
        + (d : ℝ) ^ 2 * ((d : ℝ) * ((C ^ 2 + (6 + LevyStochCalc.Brownian.Ito.gaussianFourthMoment) * C ^ 4) / 2
          * (T / (m : ℝ) * Real.sqrt (T / (m : ℝ)))))))))
      = (n : ℝ) ^ 2 * ((n : ℝ) * (4 * ((m : ℝ) * (B * (T / (m : ℝ))) ^ 3
        + (d : ℝ) ^ 2 * ((d : ℝ) * ((C ^ 2 + (6 + LevyStochCalc.Brownian.Ito.gaussianFourthMoment) * C ^ 4) / 2
          * (((m : ℝ) * (T / (m : ℝ))) * Real.sqrt (T / (m : ℝ)))))))) := by ring
  rw [hsplit, hTm]
end VectorThird

end LevyStochCalc.Brownian.Ito


