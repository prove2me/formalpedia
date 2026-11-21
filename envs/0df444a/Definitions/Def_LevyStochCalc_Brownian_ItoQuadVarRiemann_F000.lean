-- Prove2me | Definitions.Def_LevyStochCalc_Brownian_ItoQuadVarRiemann_F000
-- name    : LevyStochCalc_Brownian_ItoQuadVarRiemann_F000
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-20T19:36:06.219339+00:00
-- url     : https://prove2.me/theorems/3712acc9-9161-4e26-bd75-f11c2af4efa9
-- title:
--   LevyStochCalc source module: LevyStochCalc.Brownian.ItoQuadVarRiemann
-- statement:
--   Exact source-faithful declarations from LevyStochCalc.Brownian.ItoQuadVarRiemann in the pinned LevyStochCalc project.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Brownian_ItoProcessVersion_F000
import Definitions.Def_LevyStochCalc_Brownian_ItoQuadVarSum_F001
import Definitions.Def_LevyStochCalc_Brownian_ItoQuadVarSum_F002
import Definitions.Def_LevyStochCalc_Brownian_ItoQuadVarSum_F003
import Definitions.Def_LevyStochCalc_Brownian_ItoTimeRiemann_F000

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# The quadratic-variation Riemann sum of the Itô formula

Squaring the increments of a continuous Itô process across a uniform grid and weighting them by
a bounded Lipschitz function of the process gives a Riemann sum for `∫_0^T φ(X_s)·H_s² ds`. The
drift square and the cross term are `O(1/m)` and `O(m^{-1/2})`, the compensated squares are
`O(m^{-1/2})` by the martingale-difference bound, and the compensator itself is a frozen-weight
Riemann sum for the density `H²`.

## Main statements

* `LevyStochCalc.Brownian.Ito.IsItoVersion.integral_abs_sum_drift_sq_le` — the drift-square sum.
* `LevyStochCalc.Brownian.Ito.IsItoVersion.integral_abs_sum_cross_le` — the cross term.
* `LevyStochCalc.Brownian.Ito.IsItoVersion.integral_abs_sum_quadVar_le` — the compensated
  squares.
* `LevyStochCalc.Brownian.Ito.IsItoVersion.integral_abs_quadVarRiemann_sub_le` — the four
  pieces together.
-/

namespace LevyStochCalc.Brownian.Ito

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

universe u

variable {Ω : Type u} [MeasurableSpace Ω]

section QuadVarRiemann

variable {P : Measure Ω} [IsProbabilityMeasure P] {W : LevyStochCalc.Brownian.BrownianMotion P}
  {ℱ : Filtration ℝ ‹MeasurableSpace Ω›} {hℱ : IsBrownianFiltration W ℱ}
  {H : Ω → ℝ → ℝ} {hm : Measurable (Function.uncurry H)}
  {hp : Probability.ProgressivelyMeasurable ℱ H}
  {hq : ∀ T, 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
    (‖H ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤}
  {X₀ : Ω → ℝ} {bdrift : Ω → ℝ → ℝ} {X : ℝ → Ω → ℝ}
  {C : ℝ} (hC0 : 0 ≤ C) (hCH : ∀ ω s, |H ω s| ≤ C)

/-- **The drift-square sum is `O(1/m)`.** -/
theorem IsItoVersion.integral_abs_sum_drift_sq_le
    (h : IsItoVersion W ℱ hℱ H hm hp hq X₀ bdrift X)
    (hbm : Measurable (Function.uncurry bdrift))
    {B : ℝ} (_hB0 : 0 ≤ B) (hB : ∀ (ω : Ω) (s : ℝ), |bdrift ω s| ≤ B)
    {φ : ℝ → ℝ} (hφc : Continuous φ) {Kφ : ℝ} (hKφ0 : 0 ≤ Kφ) (hφbd : ∀ x, |φ x| ≤ Kφ)
    {T : ℝ} (hT : 0 < T) {m : ℕ} (hm0 : m ≠ 0) :
    MeasureTheory.Integrable (fun ω : Ω => ∑ i ∈ Finset.range m,
        φ (X (unifGrid T m i) ω)
          * (∫ s in Set.Ioc (unifGrid T m i) (unifGrid T m (i + 1)),
              bdrift ω s ∂volume) ^ 2) P
      ∧ ∫ ω, |∑ i ∈ Finset.range m, φ (X (unifGrid T m i) ω)
          * (∫ s in Set.Ioc (unifGrid T m i) (unifGrid T m (i + 1)),
              bdrift ω s ∂volume) ^ 2| ∂P
        ≤ (m : ℝ) * (Kφ * (B * (T / (m : ℝ))) ^ 2) := by
  have hm' : (0 : ℝ) < (m : ℝ) := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hm0)
  have hTm0 : (0 : ℝ) ≤ T / (m : ℝ) := (div_pos hT hm').le
  have hmeas : Measurable fun ω : Ω => ∑ i ∈ Finset.range m, φ (X (unifGrid T m i) ω)
      * (∫ s in Set.Ioc (unifGrid T m i) (unifGrid T m (i + 1)), bdrift ω s ∂volume) ^ 2 :=
    Finset.measurable_sum _ fun i _ =>
      (hφc.measurable.comp (h.measurable (unifGrid T m i))).mul
        ((measurable_setIntegral_Ioc hbm _ _).pow_const 2)
  have hDbd : ∀ (ω : Ω) (i : ℕ),
      |∫ s in Set.Ioc (unifGrid T m i) (unifGrid T m (i + 1)), bdrift ω s ∂volume|
        ≤ B * (T / (m : ℝ)) := by
    intro ω i
    have hle := _root_.Prove2MeSourceProof.h_0c7e85b4037c170c4bb0381a (Measurable.of_uncurry_left hbm) (hB ω)
      (unifGrid_lt_succ hT hm0 i).le
    rwa [unifGrid_succ_sub hm0 i] at hle
  have hbound : ∀ ω : Ω, |∑ i ∈ Finset.range m, φ (X (unifGrid T m i) ω)
      * (∫ s in Set.Ioc (unifGrid T m i) (unifGrid T m (i + 1)), bdrift ω s ∂volume) ^ 2|
      ≤ (m : ℝ) * (Kφ * (B * (T / (m : ℝ))) ^ 2) := by
    intro ω
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    have hterm : ∀ i ∈ Finset.range m, |φ (X (unifGrid T m i) ω)
        * (∫ s in Set.Ioc (unifGrid T m i) (unifGrid T m (i + 1)),
            bdrift ω s ∂volume) ^ 2| ≤ Kφ * (B * (T / (m : ℝ))) ^ 2 := by
      intro i _
      rw [abs_mul, abs_pow]
      refine mul_le_mul (hφbd _) (pow_le_pow_left₀ (abs_nonneg _) (hDbd ω i) 2)
        (by positivity) hKφ0
    refine (Finset.sum_le_sum hterm).trans ?_
    rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  exact integral_abs_le_of_bounded hmeas (by positivity) hbound
end QuadVarRiemann

end LevyStochCalc.Brownian.Ito


