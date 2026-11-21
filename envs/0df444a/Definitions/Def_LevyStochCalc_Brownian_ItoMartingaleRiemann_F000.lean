-- Prove2me | Definitions.Def_LevyStochCalc_Brownian_ItoMartingaleRiemann_F000
-- name    : LevyStochCalc_Brownian_ItoMartingaleRiemann_F000
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-20T19:34:21.953185+00:00
-- url     : https://prove2.me/theorems/d4c4fcf4-c528-4054-a0bf-ef7544ab823d
-- title:
--   Source declarations: LevyStochCalc.Brownian.ItoMartingaleRiemann
-- statement:
--   Source-preserving extracted declarations from LevyStochCalc.Brownian.ItoMartingaleRiemann. Existing definitions, lemmas, instances, proofs and elaboration context are retained; generated import closure remains under review.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Brownian_ItoFormula_F000
import Definitions.Def_LevyStochCalc_Brownian_ItoGridPartition_F000

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# The martingale Riemann sum of the Itô formula

Freezing a Lipschitz function of a continuous Itô process at the left endpoints of a uniform
grid and pairing it with the Itô integral's increments gives a Riemann sum for
`∫_0^T φ(X_s)·H_s dW_s`, with an `L²` error of order `√(T/m)`.

## Main statements

* `LevyStochCalc.Brownian.Ito.lintegral_sq_bounded_mul_lt_top` — a bounded weight preserves the
  `L²` bound on an integrand.
* `LevyStochCalc.Brownian.Ito.IsItoVersion.lintegral_sq_frozen_sub_le` — the `L²` distance
  between the frozen step weight and the weight itself.
* `LevyStochCalc.Brownian.Ito.IsItoVersion.lintegral_sq_martingaleRiemann_sub_le` — the `L²`
  error of the martingale Riemann sum.
-/

namespace LevyStochCalc.Brownian.Ito

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

universe u

variable {Ω : Type u} [MeasurableSpace Ω]

/-- The square of a real number's extended norm is the extended value of its square. -/
theorem sq_enn_nnnorm_eq_ofReal_sq (x : ℝ) :
    ((‖x‖₊ : ℝ≥0∞)) ^ 2 = ENNReal.ofReal (x ^ 2) := by
  have h1 : (‖x‖₊ : ℝ≥0∞) = ENNReal.ofReal |x| := by
    rw [ENNReal.ofReal_eq_coe_nnreal (abs_nonneg _)]
    exact congrArg _ (NNReal.eq (by simp [Real.norm_eq_abs]))
  rw [h1, ← ENNReal.ofReal_pow (abs_nonneg _), ← abs_pow,
    abs_of_nonneg (by positivity : (0 : ℝ) ≤ x ^ 2)]
section Weight

variable {P : Measure Ω} [IsProbabilityMeasure P] {H : Ω → ℝ → ℝ}

omit [IsProbabilityMeasure P] in
/-- Multiplying an `L²` integrand by a bounded weight keeps it `L²`. -/
theorem lintegral_sq_bounded_mul_lt_top
    (hq : ∀ T, 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
      (‖H ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
    {g : Ω → ℝ → ℝ} {Kg : ℝ} (hKg0 : 0 ≤ Kg) (hKg : ∀ ω s, |g ω s| ≤ Kg) :
    ∀ T, 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
      (‖g ω s * H ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤ := by
  intro T hT
  have hgle : ∀ (ω : Ω) (s : ℝ), (‖g ω s‖₊ : ℝ≥0∞) ≤ (Real.toNNReal Kg : ℝ≥0∞) := by
    intro ω s
    refine ENNReal.coe_le_coe.mpr ?_
    rw [← NNReal.coe_le_coe, Real.coe_toNNReal Kg hKg0, coe_nnnorm, Real.norm_eq_abs]
    exact hKg ω s
  have hpt : ∀ (ω : Ω) (s : ℝ), (‖g ω s * H ω s‖₊ : ℝ≥0∞) ^ 2
      ≤ (Real.toNNReal Kg : ℝ≥0∞) ^ 2 * (‖H ω s‖₊ : ℝ≥0∞) ^ 2 := by
    intro ω s
    rw [nnnorm_mul, ENNReal.coe_mul, mul_pow]
    gcongr
    exact ENNReal.coe_le_coe.mp (hgle ω s)
  calc ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, (‖g ω s * H ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P
      ≤ ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
          (Real.toNNReal Kg : ℝ≥0∞) ^ 2 * (‖H ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P :=
        lintegral_mono fun ω => lintegral_mono fun s => hpt ω s
    _ = (Real.toNNReal Kg : ℝ≥0∞) ^ 2
          * ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, (‖H ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P := by
        have hne : ((Real.toNNReal Kg : ℝ≥0∞) ^ 2) ≠ ⊤ := by simp
        rw [← MeasureTheory.lintegral_const_mul' _ _ hne]
        exact lintegral_congr fun ω =>
          MeasureTheory.lintegral_const_mul' _ _ hne
    _ < ⊤ := ENNReal.mul_lt_top (by simp) (hq T hT)
end Weight

section Frozen

variable {P : Measure Ω} [IsProbabilityMeasure P] {W : LevyStochCalc.Brownian.BrownianMotion P}
  {ℱ : Filtration ℝ ‹MeasurableSpace Ω›} {hℱ : IsBrownianFiltration W ℱ}
  {H : Ω → ℝ → ℝ} {hm : Measurable (Function.uncurry H)}
  {hp : Probability.ProgressivelyMeasurable ℱ H}
  {hq : ∀ T, 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
    (‖H ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤}
  {X₀ : Ω → ℝ} {bdrift : Ω → ℝ → ℝ} {X : ℝ → Ω → ℝ}
  {C : ℝ} (hC0 : 0 ≤ C) (hCH : ∀ ω s, |H ω s| ≤ C)

end Frozen

end LevyStochCalc.Brownian.Ito


