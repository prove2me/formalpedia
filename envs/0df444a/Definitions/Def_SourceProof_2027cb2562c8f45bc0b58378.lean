-- Prove2me | Definitions.Def_SourceProof_2027cb2562c8f45bc0b58378
-- name    : SourceProof_2027cb2562c8f45bc0b58378
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-20T19:34:43.898419+00:00
-- url     : https://prove2.me/theorems/dbd7b551-da90-426d-89bd-5b989d7d8531
-- title:
--   LevyStochCalc source module: SourceProof_2027cb2562c8f45bc0b58378
-- statement:
--   The original source theorem `LevyStochCalc.Brownian.Ito.integral_abs_weighted_cellSum_le` comes from the `LevyStochCalc.Brownian.VectorItoQuadVarRiemannTermBounds` module. The staged Lean declaration includes its source proof and dependency references.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Brownian_CrossVariationSum_F000
import Definitions.Def_LevyStochCalc_Brownian_PolarisedQuadVar_F001
import Definitions.Def_LevyStochCalc_Probability_AbsMoment_F000
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# Cell sums and the error terms of the quadratic-variation Riemann sum

Summing terms attached to the cells of a uniform grid against weights bounded by `Kw` multiplies
a common bound on their first absolute moments by `N·Kw`. Applied to the increments of two
coordinates of a continuous vector Itô process across a grid of `m` cells, weighted by a bounded
function of the process, this bounds the drift–drift term by `O(1/m)` and the drift–martingale
terms, the compensated products on the diagonal in the Brownian index and the cross terms off
that diagonal by `O(m^{-1/2})`.

## Main statements

* `LevyStochCalc.Brownian.Ito.integral_abs_weighted_cellSum_le` — the `L¹` bound for a weighted
  sum of cell terms with a common first-absolute-moment bound.
* `LevyStochCalc.Brownian.Ito.IsVectorItoVersion.integral_abs_sum_drift_sq_le` — the
  drift–drift term.
* `LevyStochCalc.Brownian.Ito.IsVectorItoVersion.integral_abs_sum_driftCross_le` — a
  drift–martingale term.
-/

namespace LevyStochCalc.Brownian.Ito

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

universe u

section CellSums

variable {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]

omit [IsProbabilityMeasure P] in

theorem _root_.Prove2MeSourceProof.h_2027cb2562c8f45bc0b58378 (N : ℕ) (w R : ℕ → Ω → ℝ)
    (hwm : ∀ i, Measurable (w i)) (hRm : ∀ i, Measurable (R i))
    {Kw : ℝ} (hKw0 : 0 ≤ Kw) (hwb : ∀ (i : ℕ) (ω : Ω), |w i ω| ≤ Kw)
    (hRint : ∀ i, Integrable (fun ω => |R i ω|) P)
    {ρ : ℝ} (hRle : ∀ i, ∫ ω, |R i ω| ∂P ≤ ρ) :
    Integrable (fun ω => ∑ i ∈ Finset.range N, w i ω * R i ω) P
      ∧ ∫ ω, |∑ i ∈ Finset.range N, w i ω * R i ω| ∂P ≤ (N : ℝ) * (Kw * ρ) := by
  have hdom : Integrable (fun ω => ∑ i ∈ Finset.range N, Kw * |R i ω|) P :=
    MeasureTheory.integrable_finsetSum _ fun i _ => (hRint i).const_mul _
  have hmeas : Measurable fun ω => ∑ i ∈ Finset.range N, w i ω * R i ω :=
    Finset.measurable_sum _ fun i _ => (hwm i).mul (hRm i)
  have hpt : ∀ ω, |∑ i ∈ Finset.range N, w i ω * R i ω|
      ≤ ∑ i ∈ Finset.range N, Kw * |R i ω| := by
    intro ω
    refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i _ => ?_)
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_right (hwb i ω) (abs_nonneg _)
  have hint : Integrable (fun ω => ∑ i ∈ Finset.range N, w i ω * R i ω) P := by
    refine hdom.mono hmeas.aestronglyMeasurable (Filter.Eventually.of_forall fun ω => ?_)
    rw [Real.norm_eq_abs, Real.norm_eq_abs]
    exact (hpt ω).trans (le_abs_self _)
  refine ⟨hint, ?_⟩
  calc ∫ ω, |∑ i ∈ Finset.range N, w i ω * R i ω| ∂P
      ≤ ∫ ω, ∑ i ∈ Finset.range N, Kw * |R i ω| ∂P :=
        MeasureTheory.integral_mono hint.abs hdom hpt
    _ = ∑ i ∈ Finset.range N, Kw * ∫ ω, |R i ω| ∂P := by
        rw [MeasureTheory.integral_finsetSum _ fun i _ => (hRint i).const_mul _]
        exact Finset.sum_congr rfl fun i _ => MeasureTheory.integral_const_mul _ _
    _ ≤ ∑ _i ∈ Finset.range N, Kw * ρ :=
        Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_left (hRle i) hKw0
    _ = (N : ℝ) * (Kw * ρ) := by
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
end CellSums

section VectorQuadVar

open LevyStochCalc.Brownian.Multidim

variable {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {n d : ℕ} {W : Multidim.MultidimBrownianMotion P d}
  {ℱ : Filtration ℝ ‹MeasurableSpace Ω›}
  {hcoord : ∀ k : Fin d, IsBrownianFiltration (W.W k) ℱ}
  {H : Fin n → Fin d → Ω → ℝ → ℝ}
  {hHm : ∀ m k, Measurable (Function.uncurry (H m k))}
  {hHp : ∀ m k, Probability.ProgressivelyMeasurable ℱ (H m k)}
  {hHs : ∀ (m : Fin n) (k : Fin d) (T : ℝ), 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
    (‖H m k ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤}
  {X₀ : Ω → Fin n → ℝ} {bdrift : Fin n → Ω → ℝ → ℝ} {X : ℝ → Ω → Fin n → ℝ}
  {C : ℝ} (hC0 : 0 ≤ C)
  (hCH : ∀ (m : Fin n) (k : Fin d) (ω : Ω) (s : ℝ), |H m k ω s| ≤ C)

end VectorQuadVar

end LevyStochCalc.Brownian.Ito


