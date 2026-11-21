-- Prove2me | Definitions.Def_SourceProof_8ef33315e8b9266ce62a44b6
-- name    : SourceProof_8ef33315e8b9266ce62a44b6
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-20T19:39:13.087314+00:00
-- url     : https://prove2.me/theorems/0f1d6df7-5813-42cf-b7b4-6ba0aafd9be3
-- title:
--   LevyStochCalc source module: SourceProof_8ef33315e8b9266ce62a44b6
-- statement:
--   The original source theorem `LevyStochCalc.Brownian.Ito.IsVectorItoVersion.integral_abs_sum_drift_sq_le` comes from the `LevyStochCalc.Brownian.VectorItoQuadVarRiemannTermBounds` module. The staged Lean declaration includes its source proof and dependency references.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Brownian_CrossVariationSum_F000
import Definitions.Def_LevyStochCalc_Brownian_ItoFormulaGrid_F000
import Definitions.Def_LevyStochCalc_Brownian_PolarisedQuadVar_F001
import Definitions.Def_LevyStochCalc_Brownian_VectorItoProcessVersion_F000
import Definitions.Def_SourceProof_2027cb2562c8f45bc0b58378

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


theorem _root_.Prove2MeSourceProof.h_8ef33315e8b9266ce62a44b6
    (h : IsVectorItoVersion W ℱ hcoord H hHm hHp hHs X₀ bdrift X)
    (hbm : ∀ m, Measurable (Function.uncurry (bdrift m))) {B : ℝ} (hB0 : 0 ≤ B)
    (hB : ∀ (m : Fin n) (ω : Ω) (s : ℝ), |bdrift m ω s| ≤ B) (p q : Fin n)
    {φ : (Fin n → ℝ) → ℝ} (hφc : Continuous φ) {Kφ : ℝ} (hKφ0 : 0 ≤ Kφ)
    (hφbd : ∀ x, |φ x| ≤ Kφ) {T : ℝ} (hT : 0 < T) {m : ℕ} (hm0 : m ≠ 0) :
    Integrable (fun ω : Ω => ∑ i ∈ Finset.range m, φ (X (unifGrid T m i) ω)
        * ((∫ s in Set.Ioc (unifGrid T m i) (unifGrid T m (i + 1)), bdrift p ω s ∂volume)
          * ∫ s in Set.Ioc (unifGrid T m i) (unifGrid T m (i + 1)),
              bdrift q ω s ∂volume)) P
      ∧ ∫ ω, |∑ i ∈ Finset.range m, φ (X (unifGrid T m i) ω)
          * ((∫ s in Set.Ioc (unifGrid T m i) (unifGrid T m (i + 1)), bdrift p ω s ∂volume)
            * ∫ s in Set.Ioc (unifGrid T m i) (unifGrid T m (i + 1)),
                bdrift q ω s ∂volume)| ∂P
        ≤ (m : ℝ) * (Kφ * (B * (T / (m : ℝ))) ^ 2) := by
  have hm' : (0 : ℝ) < (m : ℝ) := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hm0)
  have hTm0 : (0 : ℝ) ≤ T / (m : ℝ) := (div_pos hT hm').le
  have hDbd : ∀ (r : Fin n) (ω : Ω) (i : ℕ),
      |∫ s in Set.Ioc (LevyStochCalc.Brownian.Ito.unifGrid T m i) (LevyStochCalc.Brownian.Ito.unifGrid T m (i + 1)), bdrift r ω s ∂volume|
        ≤ B * (T / (m : ℝ)) := by
    intro r ω i
    have hle := _root_.Prove2MeSourceProof.h_0c7e85b4037c170c4bb0381a (Measurable.of_uncurry_left (hbm r)) (hB r ω)
      (LevyStochCalc.Brownian.Ito.unifGrid_lt_succ hT hm0 i).le
    rwa [LevyStochCalc.Brownian.Ito.unifGrid_succ_sub hm0 i] at hle
  have hRm : ∀ i : ℕ, Measurable fun ω : Ω =>
      (∫ s in Set.Ioc (LevyStochCalc.Brownian.Ito.unifGrid T m i) (LevyStochCalc.Brownian.Ito.unifGrid T m (i + 1)), bdrift p ω s ∂volume)
        * ∫ s in Set.Ioc (LevyStochCalc.Brownian.Ito.unifGrid T m i) (LevyStochCalc.Brownian.Ito.unifGrid T m (i + 1)), bdrift q ω s ∂volume :=
    fun i => (LevyStochCalc.measurable_setIntegral_Ioc (hbm p) _ _).mul
      (LevyStochCalc.measurable_setIntegral_Ioc (hbm q) _ _)
  have hRb : ∀ (i : ℕ) (ω : Ω),
      |(∫ s in Set.Ioc (LevyStochCalc.Brownian.Ito.unifGrid T m i) (LevyStochCalc.Brownian.Ito.unifGrid T m (i + 1)), bdrift p ω s ∂volume)
        * ∫ s in Set.Ioc (LevyStochCalc.Brownian.Ito.unifGrid T m i) (LevyStochCalc.Brownian.Ito.unifGrid T m (i + 1)), bdrift q ω s ∂volume|
      ≤ (B * (T / (m : ℝ))) ^ 2 := by
    intro i ω
    rw [abs_mul, pow_two]
    exact mul_le_mul (hDbd p ω i) (hDbd q ω i) (abs_nonneg _) (by positivity)
  have hRdata : ∀ i : ℕ, Integrable (fun ω : Ω =>
        |(∫ s in Set.Ioc (LevyStochCalc.Brownian.Ito.unifGrid T m i) (LevyStochCalc.Brownian.Ito.unifGrid T m (i + 1)), bdrift p ω s ∂volume)
          * ∫ s in Set.Ioc (LevyStochCalc.Brownian.Ito.unifGrid T m i) (LevyStochCalc.Brownian.Ito.unifGrid T m (i + 1)), bdrift q ω s ∂volume|) P
      ∧ ∫ ω, |(∫ s in Set.Ioc (LevyStochCalc.Brownian.Ito.unifGrid T m i) (LevyStochCalc.Brownian.Ito.unifGrid T m (i + 1)),
              bdrift p ω s ∂volume)
            * ∫ s in Set.Ioc (LevyStochCalc.Brownian.Ito.unifGrid T m i) (LevyStochCalc.Brownian.Ito.unifGrid T m (i + 1)),
                bdrift q ω s ∂volume| ∂P
        ≤ (B * (T / (m : ℝ))) ^ 2 := by
    intro i
    obtain ⟨hi, hle⟩ := LevyStochCalc.integral_abs_le_of_bounded (P := P) (hRm i) (by positivity) (hRb i ·)
    exact ⟨hi.abs, hle⟩
  exact _root_.Prove2MeSourceProof.h_2027cb2562c8f45bc0b58378 m (fun i ω => φ (X (LevyStochCalc.Brownian.Ito.unifGrid T m i) ω)) _
    (fun i => hφc.measurable.comp (h.measurable (LevyStochCalc.Brownian.Ito.unifGrid T m i))) hRm hKφ0
    (fun i ω => hφbd _) (fun i => (hRdata i).1) (fun i => (hRdata i).2)
end VectorQuadVar

end LevyStochCalc.Brownian.Ito


