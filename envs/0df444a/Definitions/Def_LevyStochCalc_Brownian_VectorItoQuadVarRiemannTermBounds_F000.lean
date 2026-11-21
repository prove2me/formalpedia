-- Prove2me | Definitions.Def_LevyStochCalc_Brownian_VectorItoQuadVarRiemannTermBounds_F000
-- name    : LevyStochCalc_Brownian_VectorItoQuadVarRiemannTermBounds_F000
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-20T19:36:52.611416+00:00
-- url     : https://prove2.me/theorems/89081703-e5af-4dae-8323-e87a0690878d
-- title:
--   Source declarations: LevyStochCalc.Brownian.VectorItoQuadVarRiemannTermBounds
-- statement:
--   Source-preserving extracted declarations from LevyStochCalc.Brownian.VectorItoQuadVarRiemannTermBounds. Existing definitions, lemmas, instances, proofs and elaboration context are retained; generated import closure remains under review.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Brownian_CrossVariationSum_F000
import Definitions.Def_LevyStochCalc_Brownian_ItoFormulaGrid_F000
import Definitions.Def_LevyStochCalc_Brownian_PolarisedQuadVar_F001
import Mathlib.Algebra.Order.Chebyshev

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

/-- The squared cell lengths of the uniform grid sum to `T²/m`. -/
theorem sum_unifGrid_sq_diff {T : ℝ} (hT : 0 < T) {m : ℕ} (hm0 : m ≠ 0) :
    ∑ i ∈ Finset.range m, (unifGrid T m (i + 1) - unifGrid T m i) ^ 2 = T ^ 2 / (m : ℝ) := by
  have hm' : (0 : ℝ) < (m : ℝ) := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hm0)
  have hterm : ∀ i ∈ Finset.range m,
      (unifGrid T m (i + 1) - unifGrid T m i) ^ 2 = (T / (m : ℝ)) ^ 2 :=
    fun i _ => by rw [unifGrid_succ_sub hm0 i]
  rw [Finset.sum_congr rfl hterm, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  field_simp
omit [IsProbabilityMeasure P] in
/-- The first absolute moment of a sum is at most the sum of the bounds. -/
theorem integral_abs_add_le {f g : Ω → ℝ} (hf : Integrable f P) (hg : Integrable g P)
    {a b : ℝ} (ha : ∫ ω, |f ω| ∂P ≤ a) (hb : ∫ ω, |g ω| ∂P ≤ b) :
    ∫ ω, |f ω + g ω| ∂P ≤ a + b := by
  calc ∫ ω, |f ω + g ω| ∂P ≤ ∫ ω, (|f ω| + |g ω|) ∂P :=
        MeasureTheory.integral_mono (hf.add hg).abs (hf.abs.add hg.abs)
          (fun ω => abs_add_le _ _)
    _ = (∫ ω, |f ω| ∂P) + ∫ ω, |g ω| ∂P := MeasureTheory.integral_add hf.abs hg.abs
    _ ≤ a + b := add_le_add ha hb
omit [IsProbabilityMeasure P] in
/-- The first absolute moment of a finite sum is at most the sum of the bounds. -/
theorem integral_abs_finsetSum_le {ι : Type*} (s : Finset ι) (F : ι → Ω → ℝ)
    (hF : ∀ j ∈ s, Integrable (F j) P) (c : ι → ℝ) (hc : ∀ j ∈ s, ∫ ω, |F j ω| ∂P ≤ c j) :
    ∫ ω, |∑ j ∈ s, F j ω| ∂P ≤ ∑ j ∈ s, c j := by
  have hsum : Integrable (fun ω => ∑ j ∈ s, F j ω) P :=
    MeasureTheory.integrable_finsetSum _ hF
  have habs : Integrable (fun ω => ∑ j ∈ s, |F j ω|) P :=
    MeasureTheory.integrable_finsetSum _ fun j hj => (hF j hj).abs
  calc ∫ ω, |∑ j ∈ s, F j ω| ∂P ≤ ∫ ω, ∑ j ∈ s, |F j ω| ∂P :=
        MeasureTheory.integral_mono hsum.abs habs fun ω => Finset.abs_sum_le_sum_abs _ _
    _ = ∑ j ∈ s, ∫ ω, |F j ω| ∂P :=
        MeasureTheory.integral_finsetSum _ fun j hj => (hF j hj).abs
    _ ≤ ∑ j ∈ s, c j := Finset.sum_le_sum hc
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


