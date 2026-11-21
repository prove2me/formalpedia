-- Prove2me | Definitions.Def_LevyStochCalc_Ito_PicardIntegrandBounds_F000
-- name    : LevyStochCalc_Ito_PicardIntegrandBounds_F000
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-20T20:12:09.906874+00:00
-- url     : https://prove2.me/theorems/7d171ad8-8a23-4a33-9f78-f787d2d3caf1
-- title:
--   Source declarations: LevyStochCalc.Ito.PicardIntegrandBounds
-- statement:
--   Source-preserving extracted declarations from LevyStochCalc.Ito.PicardIntegrandBounds. Existing definitions, lemmas, instances, proofs and elaboration context are retained; generated import closure remains under review.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Ito_PicardBieleckiContractionTight_F000
import Definitions.Def_LevyStochCalc_Ito_PicardBieleckiContraction_F000
import Definitions.Def_LevyStochCalc_Ito_PicardBieleckiNorm_F000
import Definitions.Def_LevyStochCalc_Ito_PicardBieleckiNorm_F001
import Definitions.Def_LevyStochCalc_Ito_PicardSelfMap_F000
import Definitions.Def_LevyStochCalc_Ito_PicardStepMap_F000
import Definitions.Def_LevyStochCalc_Ito_PicardStepMap_F001
import Definitions.Def_LevyStochCalc_Ito_PicardStochasticLipschitz_F000
import Mathlib.Algebra.Order.Chebyshev

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# Square integrability of the Picard integrands along a state process

Linear growth of the coefficients, read off the Lipschitz hypothesis by comparison with the
state `0`, turns the bounds at that single state recorded by `IsRegular` into bounds along a
state process: whenever the state has finite energy over every horizon, the drift, diffusion
and jump integrands evaluated along it are square integrable at every horizon, and a member of
the process space frozen at `T` has that energy. Composing a jointly measurable coefficient
with a measurable, respectively progressively measurable, state process supplies the matching
measurability of the integrands.
-/

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace LevyStochCalc.Ito.Picard

universe u v

variable {Ω : Type u} [MeasurableSpace Ω]
variable {E : Type v} [MeasurableSpace E]

/-- The squared extended norm as an extended real. -/
theorem sq_coe_nnnorm {α : Type*} [SeminormedAddGroup α] (v : α) :
    ((‖v‖₊ : ℝ≥0∞)) ^ 2 = ENNReal.ofReal (‖v‖ ^ 2) := by
  have h1 : (‖v‖₊ : ℝ≥0∞) = ENNReal.ofReal ‖v‖ := by
    rw [ENNReal.ofReal_eq_coe_nnreal (norm_nonneg _)]
    exact congrArg _ (NNReal.eq rfl)
  rw [h1, ← ENNReal.ofReal_pow (norm_nonneg _)]
/-- The squared extended norm of a real number as an extended real. -/
theorem sq_coe_nnnorm_real (x : ℝ) : ((‖x‖₊ : ℝ≥0∞)) ^ 2 = ENNReal.ofReal (x ^ 2) := by
  rw [sq_coe_nnnorm, Real.norm_eq_abs, ← abs_pow,
    abs_of_nonneg (by positivity : (0 : ℝ) ≤ x ^ 2)]
/-- The supremum norm on `Fin n → ℝ` is dominated by the Euclidean sum of squares. -/
theorem sq_norm_le_sum_sq {n : ℕ} (x : Fin n → ℝ) : ‖x‖ ^ 2 ≤ ∑ i, (x i) ^ 2 := by
  have hnn : (0 : ℝ) ≤ ∑ i, (x i) ^ 2 := Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hb : ‖x‖ ≤ Real.sqrt (∑ i, (x i) ^ 2) := by
    refine (pi_norm_le_iff_of_nonneg (Real.sqrt_nonneg _)).mpr fun i => ?_
    rw [Real.norm_eq_abs, ← Real.sqrt_sq_eq_abs]
    exact Real.sqrt_le_sqrt
      (Finset.single_le_sum (fun k _ => sq_nonneg (x k)) (Finset.mem_univ i))
  calc ‖x‖ ^ 2 ≤ (Real.sqrt (∑ i, (x i) ^ 2)) ^ 2 := by
        nlinarith [norm_nonneg x, Real.sqrt_nonneg (∑ i, (x i) ^ 2)]
    _ = ∑ i, (x i) ^ 2 := Real.sq_sqrt hnn
/-- **Linear growth of the diffusion coefficient in the state**, read off the Lipschitz
hypothesis by comparing with the state `0`. -/
theorem sq_sigma_le {n d : ℕ} {ν : MeasureTheory.Measure E}
    (coeffs : LevyStochCalc.Ito.Setting.JumpDiffusionCoeffs n d E) {L : ℝ}
    (hLip : LevyStochCalc.Ito.Setting.JumpDiffusionCoeffs.IsLipschitz coeffs ν L)
    (s : ℝ) (x : Fin n → ℝ) (i : Fin n) (j : Fin d) :
    (coeffs.σ s x i j) ^ 2
      ≤ 2 * (coeffs.σ s 0 i j) ^ 2 + 2 * (L ^ 2 * ∑ i', (x i') ^ 2) := by
  have hsum := hLip.2.2.1 s x 0
  have hinner : (coeffs.σ s x i j - coeffs.σ s 0 i j) ^ 2
      ≤ ∑ j', (coeffs.σ s x i j' - coeffs.σ s 0 i j') ^ 2 :=
    Finset.single_le_sum (f := fun j' => (coeffs.σ s x i j' - coeffs.σ s 0 i j') ^ 2)
      (fun _ _ => sq_nonneg _) (Finset.mem_univ j)
  have houter : (∑ j', (coeffs.σ s x i j' - coeffs.σ s 0 i j') ^ 2)
      ≤ ∑ i', ∑ j', (coeffs.σ s x i' j' - coeffs.σ s 0 i' j') ^ 2 :=
    Finset.single_le_sum
      (f := fun i' => ∑ j', (coeffs.σ s x i' j' - coeffs.σ s 0 i' j') ^ 2)
      (fun _ _ => Finset.sum_nonneg fun _ _ => sq_nonneg _) (Finset.mem_univ i)
  have hx : ‖x - 0‖ ^ 2 ≤ ∑ i', (x i') ^ 2 := by
    rw [sub_zero]
    exact sq_norm_le_sum_sq x
  have hmul : L ^ 2 * ‖x - 0‖ ^ 2 ≤ L ^ 2 * ∑ i', (x i') ^ 2 :=
    mul_le_mul_of_nonneg_left hx (sq_nonneg L)
  have hAM : (coeffs.σ s x i j) ^ 2
      ≤ 2 * (coeffs.σ s x i j - coeffs.σ s 0 i j) ^ 2 + 2 * (coeffs.σ s 0 i j) ^ 2 := by
    nlinarith [sq_nonneg (coeffs.σ s x i j - 2 * coeffs.σ s 0 i j)]
  linarith [(hinner.trans houter).trans (hsum.trans hmul)]
end LevyStochCalc.Ito.Picard


