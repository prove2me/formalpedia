-- Prove2me | Definitions.Def_LevyStochCalc_Brownian_VectorItoProcess_F000
-- name    : LevyStochCalc_Brownian_VectorItoProcess_F000
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-20T19:19:24.95811+00:00
-- url     : https://prove2.me/theorems/3efc762c-6380-47ad-9775-8afb8c999a79
-- title:
--   Source declarations: LevyStochCalc.Brownian.VectorItoProcess
-- statement:
--   Source-preserving extracted declarations from LevyStochCalc.Brownian.VectorItoProcess. Existing definitions, lemmas, instances, proofs and elaboration context are retained; generated import closure remains under review.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Brownian_ItoProcess_F000
import Definitions.Def_LevyStochCalc_Brownian_MultidimFiltered_F000
import Mathlib.Algebra.Order.Chebyshev

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# Vector Itô processes and the moments of their increments

A vector Itô process is `X_t = X₀ + ∫_{[0,t]} b_s ds + ∑ₖ ∫_0^t H^{·,k}_s dWᵏ_s` with values in
`Fin n → ℝ`, driven by a `d`-dimensional Brownian motion. Each coordinate's increment across a
window is a drift increment plus a finite sum of Itô-integral increments, so its moments follow
from the drift bound, the increment moments of the scalar Itô integral and Jensen's inequality
for sums; the supremum norm on `Fin n → ℝ` is then controlled coordinatewise.

## Main statements

* `LevyStochCalc.Brownian.Ito.vectorItoProcess` — the process itself.
* `LevyStochCalc.Brownian.Ito.vectorItoProcess_sub` — the coordinate increment splits into a
  drift part and a sum of Itô-integral increments.
* `LevyStochCalc.Brownian.Ito.integral_sq_vectorItoProcess_sub_le` — the coordinate second
  moment `𝔼|ΔXᵐ|² ≤ 2(BΔt)² + 2d²C²Δt`.
* `LevyStochCalc.Brownian.Ito.integral_abs_vectorItoProcess_sub_le` — the coordinate first
  absolute moment `𝔼|ΔXᵐ| ≤ BΔt + dC√(Δt)`.
* `LevyStochCalc.Brownian.Ito.integral_norm_vectorItoProcess_sub_le` and
  `LevyStochCalc.Brownian.Ito.integral_sq_norm_vectorItoProcess_sub_le` — the same two moments
  for the supremum norm of the vector increment.
* `LevyStochCalc.Brownian.Ito.integrable_norm_vectorItoProcess_sub_pow_three` — the cube of the
  norm of the increment is integrable.
-/

namespace LevyStochCalc.Brownian.Ito

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

universe u

section PiNorm

variable {n : ℕ}

/-- The supremum norm on `Fin n → ℝ` is at most the sum of the absolute coordinates. -/
theorem norm_pi_le_sum_abs (x : Fin n → ℝ) : ‖x‖ ≤ ∑ m, |x m| := by
  refine (pi_norm_le_iff_of_nonneg (Finset.sum_nonneg fun j _ => abs_nonneg (x j))).2 fun m => ?_
  rw [Real.norm_eq_abs]
  exact Finset.single_le_sum (fun j _ => abs_nonneg (x j)) (Finset.mem_univ m)
/-- The square of the supremum norm on `Fin n → ℝ` is at most the sum of the squared
coordinates. -/
theorem sq_norm_pi_le_sum_sq (x : Fin n → ℝ) : ‖x‖ ^ 2 ≤ ∑ m, (x m) ^ 2 := by
  have hs : (0 : ℝ) ≤ ∑ m, (x m) ^ 2 := Finset.sum_nonneg fun j _ => sq_nonneg (x j)
  have hle : ‖x‖ ≤ Real.sqrt (∑ m, (x m) ^ 2) := by
    refine (pi_norm_le_iff_of_nonneg (Real.sqrt_nonneg _)).2 fun m => ?_
    rw [Real.norm_eq_abs, ← Real.sqrt_sq_eq_abs]
    exact Real.sqrt_le_sqrt
      (Finset.single_le_sum (fun j _ => sq_nonneg (x j)) (Finset.mem_univ m))
  calc ‖x‖ ^ 2 ≤ Real.sqrt (∑ m, (x m) ^ 2) ^ 2 := pow_le_pow_left₀ (norm_nonneg x) hle 2
    _ = ∑ m, (x m) ^ 2 := Real.sq_sqrt hs
/-- The cube of the supremum norm on `Fin n → ℝ` is at most `n²` times the sum of the cubed
absolute coordinates. -/
theorem cube_norm_pi_le_sum_abs_cube (x : Fin n → ℝ) :
    ‖x‖ ^ 3 ≤ (n : ℝ) ^ 2 * ∑ m, |x m| ^ 3 := by
  have h1 : ‖x‖ ^ 3 ≤ (∑ m, |x m|) ^ 3 :=
    pow_le_pow_left₀ (norm_nonneg x) (norm_pi_le_sum_abs x) 3
  have h2 := pow_sum_le_card_mul_sum_pow (s := (Finset.univ : Finset (Fin n)))
    (f := fun m => |x m|) (fun j _ => abs_nonneg (x j)) 2
  simpa using h1.trans h2
end PiNorm

section FiniteSums

variable {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} {ι : Type*} [Fintype ι]

/-- A finite sum of functions with integrable absolute values has integrable absolute value, and
its first absolute moment is at most the sum of theirs. -/
theorem integrable_abs_sum_and_le {f : ι → Ω → ℝ} (hfm : ∀ i, Measurable (f i))
    (hfi : ∀ i, Integrable (fun ω => |f i ω|) P) :
    Integrable (fun ω => |∑ i, f i ω|) P
      ∧ ∫ ω, |∑ i, f i ω| ∂P ≤ ∑ i, ∫ ω, |f i ω| ∂P := by
  have hdom : Integrable (fun ω => ∑ i, |f i ω|) P :=
    MeasureTheory.integrable_finsetSum _ fun i _ => hfi i
  have hpt : ∀ ω, |∑ i, f i ω| ≤ ∑ i, |f i ω| := fun ω => Finset.abs_sum_le_sum_abs _ _
  have hmeas : Measurable fun ω => |∑ i, f i ω| :=
    (Finset.measurable_sum _ fun i _ => hfm i).abs
  have hint : Integrable (fun ω => |∑ i, f i ω|) P := by
    refine hdom.mono' hmeas.aestronglyMeasurable (Filter.Eventually.of_forall fun ω => ?_)
    rw [Real.norm_eq_abs, abs_abs]
    exact hpt ω
  refine ⟨hint, ?_⟩
  calc ∫ ω, |∑ i, f i ω| ∂P ≤ ∫ ω, ∑ i, |f i ω| ∂P :=
        MeasureTheory.integral_mono hint hdom hpt
    _ = ∑ i, ∫ ω, |f i ω| ∂P := MeasureTheory.integral_finsetSum _ fun i _ => hfi i
/-- A finite sum of functions with integrable squares has integrable square, and its second
moment is at most the number of summands times the sum of theirs. -/
theorem integrable_sq_sum_and_le {f : ι → Ω → ℝ} (hfm : ∀ i, Measurable (f i))
    (hfi : ∀ i, Integrable (fun ω => (f i ω) ^ 2) P) :
    Integrable (fun ω => (∑ i, f i ω) ^ 2) P
      ∧ ∫ ω, (∑ i, f i ω) ^ 2 ∂P
        ≤ (Fintype.card ι : ℝ) * ∑ i, ∫ ω, (f i ω) ^ 2 ∂P := by
  have hdom : Integrable (fun ω => (Fintype.card ι : ℝ) * ∑ i, (f i ω) ^ 2) P :=
    (MeasureTheory.integrable_finsetSum _ fun i _ => hfi i).const_mul _
  have hpt : ∀ ω, (∑ i, f i ω) ^ 2 ≤ (Fintype.card ι : ℝ) * ∑ i, (f i ω) ^ 2 := fun ω => by
    have h := sq_sum_le_card_mul_sum_sq (s := (Finset.univ : Finset ι))
      (f := fun i => f i ω)
    simpa using h
  have hmeas : Measurable fun ω => (∑ i, f i ω) ^ 2 :=
    (Finset.measurable_sum _ fun i _ => hfm i).pow_const 2
  have hint : Integrable (fun ω => (∑ i, f i ω) ^ 2) P := by
    refine hdom.mono' hmeas.aestronglyMeasurable (Filter.Eventually.of_forall fun ω => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    exact hpt ω
  refine ⟨hint, ?_⟩
  calc ∫ ω, (∑ i, f i ω) ^ 2 ∂P
      ≤ ∫ ω, (Fintype.card ι : ℝ) * ∑ i, (f i ω) ^ 2 ∂P :=
        MeasureTheory.integral_mono hint hdom hpt
    _ = (Fintype.card ι : ℝ) * ∑ i, ∫ ω, (f i ω) ^ 2 ∂P := by
        rw [MeasureTheory.integral_const_mul,
          MeasureTheory.integral_finsetSum _ fun i _ => hfi i]
end FiniteSums

section VectorProcess

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

variable {C : ℝ} (hC0 : 0 ≤ C)
  (hCH : ∀ (m : Fin n) (k : Fin d) (ω : Ω) (s : ℝ), |H m k ω s| ≤ C)

section VectorMoments

variable (X₀ : Ω → Fin n → ℝ) (bdrift : Fin n → Ω → ℝ → ℝ)
  (hbm : ∀ m, Measurable (Function.uncurry (bdrift m))) {B : ℝ} (hB0 : 0 ≤ B)
  (hB : ∀ (m : Fin n) (ω : Ω) (s : ℝ), |bdrift m ω s| ≤ B)

end VectorMoments

end VectorProcess

end LevyStochCalc.Brownian.Ito


