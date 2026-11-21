-- Prove2me | Definitions.Def_LevyStochCalc_Poisson_CompensatedDensityRefinement_F003
-- name    : LevyStochCalc_Poisson_CompensatedDensityRefinement_F003
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-20T09:23:54.527181+00:00
-- url     : https://prove2.me/theorems/3040b36c-2701-43bc-bda1-a30a3c252b7a
-- title:
--   Source declarations: LevyStochCalc.Poisson.CompensatedDensityRefinement
-- statement:
--   Source-preserving extracted declarations from LevyStochCalc.Poisson.CompensatedDensityRefinement. Existing definitions, lemmas, instances, proofs and elaboration context are retained; generated import closure remains under review.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Poisson_CompensatedDensityRefinement_F002

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# Doob `L²` bricks and dyadic cross-resolution refinement

Two preparations for the passage to the limit: the submartingale property of `‖M‖` and the
discrete tail maximal inequality for a martingale, and the re-expression of a dyadic step
integrand at level `n` on a finer dyadic level `m ≥ n`. The refinement keeps the integrand
adapted and its compensated integral unchanged, so integrands of different resolutions can be
compared on a common grid.
-/

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace LevyStochCalc.Poisson.Compensated

universe u v

variable {Ω : Type u} [MeasurableSpace Ω]
variable {E : Type v} [MeasurableSpace E]

/-! ### Doob `L²` machinery (toward the càdlàg conjunct of #6)

Mathlib has only the discrete *tail* maximal inequality (`maximal_ineq`), the
layer-cake formula, and conditional Jensen. The continuous-time Doob `L²` maximal
inequality and the càdlàg regularization are built here from those pieces. -/

/-! ### Cross-resolution refinement (toward the `L²(P)` Cauchy property)

To compare the step integrals of two density approximants at *different* dyadic
levels, both are re-expressed on the common (finer) dyadic refinement. The basic
brick is additivity of the compensated integral over a split time-interval. -/

/-- The coarse left endpoint is `≤` the fine left endpoint: `p^n_{coarse i'} ≤ p^m_{i'}`. -/
lemma dyadic_coarse_point_le {T : ℝ} (hT : 0 < T) {n m : ℕ} (hnm : n ≤ m) (i' : Fin (2 ^ m)) :
    dyadicPartition T n (dyadicCoarse n m hnm i').castSucc
      ≤ dyadicPartition T m i'.castSucc := by
  simp only [dyadicPartition, Fin.val_castSucc, dyadicCoarse]
  rw [div_le_div_iff₀ (by positivity : (0 : ℝ) < ((2 ^ n : ℕ) : ℝ))
    (by positivity : (0 : ℝ) < ((2 ^ m : ℕ) : ℝ))]
  have hkey : ((i'.val / 2 ^ (m - n) : ℕ) : ℝ) * ((2 ^ (m - n) : ℕ) : ℝ) ≤ (i'.val : ℝ) := by
    rw [← Nat.cast_mul]; exact_mod_cast Nat.div_mul_le_self i'.val (2 ^ (m - n))
  have h2m : ((2 ^ m : ℕ) : ℝ) = ((2 ^ n : ℕ) : ℝ) * ((2 ^ (m - n) : ℕ) : ℝ) := by
    rw [← Nat.cast_mul, ← pow_add, Nat.add_sub_cancel' hnm]
  rw [h2m]
  nlinarith [mul_le_mul_of_nonneg_right hkey (by positivity : (0 : ℝ) ≤ T * ((2 ^ n : ℕ) : ℝ))]
/-- Refined coefficients stay adapted at the finer dyadic endpoint: `ci(coarse i')` is
`ℱ_{p^m_{i'}}`-measurable (it is `ℱ_{p^n_{coarse i'}}`-measurable and `ℱ` is monotone). -/
lemma dyadic_refine_adapted
    {P : Measure Ω} [IsProbabilityMeasure P] {ν : Measure E} [SigmaFinite ν]
    (_N : LevyStochCalc.Poisson.PoissonRandomMeasure P ν)
    (ℱ : Filtration ℝ ‹MeasurableSpace Ω›) {T : ℝ} (hT : 0 < T) {n m : ℕ}
    (hnm : n ≤ m) {Ki : Fin (2 ^ n) → ℕ} (ci : ∀ i, Fin (Ki i) → Ω → ℝ)
    (hcia : ∀ i k, @MeasureTheory.StronglyMeasurable Ω ℝ _
      (ℱ (dyadicPartition T n i.castSucc)) (ci i k))
    (i' : Fin (2 ^ m)) (k₀ : Fin (Ki (dyadicCoarse n m hnm i'))) :
    @MeasureTheory.StronglyMeasurable Ω ℝ _
      (ℱ (dyadicPartition T m i'.castSucc))
      (ci (dyadicCoarse n m hnm i') k₀) :=
  (hcia (dyadicCoarse n m hnm i') k₀).mono
    (ℱ.mono (dyadic_coarse_point_le hT hnm i'))
omit [MeasurableSpace Ω] [MeasurableSpace E] in
/-- **Step-eval refinement.** The level-`n` step eval equals (pointwise) the level-`m`
step eval whose fine pieces inherit their coarse piece's marks and coefficients. (Sum
`dyadic_indicator_refine` over the coarse pieces via `dyadic_sum_split`.) -/
lemma stepIntegral_dyadic_refine_eval {T : ℝ} (hT : 0 < T) {n m : ℕ} (hnm : n ≤ m)
    {Ki : Fin (2 ^ n) → ℕ} (Bi : ∀ i, Fin (Ki i) → Set E) (ci : ∀ i, Fin (Ki i) → Ω → ℝ)
    (s : ℝ) (ω : Ω) (e : E) :
    (∑ i' : Fin (2 ^ m), (Set.Ioc (dyadicPartition T m i'.castSucc)
          (dyadicPartition T m i'.succ)).indicator (fun _ => (1 : ℝ)) s
        * ∑ k₀ : Fin (Ki (dyadicCoarse n m hnm i')), ci (dyadicCoarse n m hnm i') k₀ ω
            * (Bi (dyadicCoarse n m hnm i') k₀).indicator (fun _ => (1 : ℝ)) e)
      = ∑ i : Fin (2 ^ n), (Set.Ioc (dyadicPartition T n i.castSucc)
          (dyadicPartition T n i.succ)).indicator (fun _ => (1 : ℝ)) s
        * ∑ k₀, ci i k₀ ω * (Bi i k₀).indicator (fun _ => (1 : ℝ)) e := by
  classical
  rw [dyadic_sum_split hnm (fun i' => (Set.Ioc (dyadicPartition T m i'.castSucc)
      (dyadicPartition T m i'.succ)).indicator (fun _ => (1 : ℝ)) s
      * ∑ k₀ : Fin (Ki (dyadicCoarse n m hnm i')), ci (dyadicCoarse n m hnm i') k₀ ω
          * (Bi (dyadicCoarse n m hnm i') k₀).indicator (fun _ => (1 : ℝ)) e)]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [Finset.sum_congr rfl (fun j _ => by rw [dyadicCoarse_combine hnm i j]),
    ← Finset.sum_mul, dyadic_indicator_refine hT hnm i s]
end LevyStochCalc.Poisson.Compensated


