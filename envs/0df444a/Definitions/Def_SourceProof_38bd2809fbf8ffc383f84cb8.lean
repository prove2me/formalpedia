-- Prove2me | Definitions.Def_SourceProof_38bd2809fbf8ffc383f84cb8
-- name    : SourceProof_38bd2809fbf8ffc383f84cb8
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-20T09:52:56.185381+00:00
-- url     : https://prove2.me/theorems/dd11ae13-556c-471c-b605-dc0be4210d8b
-- title:
--   LevyStochCalc source module: SourceProof_38bd2809fbf8ffc383f84cb8
-- statement:
--   The original source theorem `LevyStochCalc.Poisson.Compensated.exists_sharedMark_blockDiag` comes from the `LevyStochCalc.Poisson.CompensatedDensityRefinement` module. The staged Lean declaration includes its source proof and dependency references.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Poisson_CompensatedDensityMarkSum_F001
import Definitions.Def_LevyStochCalc_Poisson_CompensatedDensityMarkSum_F002

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


theorem _root_.Prove2MeSourceProof.h_38bd2809fbf8ffc383f84cb8
    {P : Measure Ω} [IsProbabilityMeasure P] {ν : Measure E} [SigmaFinite ν]
    (_N : LevyStochCalc.Poisson.PoissonRandomMeasure P ν)
    (ℱ : Filtration ℝ ‹MeasurableSpace Ω›) {N₀ : ℕ} (p : Fin (N₀ + 1) → ℝ)
    {Ki : Fin N₀ → ℕ} (Bi : ∀ i, Fin (Ki i) → Set E) (ci : ∀ i, Fin (Ki i) → Ω → ℝ)
    (hBim : ∀ i k, MeasurableSet (Bi i k)) (hBif : ∀ i k, ν (Bi i k) ≠ ⊤)
    (hcib : ∀ i k, ∃ M, ∀ ω, |ci i k ω| ≤ M) (hcim : ∀ i k, Measurable (ci i k))
    (hcia : ∀ i k, @MeasureTheory.StronglyMeasurable Ω ℝ _
      (ℱ (p i.castSucc)) (ci i k)) :
    ∃ (K : ℕ) (B : Fin K → Set E) (ξ : Fin N₀ → Fin K → Ω → ℝ),
      (∀ k, MeasurableSet (B k)) ∧ (∀ k, ν (B k) ≠ ⊤) ∧
      (∀ i k, ∃ M, ∀ ω, |ξ i k ω| ≤ M) ∧ (∀ i k, Measurable (ξ i k)) ∧
      (∀ i k, @MeasureTheory.StronglyMeasurable Ω ℝ _
        (ℱ (p i.castSucc)) (ξ i k)) ∧
      (∀ (i : Fin N₀) (ω : Ω) (F : Set E → ℝ),
        (∑ k, ξ i k ω * F (B k)) = ∑ k₀, ci i k₀ ω * F (Bi i k₀)) := by
  classical
  set ι : Type _ := Σ i : Fin N₀, Fin (Ki i) with hι
  set e := Fintype.equivFin ι with he
  refine ⟨Fintype.card ι, fun k => Bi (e.symm k).1 (e.symm k).2,
    fun i k ω => if (e.symm k).1 = i then ci (e.symm k).1 (e.symm k).2 ω else 0,
    fun k => hBim _ _, fun k => hBif _ _, ?_, ?_, ?_, ?_⟩
  · intro i k
    obtain ⟨M, hM⟩ := hcib (e.symm k).1 (e.symm k).2
    refine ⟨M, fun ω => ?_⟩
    by_cases h : (e.symm k).1 = i
    · simp only [h, if_true]; exact hM ω
    · simp only [h, if_false, abs_zero]; exact le_trans (abs_nonneg _) (hM ω)
  · intro i k
    by_cases h : (e.symm k).1 = i
    · simp only [h, if_true]; exact hcim _ _
    · simp only [h, if_false]; exact measurable_const
  · intro i k
    by_cases h : (e.symm k).1 = i
    · simp only [h, if_true]
      rw [← h]; exact hcia (e.symm k).1 (e.symm k).2
    · simp only [h, if_false]; exact MeasureTheory.stronglyMeasurable_const
  · intro i ω F
    rw [← Equiv.sum_comp e (fun k => (if (e.symm k).1 = i then ci (e.symm k).1 (e.symm k).2 ω
      else 0) * F (Bi (e.symm k).1 (e.symm k).2))]
    simp only [Equiv.symm_apply_apply]
    rw [← Finset.univ_sigma_univ, Finset.sum_sigma]
    rw [Finset.sum_eq_single i
      (fun i₀ _ hne => Finset.sum_eq_zero (fun k₀ _ => by rw [if_neg hne, zero_mul]))
      (fun h => absurd (Finset.mem_univ i) h)]
    refine Finset.sum_congr rfl (fun k₀ _ => ?_)
    rw [Equiv.symm_apply_apply]; simp
/-! ### Cross-resolution refinement (toward the `L²(P)` Cauchy property)

To compare the step integrals of two density approximants at *different* dyadic
levels, both are re-expressed on the common (finer) dyadic refinement. The basic
brick is additivity of the compensated integral over a split time-interval. -/

end LevyStochCalc.Poisson.Compensated


