-- Prove2me | Definitions.Def_LevyStochCalc_Analysis_FiniteJumpSum_F000
-- name    : LevyStochCalc_Analysis_FiniteJumpSum_F000
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-18T22:16:49.513162+00:00
-- url     : https://prove2.me/theorems/1f08ac95-372b-46b1-ba68-01d6d59f46a2
-- title:
--   Source declarations: LevyStochCalc.Analysis.FiniteJumpSum
-- statement:
--   Source-preserving extracted declarations from LevyStochCalc.Analysis.FiniteJumpSum. Existing definitions, lemmas, instances, proofs and elaboration context are retained; generated import closure remains under review.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Analysis_DyadicGrid_F000
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Dirac

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# Sums of finitely many jumps along a dyadic grid

A finite set of points of `ℝ × E` with weights defines a step function of the time,
`jumpSum S c s`, the sum of the weights of the points with time in `(0, s]`, and its strict-past
version `jumpSumStrict S c s`. Along the dyadic grid of `[0, t]` the frozen values
`jumpSum S c (leftPt t n s)` are eventually the strict-past value, and the sums of the increments
over the cells weighted by a continuous function at the right endpoints converge to the sum of
the weights times the function at the points. A finite sum of Dirac masses integrates a function
over a time window to such a jump sum.
-/

open Filter MeasureTheory
open scoped Topology BigOperators

namespace LevyStochCalc.Analysis

variable {E : Type*}

section Sums

open scoped Classical in
/-- The sum of the weights of the points with time in `(0, s]`. -/
noncomputable def jumpSum (S : Finset (ℝ × E)) (c : ℝ × E → ℝ) (s : ℝ) : ℝ :=
  ∑ p ∈ S, if 0 < p.1 ∧ p.1 ≤ s then c p else 0
open scoped Classical in
/-- The sum of the weights of the points with time in `(0, s)`. -/
noncomputable def jumpSumStrict (S : Finset (ℝ × E)) (c : ℝ × E → ℝ) (s : ℝ) : ℝ :=
  ∑ p ∈ S, if 0 < p.1 ∧ p.1 < s then c p else 0
open scoped Classical in
/-- The increment of the jump sum over `(u, v]`. -/
theorem jumpSum_sub (S : Finset (ℝ × E)) (c : ℝ × E → ℝ) {u v : ℝ} (hu : 0 ≤ u) (huv : u ≤ v) :
    jumpSum S c v - jumpSum S c u = ∑ p ∈ S, if u < p.1 ∧ p.1 ≤ v then c p else 0 := by
  unfold jumpSum
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun p _ => ?_
  by_cases h1 : 0 < p.1
  · by_cases h2 : p.1 ≤ u
    · rw [if_pos ⟨h1, h2.trans huv⟩, if_pos ⟨h1, h2⟩,
        if_neg (fun h => absurd h.1 (not_lt.mpr h2))]
      ring
    · by_cases h3 : p.1 ≤ v
      · rw [if_pos ⟨h1, h3⟩, if_neg (fun h => h2 h.2), if_pos ⟨lt_of_not_ge h2, h3⟩]
        ring
      · rw [if_neg (fun h => h3 h.2), if_neg (fun h => h2 h.2), if_neg (fun h => h3 h.2)]
        ring
  · rw [if_neg (fun h => h1 h.1), if_neg (fun h => h1 h.1),
      if_neg (fun h => h1 (hu.trans_lt h.1))]
    ring
/-- The jump sum is bounded by the number of points times the bound on the weights. -/
theorem abs_jumpSum_le (S : Finset (ℝ × E)) {c : ℝ × E → ℝ} {C : ℝ} (hc : ∀ p, |c p| ≤ C)
    (s : ℝ) : |jumpSum S c s| ≤ S.card * C := by
  classical
  unfold jumpSum
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  rw [Finset.card_eq_sum_ones, Nat.cast_sum, Finset.sum_mul]
  refine Finset.sum_le_sum fun p _ => ?_
  rw [Nat.cast_one, one_mul]
  split_ifs
  · exact hc p
  · rw [abs_zero]; exact (abs_nonneg _).trans (hc p)
open scoped Classical in
/-- Without points in `(u, s)` the jump sum at `u < s` is the strict-past jump sum at `s`. -/
theorem jumpSum_eq_jumpSumStrict (S : Finset (ℝ × E)) (c : ℝ × E → ℝ) {u s : ℝ} (hus : u < s)
    (h : ∀ p ∈ S, ¬ (u < p.1 ∧ p.1 < s)) : jumpSum S c u = jumpSumStrict S c s := by
  unfold jumpSum jumpSumStrict
  refine Finset.sum_congr rfl fun p hp => ?_
  have hiff : (0 < p.1 ∧ p.1 ≤ u) ↔ (0 < p.1 ∧ p.1 < s) := by
    constructor
    · rintro ⟨h1, h2⟩; exact ⟨h1, h2.trans_lt hus⟩
    · rintro ⟨h1, h2⟩
      refine ⟨h1, ?_⟩
      by_contra h3
      exact h p hp ⟨lt_of_not_ge h3, h2⟩
  simp only [hiff]
/-- A positive gap below `s` clearing the finitely many points before `s`. -/
theorem exists_gap (S : Finset (ℝ × E)) (s : ℝ) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ p ∈ S, p.1 < s → p.1 + δ ≤ s := by
  classical
  induction S using Finset.induction_on with
  | empty => exact ⟨1, one_pos, fun p hp => absurd hp (Finset.notMem_empty p)⟩
  | insert q S _ ih =>
    obtain ⟨δ, hδ, hS⟩ := ih
    by_cases hq : q.1 < s
    · refine ⟨min δ (s - q.1), lt_min hδ (sub_pos.mpr hq), fun p hp hps => ?_⟩
      rcases Finset.mem_insert.mp hp with rfl | hp'
      · linarith [min_le_right δ (s - p.1)]
      · linarith [hS p hp' hps, min_le_left δ (s - q.1)]
    · exact ⟨δ, hδ, fun p hp hps => by
        rcases Finset.mem_insert.mp hp with rfl | hp'
        · exact absurd hps hq
        · exact hS p hp' hps⟩
end Sums

section Dirac

variable [MeasurableSpace E] [MeasurableSingletonClass E]

end Dirac

end LevyStochCalc.Analysis


