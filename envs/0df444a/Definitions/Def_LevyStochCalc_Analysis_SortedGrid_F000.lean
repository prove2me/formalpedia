-- Prove2me | Definitions.Def_LevyStochCalc_Analysis_SortedGrid_F000
-- name    : LevyStochCalc_Analysis_SortedGrid_F000
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-18T21:57:18.218135+00:00
-- url     : https://prove2.me/theorems/d6ff5876-db88-4308-8ee4-ca9807dce0ee
-- title:
--   Source declarations: LevyStochCalc.Analysis.SortedGrid
-- statement:
--   Source-preserving Lean declaration bundle from LevyStochCalc.Analysis.SortedGrid, retaining definitions, helper results, proofs and elaboration context where present.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Data.Finset.Sort
import Mathlib.Data.Real.Basic

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# The increasing enumeration of a finite family of times

`sortedGrid S` lists the elements of a finite set `S ⊆ ℝ` in increasing order at the indices
`1, …, #S`, and takes the value `0` at index `0` and beyond `#S`. When every element of `S` is
positive it is strictly increasing on `{0, …, #S}`.

A finite family of (coordinate, time) pairs carrying real weights is thereby rewritten as a sum
over such a grid: `posTimes` collects the strictly positive times of the family and `weightAt`
collects the weights sharing a coordinate and a time.
-/

namespace LevyStochCalc.Analysis

open Finset

/-- The increasing enumeration of `S`, extended by `0` at index `0` and beyond `S.card`. -/
noncomputable def sortedGrid (S : Finset ℝ) : ℕ → ℝ
  | 0 => 0
  | n + 1 => if h : n < S.card then S.orderEmbOfFin rfl ⟨n, h⟩ else 0
variable (S : Finset ℝ)

@[simp] theorem sortedGrid_zero : sortedGrid S 0 = 0 := rfl
theorem sortedGrid_succ_of_lt {n : ℕ} (h : n < S.card) :
    sortedGrid S (n + 1) = S.orderEmbOfFin rfl ⟨n, h⟩ := by
  simp only [sortedGrid]
  rw [dif_pos h]
theorem sortedGrid_succ_mem {n : ℕ} (h : n < S.card) : sortedGrid S (n + 1) ∈ S := by
  rw [sortedGrid_succ_of_lt S h]
  exact S.orderEmbOfFin_mem rfl _
/-- On a set of positive reals the enumeration is strictly increasing from the origin. -/
theorem sortedGrid_lt_succ (hpos : ∀ x ∈ S, 0 < x) {n : ℕ} (hn : n < S.card) :
    sortedGrid S n < sortedGrid S (n + 1) := by
  cases n with
  | zero =>
      rw [sortedGrid_zero]
      exact hpos _ (sortedGrid_succ_mem S hn)
  | succ j =>
      have hj : j < S.card := Nat.lt_of_succ_lt hn
      rw [sortedGrid_succ_of_lt S hj, sortedGrid_succ_of_lt S hn]
      exact (S.orderEmbOfFin rfl).strictMono (by exact Fin.mk_lt_mk.mpr (Nat.lt_succ_self j))
/-- A sum over `S` is a sum along the grid indices `1, …, S.card`. -/
theorem sum_Ico_sortedGrid {M : Type*} [AddCommMonoid M] (f : ℝ → M) :
    ∑ k ∈ Finset.Ico 1 (S.card + 1), f (sortedGrid S k) = ∑ x ∈ S, f x := by
  have h1 : ∑ k ∈ Finset.Ico 1 (S.card + 1), f (sortedGrid S k)
      = ∑ i ∈ Finset.range S.card, f (sortedGrid S (i + 1)) := by
    rw [Finset.sum_Ico_eq_sum_range, Nat.add_sub_cancel]
    exact Finset.sum_congr rfl fun i _ => by rw [Nat.add_comm]
  have h2 : ∑ i ∈ Finset.range S.card, f (sortedGrid S (i + 1))
      = ∑ i : Fin S.card, f (S.orderEmbOfFin rfl i) := by
    rw [← Fin.sum_univ_eq_sum_range (fun i => f (sortedGrid S (i + 1))) S.card]
    exact Finset.sum_congr rfl fun i _ => by rw [sortedGrid_succ_of_lt S i.isLt]
  have h3 : ∑ i : Fin S.card, f (S.orderEmbOfFin rfl i) = ∑ x ∈ S, f x := by
    rw [← Finset.sum_coe_sort S f]
    exact Fintype.sum_equiv (S.orderIsoOfFin rfl).toEquiv _ _ fun i =>
      congrArg f (Finset.coe_orderIsoOfFin_apply S rfl i).symm
  rw [h1, h2, h3]
variable {d : ℕ} {T : ℝ}

/-- The strictly positive times occurring in a finite family of (coordinate, time) pairs. -/
noncomputable def posTimes (F : Finset (Fin d × Set.Iic T)) : Finset ℝ :=
  (F.filter fun p => 0 < (p.2 : ℝ)).image fun p => (p.2 : ℝ)
theorem pos_of_mem_posTimes {F : Finset (Fin d × Set.Iic T)} {x : ℝ} (hx : x ∈ posTimes F) :
    0 < x := by
  rw [posTimes, Finset.mem_image] at hx
  obtain ⟨p, hp, rfl⟩ := hx
  exact (Finset.mem_filter.mp hp).2
theorem mem_posTimes {F : Finset (Fin d × Set.Iic T)} {p : Fin d × Set.Iic T} (hp : p ∈ F)
    (hx : 0 < (p.2 : ℝ)) : ((p.2 : ℝ)) ∈ posTimes F :=
  Finset.mem_image.mpr ⟨p, Finset.mem_filter.mpr ⟨hp, hx⟩, rfl⟩
theorem le_of_mem_posTimes {F : Finset (Fin d × Set.Iic T)} {x : ℝ} (hx : x ∈ posTimes F) :
    x ≤ T := by
  rw [posTimes, Finset.mem_image] at hx
  obtain ⟨p, -, rfl⟩ := hx
  exact p.2.2
/-- The total weight carried by the coordinate `i` at the time `x`. -/
noncomputable def weightAt (F : Finset (Fin d × Set.Iic T)) (w : F → ℝ) (x : ℝ) (i : Fin d) :
    ℝ :=
  ∑ p : F, if p.1.1 = i ∧ (p.1.2 : ℝ) = x then w p else 0
theorem sum_weightAt_mul (F : Finset (Fin d × Set.Iic T)) (w : F → ℝ) (v : Fin d → ℝ → ℝ)
    (x : ℝ) :
    (∑ i, weightAt F w x i * v i x)
      = ∑ p : F, (if (p.1.2 : ℝ) = x then w p * v p.1.1 (p.1.2 : ℝ) else 0) := by
  have h1 : ∀ i : Fin d, weightAt F w x i * v i x
      = ∑ p : F, (if p.1.1 = i then
          (if (p.1.2 : ℝ) = x then w p * v p.1.1 (p.1.2 : ℝ) else 0) else 0) := by
    intro i
    rw [weightAt, Finset.sum_mul]
    refine Finset.sum_congr rfl fun p _ => ?_
    by_cases hc : p.1.1 = i
    · by_cases hx : (p.1.2 : ℝ) = x
      · simp [hc, hx]
      · simp [hc, hx]
    · simp [hc]
  rw [Finset.sum_congr rfl fun i (_ : i ∈ Finset.univ) => h1 i, Finset.sum_comm]
  exact Finset.sum_congr rfl fun p _ => by simp
end LevyStochCalc.Analysis


