-- Prove2me | Definitions.Def_CSL_Sorting_Bounds_RecursiveSortBase
-- name    : CSL_Sorting_Bounds_RecursiveSortBase
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-24T12:32:15.495153+00:00
-- url     : https://prove2.me/theorems/dcb47d5a-b0c3-4454-b16d-069090c2898f
-- title:
--   Coded sorting library: Sorting / Bounds / RecursiveSortBase
-- statement:
--   Module `CodedSorting.Sorting.Bounds.RecursiveSortBase` of the Lean development accompanying B. Li, Z. Li, S. Liu, *Undirected Multiple-Unicast Network Coding and Faster External-Memory Integer Sorting*, arXiv:2610.20079, ported to Lean v4.33.1 and Mathlib `0df444a` (namespace `CodedSorting` renamed to `CSL`).
--
--   Basic executable records and exact top-sentinel padding for the actual
--   recursive local sorter. No I/O bound is asserted by these definitions.
--
--   This module is part of the machine-checked proof of Theorem 3.1 (external-memory integer sorting) and is imported by the later modules of that development.
-- source:
--   B. Li, Z. Li, S. Liu, *Undirected Multiple-Unicast Network Coding and Faster External-Memory Integer Sorting*, arXiv:2610.20079 (Theorem 3.1, p.4, and Appendix D); Lean development https://github.com/rtyu-1/coded-sorting-lean, module CodedSorting.Sorting.Bounds.RecursiveSortBase

import Definitions.Def_CSL_Compat
import Definitions.Def_CSL_Sorting_Local_Columnsort_ColumnsortParameters

/-! Basic executable records and exact top-sentinel padding for the actual
recursive local sorter. No I/O bound is asserted by these definitions. -/

namespace CSL.RecursiveColumnsort

open CSL.Columnsort

/-- The trace stores exactly the child runs issued by a sorting invocation.
The parent size excludes padding; s fixes its padded s⁴ layout. -/
inductive CallTree where
  | leaf (inputSize : ℕ)
  | node (inputSize columns : ℕ)
      (first second third fourth : List CallTree)
  deriving Repr

/-- Values and the trace are produced by the same execution. -/
structure Run (α : Type*) (n : ℕ) where
  output : Fin n → α
  trace : CallTree

abbrev Sorter (α : Type*) := ∀ n : ℕ, (Fin n → α) → Run α n

variable {α : Type*} [LinearOrder α] [OrderTop α]

/-- Top-padding retains every old index in place. -/
def pad {n N : ℕ} (f : Fin n → α) : Fin N → α := fun i =>
  if hi : i.val < n then f ⟨i.val,hi⟩ else ⊤

/-- The exact padded list, including the number of newly added sentinels. -/
theorem pad_ofFn {n N : ℕ} (h : n ≤ N) (f : Fin n → α) :
    List.ofFn (pad (N := N) f) = List.ofFn f ++ List.replicate (N-n) (⊤ : α) := by
  have he : N = n+(N-n) := by omega
  rw [List.ofFn_congr he, List.ofFn_add]
  congr 1
  · apply congrArg List.ofFn
    funext i
    simp [pad, i.isLt]
  · have hf : (fun i : Fin (N-n) => pad f (Fin.cast he.symm (Fin.natAdd n i))) =
        fun _ => (⊤ : α) := by
      funext i
      simp [pad]
    rw [hf]
    simp

/-- Appending top sentinels to a sorted array preserves sortedness. -/
theorem pad_monotone {n N : ℕ} (f : Fin n → α) (hf : Monotone f) :
    Monotone (pad (N := N) f) := by
  intro i j hij
  by_cases hj : j.val < n
  · have hi : i.val < n := lt_of_le_of_lt hij hj
    simp only [pad, dif_pos hi, dif_pos hj]
    apply hf
    exact hij
  · simp only [pad, dif_neg hj]
    exact le_top

/-- Ordinary array sorting correctness, stated with the real List.Perm. -/
def Correct {n : ℕ} (f output : Fin n → α) : Prop :=
  Monotone output ∧ (List.ofFn output).Perm (List.ofFn f)

omit [OrderTop α] in
theorem correct_sortColumn {n : ℕ} (f : Fin n → α) : Correct f (sortColumn f) :=
  ⟨sortColumn_monotone f, sortColumn_perm f⟩

omit [OrderTop α] in
theorem Correct.eq_sortColumn {n : ℕ} {f output : Fin n → α} (h : Correct f output) :
    output = sortColumn f := by
  apply List.ofFn_injective
  exact List.eq_of_perm_of_sorted (h.2.trans (sortColumn_perm f).symm)
    h.1.ofFn_sorted (sortColumn_monotone f).ofFn_sorted

/-- Sorting after adding top sentinels agrees with adding the same sentinels
after sorting the original input; equal keys cause no exception. -/
theorem sort_pad {n N : ℕ} (h : n ≤ N) (f : Fin n → α) :
    sortColumn (pad (N := N) f) = pad (N := N) (sortColumn f) := by
  have hm := pad_monotone (N := N) (sortColumn f) (sortColumn_monotone f)
  have hp : (List.ofFn (pad (N := N) (sortColumn f))).Perm
      (List.ofFn (pad (N := N) f)) := by
    rw [pad_ofFn h, pad_ofFn h]
    exact (sortColumn_perm f).append_right _
  exact (Correct.eq_sortColumn ⟨hm,hp⟩).symm

/-- Remove exactly this call's padding, preserving old input positions. -/
def trim {n N : ℕ} (h : n ≤ N) (f : Fin N → α) : Fin n → α :=
  fun i => f (Fin.castLE h i)

/-- Once the padded execution is sorted and is a permutation, removing its
newly added top sentinels yields the correct sort of the unpadded input. -/
theorem trim_correct {n N : ℕ} (h : n ≤ N) (f : Fin n → α) (out : Fin N → α)
    (hc : Correct (pad (N := N) f) out) : Correct f (trim h out) := by
  have he := hc.eq_sortColumn
  rw [he, sort_pad h]
  have ht : trim h (pad (N := N) (sortColumn f)) = sortColumn f := by
    funext i
    simp [trim, pad, i.isLt]
  rw [ht]
  exact correct_sortColumn f

end CSL.RecursiveColumnsort


