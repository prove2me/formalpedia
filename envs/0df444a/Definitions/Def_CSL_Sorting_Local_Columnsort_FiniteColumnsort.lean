-- Prove2me | Definitions.Def_CSL_Sorting_Local_Columnsort_FiniteColumnsort
-- name    : CSL_Sorting_Local_Columnsort_FiniteColumnsort
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-24T12:56:13.536928+00:00
-- url     : https://prove2.me/theorems/a9505aad-29f3-435f-be3e-1a7be1bcdeb5
-- title:
--   Coded sorting library: Sorting / Local / Columnsort / FiniteColumnsort
-- statement:
--   Module `CodedSorting.Sorting.Local.Columnsort.FiniteColumnsort` of the Lean development accompanying B. Li, Z. Li, S. Liu, *Undirected Multiple-Unicast Network Coding and Faster External-Memory Integer Sorting*, arXiv:2610.20079, ported to Lean v4.33.1 and Mathlib `0df444a` (namespace `CodedSorting` renamed to `CSL`).
--
--   Four finite batches of actual recursive-sorter calls for Columnsort.
--   The returned trace is assembled from exactly these invocations.
--
--   This module is part of the machine-checked proof of Theorem 3.1 (external-memory integer sorting) and is imported by the later modules of that development.
-- source:
--   B. Li, Z. Li, S. Liu, *Undirected Multiple-Unicast Network Coding and Faster External-Memory Integer Sorting*, arXiv:2610.20079 (Theorem 3.1, p.4, and Appendix D); Lean development https://github.com/rtyu-1/coded-sorting-lean, module CodedSorting.Sorting.Local.Columnsort.FiniteColumnsort

import Definitions.Def_CSL_Compat
import Definitions.Def_CSL_Shared_Indexing_FiniteGrid

/-! Four finite batches of actual recursive-sorter calls for Columnsort.
The returned trace is assembled from exactly these invocations. -/

namespace CSL.RecursiveColumnsort

open CSL.Columnsort

variable {α : Type*} [LinearOrder α] [OrderBot α] [OrderTop α]

/-- Entire record groups from the first returned batch, in cyclic order.
The explicit group size 1 matches the already verified generic kernel. -/
def secondInput (q s : ℕ) (one : Fin s → Fin (q*s*1) → α)
    (c : Fin s) (i : Fin (s*(q*1))) : α :=
  let p : Fin s × Fin (q*1) := finProdFinEquiv.symm i
  one p.1 ⟨stripeIndex s 1 c.val p.2.val,
    stripeIndex_lt q s 1 c.val p.2.val (by decide) c.isLt p.2.isLt⟩

/-- The inverse whole-group transpose, with a finite sentinel extension.
It only reads returned values of the second batch, never sorts them again. -/
def afterTwoTape (q s : ℕ) (two : Fin s → Fin (s*(q*1)) → α) (i : ℤ) : α :=
  if hi : 0 ≤ i ∧ i < (s*q*(s*1) : ℕ) then
    let j : Fin (s*q*(s*1)) := ⟨i.toNat, (Int.toNat_lt hi.1).2 hi.2⟩
    let p : Fin (s*q) × Fin (s*1) := finProdFinEquiv.symm j
    let cv : Fin s × Fin 1 := finProdFinEquiv.symm p.2
    two cv.1 ⟨p.1.val*1+cv.2.val, by have := p.1.isLt; have := cv.2.isLt; simpa only [Nat.mul_one] using (show p.1.val+cv.2.val < s*q by omega)⟩
  else if i < 0 then ⊥ else ⊤

/-- Four batches are retained separately for shared stream buffering at leaves. -/
structure FourRun (α : Type*) (n : ℕ) where
  output : Fin n → α
  first : List CallTree
  second : List CallTree
  third : List CallTree
  fourth : List CallTree

/-- Four actual finite batches: s,s,s,s+1 child calls. Their returned values
feed the next batch; every trace item comes from those same invocations. -/
def fourRounds (sorter : Sorter α) (q s H : ℕ)
    (f : Fin s → Fin (q*s*1) → α) : FourRun α (s*q*(s*1)) :=
  let first := fun c : Fin s => sorter (q*s*1) (f c)
  let second := fun c : Fin s => sorter (s*(q*1)) (secondInput q s (fun c => (first c).output) c)
  let A := afterTwoTape q s (fun c => (second c).output)
  let third := fun c : Fin s => sorter (q*s*1) (gridInput (q*s*1) 0 A c)
  let G := gridTape s (q*s*1) 0 (fun c => (third c).output)
  let fourth := fun c : Fin (s+1) => sorter (q*s*1) (gridInput (q*s*1) (-H) G c)
  { output := fun i => gridTape (s+1) (q*s*1) (-H) (fun c => (fourth c).output) (i : ℤ)
    first := List.ofFn (fun c => (first c).trace)
    second := List.ofFn (fun c => (second c).trace)
    third := List.ofFn (fun c => (third c).trace)
    fourth := List.ofFn (fun c => (fourth c).trace) }

theorem fourRounds_batch_lengths (sorter : Sorter α) (q s H : ℕ)
    (f : Fin s → Fin (q*s*1) → α) :
    let result := fourRounds sorter q s H f
    result.first.length = s ∧ result.second.length = s ∧
      result.third.length = s ∧ result.fourth.length = s+1 := by
  simp [fourRounds]

/-- Input to every stage-three batch has the claimed complete finite extent. -/
theorem afterTwoTape_bounds (q s : ℕ) (two : Fin s → Fin (s*(q*1)) → α) :
    TapeBounds (afterTwoTape q s two) 0 (s*q*(s*1)) := by
  constructor
  · intro i hi
    have hn : ¬(0 ≤ i ∧ i < (s*q*(s*1) : ℕ)) := by omega
    rw [afterTwoTape, dif_neg hn, if_pos hi]
  · intro i hi
    have hn : ¬(0 ≤ i ∧ i < (s*q*(s*1) : ℕ)) := by omega
    have hp : (0 : ℤ) ≤ ((s*q*(s*1) : ℕ) : ℤ) := by exact_mod_cast Nat.zero_le (s*q*(s*1))
    have h0 : ¬i<0 := by omega
    rw [afterTwoTape, dif_neg hn, if_neg h0]

/-- Enlarging the sentinel interval by half a column gives exactly s+1
finite columns in the final batch. -/
theorem gridTape_half_bounds (q s H : ℕ) (hh : q*s*1 = 2*H)
    (f : Fin s → Fin (q*s*1) → α) :
    TapeBounds (gridTape s (q*s*1) 0 f) (-H) ((s+1)*(q*s*1)) := by
  have hb := gridTape_bounds s (q*s*1) 0 f
  constructor
  · intro i hi
    apply hb.1
    have hH : (0 : ℤ) ≤ H := by exact_mod_cast Nat.zero_le H
    omega
  · intro i hi
    apply hb.2
    have he : ((q*s*1 : ℕ) : ℤ) = 2*(H : ℤ) := by exact_mod_cast hh
    have hn : (0 : ℤ) ≤ H := by exact_mod_cast Nat.zero_le H
    push_cast at hi ⊢
    nlinarith

omit [OrderBot α] [OrderTop α] in
theorem blockSortKeys_height_congr {B C : ℕ} (h : B = C) (hB : 0 < B) (hC : 0 < C)
    (offset : ℤ) (f : ℤ → α) :
    blockSortKeys B hB offset f = blockSortKeys C hC offset f := by
  subst C
  rfl

/-- All finite returned values agree with the previously verified eight-step
algorithm once each recursive child returns its correct sorted permutation.
There is no extra hidden call to the specification sorter in fourRounds. -/
theorem fourRounds_output_eq (sorter : Sorter α)
    (hc : ∀ n (f : Fin n → α), Correct f (sorter n f).output)
    (q s H : ℕ) (hH : 0 < H) (hh : q*s*1 = 2*H)
    (f : Fin s → Fin (q*s*1) → α) :
    (fourRounds sorter q s H f).output = groupedColumnsort q s 1 H (by decide) hH f := by
  have hR : 0 < q*s*1 := by omega
  have he (n : ℕ) (f : Fin n → α) := (hc n f).eq_sortColumn
  let A := afterTwoTape q s (fun c => sortColumn (secondInput q s (fun c => sortColumn (f c)) c))
  have hA : A = stepFourTapeKeys q s 1 (by decide) f := by
    funext i
    try dsimp only [A, afterTwoTape, stepFourTapeKeys]
    split_ifs with h hi
    · rfl
    · rfl
    · rfl
  have hN : s*q*(s*1) = s*(q*s*1) := by ring
  have hAbounds : TapeBounds A 0 (s*(q*s*1)) := by
    rw [← hN]
    exact afterTwoTape_bounds q s _
  let G := gridTape s (q*s*1) 0 (fun c => sortColumn (gridInput (q*s*1) 0 A c))
  have hG : G = blockSortKeys (2*H) (by omega) 0 (stepFourTapeKeys q s 1 (by decide) f) := by
    change gridTape s (q*s*1) 0 _ = _
    rw [gridTape_sort_eq s (q*s*1) hR 0 A hAbounds,
      blockSortKeys_height_congr hh hR (by omega), hA]
  have hGb := gridTape_half_bounds q s H hh (fun c => sortColumn (gridInput (q*s*1) 0 A c))
  have hlast : gridTape (s+1) (q*s*1) (-H)
      (fun c => sortColumn (gridInput (q*s*1) (-H) G c)) =
      blockSortKeys (2*H) (by omega) (-H) G := by
    rw [gridTape_sort_eq (s+1) (q*s*1) hR (-H) G hGb,
      blockSortKeys_height_congr hh hR (by omega)]
  funext i
  simp only [fourRounds, he]
  change gridTape (s+1) (q*s*1) (-H)
      (fun c => sortColumn (gridInput (q*s*1) (-H) G c)) (i : ℤ) = _
  rw [hlast, hG]
  rfl

/-- Actual finite batches preserve the full input and sort it. -/
theorem fourRounds_correct (sorter : Sorter α)
    (hc : ∀ n (f : Fin n → α), Correct f (sorter n f).output)
    (q s H : ℕ) (hs : 0 < s) (hH : 0 < H)
    (hh : q*s*1 = 2*H) (hr : 2*s*(s+1) ≤ q*s)
    (f : Fin s → Fin (q*s*1) → α) :
    Correct (flattenKeys q s 1 f) (fourRounds sorter q s H f).output := by
  rw [fourRounds_output_eq sorter hc q s H hH hh f]
  exact ⟨groupedColumnsort_monotone q s 1 H hs (by decide) hH hh hr f,
    (groupedColumnsort_correct q s 1 H hs (by decide) hH hh hr f).2⟩

end CSL.RecursiveColumnsort


