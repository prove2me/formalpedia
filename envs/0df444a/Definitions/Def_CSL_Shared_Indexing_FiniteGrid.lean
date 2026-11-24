-- Prove2me | Definitions.Def_CSL_Shared_Indexing_FiniteGrid
-- name    : CSL_Shared_Indexing_FiniteGrid
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-24T12:44:15.863799+00:00
-- url     : https://prove2.me/theorems/a59629c5-457b-467d-807e-e7f95cde6e0d
-- title:
--   Coded sorting library: Shared / Indexing / FiniteGrid
-- statement:
--   Module `CodedSorting.Shared.Indexing.FiniteGrid` of the Lean development accompanying B. Li, Z. Li, S. Liu, *Undirected Multiple-Unicast Network Coding and Faster External-Memory Integer Sorting*, arXiv:2610.20079, ported to Lean v4.33.1 and Mathlib `0df444a` (namespace `CodedSorting` renamed to `CSL`).
--
--   This module is part of the machine-checked proof of Theorem 3.1 (external-memory integer sorting) and is imported by the later modules of that development.
-- source:
--   B. Li, Z. Li, S. Liu, *Undirected Multiple-Unicast Network Coding and Faster External-Memory Integer Sorting*, arXiv:2610.20079 (Theorem 3.1, p.4, and Appendix D); Lean development https://github.com/rtyu-1/coded-sorting-lean, module CodedSorting.Shared.Indexing.FiniteGrid

import Definitions.Def_CSL_Compat
import Definitions.Def_CSL_Sorting_Bounds_RecursiveSortBase

namespace CSL.RecursiveColumnsort

open CSL.Columnsort

variable {α : Type*} [LinearOrder α] [OrderBot α] [OrderTop α]

/-- Constants outside a finite physical interval. -/
def TapeBounds (f : ℤ → α) (offset : ℤ) (N : ℕ) : Prop :=
  (∀ i, i < offset → f i = ⊥) ∧ (∀ i, offset+N ≤ i → f i = ⊤)

/-- Materialize only the n finite columns; outside them lie formal sentinels. -/
def gridTape (n B : ℕ) (offset : ℤ) (f : Fin n → Fin B → α) (i : ℤ) : α :=
  if hl : i < offset then ⊥ else
  if hu : i < offset+(n*B : ℕ) then
    let j : Fin (n*B) := ⟨(i-offset).toNat, (Int.toNat_lt (by omega)).2 (by omega)⟩
    let p : Fin n × Fin B := finProdFinEquiv.symm j
    f p.1 p.2
  else ⊤

/-- The actual finite columns read by a grid sort. -/
def gridInput (B : ℕ) (offset : ℤ) (f : ℤ → α) (c : ℤ) : Fin B → α :=
  fun j => f (offset+c*B+(j : ℤ))

theorem gridTape_at_fin (n B : ℕ) (offset : ℤ) (f : Fin n → Fin B → α)
    (i : Fin (n*B)) : gridTape n B offset f (offset+(i : ℤ)) =
      f (finProdFinEquiv.symm i).1 (finProdFinEquiv.symm i).2 := by
  have hi0 : (0 : ℤ) ≤ i := by exact_mod_cast Nat.zero_le i.val
  have hin : (i : ℤ) < ((n*B : ℕ) : ℤ) := by exact_mod_cast i.isLt
  have hn : ¬offset+(i : ℤ)<offset := by omega
  have hh : offset+(i : ℤ)<offset+((n*B : ℕ) : ℤ) := by omega
  simp only [gridTape, dif_neg hn, dif_pos hh]
  have he : (offset+(i : ℤ)-offset).toNat = i.val := by omega
  simp only [he]

theorem gridTape_at (n B : ℕ) (offset : ℤ) (f : Fin n → Fin B → α)
    (c : Fin n) (j : Fin B) :
    gridTape n B offset f (offset+(c : ℤ)*B+(j : ℤ)) = f c j := by
  have hi := gridTape_at_fin n B offset f (finProdFinEquiv (c,j))
  simp only [Equiv.symm_apply_apply] at hi
  convert hi using 1
  congr 1
  change offset+(c : ℤ)*B+(j : ℤ) = offset+((j.val+B*c.val : ℕ) : ℤ)
  push_cast
  ring

theorem gridTape_bounds (n B : ℕ) (offset : ℤ) (f : Fin n → Fin B → α) :
    TapeBounds (gridTape n B offset f) offset (n*B) := by
  constructor
  · intro i hi
    rw [gridTape, dif_pos hi]
  · intro i hi
    have hpos : (0 : ℤ) ≤ ((n*B : ℕ) : ℤ) := by exact_mod_cast Nat.zero_le (n*B)
    have hlo : ¬i<offset := by omega
    have hhi : ¬i<offset+(n*B : ℕ) := by omega
    rw [gridTape, dif_neg hlo, dif_neg hhi]

omit [OrderBot α] [OrderTop α] in
theorem blockSortKeys_at_grid (B : ℕ) (hB : 0 < B) (offset c : ℤ)
    (f : ℤ → α) (j : Fin B) :
    blockSortKeys B hB offset f (offset+c*B+(j : ℤ)) =
      sortColumn (gridInput B offset f c) j := by
  have hj0 : (0 : ℤ) ≤ j := by exact_mod_cast Nat.zero_le j.val
  have hjB : (j : ℤ) < (B : ℤ) := by exact_mod_cast j.isLt
  have ho := blockOrigin_eq B hB offset c (offset+c*B+(j : ℤ))
    (by omega) (by nlinarith)
  have hs := blockSlot_address B hB offset (offset+c*B+(j : ℤ))
  rw [ho] at hs
  have hslot : blockSlot B hB offset (offset+c*B+(j : ℤ)) = j := by
    apply Fin.ext
    exact_mod_cast (show (blockSlot B hB offset (offset+c*B+(j : ℤ)) : ℤ) =
      (j : ℤ) by omega)
  simp only [blockSortKeys, ho, hslot, gridInput]
  rfl

/-- One finite materialized batch agrees everywhere with the core's grid
semantics. Exactly n columns are needed; all other columns are constant. -/
theorem gridTape_sort_eq (n B : ℕ) (hB : 0 < B) (offset : ℤ)
    (f : ℤ → α) (hbounds : TapeBounds f offset (n*B)) :
    gridTape n B offset (fun c => sortColumn (gridInput B offset f c)) =
      blockSortKeys B hB offset f := by
  funext i
  have hB' : (0 : ℤ) < B := by exact_mod_cast hB
  have hb := blockOrigin_bounds B hB offset i
  by_cases hl : i < offset
  · rw [gridTape, dif_pos hl]
    have hk : (i-offset)/(B : ℤ) ≤ -1 := by
      by_contra hn
      have hnon : 0 ≤ (i-offset)/(B : ℤ) := by omega
      try dsimp [blockOrigin] at hb
      nlinarith
    have hend : blockOrigin B offset i+B ≤ offset := by
      try dsimp [blockOrigin]
      nlinarith
    have hcol : (fun j : Fin B => f (blockOrigin B offset i+(j : ℤ))) =
        fun _ => (⊥ : α) := by
      funext j
      apply hbounds.1
      have hj : (j : ℤ) < (B : ℤ) := by exact_mod_cast j.isLt
      omega
    simp only [blockSortKeys, hcol, sortColumn, Function.comp_apply]
  by_cases hu : i < offset+(n*B : ℕ)
  · let j : Fin (n*B) := ⟨(i-offset).toNat, (Int.toNat_lt (by omega)).2 (by omega)⟩
    let p : Fin n × Fin B := finProdFinEquiv.symm j
    have he : offset+(p.1 : ℤ)*B+(p.2 : ℤ) = i := by
      have hp : finProdFinEquiv p = j := Equiv.apply_symm_apply _ j
      have hval := congrArg (fun k : Fin (n*B) => (k : ℤ)) hp
      change ((p.2.val+B*p.1.val : ℕ) : ℤ) = ((i-offset).toNat : ℤ) at hval
      have hnon : 0 ≤ i-offset := by omega
      rw [Int.toNat_of_nonneg hnon] at hval
      push_cast at hval
      nlinarith
    rw [← he, gridTape_at, blockSortKeys_at_grid]
  · rw [gridTape, dif_neg hl, dif_neg hu]
    have hk : (n : ℤ) ≤ (i-offset)/(B : ℤ) := by
      by_contra hn
      have hlt : (i-offset)/(B : ℤ)+1 ≤ n := by omega
      try dsimp [blockOrigin] at hb
      have hhi : offset+((n*B : ℕ) : ℤ) ≤ i := by omega
      push_cast at hhi
      nlinarith
    have hstart : offset+((n*B : ℕ) : ℤ) ≤ blockOrigin B offset i := by
      try dsimp [blockOrigin]
      push_cast
      nlinarith
    have hcol : (fun j : Fin B => f (blockOrigin B offset i+(j : ℤ))) =
        fun _ => (⊤ : α) := by
      funext j
      apply hbounds.2
      have hj : (0 : ℤ) ≤ j := by exact_mod_cast Nat.zero_le j.val
      omega
    simp only [blockSortKeys, hcol, sortColumn, Function.comp_apply]

end CSL.RecursiveColumnsort


