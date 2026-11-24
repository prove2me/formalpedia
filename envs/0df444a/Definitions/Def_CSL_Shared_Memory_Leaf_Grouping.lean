-- Prove2me | Definitions.Def_CSL_Shared_Memory_Leaf_Grouping
-- name    : CSL_Shared_Memory_Leaf_Grouping
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-24T14:57:34.519302+00:00
-- url     : https://prove2.me/theorems/8f6f6f22-7538-420e-a5e9-14de9c07de9b
-- title:
--   Coded sorting library: Shared / Memory / Leaf / Grouping
-- statement:
--   Module `CodedSorting.Shared.Memory.Leaf.Grouping` of the Lean development accompanying B. Li, Z. Li, S. Liu, *Undirected Multiple-Unicast Network Coding and Faster External-Memory Integer Sorting*, arXiv:2610.20079, ported to Lean v4.33.1 and Mathlib `0df444a` (namespace `CodedSorting` renamed to `CSL`).
--
--   Packing many short Columnsort columns into resident groups.  The final
--   group is padded to a full group; all these padding cells and block endings
--   are explicitly included in the bounds below.
--
--   This module is part of the machine-checked proof of Theorem 3.1 (external-memory integer sorting) and is imported by the later modules of that development.
-- source:
--   B. Li, Z. Li, S. Liu, *Undirected Multiple-Unicast Network Coding and Faster External-Memory Integer Sorting*, arXiv:2610.20079 (Theorem 3.1, p.4, and Appendix D); Lean development https://github.com/rtyu-1/coded-sorting-lean, module CodedSorting.Shared.Memory.Leaf.Grouping

import Definitions.Def_CSL_Compat
import Definitions.Def_CSL_Sorting_Local_Framework_LocalSortingCost
import Definitions.Def_CSL_Shared_Words_WordConvention

/-! Packing many short Columnsort columns into resident groups.  The final
group is padded to a full group; all these padding cells and block endings
are explicitly included in the bounds below. -/
set_option autoImplicit false
namespace CSL.CommonLeafGrouping
open LocalSortingCost

def columns (capacity rows : ℕ) : ℕ := capacity/rows
def groups (capacity rows count : ℕ) : ℕ := blockCount (columns capacity rows) count
def groupRecords (capacity rows : ℕ) : ℕ := columns capacity rows*rows
def paddedRecords (capacity rows count : ℕ) : ℕ :=
  groups capacity rows count*groupRecords capacity rows

theorem rows_pos {capacity rows count : ℕ} (hlarge : capacity<count*rows) : 0<rows := by
  nlinarith

theorem columns_pos {capacity rows : ℕ} (hr : 0<rows) (hfit : rows≤capacity) :
    0<columns capacity rows := Nat.div_pos hfit hr

theorem group_fits (capacity rows : ℕ) : groupRecords capacity rows≤capacity :=
  Nat.div_mul_le_self capacity rows

theorem group_more_than_half {capacity rows : ℕ} (hr : 0<rows) (hfit : rows≤capacity) :
    capacity<2*groupRecords capacity rows := by
  have hpos := columns_pos hr hfit
  have hmod := Nat.mod_lt capacity hr
  have hid := Nat.div_add_mod capacity rows
  have hrow : rows≤groupRecords capacity rows := by
    exact Nat.le_mul_of_pos_left rows hpos
  try dsimp only [groupRecords,columns] at hrow ⊢
  nlinarith only [hmod,hid,hrow]

theorem groups_cover {capacity rows count : ℕ} (hr : 0<rows) (hfit : rows≤capacity) :
    count≤groups capacity rows count*columns capacity rows :=
  WordControl.frame_fits count (columns capacity rows) (columns_pos hr hfit)

theorem groups_size {capacity rows count : ℕ} (hr : 0<rows) (hfit : rows≤capacity) :
    groups capacity rows count*columns capacity rows≤count+columns capacity rows :=
  blockCount_capacity (columns capacity rows) (columns_pos hr hfit) count

theorem padded_covers {capacity rows count : ℕ} (hr : 0<rows) (hfit : rows≤capacity) :
    count*rows≤paddedRecords capacity rows count := by
  have h := Nat.mul_le_mul_right rows (groups_cover (count:=count) hr hfit)
  simpa only [paddedRecords,groupRecords,Nat.mul_assoc] using h

/-- One incomplete group adds at most one resident capacity. -/
theorem padded_le_add {capacity rows count : ℕ} (hr : 0<rows) (hfit : rows≤capacity) :
    paddedRecords capacity rows count≤count*rows+capacity := by
  have h := Nat.mul_le_mul_right rows (groups_size (count:=count) hr hfit)
  have hcap := group_fits capacity rows
  try dsimp only [paddedRecords,groupRecords] at hcap ⊢
  nlinarith only [h,hcap]

theorem padded_le_double {capacity rows count : ℕ} (hr : 0<rows) (hfit : rows≤capacity)
    (hlarge : capacity≤count*rows) : paddedRecords capacity rows count≤2*(count*rows) := by
  have h := padded_le_add (count:=count) hr hfit
  omega

theorem block_le_group {capacity rows B : ℕ} (hr : 0<rows) (hfit : rows≤capacity)
    (hB : 2*B≤capacity) : B≤groupRecords capacity rows := by
  have h := group_more_than_half hr hfit
  omega

/-- Per-group block rounding costs only a constant number of global scans.
This is the needed bound when the columns themselves may be much shorter
than a block.  The factor includes the padded final group. -/
theorem grouped_blocks_le {capacity rows count B : ℕ} (hB : 0<B)
    (hr : 0<rows) (hfit : rows≤capacity) (hcap : 2*B≤capacity)
    (hlarge : capacity≤count*rows) :
    groups capacity rows count*blockCount B (3*groupRecords capacity rows)≤
      8*blockCount B (3*(count*rows)) := by
  have hg := block_le_group hr hfit hcap
  have hpad := padded_le_double hr hfit hlarge
  have hceil := blockCount_capacity B hB (3*groupRecords capacity rows)
  have hceil' : blockCount B (3*groupRecords capacity rows)*B≤
      4*groupRecords capacity rows := by omega
  have hm := Nat.mul_le_mul_left (groups capacity rows count) hceil'
  have hout := WordControl.frame_fits (3*(count*rows)) B hB
  change 3*(count*rows)≤blockCount B (3*(count*rows))*B at hout
  have hleft : groups capacity rows count*blockCount B (3*groupRecords capacity rows)*B≤
      8*(count*rows) := by
    try dsimp only [paddedRecords] at hpad
    nlinarith only [hm,hpad]
  exact Nat.le_of_mul_le_mul_right
    (show (groups capacity rows count*blockCount B (3*groupRecords capacity rows))*B≤
      (8*blockCount B (3*(count*rows)))*B by nlinarith only [hleft,hout]) hB

/-- Specialization to the exact resident leaf capacity of the sorter. -/
theorem columnsort_groups {H B rows count : ℕ} (hB : 0<B) (hBH : B≤H)
    (hr : 0<rows) (hfit : rows≤512*H) (hlarge : 512*H≤count*rows) :
    0<columns (512*H) rows ∧ groupRecords (512*H) rows≤512*H ∧
      512*H<2*groupRecords (512*H) rows ∧
      paddedRecords (512*H) rows count≤2*(count*rows) ∧
      groups (512*H) rows count*blockCount B (3*groupRecords (512*H) rows)≤
        8*blockCount B (3*(count*rows)) :=
  ⟨columns_pos hr hfit,group_fits _ _,group_more_than_half hr hfit,
    padded_le_double hr hfit hlarge,grouped_blocks_le hB hr hfit (by omega) hlarge⟩

theorem blockCount_le_of_fits {B n k : ℕ} (hB : 0<B) (hfit : n≤k*B) :
    blockCount B n≤k := by
  apply Nat.le_of_lt_succ
  apply (Nat.div_lt_iff_lt_mul hB).2
  have hsub : n+B-1+1=n+B := by omega
  simp only [Nat.succ_mul]
  omega

theorem padded_blocks_le {capacity rows count B : ℕ} (hB : 0<B)
    (hr : 0<rows) (hfit : rows≤capacity) (hlarge : capacity≤count*rows) :
    blockCount B (3*paddedRecords capacity rows count)≤2*blockCount B (3*(count*rows)) := by
  have hp := padded_le_double hr hfit hlarge
  have hb := WordControl.frame_fits (3*(count*rows)) B hB
  change 3*(count*rows)≤blockCount B (3*(count*rows))*B at hb
  apply blockCount_le_of_fits hB
  nlinarith only [hp,hb]

/-- Account for a fixed scan charge and one instruction of startup per
resident group, together with padding and trimming scans. -/
theorem grouped_charge_le {capacity rows count B : ℕ} (hB : 0<B)
    (hr : 0<rows) (hfit : rows≤capacity) (hcap : 2*B≤capacity)
    (hlarge : capacity≤count*rows) (K A D : ℕ) :
    groups capacity rows count*(K*blockCount B (3*groupRecords capacity rows)+1)+
      A*blockCount B (3*paddedRecords capacity rows count)+
      D*blockCount B (3*(count*rows))≤
        (8*(K+1)+2*A+D)*blockCount B (3*(count*rows)) := by
  have hg := grouped_blocks_le hB hr hfit hcap hlarge
  have hp := padded_blocks_le hB hr hfit hlarge
  have hGB := block_le_group hr hfit hcap
  have hc := WordControl.frame_fits (3*groupRecords capacity rows) B hB
  change 3*groupRecords capacity rows≤blockCount B (3*groupRecords capacity rows)*B at hc
  have hpos : 1≤blockCount B (3*groupRecords capacity rows) := by nlinarith only [hc,hGB,hB]
  have hng := Nat.mul_le_mul_left (groups capacity rows count) hpos
  have hKg := Nat.mul_le_mul_left (K+1) hg
  have hAp := Nat.mul_le_mul_left A hp
  nlinarith only [hng,hKg,hAp]

end CSL.CommonLeafGrouping


