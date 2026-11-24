-- Prove2me | Definitions.Def_CSL_Sorting_SmallMemory_Radix_Build
-- name    : CSL_Sorting_SmallMemory_Radix_Build
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-24T13:38:04.947945+00:00
-- url     : https://prove2.me/theorems/64f8be28-cb1c-488f-b796-bf69239f3be7
-- title:
--   Coded sorting library: Sorting / SmallMemory / Radix / Build
-- statement:
--   Module `CodedSorting.Sorting.SmallMemory.Radix.Build` of the Lean development accompanying B. Li, Z. Li, S. Liu, *Undirected Multiple-Unicast Network Coding and Faster External-Memory Integer Sorting*, arXiv:2610.20079, ported to Lean v4.33.1 and Mathlib `0df444a` (namespace `CodedSorting` renamed to `CSL`).
--
--   # A concrete fixed program for linked-directory insertion
--
--   This program is the backward-scan insertion used by DirectRadix.  Its five
--   virtual scalar registers and all list headers/links live on disk.  Null is
--   encoded by a separate validity region; no n+1st pointer value is squeezed
--   into a word.  Ten fixed virtual instructions read the actual input/header,
--   write the next link, and replace the header.  TwoWordUniformLoop supplies the
--   two-word physical execution with atomic effective-address selection.
--
--   This module does not count a separate physical address port and does not
--   yet implement the outer build/gather/radix loops.
--
--   This module is part of the machine-checked proof of Theorem 3.1 (external-memory integer sorting) and is imported by the later modules of that development.
-- source:
--   B. Li, Z. Li, S. Liu, *Undirected Multiple-Unicast Network Coding and Faster External-Memory Integer Sorting*, arXiv:2610.20079 (Theorem 3.1, p.4, and Appendix D); Lean development https://github.com/rtyu-1/coded-sorting-lean, module CodedSorting.Sorting.SmallMemory.Radix.Build

import Definitions.Def_CSL_Compat
import Definitions.Def_CSL_Sorting_SmallMemory_Uniform_Loop
import Definitions.Def_CSL_Sorting_Radix_Model_DirectRadix
import Mathlib.Tactic.FinCases

section Insert
/-!
# A concrete fixed program for linked-directory insertion

This program is the backward-scan insertion used by DirectRadix.  Its five
virtual scalar registers and all list headers/links live on disk.  Null is
encoded by a separate validity region; no n+1st pointer value is squeezed
into a word.  Ten fixed virtual instructions read the actual input/header,
write the next link, and replace the header.  TwoWordUniformLoop supplies the
two-word physical execution with atomic effective-address selection.

This module does not count a separate physical address port and does not
yet implement the outer build/gather/radix loops.
-/

set_option autoImplicit false
namespace CSL.TwoWordRadixInsert
open TwoWordSpill TwoWordIndirect TwoWordUniformLoop

abbrev Word (w : ℕ) := Fin (2^w)
abbrev Logical (w : ℕ) := TwoWordIndirect.Logical (Fin 5) (Fin 5) (Word w)

def label {w : ℕ} (hcap : 11 ≤ 2^w) (i : Fin 11) : Word w := i.castLE hcap

@[simp] theorem label_val {w : ℕ} (hcap : 11 ≤ 2^w) (i : Fin 11) :
    (label hcap i).val = i.val := rfl

theorem label_injective {w : ℕ} (hcap : 11 ≤ 2^w) :
    Function.Injective (label hcap) := by
  intro a b h
  exact Fin.ext (congrArg (fun x : Word w => x.val) h)

@[simp] theorem label_eq {w : ℕ} (hcap : 11 ≤ 2^w) (i j : Fin 11) :
    label hcap i = label hcap j ↔ i = j := (label_injective hcap).eq_iff

def arithmetic {w : ℕ} (source target : Fin 5) (f : Word w → Word w)
    (next : Word w) : TwoWordIndirect.Instruction (Fin 5) (Fin 5) (Word w) :=
  .arithmetic ⟨.inl source, .inl source, .inl target, fun x _ => f x, fun _ _ => next⟩

/-- Registers: cursor, record, bucket, pointer value, pointer validity.
Regions: input, head value, head validity, next value, next validity. -/
def instruction {w : ℕ} (hcap : 11 ≤ 2^w) (key : Word w → Word w)
    (j : Fin 10) : TwoWordIndirect.Instruction (Fin 5) (Fin 5) (Word w) :=
  match j.val with
  | 0 => .load 0 0 1 (label hcap 1)
  | 1 => arithmetic 1 2 key (label hcap 2)
  | 2 => .load 1 2 3 (label hcap 3)
  | 3 => .load 2 2 4 (label hcap 4)
  | 4 => .store 3 0 3 (label hcap 5)
  | 5 => .store 4 0 4 (label hcap 6)
  | 6 => arithmetic 0 3 id (label hcap 7)
  | 7 => arithmetic 0 4 (fun _ => label hcap 1) (label hcap 8)
  | 8 => .store 1 2 3 (label hcap 9)
  | _ => .store 2 2 4 (label hcap 10)

def table {w : ℕ} (hcap : 11 ≤ 2^w) (key : Word w → Word w) :
    TwoWordIndirect.Table (Fin 5) (Fin 5) (Word w) :=
  (List.finRange 10).map (fun j => (label hcap j.castSucc, instruction hcap key j))

theorem selected_of_mem
    {R Region W : Type*} [DecidableEq R] [DecidableEq Region] [DecidableEq W]
    (xs : TwoWordIndirect.Table R Region W) (tag : W)
    (i : TwoWordIndirect.Instruction R Region W)
    (hm : (tag,i) ∈ xs) (hn : (xs.map Prod.fst).Nodup)
    (v : TwoWordIndirect.Logical R Region W) :
    tableEffect tag xs v = effect i v := by
  induction xs generalizing v with
  | nil => simp at hm
  | cons entry rest ih =>
      obtain ⟨hnot, hrest⟩ := List.nodup_cons.mp hn
      rcases List.mem_cons.mp hm with he | hm
      · subst entry
        rw [tableEffect, if_pos rfl]
        apply tableEffect_disabled
        intro e he ht
        apply hnot
        exact List.mem_map.mpr ⟨e, he, ht.symm⟩
      · have hh : tag ≠ entry.1 := by
          intro he
          apply hnot
          exact List.mem_map.mpr ⟨(tag,i), hm, he⟩
        rw [tableEffect, if_neg hh]
        exact ih hm hrest v

theorem table_tags_nodup {w : ℕ} (hcap : 11 ≤ 2^w) (key : Word w → Word w) :
    ((table hcap key).map Prod.fst).Nodup := by
  simp only [table, List.map_map, Function.comp_apply]
  exact (List.nodup_finRange 10).map (fun a b h =>
    Fin.ext (congrArg (fun x : Fin 11 => x.val) ((label_injective hcap) h)))

theorem step_at {w : ℕ} (hcap : 11 ≤ 2^w) (key : Word w → Word w)
    (j : Fin 10) (v : Logical w) (hp : v.pc = label hcap j.castSucc) :
    logicalStep (table hcap key) v = effect (instruction hcap key j) v := by
  unfold logicalStep
  rw [hp]
  apply selected_of_mem _ _ _ _ (table_tags_nodup hcap key)
  exact List.mem_map.mpr ⟨j, List.mem_finRange j, rfl⟩

theorem instruction_pc {w : ℕ} (hcap : 11 ≤ 2^w) (key : Word w → Word w)
    (j : Fin 10) (v : Logical w) :
    (effect (instruction hcap key j) v).pc = label hcap j.succ := by
  fin_cases j <;> rfl

def after {w : ℕ} (hcap : 11 ≤ 2^w) (key : Word w → Word w)
    (v : Logical w) : Logical w :=
  (List.finRange 10).foldl (fun state j => effect (instruction hcap key j) state) v

theorem halts_after_ten {w : ℕ} (hcap : 11 ≤ 2^w) (key : Word w → Word w)
    (v : Logical w) (hp : v.pc = label hcap 0) :
    HaltsAfter (table hcap key) (label hcap 10) 10 v (after hcap key v) := by
  have hn (j : Fin 10) : label hcap j.castSucc ≠ label hcap 10 := by
    intro he
    have hv : j.val = 10 := congrArg (fun x : Fin 11 => x.val) ((label_injective hcap) he)
    have hj := j.isLt
    omega
  let s1 := effect (instruction hcap key 0) v
  have p1 : s1.pc = label hcap 1 := instruction_pc hcap key 0 v
  have e0 : logicalStep (table hcap key) v = s1 := step_at hcap key 0 v hp
  let s2 := effect (instruction hcap key 1) s1
  have p2 : s2.pc = label hcap 2 := instruction_pc hcap key 1 s1
  have e1 : logicalStep (table hcap key) s1 = s2 := step_at hcap key 1 s1 p1
  let s3 := effect (instruction hcap key 2) s2
  have p3 : s3.pc = label hcap 3 := instruction_pc hcap key 2 s2
  have e2 : logicalStep (table hcap key) s2 = s3 := step_at hcap key 2 s2 p2
  let s4 := effect (instruction hcap key 3) s3
  have p4 : s4.pc = label hcap 4 := instruction_pc hcap key 3 s3
  have e3 : logicalStep (table hcap key) s3 = s4 := step_at hcap key 3 s3 p3
  let s5 := effect (instruction hcap key 4) s4
  have p5 : s5.pc = label hcap 5 := instruction_pc hcap key 4 s4
  have e4 : logicalStep (table hcap key) s4 = s5 := step_at hcap key 4 s4 p4
  let s6 := effect (instruction hcap key 5) s5
  have p6 : s6.pc = label hcap 6 := instruction_pc hcap key 5 s5
  have e5 : logicalStep (table hcap key) s5 = s6 := step_at hcap key 5 s5 p5
  let s7 := effect (instruction hcap key 6) s6
  have p7 : s7.pc = label hcap 7 := instruction_pc hcap key 6 s6
  have e6 : logicalStep (table hcap key) s6 = s7 := step_at hcap key 6 s6 p6
  let s8 := effect (instruction hcap key 7) s7
  have p8 : s8.pc = label hcap 8 := instruction_pc hcap key 7 s7
  have e7 : logicalStep (table hcap key) s7 = s8 := step_at hcap key 7 s7 p7
  let s9 := effect (instruction hcap key 8) s8
  have p9 : s9.pc = label hcap 9 := instruction_pc hcap key 8 s8
  have e8 : logicalStep (table hcap key) s8 = s9 := step_at hcap key 8 s8 p8
  let s10 := effect (instruction hcap key 9) s9
  have p10 : s10.pc = label hcap 10 := instruction_pc hcap key 9 s9
  have e9 : logicalStep (table hcap key) s9 = s10 := step_at hcap key 9 s9 p9
  simp only [HaltsAfter]
  rw [e0, e1, e2, e3, e4, e5, e6, e7, e8, e9]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, p10, ?_⟩
  · rw [hp]; exact hn 0
  · rw [p1]; exact hn 1
  · rw [p2]; exact hn 2
  · rw [p3]; exact hn 3
  · rw [p4]; exact hn 4
  · rw [p5]; exact hn 5
  · rw [p6]; exact hn 6
  · rw [p7]; exact hn 7
  · rw [p8]; exact hn 8
  · rw [p9]; exact hn 9
  · simp [after, List.finRange_succ, List.foldl_append, s1, s2, s3, s4, s5, s6, s7, s8, s9, s10]

theorem table_cost {w : ℕ} (hcap : 11 ≤ 2^w) (key : Word w → Word w) :
    tableCost (table hcap key) = 82 := by
  simp [table, List.finRange_succ, List.map_append, tableCost, instruction,
    arithmetic, instructionCost]

theorem after_cursor {w : ℕ} (hcap : 11 ≤ 2^w) (key : Word w → Word w)
    (v : Logical w) : (after hcap key v).regs (.inl 0) = v.regs (.inl 0) := by
  simp [after, List.finRange_succ, List.foldl_append, instruction, effect,
    arithmetic, applyInstruction, loadEffect, storeEffect, Function.update_apply]

theorem after_input {w : ℕ} (hcap : 11 ≤ 2^w) (key : Word w → Word w)
    (v : Logical w) (x : Word w) :
    (after hcap key v).regs (.inr (0,x)) = v.regs (.inr (0,x)) := by
  simp [after, List.finRange_succ, List.foldl_append, instruction, effect,
    arithmetic, applyInstruction, loadEffect, storeEffect, Function.update_apply]

theorem after_next_value {w : ℕ} (hcap : 11 ≤ 2^w) (key : Word w → Word w)
    (v : Logical w) (x : Word w) :
    (after hcap key v).regs (.inr (3,x)) =
      if x = v.regs (.inl 0) then
        v.regs (.inr (1,key (v.regs (.inr (0,v.regs (.inl 0))))))
      else v.regs (.inr (3,x)) := by
  simp [after, List.finRange_succ, List.foldl_append, instruction, effect,
    arithmetic, applyInstruction, loadEffect, storeEffect, Function.update_apply]

theorem after_next_valid {w : ℕ} (hcap : 11 ≤ 2^w) (key : Word w → Word w)
    (v : Logical w) (x : Word w) :
    (after hcap key v).regs (.inr (4,x)) =
      if x = v.regs (.inl 0) then
        v.regs (.inr (2,key (v.regs (.inr (0,v.regs (.inl 0))))))
      else v.regs (.inr (4,x)) := by
  simp [after, List.finRange_succ, List.foldl_append, instruction, effect,
    arithmetic, applyInstruction, loadEffect, storeEffect, Function.update_apply]

theorem after_head_value {w : ℕ} (hcap : 11 ≤ 2^w) (key : Word w → Word w)
    (v : Logical w) (x : Word w) :
    (after hcap key v).regs (.inr (1,x)) =
      if x = key (v.regs (.inr (0,v.regs (.inl 0)))) then v.regs (.inl 0)
      else v.regs (.inr (1,x)) := by
  simp [after, List.finRange_succ, List.foldl_append, instruction, effect,
    arithmetic, applyInstruction, loadEffect, storeEffect, Function.update_apply]

theorem after_head_valid {w : ℕ} (hcap : 11 ≤ 2^w) (key : Word w → Word w)
    (v : Logical w) (x : Word w) :
    (after hcap key v).regs (.inr (2,x)) =
      if x = key (v.regs (.inr (0,v.regs (.inl 0)))) then label hcap 1
      else v.regs (.inr (2,x)) := by
  simp [after, List.finRange_succ, List.foldl_append, instruction, effect,
    arithmetic, applyInstruction, loadEffect, storeEffect, Function.update_apply]

def position {w n : ℕ} (h : n ≤ 2^w) (i : Fin n) : Word w := i.castLE h

@[simp] theorem position_eq {w n : ℕ} (h : n ≤ 2^w) (i j : Fin n) :
    position h i = position h j ↔ i = j := by
  constructor
  · intro he; exact Fin.ext (congrArg (fun x : Word w => x.val) he)
  · intro he; cases he; rfl

def pointerValue {w n : ℕ} (hcap : 11 ≤ 2^w) (hN : n ≤ 2^w) :
    DirectRadix.Pointer n → Word w
  | none => label hcap 0
  | some i => position hN i

def pointerValid {w n : ℕ} (hcap : 11 ≤ 2^w) : DirectRadix.Pointer n → Word w
  | none => label hcap 0
  | some _ => label hcap 1

structure Represents {w n K : ℕ} (hcap : 11 ≤ 2^w)
    (hN : n ≤ 2^w) (hK : K ≤ 2^w) (heap : DirectRadix.Heap n K) (v : Logical w) : Prop where
  headValue : ∀ k, v.regs (.inr (1,position hK k)) = pointerValue hcap hN (heap.head k)
  headValid : ∀ k, v.regs (.inr (2,position hK k)) = pointerValid hcap (heap.head k)
  nextValue : ∀ i, v.regs (.inr (3,position hN i)) = pointerValue hcap hN (heap.next i)
  nextValid : ∀ i, v.regs (.inr (4,position hN i)) = pointerValid hcap (heap.next i)

theorem after_represents {w n K : ℕ} (hcap : 11 ≤ 2^w)
    (hN : n ≤ 2^w) (hK : K ≤ 2^w) (input : Fin n → Word w) (key : Word w → Fin K)
    (i : Fin n) (heap : DirectRadix.Heap n K) (v : Logical w)
    (hr : Represents hcap hN hK heap v)
    (hin : ∀ j, v.regs (.inr (0,position hN j)) = input j)
    (hc : v.regs (.inl 0) = position hN i) :
    Represents hcap hN hK (DirectRadix.prepend (fun j => key (input j)) i heap)
      (after hcap (fun x => position hK (key x)) v) := by
  constructor
  · intro k
    rw [after_head_value, hc, hin]
    simp only [position_eq]
    by_cases hk : k = key (input i)
    · simp [DirectRadix.prepend, Function.update_apply, hk, pointerValue]
    · simp [DirectRadix.prepend, Function.update_apply, hk, hr.headValue]
  · intro k
    rw [after_head_valid, hc, hin]
    simp only [position_eq]
    by_cases hk : k = key (input i)
    · simp [DirectRadix.prepend, Function.update_apply, hk, pointerValid]
    · simp [DirectRadix.prepend, Function.update_apply, hk, hr.headValid]
  · intro j
    rw [after_next_value, hc, hin]
    simp only [position_eq]
    by_cases hj : j = i
    · simp [DirectRadix.prepend, Function.update_apply, hj, hr.headValue]
    · simp [DirectRadix.prepend, Function.update_apply, hj, hr.nextValue]
  · intro j
    rw [after_next_valid, hc, hin]
    simp only [position_eq]
    by_cases hj : j = i
    · simp [DirectRadix.prepend, Function.update_apply, hj, hr.headValid]
    · simp [DirectRadix.prepend, Function.update_apply, hj, hr.nextValid]

/-- This is a concrete physical instance, not a generic executor contract:
the fixed ten-instruction program realizes the existing DirectRadix heap
update, from the actual input and actual old linked-directory contents. -/
theorem physical_insertRecord {w n K : ℕ} (hcap : 11 ≤ 2^w)
    (hN : n ≤ 2^w) (hK : K ≤ 2^w) (input : Fin n → Word w) (key : Word w → Fin K)
    (i : Fin n) (old : DirectRadix.Machine (Word w) n K)
    (s : TwoWordPhysicalAddresses.State (Word w))
    (hr : Represents hcap hN hK old.heap (view 5 5 w s))
    (hin : ∀ j, (view 5 5 w s).regs (.inr (0,position hN j)) = input j)
    (hc : (view 5 5 w s).regs (.inl 0) = position hN i)
    (hp : (view 5 5 w s).pc = label hcap 0) :
    ∃ t, Physical.Executes
      (program 5 5 w (table hcap (fun x => position hK (key x))) (label hcap 10)) s t 841 ∧
      Represents hcap hN hK (DirectRadix.insertRecord input key i old).heap (view 5 5 w t) ∧
      (∀ j, (view 5 5 w t).regs (.inr (0,position hN j)) = input j) := by
  obtain ⟨t, ht, hv⟩ := terminates_of_source 5 5 w
    (table hcap (fun x => position hK (key x))) (label hcap 10) 10 s _
    (halts_after_ten hcap _ _ hp)
  refine ⟨t, ?_, ?_, ?_⟩
  · simpa [table_cost] using ht
  · rw [hv, DirectRadix.insertRecord_heap]
    exact after_represents hcap hN hK input key i old.heap _ hr hin hc
  · intro j
    rw [hv, after_input]
    exact hin j

end CSL.TwoWordRadixInsert
end Insert

section Build
/-!
# The actual backward insertion loop

A fixed eleventh instruction decrements the external cursor and branches
back to the insertion entry point, or reaches a distinct halt tag at zero.
There is no host-side list of invocations in the executed program. Initial
directory initialization is still an explicit precondition of the empty-
heap specialization, rather than an assumption that fresh disk is zero.
-/

set_option autoImplicit false
namespace CSL.TwoWordRadixBuild
open TwoWordSpill TwoWordIndirect TwoWordUniformLoop TwoWordRadixInsert

def smallCap {w : ℕ} (hcap : 12 ≤ 2^w) : 11 ≤ 2^w := by omega
def halt {w : ℕ} (hcap : 12 ≤ 2^w) : Word w := ⟨11, by omega⟩

def predecessor {w : ℕ} (x : Word w) : Word w :=
  ⟨x.val-1, lt_of_le_of_lt (Nat.sub_le _ _) x.isLt⟩

def advance {w : ℕ} (hcap : 12 ≤ 2^w) :
    TwoWordIndirect.Instruction (Fin 5) (Fin 5) (Word w) :=
  .arithmetic ⟨.inl 0,.inl 0,.inl 0,fun x _ => predecessor x,
    fun x _ => if x.val = 0 then halt hcap else label (smallCap hcap) 0⟩

def table {w : ℕ} (hcap : 12 ≤ 2^w) (key : Word w → Word w) :
    TwoWordIndirect.Table (Fin 5) (Fin 5) (Word w) :=
  TwoWordRadixInsert.table (smallCap hcap) key ++
    [(label (smallCap hcap) 10, advance hcap)]

theorem step_before_advance {w : ℕ} (hcap : 12 ≤ 2^w) (key : Word w → Word w)
    (v : Logical w) (hc : v.pc ≠ label (smallCap hcap) 10) :
    logicalStep (table hcap key) v =
      logicalStep (TwoWordRadixInsert.table (smallCap hcap) key) v := by
  simp [table, logicalStep, tableEffect_append, tableEffect, hc]

theorem step_advance {w : ℕ} (hcap : 12 ≤ 2^w) (key : Word w → Word w)
    (v : Logical w) (hc : v.pc = label (smallCap hcap) 10) :
    logicalStep (table hcap key) v = effect (advance hcap) v := by
  unfold logicalStep
  rw [hc]
  apply tableEffect_selected
  · intro e he hh
    obtain ⟨j,hj,rfl⟩ := List.mem_map.mp he
    have hx : 10 = j.val := congrArg (fun x : Fin 11 => x.val)
      ((label_injective (smallCap hcap)) hh)
    have hj := j.isLt
    omega
  · simp

private theorem tableEffect_pc_bound
    {R Region W : Type*} [DecidableEq R] [DecidableEq Region] [DecidableEq W]
    (measure : W → ℕ) (bound : ℕ) (key : W) (xs : TwoWordIndirect.Table R Region W)
    (hi : ∀ e ∈ xs, ∀ v, measure (effect e.2 v).pc ≤ bound)
    (v : TwoWordIndirect.Logical R Region W) (hv : measure v.pc ≤ bound) :
    measure (tableEffect key xs v).pc ≤ bound := by
  induction xs generalizing v with
  | nil => exact hv
  | cons entry rest ih =>
      apply ih (by intro e he; exact hi e (by simp [he]))
      by_cases hh : key = entry.1
      · simpa [hh] using hi entry (by simp) v
      · simpa [hh] using hv

theorem insert_step_pc_bound {w : ℕ} (hcap : 12 ≤ 2^w) (key : Word w → Word w)
    (v : Logical w) (hv : v.pc.val ≤ 10) :
    (logicalStep (TwoWordRadixInsert.table (smallCap hcap) key) v).pc.val ≤ 10 := by
  apply tableEffect_pc_bound Fin.val 10 v.pc _ _ v hv
  intro e he u
  obtain ⟨j,hj,rfl⟩ := List.mem_map.mp he
  rw [instruction_pc, label_val]
  have hj := j.isLt
  simp only [Fin.val_succ]
  omega

theorem transfer_insert_prefix {w : ℕ} (hcap : 12 ≤ 2^w) (key : Word w → Word w)
    (n m : ℕ) (v middle final : Logical w)
    (hp : HaltsAfter (TwoWordRadixInsert.table (smallCap hcap) key)
      (label (smallCap hcap) 10) n v middle)
    (hv : v.pc.val ≤ 10)
    (hr : HaltsAfter (table hcap key) (halt hcap) m middle final) :
    HaltsAfter (table hcap key) (halt hcap) (n+m) v final := by
  induction n generalizing v with
  | zero => obtain ⟨_,rfl⟩ := hp; simpa using hr
  | succ n ih =>
      obtain ⟨hh,hn⟩ := hp
      rw [Nat.succ_add]
      refine ⟨?_, ?_⟩
      · intro he
        have hv' : v.pc.val = 11 := congrArg Fin.val he
        omega
      · rw [step_before_advance hcap key v hh]
        exact ih _ hn (insert_step_pc_bound hcap key v hv)

theorem after_pc {w : ℕ} (hcap : 12 ≤ 2^w) (key : Word w → Word w)
    (v : Logical w) : (after (smallCap hcap) key v).pc = label (smallCap hcap) 10 := by
  simp [after, List.finRange_succ, List.foldl_append, instruction, effect,
    storeEffect]

theorem advance_pc {w : ℕ} (hcap : 12 ≤ 2^w) (v : Logical w) :
    (effect (advance hcap) v).pc =
      if (v.regs (.inl 0)).val = 0 then halt hcap else label (smallCap hcap) 0 := rfl

theorem advance_cursor {w : ℕ} (hcap : 12 ≤ 2^w) (v : Logical w) :
    (effect (advance hcap) v).regs (.inl 0) = predecessor (v.regs (.inl 0)) := by
  simp [advance, effect, applyInstruction]

theorem advance_data {w : ℕ} (hcap : 12 ≤ 2^w) (v : Logical w)
    (region : Fin 5) (x : Word w) :
    (effect (advance hcap) v).regs (.inr (region,x)) = v.regs (.inr (region,x)) := by
  simp [advance, effect, applyInstruction]

theorem advance_represents {w n K : ℕ} (hcap : 12 ≤ 2^w)
    (hN : n ≤ 2^w) (hK : K ≤ 2^w) (heap : DirectRadix.Heap n K) (v : Logical w)
    (h : Represents (smallCap hcap) hN hK heap v) :
    Represents (smallCap hcap) hN hK heap (effect (advance hcap) v) := by
  constructor
  · intro k; rw [advance_data]; exact h.headValue k
  · intro k; rw [advance_data]; exact h.headValid k
  · intro i; rw [advance_data]; exact h.nextValue i
  · intro i; rw [advance_data]; exact h.nextValid i

def buildBelow {n K : ℕ} (key : Fin n → Fin K) :
    (count : ℕ) → count ≤ n → DirectRadix.Heap n K → DirectRadix.Heap n K
  | 0, _, heap => heap
  | count+1, hc, heap =>
      buildBelow key count (by omega) (DirectRadix.prepend key ⟨count,by omega⟩ heap)

theorem table_cost {w : ℕ} (hcap : 12 ≤ 2^w) (key : Word w → Word w) :
    tableCost (table hcap key) = 91 := by
  have hadd (xs ys : TwoWordIndirect.Table (Fin 5) (Fin 5) (Word w)) :
      tableCost (xs ++ ys) = tableCost xs + tableCost ys := by
    induction xs with
    | nil => simp [tableCost]
    | cons x xs ih => simp [tableCost, ih, Nat.add_assoc]
  simp [table, hadd, TwoWordRadixInsert.table_cost, tableCost, advance, instructionCost]

theorem backward_loop {w n K : ℕ} (hcap : 12 ≤ 2^w)
    (hN : n ≤ 2^w) (hK : K ≤ 2^w) (input : Fin n → Word w) (key : Word w → Fin K)
    (count : ℕ) (hcount : count+1 ≤ n) (heap : DirectRadix.Heap n K) (v : Logical w)
    (hr : Represents (smallCap hcap) hN hK heap v)
    (hin : ∀ j, v.regs (.inr (0,position hN j)) = input j)
    (hc : v.regs (.inl 0) = position hN ⟨count,by omega⟩)
    (hp : v.pc = label (smallCap hcap) 0) :
    ∃ final, HaltsAfter (table hcap (fun x => position hK (key x))) (halt hcap)
        (11*(count+1)) v final ∧
      Represents (smallCap hcap) hN hK
        (buildBelow (fun j => key (input j)) (count+1) hcount heap) final ∧
      (∀ j, final.regs (.inr (0,position hN j)) = input j) := by
  induction count generalizing heap v with
  | zero =>
      let mid := after (smallCap hcap) (fun x => position hK (key x)) v
      let final := effect (advance hcap) mid
      have hmcur : mid.regs (.inl 0) = position hN ⟨0,by omega⟩ :=
        (after_cursor _ _ _).trans hc
      have hmrep := after_represents (smallCap hcap) hN hK input key
        ⟨0,by omega⟩ heap v hr hin hc
      have hcont : HaltsAfter (table hcap (fun x => position hK (key x))) (halt hcap)
          1 mid final := by
        refine ⟨?_, ?_, rfl⟩
        · rw [after_pc hcap]; intro he
          have hx : (10 : ℕ) = 11 := congrArg (fun x : Word w => x.val) he
          omega
        · rw [step_advance hcap _ _ (after_pc hcap _ _), advance_pc, hmcur]
          rfl
      have hprefix := transfer_insert_prefix hcap (fun x => position hK (key x)) 10 1 v mid final
        (halts_after_ten _ _ _ hp) (by rw [hp, label_val]; decide) hcont
      refine ⟨final, hprefix, ?_, ?_⟩
      · exact advance_represents hcap hN hK _ _ hmrep
      · intro j; rw [advance_data, after_input]; exact hin j
  | succ count ih =>
      let mid := after (smallCap hcap) (fun x => position hK (key x)) v
      let next := effect (advance hcap) mid
      let i : Fin n := ⟨count+1,by omega⟩
      have hmcur : mid.regs (.inl 0) = position hN i := (after_cursor _ _ _).trans hc
      have hmrep := after_represents (smallCap hcap) hN hK input key i heap v hr hin hc
      have hnrep := advance_represents hcap hN hK _ _ hmrep
      have hncur : next.regs (.inl 0) = position hN ⟨count,by omega⟩ := by
        rw [advance_cursor, hmcur]
        apply Fin.ext
        simp [predecessor, position, i]
      have hnpc : next.pc = label (smallCap hcap) 0 := by
        rw [advance_pc, hmcur]
        simp [position, i]
      have hnin (j : Fin n) : next.regs (.inr (0,position hN j)) = input j := by
        rw [advance_data, after_input]
        exact hin j
      obtain ⟨final, hrun, hrep, hinput⟩ := ih (by omega)
        (DirectRadix.prepend (fun j => key (input j)) i heap) next hnrep hnin hncur hnpc
      have hcont : HaltsAfter (table hcap (fun x => position hK (key x))) (halt hcap)
          (11*(count+1)+1) mid final := by
        refine ⟨?_, ?_⟩
        · rw [after_pc hcap]; intro he
          have hx : (10 : ℕ) = 11 := congrArg (fun x : Word w => x.val) he
          omega
        · rw [step_advance hcap _ _ (after_pc hcap _ _)]
          exact hrun
      have hprefix := transfer_insert_prefix hcap (fun x => position hK (key x))
        10 (11*(count+1)+1) v mid final (halts_after_ten _ _ _ hp)
        (by rw [hp,label_val]; decide) hcont
      refine ⟨final, ?_, hrep, hinput⟩
      convert hprefix using 1 <;> omega

theorem buildBelow_eq_fold {n K : ℕ} (key : Fin n → Fin K) (count : ℕ)
    (hc : count ≤ n) (heap : DirectRadix.Heap n K) :
    buildBelow key count hc heap =
      (List.ofFn (fun j : Fin count => j.castLE hc)).reverse.foldl
        (fun h i => DirectRadix.prepend key i h) heap := by
  induction count generalizing heap with
  | zero => simp [buildBelow]
  | succ count ih =>
      rw [buildBelow, ih, List.ofFn_succ', List.concat_eq_append, List.reverse_concat, List.foldl_cons]
      rfl

theorem buildBelow_empty {n K : ℕ} (key : Fin n → Fin K) :
    buildBelow key n le_rfl DirectRadix.Heap.empty =
      DirectRadix.build key (List.finRange n) := by
  rw [buildBelow_eq_fold]
  rfl

/-- A fixed while-program performs the entire backward input scan. Its
cursor and PC are external virtual registers; the input length never becomes
a free host-side loop index in the physical execution. -/
theorem physical_buildBelow {w n K : ℕ} (hcap : 12 ≤ 2^w)
    (hN : n ≤ 2^w) (hK : K ≤ 2^w) (hn : 0 < n)
    (input : Fin n → Word w) (key : Word w → Fin K) (heap : DirectRadix.Heap n K)
    (s : TwoWordPhysicalAddresses.State (Word w))
    (hr : Represents (smallCap hcap) hN hK heap (view 5 5 w s))
    (hin : ∀ j, (view 5 5 w s).regs (.inr (0,position hN j)) = input j)
    (hc : (view 5 5 w s).regs (.inl 0) = position hN ⟨n-1, by omega⟩)
    (hp : (view 5 5 w s).pc = label (smallCap hcap) 0) :
    ∃ t, Physical.Executes
      (program 5 5 w (table hcap (fun x => position hK (key x))) (halt hcap)) s t
        (1023*n+1) ∧
      Represents (smallCap hcap) hN hK
        (buildBelow (fun j => key (input j)) n le_rfl heap) (view 5 5 w t) ∧
      (∀ j, (view 5 5 w t).regs (.inr (0,position hN j)) = input j) := by
  cases n with
  | zero => omega
  | succ count =>
      obtain ⟨final, hrun, hrep, hi⟩ := backward_loop hcap hN hK input key count le_rfl
        heap (view 5 5 w s) hr hin hc hp
      obtain ⟨t, ht, hv⟩ := terminates_of_source 5 5 w
        (table hcap (fun x => position hK (key x))) (halt hcap) _ s final hrun
      refine ⟨t, ?_, ?_, ?_⟩
      · convert ht using 1 <;> rw [table_cost] <;> omega
      · rw [hv]; exact hrep
      · rw [hv]; exact hi

/-- Given an explicitly represented empty directory, the loop constructs exactly the heap specified by DirectRadix.build. 

-/
theorem physical_build {w n K : ℕ} (hcap : 12 ≤ 2^w)
    (hN : n ≤ 2^w) (hK : K ≤ 2^w) (hn : 0 < n)
    (input : Fin n → Word w) (key : Word w → Fin K)
    (s : TwoWordPhysicalAddresses.State (Word w))
    (hr : Represents (smallCap hcap) hN hK DirectRadix.Heap.empty (view 5 5 w s))
    (hin : ∀ j, (view 5 5 w s).regs (.inr (0,position hN j)) = input j)
    (hc : (view 5 5 w s).regs (.inl 0) = position hN ⟨n-1, by omega⟩)
    (hp : (view 5 5 w s).pc = label (smallCap hcap) 0) :
    ∃ t, Physical.Executes
      (program 5 5 w (table hcap (fun x => position hK (key x))) (halt hcap)) s t
        (1023*n+1) ∧
      Represents (smallCap hcap) hN hK
        (DirectRadix.build (fun j => key (input j)) (List.finRange n)) (view 5 5 w t) ∧
      (∀ j, (view 5 5 w t).regs (.inr (0,position hN j)) = input j) := by
  simpa only [buildBelow_empty] using
    physical_buildBelow hcap hN hK hn input key DirectRadix.Heap.empty s hr hin hc hp

end CSL.TwoWordRadixBuild
end Build


