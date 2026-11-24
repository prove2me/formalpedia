-- Prove2me | Definitions.Def_CSL_Sorting_SmallMemory_PhysicalAddresses
-- name    : CSL_Sorting_SmallMemory_PhysicalAddresses
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-24T12:10:38.202344+00:00
-- url     : https://prove2.me/theorems/d1fba50b-63ac-4841-b915-15c07d4622aa
-- title:
--   Coded sorting library: Sorting / SmallMemory / PhysicalAddresses
-- statement:
--   Module `CodedSorting.Sorting.SmallMemory.PhysicalAddresses` of the Lean development accompanying B. Li, Z. Li, S. Liu, *Undirected Multiple-Unicast Network Coding and Faster External-Memory Integer Sorting*, arXiv:2610.20079, ported to Lean v4.33.1 and Mathlib `0df444a` (namespace `CodedSorting` renamed to `CSL`).
--
--   # Two resident words for a fixed virtual-register instruction table
--
--   This is a small-memory compilation lemma, not a sorting implementation.
--   All virtual registers and the data-dependent virtual program counter live
--   on disk.  The physical schedule is fixed before the input: copy the virtual
--   PC to a snapshot cell, then visit every instruction in the same order.
--   Each instruction is predicated by the snapshot.  In particular the selected
--   instruction or continuation is never retained for free across a disk read.
--
--   The physical resident state is exactly a pair of words.  The recursion over
--   the fixed schedule is program syntax, not an input-dependent stack.  A
--   caller claiming a uniform sorting algorithm must still supply the fixed
--   virtual program, indirect data-access instructions, address encodings, its
--   termination/step bound, and the connection to packed input/output.
--
--   This module is part of the machine-checked proof of Theorem 3.1 (external-memory integer sorting) and is imported by the later modules of that development.
-- source:
--   B. Li, Z. Li, S. Liu, *Undirected Multiple-Unicast Network Coding and Faster External-Memory Integer Sorting*, arXiv:2610.20079 (Theorem 3.1, p.4, and Appendix D); Lean development https://github.com/rtyu-1/coded-sorting-lean, module CodedSorting.Sorting.SmallMemory.PhysicalAddresses

import Definitions.Def_CSL_Compat
import Mathlib.Data.List.Defs
import Mathlib.Data.Fin.Basic
import Mathlib.Logic.Function.Basic
import Lean.Elab.Tactic.Omega
import Mathlib.Logic.Equiv.Fin.Basic

section Spill
/-!
# Two resident words for a fixed virtual-register instruction table

This is a small-memory compilation lemma, not a sorting implementation.
All virtual registers and the data-dependent virtual program counter live
on disk.  The physical schedule is fixed before the input: copy the virtual
PC to a snapshot cell, then visit every instruction in the same order.
Each instruction is predicated by the snapshot.  In particular the selected
instruction or continuation is never retained for free across a disk read.

The physical resident state is exactly a pair of words.  The recursion over
the fixed schedule is program syntax, not an input-dependent stack.  A
caller claiming a uniform sorting algorithm must still supply the fixed
virtual program, indirect data-access instructions, address encodings, its
termination/step bound, and the connection to packed input/output.
-/

set_option autoImplicit false
namespace CSL.TwoWordSpill

variable {Reg Word : Type*} [DecidableEq Reg] [DecidableEq Word]

inductive Address (Reg : Type*) where
  | reg (r : Reg)
  | pc
  | snapshot
  | valueTemp
  | pcTemp
  | trash
  deriving DecidableEq

structure State (Reg Word : Type*) where
  left : Word
  right : Word
  disk : Address Reg → Word

abbrev Resident (Word : Type*) := Word × Word

def resident (s : State Reg Word) : Resident Word := (s.left, s.right)

/-- All command functions are part of the fixed program.  A read changes
one of the two existing words.  Writes inspect only those two words. -/
inductive Command (Reg Word : Type*) where
  | readLeft (a : Address Reg)
  | readRight (a : Address Reg)
  | readRightAt (a : Resident Word → Address Reg)
  | writeLeft (a : Address Reg)
  | writeRight (a : Resident Word → Address Reg)
  | localOp (f : Resident Word → Resident Word)

def cost : Command Reg Word → ℕ
  | .localOp _ => 0
  | _ => 1

def step (cmd : Command Reg Word) (s : State Reg Word) : State Reg Word :=
  match cmd with
  | .readLeft a => { s with left := s.disk a }
  | .readRight a => { s with right := s.disk a }
  | .readRightAt a => { s with right := s.disk (a (resident s)) }
  | .writeLeft a => { s with disk := Function.update s.disk a s.left }
  | .writeRight a =>
      { s with disk := Function.update s.disk (a (resident s)) s.right }
  | .localOp f =>
      { s with left := (f (resident s)).1, right := (f (resident s)).2 }

def execute : List (Command Reg Word) → State Reg Word → State Reg Word
  | [], s => s
  | cmd :: rest, s => execute rest (step cmd s)

def transfers : List (Command Reg Word) → ℕ
  | [] => 0
  | cmd :: rest => cost cmd + transfers rest

/-- The returned transfer count belongs to this same fixed-schedule run. -/
def run (code : List (Command Reg Word)) (s : State Reg Word) :
    State Reg Word × ℕ := (execute code s, transfers code)

theorem execute_append (xs ys : List (Command Reg Word)) (s : State Reg Word) :
    execute (xs ++ ys) s = execute ys (execute xs s) := by
  induction xs generalizing s with
  | nil => rfl
  | cons x xs ih => exact ih (step x s)

theorem transfers_append (xs ys : List (Command Reg Word)) :
    transfers (xs ++ ys) = transfers xs + transfers ys := by
  induction xs with
  | nil => simp [transfers]
  | cons x xs ih => simp only [List.cons_append, transfers, ih, Nat.add_assoc]

theorem zero_cost_locality (cmd : Command Reg Word) (s t : State Reg Word)
    (hc : cost cmd = 0) (hr : resident s = resident t) :
    resident (step cmd s) = resident (step cmd t) ∧
      (step cmd s).disk = s.disk := by
  cases cmd <;> simp_all [cost, step, resident]

structure Virtual (Reg Word : Type*) where
  regs : Reg → Word
  pc : Word

def observe (s : State Reg Word) : Virtual Reg Word :=
  ⟨fun r => s.disk (.reg r), s.disk .pc⟩

/-- Both results use the old operands; the next-PC function can implement
conditional jumps without making the physical schedule data-dependent. -/
structure Instruction (Reg Word : Type*) where
  source₁ : Reg
  source₂ : Reg
  target : Reg
  result : Word → Word → Word
  nextPC : Word → Word → Word

def applyInstruction (i : Instruction Reg Word) (v : Virtual Reg Word) :
    Virtual Reg Word :=
  ⟨Function.update v.regs i.target (i.result (v.regs i.source₁) (v.regs i.source₂)),
    i.nextPC (v.regs i.source₁) (v.regs i.source₂)⟩

def guarded (key tag : Word) (i : Instruction Reg Word) (v : Virtual Reg Word) :
    Virtual Reg Word := if key = tag then applyInstruction i v else v

/-- Nine real word transfers and one free two-word local operation.
Disabled writes go to a dedicated scratch cell, never to a virtual register.
The snapshot word stays in the left resident cell during the final reads. -/
def compileInstruction (tag : Word) (i : Instruction Reg Word) :
    List (Command Reg Word) :=
  [.readLeft (.reg i.source₁),
   .readRight (.reg i.source₂),
   .localOp (fun r => (i.result r.1 r.2, i.nextPC r.1 r.2)),
   .writeLeft .valueTemp,
   .writeRight (fun _ => .pcTemp),
   .readLeft .snapshot,
   .readRight .valueTemp,
   .writeRight (fun r => if r.1 = tag then .reg i.target else .trash),
   .readRight .pcTemp,
   .writeRight (fun r => if r.1 = tag then .pc else .trash)]

theorem compileInstruction_cost (tag : Word) (i : Instruction Reg Word) :
    transfers (compileInstruction tag i) = 9 := by rfl

theorem compileInstruction_snapshot (tag : Word) (i : Instruction Reg Word)
    (s : State Reg Word) :
    (execute (compileInstruction tag i) s).disk .snapshot = s.disk .snapshot := by
  by_cases h : s.disk .snapshot = tag <;>
    simp [compileInstruction, execute, step, resident, Function.update_apply, h]

theorem compileInstruction_correct (tag : Word) (i : Instruction Reg Word)
    (s : State Reg Word) :
    observe (execute (compileInstruction tag i) s) =
      guarded (s.disk .snapshot) tag i (observe s) := by
  by_cases h : s.disk .snapshot = tag
  · simp [compileInstruction, execute, step, resident, observe, guarded, Function.update_apply, h,
      applyInstruction]
    funext r
    simp [Function.update_apply]
  · simp [compileInstruction, execute, step, resident, observe, guarded, Function.update_apply, h]

abbrev Table (Reg Word : Type*) := List (Word × Instruction Reg Word)

def compileTable : Table Reg Word → List (Command Reg Word)
  | [] => []
  | (tag, i) :: rest => compileInstruction tag i ++ compileTable rest

def tableSemantics (key : Word) : Table Reg Word → Virtual Reg Word → Virtual Reg Word
  | [], v => v
  | (tag, i) :: rest, v => tableSemantics key rest (guarded key tag i v)

theorem compileTable_cost (table : Table Reg Word) :
    transfers (compileTable table) = 9 * table.length := by
  induction table with
  | nil => rfl
  | cons entry rest ih =>
      rcases entry with ⟨tag, i⟩
      simp [compileTable, transfers_append, compileInstruction_cost, ih,
        Nat.mul_add, Nat.add_comm]

theorem compileTable_snapshot (table : Table Reg Word) (s : State Reg Word) :
    (execute (compileTable table) s).disk .snapshot = s.disk .snapshot := by
  induction table generalizing s with
  | nil => rfl
  | cons entry rest ih =>
      rcases entry with ⟨tag, i⟩
      rw [compileTable, execute_append, ih, compileInstruction_snapshot]

theorem compileTable_correct (table : Table Reg Word) (s : State Reg Word) :
    observe (execute (compileTable table) s) =
      tableSemantics (s.disk .snapshot) table (observe s) := by
  induction table generalizing s with
  | nil => rfl
  | cons entry rest ih =>
      rcases entry with ⟨tag, i⟩
      rw [compileTable, execute_append, ih, compileInstruction_snapshot,
        compileInstruction_correct]
      rfl

theorem tableSemantics_append (key : Word) (xs ys : Table Reg Word)
    (v : Virtual Reg Word) :
    tableSemantics key (xs ++ ys) v =
      tableSemantics key ys (tableSemantics key xs v) := by
  induction xs generalizing v with
  | nil => rfl
  | cons x xs ih => exact ih (guarded key x.1 x.2 v)

theorem tableSemantics_disabled (key : Word) (table : Table Reg Word)
    (h : ∀ entry ∈ table, key ≠ entry.1) (v : Virtual Reg Word) :
    tableSemantics key table v = v := by
  induction table generalizing v with
  | nil => rfl
  | cons entry rest ih =>
      have hh : key ≠ entry.1 := h entry (by simp)
      rw [tableSemantics, guarded, if_neg hh]
      exact ih (by intro e he; exact h e (by simp [he])) v

/-- With a unique tag, a table pass executes precisely that instruction;
the rest of the fixed table only performs charged scratch accesses. -/
theorem tableSemantics_selected (key : Word) (i : Instruction Reg Word)
    (before after : Table Reg Word)
    (hb : ∀ e ∈ before, key ≠ e.1) (ha : ∀ e ∈ after, key ≠ e.1)
    (v : Virtual Reg Word) :
    tableSemantics key (before ++ (key, i) :: after) v = applyInstruction i v := by
  rw [tableSemantics_append, tableSemantics_disabled key before hb,
    tableSemantics, guarded, if_pos rfl, tableSemantics_disabled key after ha]

/-- The snapshot is frozen for the entire pass: changing PC at one instruction
does not accidentally enable a later instruction in that same pass. -/
def cycle (table : Table Reg Word) : List (Command Reg Word) :=
  [.readLeft .pc, .writeLeft .snapshot] ++ compileTable table

def virtualStep (table : Table Reg Word) (v : Virtual Reg Word) : Virtual Reg Word :=
  tableSemantics v.pc table v

theorem cycle_cost (table : Table Reg Word) :
    transfers (cycle table) = 2 + 9 * table.length := by
  rw [cycle, transfers_append, compileTable_cost]
  rfl

theorem cycle_correct (table : Table Reg Word) (s : State Reg Word) :
    observe (execute (cycle table) s) = virtualStep table (observe s) := by
  rw [cycle, execute_append, compileTable_correct]
  simp [execute, step, observe, virtualStep, Function.update_apply]

def repeatCode (code : List (Command Reg Word)) : ℕ → List (Command Reg Word)
  | 0 => []
  | n+1 => code ++ repeatCode code n

def virtualRun (table : Table Reg Word) : ℕ → Virtual Reg Word → Virtual Reg Word
  | 0, v => v
  | n+1, v => virtualRun table n (virtualStep table v)

theorem repeated_cost (code : List (Command Reg Word)) (n : ℕ) :
    transfers (repeatCode code n) = n * transfers code := by
  induction n with
  | zero => simp [repeatCode, transfers]
  | succ n ih =>
      rw [repeatCode, transfers_append, ih, Nat.succ_mul, Nat.add_comm]

theorem repeated_correct (table : Table Reg Word) (n : ℕ) (s : State Reg Word) :
    observe (execute (repeatCode (cycle table) n) s) =
      virtualRun table n (observe s) := by
  induction n generalizing s with
  | zero => rfl
  | succ n ih =>
      rw [repeatCode, execute_append, ih, cycle_correct]
      rfl

/-- One program schedule works for every input disk and both initial words.
All value-dependent control is the externally stored virtual PC. -/
theorem simulation (table : Table Reg Word) (n : ℕ) (s : State Reg Word) :
    observe (run (repeatCode (cycle table) n) s).1 = virtualRun table n (observe s) ∧
      (run (repeatCode (cycle table) n) s).2 = n * (2 + 9 * table.length) := by
  exact ⟨repeated_correct table n s, by simp only [run, repeated_cost, cycle_cost]⟩

/-- Specialization fixes the global word size without increasing it. -/
theorem resident_words (w : ℕ) (s : State Reg (Fin (2^w))) :
    ∃ words : Fin 2 → Fin (2^w), words 0 = s.left ∧ words 1 = s.right := by
  exact ⟨fun i => if i = 0 then s.left else s.right, by simp, by simp⟩

end CSL.TwoWordSpill
end Spill

section Indirect
/-!
# Indirect accesses in the two-word fixed-schedule simulator

An indirect address is ONE Word, used as an offset in a fixed data region.
The program's virtual scalar registers form a separate fixed region.  This
does not prove that arbitrary polynomial addresses fit a word, nor change
the global word size.  In particular its use for the M=2,B=1 corner requires
checking the paper's word/address convention explicitly.

Disabled stores read and write back the old data.  They do not retain an
input-dependent address or continuation outside the two resident words.
All indirect reads and writes are actual charged commands.
-/

set_option autoImplicit false
namespace CSL.TwoWordIndirect
open TwoWordSpill

variable {R Region W : Type*} [DecidableEq R] [DecidableEq Region] [DecidableEq W]

abbrev Registers (R Region W : Type*) := Sum R (Region × W)
abbrev Physical (R Region W : Type*) := State (Registers R Region W) W
abbrev Logical (R Region W : Type*) := Virtual (Registers R Region W) W

def loadEffect (region : Region) (pointer destination : R) (next : W) (v : Logical R Region W) : Logical R Region W :=
  ⟨Function.update v.regs (.inl destination)
      (v.regs (.inr (region, v.regs (.inl pointer)))), next⟩

def storeEffect (region : Region) (pointer source : R) (next : W) (v : Logical R Region W) : Logical R Region W :=
  ⟨Function.update v.regs (.inr (region, v.regs (.inl pointer))) (v.regs (.inl source)), next⟩

/-- Three reads (pointer, payload, snapshot), two writes (target, PC). -/
def compileLoad (tag : W) (region : Region) (pointer destination : R) (next : W) :
    List (Command (Registers R Region W) W) :=
  [.readLeft (.reg (.inl pointer)),
   .readRightAt (fun r => .reg (.inr (region, r.1))),
   .readLeft .snapshot,
   .writeRight (fun r => if r.1 = tag then .reg (.inl destination) else .trash),
   .localOp (fun r => (r.1, next)),
   .writeRight (fun r => if r.1 = tag then .pc else .trash)]

theorem compileLoad_cost (tag : W) (region : Region) (pointer destination : R) (next : W) :
    transfers (compileLoad tag region pointer destination next) = 5 := by rfl

theorem compileLoad_snapshot (tag : W) (region : Region) (pointer destination : R) (next : W)
    (s : Physical R Region W) :
    (execute (compileLoad tag region pointer destination next) s).disk .snapshot =
      s.disk .snapshot := by
  by_cases h : s.disk .snapshot = tag <;>
    simp [compileLoad, execute, step, resident, Function.update_apply, h]

theorem compileLoad_correct (tag : W) (region : Region) (pointer destination : R) (next : W)
    (s : Physical R Region W) :
    observe (execute (compileLoad tag region pointer destination next) s) =
      if s.disk .snapshot = tag then loadEffect region pointer destination next (observe s)
      else observe s := by
  by_cases h : s.disk .snapshot = tag
  · simp [compileLoad, execute, step, resident, observe, loadEffect, Function.update_apply, h]
    funext r
    simp [Function.update_apply]
  · simp [compileLoad, execute, step, resident, observe, loadEffect, Function.update_apply, h]

/-- The two masked values occupy opposite branches, so their merge needs
only two words and no retained guard.  No unused pointer/sentinel is needed. -/
def compileStore (zero tag : W) (region : Region) (pointer source : R) (next : W) :
    List (Command (Registers R Region W) W) :=
  [.readLeft (.reg (.inl pointer)),
   .readRightAt (fun r => .reg (.inr (region, r.1))),
   .readLeft .snapshot,
   .localOp (fun r => (r.1, if r.1 = tag then zero else r.2)),
   .writeRight (fun _ => .valueTemp),
   .readRight (.reg (.inl source)),
   .localOp (fun r => (r.1, if r.1 = tag then r.2 else zero)),
   .readLeft .valueTemp,
   .localOp (fun r => (r.1, if r.1 = zero then r.2 else r.1)),
   .readLeft (.reg (.inl pointer)),
   .writeRight (fun r => .reg (.inr (region, r.1))),
   .readLeft .snapshot,
   .localOp (fun r => (r.1, next)),
   .writeRight (fun r => if r.1 = tag then .pc else .trash)]

theorem compileStore_cost (zero tag : W) (region : Region) (pointer source : R) (next : W) :
    transfers (compileStore zero tag region pointer source next) = 10 := by rfl

theorem compileStore_snapshot (zero tag : W) (region : Region) (pointer source : R) (next : W)
    (s : Physical R Region W) :
    (execute (compileStore zero tag region pointer source next) s).disk .snapshot =
      s.disk .snapshot := by
  by_cases h : s.disk .snapshot = tag <;>
    simp [compileStore, execute, step, resident, Function.update_apply, h]

theorem compileStore_correct (zero tag : W) (region : Region) (pointer source : R) (next : W)
    (s : Physical R Region W) :
    observe (execute (compileStore zero tag region pointer source next) s) =
      if s.disk .snapshot = tag then storeEffect region pointer source next (observe s)
      else observe s := by
  by_cases h : s.disk .snapshot = tag
  · simp [compileStore, execute, step, resident, observe, storeEffect, Function.update_apply, h]
    funext r
    simp [Function.update_apply]
  · have hm (x : W) : (if x = zero then zero else x) = x := by
      split <;> simp_all
    simp [compileStore, execute, step, resident, observe, storeEffect, Function.update_apply, h, hm]
    funext r
    split <;> simp_all

inductive Instruction (R Region W : Type*) where
  | arithmetic (i : TwoWordSpill.Instruction (Registers R Region W) W)
  | load (region : Region) (pointer destination : R) (next : W)
  | store (region : Region) (pointer source : R) (next : W)

def effect (i : Instruction R Region W) (v : Logical R Region W) : Logical R Region W :=
  match i with
  | .arithmetic a => applyInstruction a v
  | .load region p dst next => loadEffect region p dst next v
  | .store region p src next => storeEffect region p src next v

def compile (zero tag : W) : Instruction R Region W → List (Command (Registers R Region W) W)
  | .arithmetic a => compileInstruction tag a
  | .load region p dst next => compileLoad tag region p dst next
  | .store region p src next => compileStore zero tag region p src next

def instructionCost : Instruction R Region W → ℕ
  | .arithmetic _ => 9
  | .load _ _ _ _ => 5
  | .store _ _ _ _ => 10

theorem compile_cost (zero tag : W) (i : Instruction R Region W) :
    transfers (compile zero tag i) = instructionCost i := by
  cases i <;> rfl

theorem instructionCost_le (i : Instruction R Region W) : instructionCost i ≤ 10 := by
  cases i <;> simp [instructionCost]

theorem compile_snapshot (zero tag : W) (i : Instruction R Region W) (s : Physical R Region W) :
    (execute (compile zero tag i) s).disk .snapshot = s.disk .snapshot := by
  cases i with
  | arithmetic a => exact compileInstruction_snapshot tag a s
  | load region p dst n => exact compileLoad_snapshot tag region p dst n s
  | store region p src n => exact compileStore_snapshot zero tag region p src n s

theorem compile_correct (zero tag : W) (i : Instruction R Region W) (s : Physical R Region W) :
    observe (execute (compile zero tag i) s) =
      if s.disk .snapshot = tag then effect i (observe s) else observe s := by
  cases i with
  | arithmetic a => exact compileInstruction_correct tag a s
  | load region p dst n => exact compileLoad_correct tag region p dst n s
  | store region p src n => exact compileStore_correct zero tag region p src n s

abbrev Table (R Region W : Type*) := List (W × Instruction R Region W)

def tableCode (zero : W) : Table R Region W → List (Command (Registers R Region W) W)
  | [] => []
  | (tag, i) :: rest => compile zero tag i ++ tableCode zero rest

def tableEffect (key : W) : Table R Region W → Logical R Region W → Logical R Region W
  | [], v => v
  | (tag, i) :: rest, v =>
      tableEffect key rest (if key = tag then effect i v else v)

def tableCost : Table R Region W → ℕ
  | [] => 0
  | (_, i) :: rest => instructionCost i + tableCost rest

theorem tableEffect_append (key : W) (xs ys : Table R Region W)
    (v : Logical R Region W) :
    tableEffect key (xs ++ ys) v = tableEffect key ys (tableEffect key xs v) := by
  induction xs generalizing v with
  | nil => rfl
  | cons x xs ih => exact ih (if key = x.1 then effect x.2 v else v)

theorem tableEffect_disabled (key : W) (table : Table R Region W)
    (h : ∀ entry ∈ table, key ≠ entry.1) (v : Logical R Region W) :
    tableEffect key table v = v := by
  induction table generalizing v with
  | nil => rfl
  | cons entry rest ih =>
      have hh : key ≠ entry.1 := h entry (by simp)
      rw [tableEffect, if_neg hh]
      exact ih (by intro e he; exact h e (by simp [he])) v

theorem tableEffect_selected (key : W) (i : Instruction R Region W)
    (before after : Table R Region W)
    (hb : ∀ e ∈ before, key ≠ e.1) (ha : ∀ e ∈ after, key ≠ e.1)
    (v : Logical R Region W) :
    tableEffect key (before ++ (key, i) :: after) v = effect i v := by
  rw [tableEffect_append, tableEffect_disabled key before hb,
    tableEffect, if_pos rfl, tableEffect_disabled key after ha]

theorem tableCode_cost (zero : W) (table : Table R Region W) :
    transfers (tableCode zero table) = tableCost table := by
  induction table with
  | nil => rfl
  | cons entry rest ih =>
      rcases entry with ⟨tag, i⟩
      rw [tableCode, transfers_append, compile_cost, ih]
      rfl

theorem tableCost_le (table : Table R Region W) : tableCost table ≤ 10 * table.length := by
  induction table with
  | nil => simp [tableCost]
  | cons entry rest ih =>
      have hi := instructionCost_le entry.2
      simp only [tableCost, List.length_cons, Nat.mul_add, Nat.mul_one]
      omega

theorem tableCode_snapshot (zero : W) (table : Table R Region W) (s : Physical R Region W) :
    (execute (tableCode zero table) s).disk .snapshot = s.disk .snapshot := by
  induction table generalizing s with
  | nil => rfl
  | cons entry rest ih =>
      rcases entry with ⟨tag, i⟩
      rw [tableCode, execute_append, ih, compile_snapshot]

theorem tableCode_correct (zero : W) (table : Table R Region W) (s : Physical R Region W) :
    observe (execute (tableCode zero table) s) =
      tableEffect (s.disk .snapshot) table (observe s) := by
  induction table generalizing s with
  | nil => rfl
  | cons entry rest ih =>
      rcases entry with ⟨tag, i⟩
      rw [tableCode, execute_append, ih, compile_snapshot, compile_correct]
      rfl

def cycleCode (zero : W) (table : Table R Region W) : List (Command (Registers R Region W) W) :=
  [.readLeft .pc, .writeLeft .snapshot] ++ tableCode zero table

def logicalStep (table : Table R Region W) (v : Logical R Region W) : Logical R Region W :=
  tableEffect v.pc table v

theorem cycleCode_correct (zero : W) (table : Table R Region W) (s : Physical R Region W) :
    observe (execute (cycleCode zero table) s) = logicalStep table (observe s) := by
  rw [cycleCode, execute_append, tableCode_correct]
  simp [execute, step, observe, logicalStep, Function.update_apply]

theorem cycleCode_cost (zero : W) (table : Table R Region W) :
    transfers (cycleCode zero table) = 2 + tableCost table := by
  rw [cycleCode, transfers_append, tableCode_cost]
  rfl

def logicalRun (table : Table R Region W) : ℕ → Logical R Region W → Logical R Region W
  | 0, v => v
  | n+1, v => logicalRun table n (logicalStep table v)

theorem repeated_correct (zero : W) (table : Table R Region W) (n : ℕ) (s : Physical R Region W) :
    observe (execute (repeatCode (cycleCode zero table) n) s) =
      logicalRun table n (observe s) := by
  induction n generalizing s with
  | zero => rfl
  | succ n ih =>
      rw [repeatCode, execute_append, ih, cycleCode_correct]
      rfl

/-- Every virtual step, including inactive instructions' actual indirect
accesses, has a fixed transfer count independent of the stored input. -/
theorem simulation (zero : W) (table : Table R Region W) (n : ℕ) (s : Physical R Region W) :
    observe (run (repeatCode (cycleCode zero table) n) s).1 =
      logicalRun table n (observe s) ∧
    (run (repeatCode (cycleCode zero table) n) s).2 = n * (2 + tableCost table) ∧
    (run (repeatCode (cycleCode zero table) n) s).2 ≤ n * (2 + 10 * table.length) := by
  refine ⟨repeated_correct zero table n s, ?_, ?_⟩
  · simp only [run, repeated_cost, cycleCode_cost]
  · simp only [run, repeated_cost, cycleCode_cost]
    exact Nat.mul_le_mul_left n (Nat.add_le_add_left (tableCost_le table) 2)

end CSL.TwoWordIndirect
end Indirect

section PhysicalAddresses
/-!
# A single natural-addressed word disk for the two-word simulator

Regions are fixed program fields, never an uncounted dynamic region register.
An indirect offset is the word fetched into the existing left resident cell.
All logical register and scratch cells are assigned distinct natural block
addresses.  This is a physical B=1 simulation; no sorting program or larger
physical-block layout conversion is asserted here.
-/

set_option autoImplicit false
namespace CSL.TwoWordPhysicalAddresses
open TwoWordSpill

variable {Reg W : Type*} [DecidableEq Reg] [DecidableEq W]

structure State (W : Type*) where
  left : W
  right : W
  disk : ℕ → W

inductive Command (W : Type*) where
  | readLeft (a : ℕ)
  | readRight (a : ℕ)
  | readRightAt (a : Resident W → ℕ)
  | writeLeft (a : ℕ)
  | writeRight (a : Resident W → ℕ)
  | localOp (f : Resident W → Resident W)

def step (cmd : Command W) (s : State W) : State W :=
  match cmd with
  | .readLeft a => {s with left := s.disk a}
  | .readRight a => {s with right := s.disk a}
  | .readRightAt a => {s with right := s.disk (a (s.left, s.right))}
  | .writeLeft a => {s with disk := Function.update s.disk a s.left}
  | .writeRight a => {s with disk := Function.update s.disk (a (s.left, s.right)) s.right}
  | .localOp f => {s with left := (f (s.left, s.right)).1, right := (f (s.left, s.right)).2}

def cost : Command W → ℕ
  | .localOp _ => 0
  | _ => 1

def execute : List (Command W) → State W → State W
  | [], s => s
  | c :: rest, s => execute rest (step c s)

def transfers : List (Command W) → ℕ
  | [] => 0
  | c :: rest => cost c + transfers rest

def run (code : List (Command W)) (s : State W) : State W × ℕ :=
  (execute code s, transfers code)

def pullback (address : Address Reg → ℕ) (s : State W) : TwoWordSpill.State Reg W :=
  ⟨s.left, s.right, fun a => s.disk (address a)⟩

def compile (address : Address Reg → ℕ) : TwoWordSpill.Command Reg W → Command W
  | .readLeft a => .readLeft (address a)
  | .readRight a => .readRight (address a)
  | .readRightAt a => .readRightAt (fun r => address (a r))
  | .writeLeft a => .writeLeft (address a)
  | .writeRight a => .writeRight (fun r => address (a r))
  | .localOp f => .localOp f

theorem update_pullback (address : Address Reg → ℕ) (hi : Function.Injective address)
    (disk : ℕ → W) (a : Address Reg) (value : W) :
    (fun b => Function.update disk (address a) value (address b)) =
      Function.update (fun b => disk (address b)) a value := by
  funext b
  by_cases h : b = a
  · subst b; simp
  · have he : address b ≠ address a := fun e => h (hi e)
    simp [Function.update_of_ne, h, he]

/-- Reads fetch exactly the represented address; writes update it, with no
other payload read. This includes the dynamically addressed commands. -/
theorem step_pullback (address : Address Reg → ℕ) (hi : Function.Injective address)
    (cmd : TwoWordSpill.Command Reg W) (s : State W) :
    pullback address (step (compile address cmd) s) =
      TwoWordSpill.step cmd (pullback address s) := by
  cases cmd <;>
    simp [pullback, compile, step, TwoWordSpill.step, resident, update_pullback address hi]

theorem compile_cost (address : Address Reg → ℕ) (cmd : TwoWordSpill.Command Reg W) :
    cost (compile address cmd) = TwoWordSpill.cost cmd := by
  cases cmd <;> rfl

theorem execute_pullback (address : Address Reg → ℕ) (hi : Function.Injective address)
    (code : List (TwoWordSpill.Command Reg W)) (s : State W) :
    pullback address (execute (code.map (compile address)) s) =
      TwoWordSpill.execute code (pullback address s) := by
  induction code generalizing s with
  | nil => rfl
  | cons cmd rest ih =>
      simp only [List.map_cons, execute, TwoWordSpill.execute]
      rw [ih, step_pullback address hi]

theorem transfers_compile (address : Address Reg → ℕ)
    (code : List (TwoWordSpill.Command Reg W)) :
    transfers (code.map (compile address)) = TwoWordSpill.transfers code := by
  induction code with
  | nil => rfl
  | cons cmd rest ih => simp only [List.map_cons, transfers, compile_cost, ih,
      TwoWordSpill.transfers]

theorem step_outside (address : Address Reg → ℕ) (cmd : TwoWordSpill.Command Reg W)
    (s : State W) (a : ℕ) (ha : ∀ b, a ≠ address b) :
    (step (compile address cmd) s).disk a = s.disk a := by
  cases cmd <;> simp [step, compile, Function.update_of_ne, ha]

theorem execute_outside (address : Address Reg → ℕ)
    (code : List (TwoWordSpill.Command Reg W)) (s : State W)
    (a : ℕ) (ha : ∀ b, a ≠ address b) :
    (execute (code.map (compile address)) s).disk a = s.disk a := by
  induction code generalizing s with
  | nil => rfl
  | cons cmd rest ih =>
      simp only [List.map_cons, execute]
      rw [ih, step_outside address cmd s a ha]

abbrev Register (r regions w : ℕ) := Fin r ⊕ (Fin regions × Fin (2^w))

def registerNumber (r regions w : ℕ) : Register r regions w ≃ Fin (r + regions * 2^w) :=
  (Equiv.sumCongr (Equiv.refl (Fin r)) finProdFinEquiv).trans finSumFinEquiv

/-- Virtual registers, each complete word-indexed region, and five fixed
control/scratch cells occupy pairwise disjoint contiguous address ranges. -/
def addressNumber (r regions w : ℕ) : Address (Register r regions w) → ℕ
  | .reg a => (registerNumber r regions w a).val
  | .pc => r + regions * 2^w
  | .snapshot => r + regions * 2^w + 1
  | .valueTemp => r + regions * 2^w + 2
  | .pcTemp => r + regions * 2^w + 3
  | .trash => r + regions * 2^w + 4

theorem addressNumber_bound (r regions w : ℕ) (a : Address (Register r regions w)) :
    addressNumber r regions w a < r + regions * 2^w + 5 := by
  cases a with
  | reg a => have h := (registerNumber r regions w a).isLt; simp [addressNumber]; omega
  | pc => simp [addressNumber]
  | snapshot => simp [addressNumber]
  | valueTemp => simp [addressNumber]
  | pcTemp => simp [addressNumber]
  | trash => simp [addressNumber]

theorem addressNumber_injective (r regions w : ℕ) :
    Function.Injective (addressNumber r regions w) := by
  intro a b h
  cases a <;> cases b <;> simp only [addressNumber] at h
  all_goals first
    | rfl
    | exact congrArg Address.reg ((registerNumber r regions w).injective (Fin.ext h))
    | (have hbound := (registerNumber r regions w ‹Register r regions w›).isLt; omega)
    | omega

theorem data_address (r regions w : ℕ) (region : Fin regions) (offset : Fin (2^w)) :
    addressNumber r regions w (.reg (.inr (region, offset))) =
      r + region.val * 2^w + offset.val := by
  simp [addressNumber, registerNumber, Nat.add_assoc, Nat.add_comm, Nat.mul_comm]
  omega

def physicalCode (r regions w : ℕ)
    (table : TwoWordIndirect.Table (Fin r) (Fin regions) (Fin (2^w))) (steps : ℕ) :
    List (Command (Fin (2^w))) :=
  (repeatCode (TwoWordIndirect.cycleCode 0 table) steps).map
    (compile (addressNumber r regions w))

/-- The same disk execution realizes all arithmetic and indirect virtual
steps, with the exact charged transfer count, in the original word size. -/
theorem physical_simulation (r regions w : ℕ)
    (table : TwoWordIndirect.Table (Fin r) (Fin regions) (Fin (2^w))) (steps : ℕ)
    (s : State (Fin (2^w))) :
    observe (pullback (addressNumber r regions w)
      (run (physicalCode r regions w table steps) s).1) =
        TwoWordIndirect.logicalRun table steps
          (observe (pullback (addressNumber r regions w) s)) ∧
    (run (physicalCode r regions w table steps) s).2 =
      steps * (2 + TwoWordIndirect.tableCost table) ∧
    (run (physicalCode r regions w table steps) s).2 ≤
      steps * (2 + 10 * table.length) := by
  have h := TwoWordIndirect.simulation (0 : Fin (2^w)) table steps
    (pullback (addressNumber r regions w) s)
  simpa only [run, physicalCode, execute_pullback _ (addressNumber_injective r regions w),
    transfers_compile, TwoWordSpill.run] using h

/-- Quantifier order is explicit: the schedule is chosen before any input
disk or initial resident values. The public horizon is not read from input. -/
theorem one_schedule_all_inputs (r regions w : ℕ)
    (table : TwoWordIndirect.Table (Fin r) (Fin regions) (Fin (2^w))) (steps : ℕ) :
    ∃ code : List (Command (Fin (2^w))), ∀ s : State (Fin (2^w)),
      observe (pullback (addressNumber r regions w) (run code s).1) =
        TwoWordIndirect.logicalRun table steps
          (observe (pullback (addressNumber r regions w) s)) ∧
      (run code s).2 = steps * (2 + TwoWordIndirect.tableCost table) ∧
      (run code s).2 ≤ steps * (2 + 10 * table.length) := by
  exact ⟨physicalCode r regions w table steps, physical_simulation r regions w table steps⟩

/-- No location outside the single allocated disk interval is modified. -/
theorem physical_outside (r regions w : ℕ)
    (table : TwoWordIndirect.Table (Fin r) (Fin regions) (Fin (2^w))) (steps : ℕ)
    (s : State (Fin (2^w))) (a : ℕ) (ha : r + regions * 2^w + 5 ≤ a) :
    (run (physicalCode r regions w table steps) s).1.disk a = s.disk a := by
  apply execute_outside
  intro b hb
  have hbound := addressNumber_bound r regions w b
  omega

end CSL.TwoWordPhysicalAddresses
end PhysicalAddresses


