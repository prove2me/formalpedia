-- Prove2me | Definitions.Def_CSL_Sorting_SmallMemory_Radix_Initialize
-- name    : CSL_Sorting_SmallMemory_Radix_Initialize
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-24T13:56:03.948114+00:00
-- url     : https://prove2.me/theorems/01680b7b-23b2-46f9-bc09-55acc70fe0aa
-- title:
--   Coded sorting library: Sorting / SmallMemory / Radix / Initialize
-- statement:
--   Module `CodedSorting.Sorting.SmallMemory.Radix.Initialize` of the Lean development accompanying B. Li, Z. Li, S. Liu, *Undirected Multiple-Unicast Network Coding and Faster External-Memory Integer Sorting*, arXiv:2610.20079, ported to Lean v4.33.1 and Mathlib `0df444a` (namespace `CodedSorting` renamed to `CSL`).
--
--   # Actual directory initialization
--
--   The fixed four-instruction program clears two designated disk regions in
--   one backward scan.  It sets its own zero register, never assumes fresh disk
--   contents, and stores cursor/PC externally.  All physical accesses use the
--   already stated atomic effective-address model, with two resident data words.
--
--   This module is part of the machine-checked proof of Theorem 3.1 (external-memory integer sorting) and is imported by the later modules of that development.
-- source:
--   B. Li, Z. Li, S. Liu, *Undirected Multiple-Unicast Network Coding and Faster External-Memory Integer Sorting*, arXiv:2610.20079 (Theorem 3.1, p.4, and Appendix D); Lean development https://github.com/rtyu-1/coded-sorting-lean, module CodedSorting.Sorting.SmallMemory.Radix.Initialize

import Definitions.Def_CSL_Compat
import Definitions.Def_CSL_Sorting_SmallMemory_Radix_Build

section Initialize
/-!
# Actual directory initialization

The fixed four-instruction program clears two designated disk regions in
one backward scan.  It sets its own zero register, never assumes fresh disk
contents, and stores cursor/PC externally.  All physical accesses use the
already stated atomic effective-address model, with two resident data words.
-/

set_option autoImplicit false
namespace CSL.TwoWordRadixInitialize
open TwoWordSpill TwoWordIndirect TwoWordUniformLoop TwoWordRadixInsert

def zeroRegister {w : ℕ} (hcap : 11 ≤ 2^w) :
    TwoWordIndirect.Instruction (Fin 5) (Fin 5) (Word w) :=
  arithmetic 0 3 (fun _ => label hcap 0) (label hcap 1)

def decrement {w : ℕ} (hcap : 11 ≤ 2^w) :
    TwoWordIndirect.Instruction (Fin 5) (Fin 5) (Word w) :=
  .arithmetic ⟨.inl 0,.inl 0,.inl 0,fun x _ => TwoWordRadixBuild.predecessor x,
    fun x _ => if x.val = 0 then label hcap 4 else label hcap 1⟩

def table {w : ℕ} (hcap : 11 ≤ 2^w) (a b : Fin 5) :
    TwoWordIndirect.Table (Fin 5) (Fin 5) (Word w) :=
  [(label hcap 0, zeroRegister hcap),
   (label hcap 1, .store a 0 3 (label hcap 2)),
   (label hcap 2, .store b 0 3 (label hcap 3)),
   (label hcap 3, decrement hcap)]

def clearOne {w : ℕ} (hcap : 11 ≤ 2^w) (a b : Fin 5) (v : Logical w) : Logical w :=
  effect (decrement hcap)
    (storeEffect b 0 3 (label hcap 3) (storeEffect a 0 3 (label hcap 2) v))

theorem step_zero {w : ℕ} (hcap : 11 ≤ 2^w) (a b : Fin 5) (v : Logical w)
    (hp : v.pc = label hcap 0) :
    logicalStep (table hcap a b) v = effect (zeroRegister hcap) v := by
  simp [logicalStep, table, tableEffect, hp]

theorem step_one {w : ℕ} (hcap : 11 ≤ 2^w) (a b : Fin 5) (v : Logical w)
    (hp : v.pc = label hcap 1) :
    logicalStep (table hcap a b) v = storeEffect a 0 3 (label hcap 2) v := by
  simp [logicalStep, table, tableEffect, hp, effect]

theorem step_two {w : ℕ} (hcap : 11 ≤ 2^w) (a b : Fin 5) (v : Logical w)
    (hp : v.pc = label hcap 2) :
    logicalStep (table hcap a b) v = storeEffect b 0 3 (label hcap 3) v := by
  simp [logicalStep, table, tableEffect, hp, effect]

theorem step_three {w : ℕ} (hcap : 11 ≤ 2^w) (a b : Fin 5) (v : Logical w)
    (hp : v.pc = label hcap 3) :
    logicalStep (table hcap a b) v = effect (decrement hcap) v := by
  simp [logicalStep, table, tableEffect, hp]

theorem clearOne_cursor {w : ℕ} (hcap : 11 ≤ 2^w) (a b : Fin 5) (v : Logical w) :
    (clearOne hcap a b v).regs (.inl 0) = TwoWordRadixBuild.predecessor (v.regs (.inl 0)) := by
  simp [clearOne, decrement, effect, applyInstruction, storeEffect]

theorem clearOne_pc {w : ℕ} (hcap : 11 ≤ 2^w) (a b : Fin 5) (v : Logical w) :
    (clearOne hcap a b v).pc =
      if (v.regs (.inl 0)).val = 0 then label hcap 4 else label hcap 1 := by
  simp [clearOne, decrement, effect, applyInstruction, storeEffect]

theorem clearOne_zero {w : ℕ} (hcap : 11 ≤ 2^w) (a b : Fin 5) (v : Logical w) :
    (clearOne hcap a b v).regs (.inl 3) = v.regs (.inl 3) := by
  simp [clearOne, decrement, effect, applyInstruction, storeEffect]

theorem clearOne_data {w : ℕ} (hcap : 11 ≤ 2^w) (a b : Fin 5) (v : Logical w)
    (region : Fin 5) (x : Word w) :
    (clearOne hcap a b v).regs (.inr (region,x)) =
      if (region = a ∨ region = b) ∧ x = v.regs (.inl 0) then v.regs (.inl 3)
      else v.regs (.inr (region,x)) := by
  simp only [clearOne, decrement, effect, applyInstruction, storeEffect]
  by_cases ha : region = a <;> by_cases hb : region = b <;>
    by_cases hx : x = v.regs (.inl 0) <;>
    simp [Function.update_apply, ha, hb, hx]

theorem prepend_three {w : ℕ} (hcap : 11 ≤ 2^w) (a b : Fin 5) (v final : Logical w)
    (steps : ℕ) (hp : v.pc = label hcap 1)
    (hr : HaltsAfter (table hcap a b) (label hcap 4) steps (clearOne hcap a b v) final) :
    HaltsAfter (table hcap a b) (label hcap 4) (steps+3) v final := by
  have h1 : v.pc ≠ label hcap 4 := by rw [hp]; simp
  have h2 : (storeEffect a 0 3 (label hcap 2) v).pc = label hcap 2 := rfl
  have h3 : (storeEffect b 0 3 (label hcap 3) (storeEffect a 0 3 (label hcap 2) v)).pc =
      label hcap 3 := rfl
  change v.pc ≠ _ ∧ _
  refine ⟨h1, ?_⟩
  rw [step_one hcap a b v hp]
  refine ⟨by rw [h2]; simp, ?_⟩
  rw [step_two hcap a b _ h2]
  refine ⟨by rw [h3]; simp, ?_⟩
  rw [step_three hcap a b _ h3]
  exact hr

theorem clear_loop {w : ℕ} (hcap : 11 ≤ 2^w) (a b : Fin 5)
    (count : ℕ) (v : Logical w) (hp : v.pc = label hcap 1)
    (hc : (v.regs (.inl 0)).val = count) (hz : v.regs (.inl 3) = label hcap 0) :
    ∃ final, HaltsAfter (table hcap a b) (label hcap 4) (3*(count+1)) v final ∧
      ∀ (region : Fin 5) (x : Word w), final.regs (.inr (region,x)) =
        if (region = a ∨ region = b) ∧ x.val ≤ count then label hcap 0
        else v.regs (.inr (region,x)) := by
  induction count generalizing v with
  | zero =>
      let final := clearOne hcap a b v
      have hstop : HaltsAfter (table hcap a b) (label hcap 4) 0 final final := by
        exact ⟨by rw [clearOne_pc, hc]; rfl, rfl⟩
      refine ⟨final, prepend_three hcap a b v final 0 hp hstop, ?_⟩
      intro region x
      rw [clearOne_data, hz]
      have hx : x = v.regs (.inl 0) ↔ x.val ≤ 0 := by
        rw [Fin.ext_iff, hc]
        omega
      simp only [hx]
  | succ count ih =>
      let next := clearOne hcap a b v
      have hpc : next.pc = label hcap 1 := by rw [clearOne_pc, hc]; simp
      have hcur : (next.regs (.inl 0)).val = count := by
        rw [clearOne_cursor]
        simp [TwoWordRadixBuild.predecessor, hc]
      have hzero : next.regs (.inl 3) = label hcap 0 := (clearOne_zero _ _ _ _).trans hz
      obtain ⟨final, hrun, hdata⟩ := ih next hpc hcur hzero
      refine ⟨final, ?_, ?_⟩
      · convert prepend_three hcap a b v final (3*(count+1)) hp hrun using 1 <;> omega
      · intro region x
        rw [hdata, clearOne_data, hz]
        have hx : x = v.regs (.inl 0) ↔ x.val = count+1 := by rw [Fin.ext_iff, hc]
        simp only [hx]
        by_cases hr : region = a ∨ region = b
        · by_cases hl : x.val ≤ count
          · simp [hr, hl, show x.val ≤ count+1 by omega]
          · by_cases he : x.val = count+1
            · simp [hr, hl, he]
            · simp [hr, hl, he, show ¬x.val ≤ count+1 by omega]
        · simp [hr]

theorem initialize_loop {w : ℕ} (hcap : 11 ≤ 2^w) (a b : Fin 5)
    (count : ℕ) (v : Logical w) (hp : v.pc = label hcap 0)
    (hc : (v.regs (.inl 0)).val = count) :
    ∃ final, HaltsAfter (table hcap a b) (label hcap 4) (3*(count+1)+1) v final ∧
      ∀ (region : Fin 5) (x : Word w), final.regs (.inr (region,x)) =
        if (region = a ∨ region = b) ∧ x.val ≤ count then label hcap 0
        else v.regs (.inr (region,x)) := by
  let first := effect (zeroRegister hcap) v
  have hpc : first.pc = label hcap 1 := rfl
  have hcur : (first.regs (.inl 0)).val = count := by
    simpa [first, zeroRegister, arithmetic, effect, applyInstruction] using hc
  have hz : first.regs (.inl 3) = label hcap 0 := by
    simp [first, zeroRegister, arithmetic, effect, applyInstruction]
  obtain ⟨final, hrun, hdata⟩ := clear_loop hcap a b count first hpc hcur hz
  refine ⟨final, ?_, ?_⟩
  · refine ⟨by rw [hp]; simp, ?_⟩
    rw [step_zero hcap a b v hp]
    exact hrun
  · intro region x
    simpa [first, zeroRegister, arithmetic, effect, applyInstruction] using hdata region x

theorem table_cost {w : ℕ} (hcap : 11 ≤ 2^w) (a b : Fin 5) :
    tableCost (table hcap a b) = 38 := by
  rfl

theorem physical_initialize {w : ℕ} (hcap : 11 ≤ 2^w) (a b : Fin 5)
    (count : ℕ) (s : TwoWordPhysicalAddresses.State (Word w))
    (hp : (view 5 5 w s).pc = label hcap 0)
    (hc : ((view 5 5 w s).regs (.inl 0)).val = count) :
    ∃ t, Physical.Executes (program 5 5 w (table hcap a b) (label hcap 4)) s t
      (120*(count+1)+41) ∧
      ∀ (region : Fin 5) (x : Word w), (view 5 5 w t).regs (.inr (region,x)) =
        if (region = a ∨ region = b) ∧ x.val ≤ count then label hcap 0
        else (view 5 5 w s).regs (.inr (region,x)) := by
  obtain ⟨final, hrun, hdata⟩ := initialize_loop hcap a b count (view 5 5 w s) hp hc
  obtain ⟨t, ht, hv⟩ := terminates_of_source 5 5 w (table hcap a b) (label hcap 4) _ s final hrun
  refine ⟨t, ?_, ?_⟩
  · convert ht using 1 <;> rw [table_cost] <;> omega
  · rw [hv]; exact hdata

end CSL.TwoWordRadixInitialize
end Initialize

section PreparedBuild
/-!
# A prepared linked-directory build from arbitrary scratch contents

This concrete six-stage program initializes the head and next-pointer
regions, then performs the actual backward build. All resets of the external
cursor and PC are charged writes. The stage list has fixed length; each
data-dependent loop uses the previously proved physical read-PC semantics.
This remains the B=1, two-resident-word, atomic-effective-address model.
-/

set_option autoImplicit false
namespace CSL.TwoWordRadixPreparedBuild
open TwoWordSpill TwoWordUniformLoop TwoWordRadixInsert

inductive Stage (W : Type*) where
  | straight (code : List (TwoWordPhysicalAddresses.Command W))
  | loop (program : Physical.Program W)

/-- A finite sequence of straight-line code and true while-programs.
No stage is selected as an uncounted function of the input. -/
inductive Executes {W : Type*} [DecidableEq W] :
    List (Stage W) → TwoWordPhysicalAddresses.State W → TwoWordPhysicalAddresses.State W → ℕ → Prop where
  | done (s : TwoWordPhysicalAddresses.State W) : Executes [] s s 0
  | straight (code : List (TwoWordPhysicalAddresses.Command W)) (rest : List (Stage W))
      (s t : TwoWordPhysicalAddresses.State W) (cost : ℕ)
      (tail : Executes rest (TwoWordPhysicalAddresses.execute code s) t cost) :
      Executes (.straight code :: rest) s t (TwoWordPhysicalAddresses.transfers code + cost)
  | loop (p : Physical.Program W) (rest : List (Stage W))
      (s mid t : TwoWordPhysicalAddresses.State W) (firstCost restCost : ℕ)
      (first : Physical.Executes p s mid firstCost)
      (tail : Executes rest mid t restCost) :
      Executes (.loop p :: rest) s t (firstCost + restCost)

def setupAbstract {w : ℕ} (hcap : 11 ≤ 2^w) (cursor : Word w) :
    List (TwoWordSpill.Command (TwoWordPhysicalAddresses.Register 5 5 w) (Word w)) :=
  [.localOp (fun _ => (cursor,label hcap 0)),
   .writeLeft (.reg (.inl 0)), .writeRight (fun _ => .pc)]

def setup {w : ℕ} (hcap : 11 ≤ 2^w) (cursor : Word w) :
    List (TwoWordPhysicalAddresses.Command (Word w)) :=
  (setupAbstract hcap cursor).map (TwoWordPhysicalAddresses.compile (TwoWordPhysicalAddresses.addressNumber 5 5 w))

def setCursor {w : ℕ} (hcap : 11 ≤ 2^w) (cursor : Word w)
    (s : TwoWordPhysicalAddresses.State (Word w)) : TwoWordPhysicalAddresses.State (Word w) := TwoWordPhysicalAddresses.execute (setup hcap cursor) s

theorem setup_cost {w : ℕ} (hcap : 11 ≤ 2^w) (cursor : Word w) :
    TwoWordPhysicalAddresses.transfers (setup hcap cursor) = 2 := by
  rw [setup, TwoWordPhysicalAddresses.transfers_compile]; rfl

theorem setup_view {w : ℕ} (hcap : 11 ≤ 2^w) (cursor : Word w)
    (s : TwoWordPhysicalAddresses.State (Word w)) :
    view 5 5 w (setCursor hcap cursor s) =
      ⟨Function.update (view 5 5 w s).regs (.inl 0) cursor, label hcap 0⟩ := by
  unfold view setCursor setup
  rw [TwoWordPhysicalAddresses.execute_pullback _ (TwoWordPhysicalAddresses.addressNumber_injective 5 5 w)]
  simp [setupAbstract, TwoWordSpill.execute, TwoWordSpill.step, observe, resident]
  funext r
  simp [Function.update_apply]

@[simp] theorem setup_pc {w : ℕ} (hcap : 11 ≤ 2^w) (cursor : Word w)
    (s : TwoWordPhysicalAddresses.State (Word w)) :
    (view 5 5 w (setCursor hcap cursor s)).pc = label hcap 0 := by rw [setup_view]

@[simp] theorem setup_cursor {w : ℕ} (hcap : 11 ≤ 2^w) (cursor : Word w)
    (s : TwoWordPhysicalAddresses.State (Word w)) :
    (view 5 5 w (setCursor hcap cursor s)).regs (.inl 0) = cursor := by
  rw [setup_view]; simp

@[simp] theorem setup_data {w : ℕ} (hcap : 11 ≤ 2^w) (cursor : Word w)
    (s : TwoWordPhysicalAddresses.State (Word w)) (region : Fin 5) (x : Word w) :
    (view 5 5 w (setCursor hcap cursor s)).regs (.inr (region,x)) =
      (view 5 5 w s).regs (.inr (region,x)) := by rw [setup_view]; simp

def code {w : ℕ} (hcap : 12 ≤ 2^w) (headLast inputLast : Word w)
    (key : Word w → Word w) : List (Stage (Word w)) :=
  [.straight (setup (TwoWordRadixBuild.smallCap hcap) headLast),
   .loop (program 5 5 w (TwoWordRadixInitialize.table (TwoWordRadixBuild.smallCap hcap) 1 2) (label (TwoWordRadixBuild.smallCap hcap) 4)),
   .straight (setup (TwoWordRadixBuild.smallCap hcap) inputLast),
   .loop (program 5 5 w (TwoWordRadixInitialize.table (TwoWordRadixBuild.smallCap hcap) 3 4) (label (TwoWordRadixBuild.smallCap hcap) 4)),
   .straight (setup (TwoWordRadixBuild.smallCap hcap) inputLast),
   .loop (program 5 5 w (TwoWordRadixBuild.table hcap key) (TwoWordRadixBuild.halt hcap))]

/-- Starting from the input array, the program initializes its temporary storage and virtual registers and constructs the DirectRadix heap. 

-/
theorem physical_prepared_build {w n K : ℕ} (hcap : 12 ≤ 2^w)
    (hN : n ≤ 2^w) (hK : K ≤ 2^w) (hn : 0 < n) (hk : 0 < K)
    (input : Fin n → Word w) (key : Word w → Fin K)
    (s : TwoWordPhysicalAddresses.State (Word w))
    (hin : ∀ j, (view 5 5 w s).regs (.inr (0,position hN j)) = input j) :
    ∃ t, Executes
      (code hcap (position hK ⟨K-1, by omega⟩) (position hN ⟨n-1, by omega⟩)
        (fun x => position hK (key x))) s t (1143*n+120*K+89) ∧
      Represents (TwoWordRadixBuild.smallCap hcap) hN hK
        (DirectRadix.build (fun j => key (input j)) (List.finRange n)) (view 5 5 w t) ∧
      (∀ j, (view 5 5 w t).regs (.inr (0,position hN j)) = input j) := by
  let cap := TwoWordRadixBuild.smallCap hcap
  let klast : Word w := position hK ⟨K-1, by omega⟩
  let nlast : Word w := position hN ⟨n-1, by omega⟩
  let s0 := setCursor cap klast s
  obtain ⟨s1, hr1, hd1⟩ := TwoWordRadixInitialize.physical_initialize cap 1 2 (K-1) s0
    (setup_pc cap klast s) (by simp [s0, klast, position])
  let s2 := setCursor cap nlast s1
  obtain ⟨s3, hr3, hd3⟩ := TwoWordRadixInitialize.physical_initialize cap 3 4 (n-1) s2
    (setup_pc cap nlast s1) (by simp [s2, nlast, position])
  let s4 := setCursor cap nlast s3
  have hdata : ∀ (region : Fin 5) (x : Word w),
      (view 5 5 w s4).regs (.inr (region,x)) =
        if (region=3 ∨ region=4) ∧ x.val ≤ n-1 then label cap 0
        else if (region=1 ∨ region=2) ∧ x.val ≤ K-1 then label cap 0
        else (view 5 5 w s).regs (.inr (region,x)) := by
    intro region x
    rw [show (view 5 5 w s4).regs (.inr (region,x)) =
      (view 5 5 w s3).regs (.inr (region,x)) from setup_data cap nlast s3 region x]
    rw [hd3]
    simp only [s2, setup_data]
    rw [hd1]
    simp only [s0, setup_data]
  have hrep : Represents cap hN hK DirectRadix.Heap.empty (view 5 5 w s4) := by
    constructor
    · intro k
      have hx : (position hK k).val ≤ K-1 := by change k.val ≤ K-1; omega
      rw [hdata]
      simp [hx, DirectRadix.Heap.empty, pointerValue]
    · intro k
      have hx : (position hK k).val ≤ K-1 := by change k.val ≤ K-1; omega
      rw [hdata]
      simp [hx, DirectRadix.Heap.empty, pointerValid]
    · intro i
      have hx : (position hN i).val ≤ n-1 := by change i.val ≤ n-1; omega
      rw [hdata]
      simp [hx, DirectRadix.Heap.empty, pointerValue]
    · intro i
      have hx : (position hN i).val ≤ n-1 := by change i.val ≤ n-1; omega
      rw [hdata]
      simp [hx, DirectRadix.Heap.empty, pointerValid]
  have hi4 : ∀ j, (view 5 5 w s4).regs (.inr (0,position hN j)) = input j := by
    intro j; rw [hdata]; simpa using hin j
  obtain ⟨t, hr5, hrep5, hi5⟩ := TwoWordRadixBuild.physical_build hcap hN hK hn input key s4 hrep hi4
    (setup_cursor cap nlast s3) (setup_pc cap nlast s3)
  refine ⟨t, ?_, hrep5, hi5⟩
  have hrun := Executes.straight (setup cap klast) _ s t _
    (Executes.loop _ _ s0 s1 t _ _ hr1
      (Executes.straight (setup cap nlast) _ s1 t _
        (Executes.loop _ _ s2 s3 t _ _ hr3
          (Executes.straight (setup cap nlast) _ s3 t _
            (Executes.loop _ [] s4 t t _ 0 hr5 (Executes.done t))))))
  convert hrun using 1
  all_goals first | rfl | (simp only [setup_cost]; omega)

end CSL.TwoWordRadixPreparedBuild
end PreparedBuild

section Gather
/-! A fixed nine-instruction directory traversal.  Region 5 is the output
array; the five scalar registers are bucket, pointer, valid, record, output
cursor.  All registers and the program counter are external. -/

set_option autoImplicit false
namespace CSL.TwoWordRadixGather
open TwoWordSpill TwoWordIndirect TwoWordUniformLoop TwoWordRadixInsert

abbrev State (w : ℕ) := TwoWordIndirect.Logical (Fin 5) (Fin 6) (Word w)

def word {w : ℕ} (i : ℕ) : Word w := ⟨i % 2^w, Nat.mod_lt _ (by positivity)⟩
def increment {w : ℕ} (x : Word w) : Word w := word (x.val+1)

theorem increment_word {w : ℕ} (i : ℕ) : increment (word (w:=w) i) = word (i+1) := by
  apply Fin.ext
  simp [increment,word,Nat.add_mod]

def arithmetic {w : ℕ} (source target : Fin 5) (f : Word w → Word w)
    (next : Word w → Word w) : TwoWordIndirect.Instruction (Fin 5) (Fin 6) (Word w) :=
  .arithmetic ⟨.inl source,.inl source,.inl target,fun x _ => f x,fun x _ => next x⟩

def instruction {w : ℕ} (hcap : 11 ≤ 2^w) (last : Word w) (j : Fin 9) :
    TwoWordIndirect.Instruction (Fin 5) (Fin 6) (Word w) :=
  match j.val with
  | 0 => .load 1 0 1 (label hcap 1)
  | 1 => .load 2 0 2 (label hcap 2)
  | 2 => arithmetic 2 2 id (fun x => if x=label hcap 0 then label hcap 8 else label hcap 3)
  | 3 => .load 0 1 3 (label hcap 4)
  | 4 => .store 5 4 3 (label hcap 5)
  | 5 => arithmetic 4 4 increment (fun _ => label hcap 6)
  | 6 => .load 4 1 2 (label hcap 7)
  | 7 => .load 3 1 1 (label hcap 2)
  | _ => arithmetic 0 0 increment (fun x => if x=last then label hcap 9 else label hcap 0)

def table {w : ℕ} (hcap : 11 ≤ 2^w) (last : Word w) :
    TwoWordIndirect.Table (Fin 5) (Fin 6) (Word w) :=
  (List.finRange 9).map (fun j => (label hcap (j.castLE (by decide)),instruction hcap last j))

theorem step_at {w : ℕ} (hcap : 11 ≤ 2^w) (last : Word w)
    (j : Fin 9) (v : State w) (hp : v.pc = label hcap (j.castLE (by decide))) :
    logicalStep (table hcap last) v = effect (instruction hcap last j) v := by
  unfold logicalStep
  rw [hp]
  apply selected_of_mem
  · exact List.mem_map.mpr ⟨j,List.mem_finRange j,rfl⟩
  · simp only [table,List.map_map,Function.comp_apply]
    exact (List.nodup_finRange 9).map (fun a b h =>
      Fin.ext (congrArg (fun x : Fin 11 => x.val) ((label_injective hcap) h)))

theorem table_cost {w : ℕ} (hcap : 11 ≤ 2^w) (last : Word w) :
    tableCost (table hcap last) = 62 := by
  simp [table,List.finRange_succ,List.map_append,tableCost,instruction,arithmetic,instructionCost]

/-- A finite actual source execution prefix, with no premature halt. -/
def Runs {w : ℕ} (hcap : 11 ≤ 2^w) (last : Word w) : ℕ → State w → State w → Prop
  | 0,v,t => t=v
  | steps+1,v,t => v.pc ≠ label hcap 9 ∧ Runs hcap last steps (logicalStep (table hcap last) v) t

theorem Runs.trans {w : ℕ} {hcap : 11 ≤ 2^w} {last : Word w}
    {a b : ℕ} {v mid t : State w} (ha : Runs hcap last a v mid) (hb : Runs hcap last b mid t) :
    Runs hcap last (a+b) v t := by
  induction a generalizing v with
  | zero => obtain rfl := ha; simpa using hb
  | succ a ih => first
    | exact And.intro ha.1 (ih ha.2)
    | (have h_sx := And.intro ha.1 (ih ha.2); simp only [Nat.succ_add] at h_sx ⊢; exact h_sx)
    | (have h_sx := And.intro ha.1 (ih ha.2); simp only [Nat.succ_add] at h_sx; exact h_sx)
    | (simp only [Nat.succ_add]; exact And.intro ha.1 (ih ha.2))

theorem Runs.halts {w : ℕ} {hcap : 11 ≤ 2^w} {last : Word w}
    {steps : ℕ} {v t : State w} (h : Runs hcap last steps v t) (hp : t.pc=label hcap 9) :
    HaltsAfter (table hcap last) (label hcap 9) steps v t := by
  induction steps generalizing v with
  | zero => obtain rfl := h; exact ⟨hp,rfl⟩
  | succ steps ih => exact ⟨h.1,ih h.2⟩

def body {w : ℕ} (hcap : 11 ≤ 2^w) (last : Word w) (v : State w) : State w :=
  ([2,3,4,5,6,7] : List (Fin 9)).foldl (fun s j => effect (instruction hcap last j) s) v

def header {w : ℕ} (hcap : 11 ≤ 2^w) (last : Word w) (v : State w) : State w :=
  effect (instruction hcap last 1) (effect (instruction hcap last 0) v)

def finish {w : ℕ} (hcap : 11 ≤ 2^w) (last : Word w) (v : State w) : State w :=
  effect (instruction hcap last 2) v

def advance {w : ℕ} (hcap : 11 ≤ 2^w) (last : Word w) (v : State w) : State w :=
  effect (instruction hcap last 8) v

theorem body_runs {w : ℕ} (hcap : 11 ≤ 2^w) (last : Word w) (v : State w)
    (hp : v.pc=label hcap 2) (hv : v.regs (.inl 2) ≠ label hcap 0) :
    Runs hcap last 6 v (body hcap last v) := by
  let s1 := effect (instruction hcap last 2) v
  have p1 : s1.pc=label hcap 3 := by simp [s1,instruction,arithmetic,effect,applyInstruction,hv]
  let s2 := effect (instruction hcap last 3) s1
  have p2 : s2.pc=label hcap 4 := rfl
  let s3 := effect (instruction hcap last 4) s2
  have p3 : s3.pc=label hcap 5 := rfl
  let s4 := effect (instruction hcap last 5) s3
  have p4 : s4.pc=label hcap 6 := rfl
  let s5 := effect (instruction hcap last 6) s4
  have p5 : s5.pc=label hcap 7 := rfl
  simp only [Runs]
  rw [step_at hcap last 2 v hp,step_at hcap last 3 s1 p1,step_at hcap last 4 s2 p2,
    step_at hcap last 5 s3 p3,step_at hcap last 6 s4 p4,step_at hcap last 7 s5 p5]
  exact ⟨by rw [hp]; simp,by rw [p1]; simp,by rw [p2]; simp,
    by rw [p3]; simp,by rw [p4]; simp,by rw [p5]; simp,rfl⟩

theorem header_runs {w : ℕ} (hcap : 11 ≤ 2^w) (last : Word w) (v : State w)
    (hp : v.pc=label hcap 0) : Runs hcap last 2 v (header hcap last v) := by
  refine ⟨by rw [hp]; simp,?_⟩
  rw [step_at hcap last 0 v hp]
  refine ⟨by simp [instruction,effect,loadEffect],?_⟩
  rw [step_at hcap last 1 _ rfl]
  rfl

theorem finish_runs {w : ℕ} (hcap : 11 ≤ 2^w) (last : Word w) (v : State w)
    (hp : v.pc=label hcap 2) : Runs hcap last 1 v (finish hcap last v) := by
  exact ⟨by rw [hp]; simp,by rw [step_at hcap last 2 v hp]; rfl⟩

theorem advance_runs {w : ℕ} (hcap : 11 ≤ 2^w) (last : Word w) (v : State w)
    (hp : v.pc=label hcap 8) : Runs hcap last 1 v (advance hcap last v) := by
  exact ⟨by rw [hp]; simp,by rw [step_at hcap last 8 v hp]; rfl⟩

theorem body_pc {w : ℕ} (hcap : 11 ≤ 2^w) (last : Word w) (v : State w) :
    (body hcap last v).pc=label hcap 2 := rfl

theorem body_bucket {w : ℕ} (hcap : 11 ≤ 2^w) (last : Word w) (v : State w) :
    (body hcap last v).regs (.inl 0)=v.regs (.inl 0) := by
  simp [body,instruction,arithmetic,effect,applyInstruction,loadEffect,storeEffect]

theorem body_cursor {w : ℕ} (hcap : 11 ≤ 2^w) (last : Word w) (v : State w) :
    (body hcap last v).regs (.inl 4)=increment (v.regs (.inl 4)) := by
  simp [body,instruction,arithmetic,effect,applyInstruction,loadEffect,storeEffect]

theorem body_pointer {w : ℕ} (hcap : 11 ≤ 2^w) (last : Word w) (v : State w) :
    (body hcap last v).regs (.inl 1)=v.regs (.inr (3,v.regs (.inl 1))) := by
  simp [body,instruction,arithmetic,effect,applyInstruction,loadEffect,storeEffect]

theorem body_valid {w : ℕ} (hcap : 11 ≤ 2^w) (last : Word w) (v : State w) :
    (body hcap last v).regs (.inl 2)=v.regs (.inr (4,v.regs (.inl 1))) := by
  simp [body,instruction,arithmetic,effect,applyInstruction,loadEffect,storeEffect]

theorem body_data {w : ℕ} (hcap : 11 ≤ 2^w) (last : Word w) (v : State w)
    (r : Fin 6) (x : Word w) :
    (body hcap last v).regs (.inr (r,x)) =
      if r=5 ∧ x=v.regs (.inl 4) then v.regs (.inr (0,v.regs (.inl 1)))
      else v.regs (.inr (r,x)) := by
  simp [body,instruction,arithmetic,effect,applyInstruction,loadEffect,storeEffect,Function.update_apply]

def Preserves {w : ℕ} (v t : State w) : Prop :=
  ∀ (r : Fin 6) (x : Word w), r≠5 → t.regs (.inr (r,x))=v.regs (.inr (r,x))

theorem Preserves.trans {w : ℕ} {v mid t : State w} (h1 : Preserves v mid)
    (h2 : Preserves mid t) : Preserves v t := by
  intro r x hr; exact (h2 r x hr).trans (h1 r x hr)

structure HeapRep {w n K : ℕ} (hcap : 11 ≤ 2^w) (hN : n≤2^w) (hK : K≤2^w)
    (heap : DirectRadix.Heap n K) (v : State w) : Prop where
  headValue : ∀ k, v.regs (.inr (1,position hK k))=pointerValue hcap hN (heap.head k)
  headValid : ∀ k, v.regs (.inr (2,position hK k))=pointerValid hcap (heap.head k)
  nextValue : ∀ i, v.regs (.inr (3,position hN i))=pointerValue hcap hN (heap.next i)
  nextValid : ∀ i, v.regs (.inr (4,position hN i))=pointerValid hcap (heap.next i)

theorem HeapRep.of_preserves {w n K : ℕ} {hcap : 11 ≤ 2^w} {hN : n≤2^w} {hK : K≤2^w}
    {heap : DirectRadix.Heap n K} {v t : State w} (h : HeapRep hcap hN hK heap v)
    (hp : Preserves v t) : HeapRep hcap hN hK heap t := by
  constructor
  · intro k; rw [hp 1 _ (by decide)]; exact h.headValue k
  · intro k; rw [hp 2 _ (by decide)]; exact h.headValid k
  · intro i; rw [hp 3 _ (by decide)]; exact h.nextValue i
  · intro i; rw [hp 4 _ (by decide)]; exact h.nextValid i

def writeList {w : ℕ} : List (Word w) → (Word w → Word w) → Word w → (Word w → Word w)
  | [],out,_ => out
  | x::xs,out,cursor => writeList xs (Function.update out cursor x) (increment cursor)

theorem walk_runs {w n K : ℕ} (hcap : 11 ≤ 2^w) (hN : n≤2^w) (hK : K≤2^w)
    (last : Word w) (input : Fin n → Word w) (heap : DirectRadix.Heap n K)
    (ids : List (Fin n)) (p : DirectRadix.Pointer n) (v : State w)
    (hc : DirectRadix.Chain heap.next p ids) (hr : HeapRep hcap hN hK heap v)
    (hin : ∀ i, v.regs (.inr (0,position hN i))=input i)
    (hp : v.pc=label hcap 2)
    (hv : v.regs (.inl 1)=pointerValue hcap hN p)
    (hb : v.regs (.inl 2)=pointerValid hcap p) :
    ∃ t, Runs hcap last (6*ids.length+1) v t ∧ t.pc=label hcap 8 ∧ Preserves v t ∧
      t.regs (.inl 0)=v.regs (.inl 0) ∧
      t.regs (.inl 4)=word ((v.regs (.inl 4)).val+ids.length) ∧
      (fun x => t.regs (.inr (5,x)))=
        writeList (ids.map input) (fun x => v.regs (.inr (5,x))) (v.regs (.inl 4)) := by
  induction ids generalizing p v with
  | nil =>
      have hnone : p=none := hc
      subst p
      refine ⟨finish hcap last v,finish_runs hcap last v hp,?_,?_,?_,?_,?_⟩
      · simp [finish,instruction,arithmetic,effect,applyInstruction,hb,pointerValid]
      · intro r x _; simp [finish,instruction,arithmetic,effect,applyInstruction]
      · simp [finish,instruction,arithmetic,effect,applyInstruction]
      · simp only [finish,instruction,arithmetic,effect,applyInstruction,
          Function.update_of_ne (by simp : (Sum.inl (4 : Fin 5) : Fin 5 ⊕ (Fin 6 × Word w)) ≠ .inl 2),
          List.length_nil,Nat.add_zero]
        apply Fin.ext
        exact (Nat.mod_eq_of_lt (v.regs (.inl 4)).isLt).symm
      · simp [finish,instruction,arithmetic,effect,applyInstruction,writeList]
  | cons i ids ih =>
      obtain ⟨rfl,hchain⟩ := hc
      have hptr : v.regs (.inl 1)=position hN i := hv
      have hvalid : v.regs (.inl 2)≠label hcap 0 := by rw [hb]; simp [pointerValid]
      let next := body hcap last v
      have hpres : Preserves v next := by
        intro r x hr'; rw [body_data]; simp [hr']
      have hinput : ∀ j, next.regs (.inr (0,position hN j))=input j := by
        intro j; rw [hpres 0 _ (by decide)]; exact hin j
      have hptr' : next.regs (.inl 1)=pointerValue hcap hN (heap.next i) := by
        rw [body_pointer,hptr]; exact hr.nextValue i
      have hvalid' : next.regs (.inl 2)=pointerValid hcap (heap.next i) := by
        rw [body_valid,hptr]; exact hr.nextValid i
      obtain ⟨t,ht,hpc,hpres',hbucket,hcursor,hout⟩ := ih (heap.next i) next hchain
        (hr.of_preserves hpres) hinput (body_pc hcap last v) hptr' hvalid'
      refine ⟨t,?_,hpc,hpres.trans hpres',?_,?_,?_⟩
      · convert (body_runs hcap last v hp hvalid).trans ht using 1 <;> simp <;> omega
      · exact hbucket.trans (body_bucket hcap last v)
      · rw [hcursor,body_cursor]
        apply Fin.ext
        simp only [increment,word,List.length_cons,Nat.mod_add_mod]
        congr 1
        omega
      · rw [hout]
        have ho : (fun x => next.regs (.inr (5,x)))=
            Function.update (fun x => v.regs (.inr (5,x))) (v.regs (.inl 4)) (input i) := by
          funext x
          rw [body_data,hptr,hin]
          simp [Function.update_apply]
        rw [ho,show next.regs (.inl 4)=increment (v.regs (.inl 4)) from body_cursor hcap last v]
        rfl

end CSL.TwoWordRadixGather
end Gather


