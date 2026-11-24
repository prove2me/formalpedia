-- Prove2me | Definitions.Def_CSL_Shared_Programs_ControlledNormalization
-- name    : CSL_Shared_Programs_ControlledNormalization
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-24T12:56:15.563807+00:00
-- url     : https://prove2.me/theorems/f7bd95cf-0ad1-4158-bf5f-1746c6eb0b71
-- title:
--   Coded sorting library: Shared / Programs / ControlledNormalization
-- statement:
--   Module `CodedSorting.Shared.Programs.ControlledNormalization` of the Lean development accompanying B. Li, Z. Li, S. Liu, *Undirected Multiple-Unicast Network Coding and Faster External-Memory Integer Sorting*, arXiv:2610.20079, ported to Lean v4.33.1 and Mathlib `0df444a` (namespace `CodedSorting` renamed to `CSL`).
--
--   A complete RAM-controlled instruction may update its program counter
--   after an I/O operation. Merely selecting a read from RAM and leaving its
--   control words unchanged cannot express every usual sequential program.
--   Here the continuation is a RAM-only operation, compiled explicitly after
--   the transfer. Both machines store all control words in their existing RAM.
--
--   This module is part of the machine-checked proof of Theorem 3.1 (external-memory integer sorting) and is imported by the later modules of that development.
-- source:
--   B. Li, Z. Li, S. Liu, *Undirected Multiple-Unicast Network Coding and Faster External-Memory Integer Sorting*, arXiv:2610.20079 (Theorem 3.1, p.4, and Appendix D); Lean development https://github.com/rtyu-1/coded-sorting-lean, module CodedSorting.Shared.Programs.ControlledNormalization

import Definitions.Def_CSL_Compat
import Definitions.Def_CSL_Shared_Programs_NormalizationComplete

/-! A complete RAM-controlled instruction may update its program counter
after an I/O operation. Merely selecting a read from RAM and leaving its
control words unchanged cannot express every usual sequential program.
Here the continuation is a RAM-only operation, compiled explicitly after
the transfer. Both machines store all control words in their existing RAM. -/

set_option autoImplicit false
namespace CSL.ControlledNormalization
open Normalization LayoutConversion NormalizationComplete
variable {Word : Type*} {L b B D : ℕ}

structure Instruction (L b D : ℕ) (Word : Type*) where
  operation : Command L b D Word
  resume : Words L Word → Words L Word

abbrev Policy (L b D : ℕ) (Word : Type*) :=
  Words L Word → Option (Instruction L b D Word)

def logicalStep (i : Instruction L b D Word) (s : LogicalState L b D Word) :
    LogicalState L b D Word :=
  Normalization.logicalStep (.localOp i.resume) (Normalization.logicalStep i.operation s)

def compile (i : Instruction L b D Word) : List (PhysicalCommand L b D Word) :=
  compileCommand i.operation ++ [.localOp i.resume]

def physicalStep (hb : b≤B) (padding : Word) (i : Instruction L b D Word)
    (s : PhysicalState L B D Word) : PhysicalState L B D Word :=
  executePrimitives hb padding (compile i) s

theorem execute_append (hb : b≤B) (padding : Word)
    (xs ys : List (PhysicalCommand L b D Word)) (s : PhysicalState L B D Word) :
    executePrimitives hb padding (xs++ys) s =
      executePrimitives hb padding ys (executePrimitives hb padding xs s) := by
  induction xs generalizing s with
  | nil => rfl
  | cons x xs ih => exact ih _

theorem cost_append (xs ys : List (PhysicalCommand L b D Word)) :
    primitiveListCost (xs++ys) = primitiveListCost xs+primitiveListCost ys := by
  induction xs with
  | nil => simp [primitiveListCost]
  | cons x xs ih => simp [primitiveListCost,ih,Nat.add_assoc]

theorem compiled_cost (i : Instruction L b D Word) :
    primitiveListCost (compile i) = transferCost i.operation := by
  simp [compile,cost_append,compiled_cost_eq,primitiveListCost,primitiveCost]

theorem physicalStep_eq (hb : b≤B) (padding : Word)
    (i : Instruction L b D Word) (s : PhysicalState L B D Word) :
    physicalStep hb padding i s =
      Normalization.physicalStep hb padding (.localOp i.resume)
        (Normalization.physicalStep hb padding i.operation s) := by
  rw [physicalStep,compile,execute_append,compiled_step_eq]
  rfl

theorem step_represents (hb : b≤B) (padding : Word) (i : Instruction L b D Word)
    (s : LogicalState L b D Word) (t : PhysicalState L B D Word)
    (h : Represents hb s t) :
    Represents hb (logicalStep i s) (physicalStep hb padding i t) := by
  rw [physicalStep_eq]
  exact Normalization.step_represents hb padding (.localOp i.resume) _ _
    (Normalization.step_represents hb padding i.operation s t h)

def runLogical (policy : Policy L b D Word) :
    ℕ → LogicalState L b D Word → LogicalState L b D Word × ℕ
  | 0,s => (s,0)
  | fuel+1,s => match policy s.ram with
      | none => (s,0)
      | some i =>
          let result := runLogical policy fuel (logicalStep i s)
          (result.1,transferCost i.operation+result.2)

def runPhysical (hb : b≤B) (padding : Word) (policy : Policy L b D Word) :
    ℕ → PhysicalState L B D Word → PhysicalState L B D Word × ℕ
  | 0,s => (s,0)
  | fuel+1,s => match policy s.ram with
      | none => (s,0)
      | some i =>
          let result := runPhysical hb padding policy fuel (physicalStep hb padding i s)
          (result.1,primitiveListCost (compile i)+result.2)

/-- The simulator covers actual sequential PC-changing programs, including
a read whose data equals the previous contents of its destination window. -/
theorem run_represents_and_cost (hb : b≤B) (padding : Word)
    (policy : Policy L b D Word) (fuel : ℕ)
    (s : LogicalState L b D Word) (t : PhysicalState L B D Word)
    (h : Represents hb s t) :
    Represents hb (runLogical policy fuel s).1 (runPhysical hb padding policy fuel t).1 ∧
      (runLogical policy fuel s).2=(runPhysical hb padding policy fuel t).2 := by
  induction fuel generalizing s t with
  | zero => exact ⟨h,rfl⟩
  | succ fuel ih =>
    have hram := h.1
    cases hp : policy s.ram with
    | none =>
      have ht : policy t.ram=none := by rw [←hram]; exact hp
      simpa only [runLogical,runPhysical,hp,ht] using And.intro h (show (0:ℕ)=0 from rfl)
    | some i =>
      have ht : policy t.ram=some i := by rw [←hram]; exact hp
      obtain ⟨hstate,hcost⟩ := ih (logicalStep i s) (physicalStep hb padding i t)
        (step_represents hb padding i s t h)
      exact ⟨by simpa only [runLogical,runPhysical,hp,ht] using hstate,
        by simpa only [runLogical,runPhysical,hp,ht,compiled_cost,hcost]⟩

def readNext (address : Fin D) (window : Window L b) (pc : Fin L) (next : Word) :
    Instruction L b D Word :=
  ⟨.read address window,fun ram => Function.update ram pc next⟩

@[simp] theorem readNext_pc (address : Fin D) (window : Window L b)
    (pc : Fin L) (next : Word) (s : LogicalState L b D Word) :
    (logicalStep (readNext address window pc next) s).ram pc = next := by
  simp [logicalStep,readNext,Normalization.logicalStep]

/-- Resume touches only the designated control slot; all other fetched
payload words retain the value delivered by the read. -/
theorem readNext_payload (address : Fin D) (window : Window L b)
    (pc j : Fin L) (next : Word) (s : LogicalState L b D Word) (hj : j≠pc) :
    (logicalStep (readNext address window pc next) s).ram j =
      load s.ram window (s.disk address) j := by
  simp [logicalStep,readNext,Normalization.logicalStep,Function.update_of_ne hj]

/-- Existing Policy programs embed by choosing an identity continuation. -/
def liftPolicy (policy : Normalization.Policy L b D Word) : Policy L b D Word :=
  fun ram => (policy ram).map (fun command => ⟨command,id⟩)

theorem liftPolicy_run (policy : Normalization.Policy L b D Word) (fuel : ℕ)
    (s : LogicalState L b D Word) :
    runLogical (liftPolicy policy) fuel s = Normalization.runLogical policy fuel s := by
  induction fuel generalizing s with
  | zero => rfl
  | succ fuel ih =>
    cases hp : policy s.ram with
    | none => simp [runLogical,liftPolicy,Normalization.runLogical,hp]
    | some cmd =>
      have hstep : logicalStep (⟨cmd,id⟩ : Instruction L b D Word) s =
          Normalization.logicalStep cmd s := rfl
      simp only [runLogical,liftPolicy,Normalization.runLogical,hp,Option.map]
      rw [hstep,ih]

/-- Full live-layout simulation with PC-changing instructions. Scratch
capacity D does not appear in the conversion charge. -/
theorem simulation_live_layout (source backing target : BlockReflection.Disk Word)
    (padding : Word) (ram : Words L Word) (D B b nIn nOut : ℕ)
    (hB : 0<B) (hb : b≤B) (hout : nOut≤D)
    (policy : Policy L b D Word) (fuel : ℕ) :
    let logical := runLogical policy fuel (liveLogicalInput source backing ram D B b nIn)
    let physical := runPhysical hb padding policy fuel
      (livePhysicalInput source backing padding ram D B b nIn hB)
    let restored := compactRun (flattenBlocks D B hB padding physical.1.disk)
      B b hB hb nOut ⟨target,[]⟩
    (∀ j : Fin nOut,∀ i : Fin b,
      restored.disk (j.val*b+i.val)=logical.1.disk (j.castLE hout) i) ∧
    (expandRun source padding B b hB nIn ⟨backing,[]⟩).trace.length+
      physical.2+restored.trace.length=logical.2+3*nIn+5*nOut := by
  try dsimp
  have href := run_represents_and_cost hb padding policy fuel
    (liveLogicalInput source backing ram D B b nIn)
    (livePhysicalInput source backing padding ram D B b nIn hB)
    (liveInput_represents source backing padding ram D B b nIn hB hb)
  constructor
  · intro j i
    rw [compactRun_correct _ B b nOut hB hb _ j.val j.isLt i]
    have he := flattenBlocks_at D B hB padding
      (runPhysical hb padding policy fuel
        (livePhysicalInput source backing padding ram D B b nIn hB)).1.disk
      (j.castLE hout) (i.castLE hb)
    change flattenBlocks D B hB padding _ (j.val*B+i.val)=_ at he
    rw [he]
    exact (congrFun (href.1.2 (j.castLE hout)) i).symm
  · rw [expandRun_cost,compactRun_cost,←href.2]
    simp only [List.length_nil,Nat.zero_add]
    omega

end CSL.ControlledNormalization


