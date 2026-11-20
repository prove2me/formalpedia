-- Prove2me | Definitions.Def_NearlyOptimalPPR_Computation_compiler_runtime
-- name    : NearlyOptimalPPR_Computation_compiler_runtime
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-19T06:16:42.056079+00:00
-- url     : https://prove2.me/theorems/47e4ae75-8f88-4d7a-a2af-5574b6ed744e
-- title:
--   Sparse local-machine compiler interfaces for recursive PageRank
-- statement:
--   This module specifies the sparse operational representation used to implement the recursive Personalized PageRank algorithms on the charged local machine. It supplies structured code and finite-execution semantics; owned sparse adjacency, list, heap, and solve representations; active-frame and ancestor records; the recursive controller code; and its storage and work-accounting quantities.
--
--   For each logical recursive state, the memory predicates describe its concrete representation. They impose no accuracy, termination, or desired running-time conclusion. Those properties are proved separately by the implementation theorems.
--
--   The representation preserves the column-oriented PageRank convention and the exact-SDDM primitive of the mission model. These interfaces allow the queue, propagation, solve, initialization, and controller proofs to be reused independently.
-- source:
--   Li, Xu, Yang, Zhou, Nearly optimal Personalized PageRank computation, STOC 2027 submission #884, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/884.pdf, Algorithms 1 and 6–9, pp.5,14–22; operational representation in the mission charged exact-SDDM local-machine model.

import Batteries.Data.BinomialHeap
import Definitions.Def_NearlyOptimalPPR_Computation_machine
import Definitions.Def_NearlyOptimalPPR_Computation_proof_invariants
import Definitions.Def_NearlyOptimalPPR_Computation_push
import Definitions.Def_NearlyOptimalPPR_Computation_recursive
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Lattice.Basic
import Mathlib.Data.Finset.Union
import Mathlib.Data.Int.Basic
import Mathlib.Data.Nat.Basic
import Mathlib.Data.Nat.Log
set_option linter.all false
-- Runtime interface from Solutions.StructuredMachine

set_option autoImplicit false
open Finset Matrix MeasureTheory
open scoped ENNReal
namespace NearlyOptimalPPR.Computation
noncomputable section


inductive MachineCode where
  | skip
  | atom (i : Instruction)
  | seq (a b : MachineCode)
  | branchReal (r : ℕ) (nonpos positive : MachineCode)
  | branchPointer (a b : ℕ) (le gt : MachineCode)
  | whileReal (r : ℕ) (body : MachineCode)
  | whilePointer (a b : ℕ) (body : MachineCode)

namespace MachineCode

end MachineCode
end
end NearlyOptimalPPR.Computation

-- Runtime interface from Solutions.MachineRelocation

set_option autoImplicit false
open Finset Matrix MeasureTheory
open scoped ENNReal
namespace NearlyOptimalPPR.Computation
noncomputable section


def pcSet (st : MachineState) (pc : ℕ) : MachineState :=
  {st with scalar := {st.scalar with core := {st.scalar.core with pc := pc}}}

set_option maxRecDepth 4096 in
end
end NearlyOptimalPPR.Computation

-- Runtime interface from Solutions.MachineBranches

set_option autoImplicit false
open Finset Matrix MeasureTheory
open scoped ENNReal
namespace NearlyOptimalPPR.Computation
noncomputable section


def payUnit (st : MachineState) : MachineState :=
  pcSet {st with work := st.work+1,scalar := {st.scalar with work := st.scalar.work+1}} 0

end
end NearlyOptimalPPR.Computation

-- Runtime interface from Solutions.MachineCodeSemantics

set_option autoImplicit false
open Finset Matrix MeasureTheory
open scoped ENNReal
namespace NearlyOptimalPPR.Computation
noncomputable section


def atomState (m : SolveModel) {n : ℕ} (g : InputGraph n) (ω : ℕ → Bool)
    (i : Instruction) (st : MachineState) : MachineState :=
  machineStep m [i] g ω (pcSet st 0)


inductive MachineEval (m : SolveModel) {n : ℕ} (g : InputGraph n) (ω : ℕ → Bool) :
    MachineCode → MachineState → ℕ → MachineState → Prop where
  | skip (st : MachineState) : MachineEval m g ω .skip st 0 st
  | atom (i : Instruction) (st : MachineState)
      (ready : (atomState m g ω i st).scalar.core.pc=1) :
      MachineEval m g ω (.atom i) st 1 (pcSet (atomState m g ω i st) 0)
  | seq {a b : MachineCode} {st mid out : MachineState} {u v : ℕ}
      (ea : MachineEval m g ω a st u mid) (eb : MachineEval m g ω b mid v out) :
      MachineEval m g ω (.seq a b) st (u+v) out
  | realNonpos {r : ℕ} {a b : MachineCode} {st out : MachineState} {u : ℕ}
      (hh : st.scalar.halted=false) (guard : st.scalar.core.regs r ≤ 0)
      (ea : MachineEval m g ω a (payUnit st) u out) :
      MachineEval m g ω (.branchReal r a b) st (1+u) out
  | realPos {r : ℕ} {a b : MachineCode} {st mid : MachineState} {u : ℕ}
      (hh : st.scalar.halted=false) (guard : ¬st.scalar.core.regs r ≤ 0)
      (eb : MachineEval m g ω b (payUnit st) u mid) :
      MachineEval m g ω (.branchReal r a b) st (1+u+1) (payUnit mid)
  | pointerLe {r s : ℕ} {a b : MachineCode} {st out : MachineState} {u : ℕ}
      (hh : st.scalar.halted=false) (guard : st.scalar.core.ptrs r ≤ st.scalar.core.ptrs s)
      (ea : MachineEval m g ω a (payUnit st) u out) :
      MachineEval m g ω (.branchPointer r s a b) st (1+u) out
  | pointerGt {r s : ℕ} {a b : MachineCode} {st mid : MachineState} {u : ℕ}
      (hh : st.scalar.halted=false) (guard : ¬st.scalar.core.ptrs r ≤ st.scalar.core.ptrs s)
      (eb : MachineEval m g ω b (payUnit st) u mid) :
      MachineEval m g ω (.branchPointer r s a b) st (1+u+1) (payUnit mid)
  | realDone {r : ℕ} {body : MachineCode} {st : MachineState}
      (hh : st.scalar.halted=false) (guard : st.scalar.core.regs r ≤ 0) :
      MachineEval m g ω (.whileReal r body) st 1 (payUnit st)
  | realNext {r : ℕ} {body : MachineCode} {st mid out : MachineState} {u v : ℕ}
      (hh : st.scalar.halted=false) (guard : ¬st.scalar.core.regs r ≤ 0)
      (eb : MachineEval m g ω body (payUnit st) u mid)
      (er : MachineEval m g ω (.whileReal r body) (payUnit mid) v out) :
      MachineEval m g ω (.whileReal r body) st (1+u+1+v) out
  | pointerDone {r s : ℕ} {body : MachineCode} {st : MachineState}
      (hh : st.scalar.halted=false) (guard : st.scalar.core.ptrs r ≤ st.scalar.core.ptrs s) :
      MachineEval m g ω (.whilePointer r s body) st 1 (payUnit st)
  | pointerNext {r s : ℕ} {body : MachineCode} {st mid out : MachineState} {u v : ℕ}
      (hh : st.scalar.halted=false) (guard : ¬st.scalar.core.ptrs r ≤ st.scalar.core.ptrs s)
      (eb : MachineEval m g ω body (payUnit st) u mid)
      (er : MachineEval m g ω (.whilePointer r s body) (payUnit mid) v out) :
      MachineEval m g ω (.whilePointer r s body) st (1+u+1+v) out

end
end NearlyOptimalPPR.Computation

-- Runtime interface from Solutions.ScalarCode

set_option autoImplicit false
namespace NearlyOptimalPPR.Computation
noncomputable section


inductive RealOperation where
  | add | sub | mul | div

def RealOperation.value (op : RealOperation) (x y : ℝ) : ℝ :=
  match op with | .add => x+y | .sub => x-y | .mul => x*y | .div => x/y

def RealOperation.instruction (op : RealOperation) (r a b : ℕ) : Instruction :=
  .scalar (.core (match op with
    | .add => .add r a b | .sub => .sub r a b | .mul => .mul r a b | .div => .div r a b))

end
end NearlyOptimalPPR.Computation

-- Runtime interface from Solutions.PowerCode

set_option autoImplicit false
open scoped ENNReal
namespace NearlyOptimalPPR.Computation
noncomputable section


def powerBody : MachineCode :=
  .seq (.atom (RealOperation.mul.instruction 1 1 0)) (.atom (.scalar (.core (.pinc 0))))

def powerLoop : MachineCode := .whilePointer 1 0 powerBody

def powerCode : MachineCode :=
  .seq (.atom (.scalar (.core (.const 1 1))))
    (.seq (.atom (.scalar (.core (.pset 0 0)))) powerLoop)

end
end NearlyOptimalPPR.Computation

-- Runtime interface from Solutions.PointerRoutine

set_option autoImplicit false
open scoped ENNReal
namespace NearlyOptimalPPR.Computation
noncomputable section

inductive PointerOp where
  | set (r : ℕ) (z : ℤ)
  | copy (r s : ℕ)
  | inc (r : ℕ)
  | add (r s t : ℕ)
  | load (r s : ℕ)

def PointerOp.instruction : PointerOp → Instruction
  | .set r z => .scalar (.core (.pset r z))
  | .copy r s => .scalar (.core (.pcopy r s))
  | .inc r => .scalar (.core (.pinc r))
  | .add r s t => .scalar (.pointerAdd r s t)
  | .load r s => .scalar (.integerLoad r s)

inductive PointerRoutine where
  | skip
  | atom (op : PointerOp)
  | seq (a b : PointerRoutine)
  | branch (r s : ℕ) (a b : PointerRoutine)

def PointerRoutine.code : PointerRoutine → MachineCode
  | .skip => .skip
  | .atom op => .atom op.instruction
  | .seq a b => .seq a.code b.code
  | .branch r s a b => .branchPointer r s a.code b.code

end
end NearlyOptimalPPR.Computation

-- Runtime interface from Solutions.BinomialQueue

set_option autoImplicit false
namespace NearlyOptimalPPR.Computation
namespace SparseQueue
open Batteries.BinomialHeap.Imp

abbrev keyLE (a b : ℕ) : Bool := decide (a ≤ b)

def nodeSupport : HeapNode ℕ → Finset ℕ
  | .nil => ∅
  | .node a c s => insert a (nodeSupport c ∪ nodeSupport s)

end SparseQueue
end NearlyOptimalPPR.Computation

-- Runtime interface from Solutions.HeapMemory

set_option autoImplicit false
namespace NearlyOptimalPPR.Computation
namespace SparseQueue
open Batteries.BinomialHeap.Imp
noncomputable section


def nodeCells (p : ℤ) : Finset ℤ := {p,p+1,p+2}


inductive ForestRep (I : ℤ → ℤ) : ℤ → HeapNode ℕ → Finset ℤ → Prop where
  | nil : ForestRep I 0 .nil ∅
  | node (p : ℤ) (a : ℕ) (cp sp : ℤ) (c s : HeapNode ℕ) (C S : Finset ℤ)
      (positive : 2 ≤ p) (key : I p=(a : ℤ))
      (child : I (p+1)=cp) (sibling : I (p+2)=sp)
      (rc : ForestRep I cp c C) (rs : ForestRep I sp s S)
      (hc : Disjoint (nodeCells p) C) (hs : Disjoint (nodeCells p) S) (hcs : Disjoint C S) :
      ForestRep I p (.node a c s) (nodeCells p ∪ C ∪ S)

end
end SparseQueue
end NearlyOptimalPPR.Computation

-- Runtime interface from Solutions.SquareCode

set_option autoImplicit false
open scoped ENNReal
namespace NearlyOptimalPPR.Computation
noncomputable section

def squareBody : MachineCode :=
  .seq (.atom (.scalar (.pointerAdd 1 1 2))) (.atom (.scalar (.core (.pinc 3))))
def squareLoop : MachineCode := .whilePointer 2 3 squareBody
def squareCode : MachineCode :=
  .seq (.atom (.scalar (.core (.pset 1 0))))
    (.seq (.atom (.scalar (.core (.pset 3 0)))) squareLoop)

end
end NearlyOptimalPPR.Computation

-- Runtime interface from Solutions.DepthCandidateCode

set_option autoImplicit false
open scoped ENNReal
namespace NearlyOptimalPPR.Computation
noncomputable section

def depthCandidateCode : MachineCode :=
  .seq squareCode (.seq (.atom (.scalar (.pointerReal 0 2))) powerCode)

end
end NearlyOptimalPPR.Computation

-- Runtime interface from Solutions.AccessibleDepth

set_option autoImplicit false
namespace NearlyOptimalPPR.Computation
noncomputable section
attribute [local instance] Classical.propDecidable


def depthPowerTest (K : ℝ) (j : ℕ) : Prop :=
  K < ((j+2 : ℕ) : ℝ)^((j+2)*(j+2))

lemma depthPowerTest_exists (K : ℝ) : ∃ j, depthPowerTest K j := by
  obtain ⟨j,hj⟩ := exists_nat_gt K
  refine ⟨j,?_⟩
  unfold depthPowerTest
  have hh : (1 : ℝ) ≤ ((j+2 : ℕ) : ℝ) := by norm_cast; omega
  calc
    K < (j : ℝ) := hj
    _ ≤ ((j+2 : ℕ) : ℝ) := by exact_mod_cast (show j ≤ j+2 by omega)
    _ ≤ _ := le_self_pow₀ hh (Nat.mul_ne_zero (by omega) (by omega))

def accessibleDepth (K : ℝ) : ℕ := Nat.find (depthPowerTest_exists K)

end
end NearlyOptimalPPR.Computation

-- Runtime interface from Solutions.DepthSearchCode

set_option autoImplicit false
namespace NearlyOptimalPPR.Computation
noncomputable section

def coreCode (i : SmaleNinth.RAMInstr) : MachineCode := .atom (.scalar (.core i))

def sequenceCode : List MachineCode → MachineCode
  | [] => .skip
  | a :: rest => .seq a (sequenceCode rest)

def depthDecisionCode : MachineCode := .branchReal 1
  (.seq (coreCode (.pinc 2)) (coreCode (.const 3 1)))
  (coreCode (.const 3 0))

def depthTestCode : MachineCode := sequenceCode [
  coreCode (.pset 3 1),coreCode (.load 2 3),
  .atom (RealOperation.mul.instruction 1 1 2),coreCode (.const 4 1),
  .atom (RealOperation.sub.instruction 1 1 4),depthDecisionCode]

def depthBodyCode : MachineCode := .seq depthCandidateCode depthTestCode

def depthLoopCode : MachineCode := .whileReal 3 depthBodyCode

def depthSearchCode : MachineCode :=
  .seq (coreCode (.pset 2 2)) (.seq (coreCode (.const 3 1)) depthLoopCode)

end
end NearlyOptimalPPR.Computation

-- Runtime interface from Solutions.HeapLinkCode

set_option autoImplicit false
open scoped ENNReal
namespace NearlyOptimalPPR.Computation
noncomputable section


def heapLinkCode : MachineCode := sequenceCode [
  coreCode (.pcopy 7 5),coreCode (.pinc 7),.atom (.scalar (.integerLoad 8 7)),
  coreCode (.pcopy 9 6),coreCode (.pinc 9),coreCode (.pinc 9),
  .atom (.scalar (.integerStore 9 8)),.atom (.scalar (.integerStore 7 6))]

end
end NearlyOptimalPPR.Computation

-- Runtime interface from Solutions.RankArrayQueue

set_option autoImplicit false
namespace NearlyOptimalPPR.Computation
namespace SparseQueue
open Batteries.BinomialHeap.Imp

structure RankedTree where
  key : ℕ
  children : HeapNode ℕ

def RankedTree.valid (r : ℕ) (t : RankedTree) : Prop := t.children.WF keyLE t.key r

def RankedTree.support (t : RankedTree) : Finset ℕ := insert t.key (nodeSupport t.children)

abbrev RankSlots := ℕ → Option RankedTree

def SlotsValid (slots : RankSlots) : Prop := ∀ r t, slots r=some t → t.valid r


def RankedTree.size (t : RankedTree) : ℕ := t.children.realSize+1

end SparseQueue
end NearlyOptimalPPR.Computation

-- Runtime interface from Solutions.RankArrayMemory

set_option autoImplicit false
namespace NearlyOptimalPPR.Computation
namespace SparseQueue
noncomputable section

def arrayCells (base : ℤ) (length : ℕ) : Finset ℤ :=
  (Finset.range length).image (fun i : ℕ => base+(i : ℤ))

def queueCells (base : ℤ) (length : ℕ) (feet : ℕ → Finset ℤ) : Finset ℤ :=
  arrayCells base length ∪ (Finset.range length).biUnion feet

def SlotRep (I : ℤ → ℤ) (p : ℤ) (value : Option RankedTree) (F : Finset ℤ) : Prop :=
  match value with
  | none => p=0 ∧ F=∅
  | some t => ForestRep I p (.node t.key t.children .nil) F

structure RankArrayRep (I : ℤ → ℤ) (base : ℤ) (length : ℕ) (slots : RankSlots)
    (roots : ℕ → ℤ) (feet : ℕ → Finset ℤ) : Prop where
  positive : 2 ≤ base
  array : ∀ i < length, I (base+(i : ℤ))=roots i
  node : ∀ i < length, SlotRep I (roots i) (slots i) (feet i)
  separate : ∀ i < length, Disjoint (arrayCells base length) (feet i)
  pairwise : ∀ i < length, ∀ j < length, i ≠ j → Disjoint (feet i) (feet j)
  bounded : ∀ i, length ≤ i → slots i=none
  valid : SlotsValid slots

end
end SparseQueue
end NearlyOptimalPPR.Computation

-- Runtime interface from Solutions.PointerSwapCode

set_option autoImplicit false
namespace NearlyOptimalPPR.Computation
noncomputable section

def swapRootsCode : MachineCode := sequenceCode [
  coreCode (.pcopy 12 5),coreCode (.pcopy 5 6),coreCode (.pcopy 6 12)]

end
end NearlyOptimalPPR.Computation

-- Runtime interface from Solutions.HeapCombineCode

set_option autoImplicit false
open scoped ENNReal
namespace NearlyOptimalPPR.Computation
noncomputable section

def heapCombineCode : MachineCode := .seq (.atom (.scalar (.integerLoad 10 5)))
  (.seq (.atom (.scalar (.integerLoad 11 6)))
    (.branchPointer 10 11 heapLinkCode (.seq swapRootsCode heapLinkCode)))

end
end NearlyOptimalPPR.Computation

-- Runtime interface from Solutions.HeapCarryCode

set_option autoImplicit false
namespace NearlyOptimalPPR.Computation
noncomputable section


def heapCarryBodyCode : MachineCode := sequenceCode [
  .atom (.scalar (.integerStore 15 0)),heapCombineCode,coreCode (.pinc 14),
  .atom (.scalar (.pointerAdd 15 13 14)),.atom (.scalar (.integerLoad 6 15))]

def heapCarryLoopCode : MachineCode := .whilePointer 6 0 heapCarryBodyCode

def heapCarryCode : MachineCode := sequenceCode [
  coreCode (.pset 0 0),.atom (.scalar (.pointerAdd 15 13 14)),
  .atom (.scalar (.integerLoad 6 15)),heapCarryLoopCode,.atom (.scalar (.integerStore 15 5))]

end
end NearlyOptimalPPR.Computation

-- Runtime interface from Solutions.HeapMinScanCode

set_option autoImplicit false
namespace NearlyOptimalPPR.Computation
noncomputable section


def chooseMinRootCode : MachineCode := sequenceCode [
  coreCode (.pcopy 27 29),coreCode (.pcopy 28 26),coreCode (.pcopy 31 30)]

def compareMinRootCode : MachineCode := .branchPointer 27 0 chooseMinRootCode
  (.branchPointer 30 31 chooseMinRootCode .skip)

def inspectMinRootCode : MachineCode := .branchPointer 29 0 .skip
  (.seq (.atom (.scalar (.integerLoad 30 29))) compareMinRootCode)

def minScanBodyCode : MachineCode := sequenceCode [
  .atom (.scalar (.pointerAdd 32 13 26)),.atom (.scalar (.integerLoad 29 32)),
  inspectMinRootCode,coreCode (.pinc 26)]

def minScanLoopCode : MachineCode := .whilePointer 25 26 minScanBodyCode

def heapMinScanCode : MachineCode := sequenceCode [
  coreCode (.pset 0 0),coreCode (.pset 26 0),coreCode (.pset 27 0),coreCode (.pset 28 0),minScanLoopCode]

end
end NearlyOptimalPPR.Computation

-- Runtime interface from Solutions.MinScanRoutine

set_option autoImplicit false
namespace NearlyOptimalPPR.Computation
noncomputable section

def PointerRoutine.sequence (ops : List PointerRoutine) : PointerRoutine := ops.foldr .seq .skip

end
end NearlyOptimalPPR.Computation

-- Runtime interface from Solutions.IntegerScaleCode

set_option autoImplicit false
open scoped ENNReal
namespace NearlyOptimalPPR.Computation
noncomputable section


def integerScaleBodyRoutine : PointerRoutine := .sequence [
  .atom (.add 42 42 40),.atom (.inc 43)]

def integerScaleBodyCode : MachineCode := integerScaleBodyRoutine.code

def integerScaleLoopCode : MachineCode := .whilePointer 41 43 integerScaleBodyCode

def integerScaleCode : MachineCode := sequenceCode [
  coreCode (.pset 42 0),coreCode (.pset 43 0),integerScaleLoopCode]

end
end NearlyOptimalPPR.Computation

-- Runtime interface from Solutions.LinearRoutine

set_option autoImplicit false
open scoped ENNReal
namespace NearlyOptimalPPR.Computation
noncomputable section


def linearCode (instructions : List Instruction) : MachineCode := sequenceCode (instructions.map .atom)

end
end NearlyOptimalPPR.Computation

-- Runtime interface from Solutions.LevelHeaderCode

set_option autoImplicit false
namespace NearlyOptimalPPR.Computation
noncomputable section


def levelHeaderAddress (level slot : ℕ) : ℤ := 128+32*(level : ℤ)+(slot : ℤ)

def levelHeaderAddressInstructions (slot : ℕ) : List Instruction := [
  .scalar (.core (.pcopy 102 100)),
  .scalar (.pointerAdd 102 102 102),.scalar (.pointerAdd 102 102 102),
  .scalar (.pointerAdd 102 102 102),.scalar (.pointerAdd 102 102 102),
  .scalar (.pointerAdd 102 102 102),.scalar (.core (.pset 106 (128+slot))),
  .scalar (.pointerAdd 102 102 106)]
def levelHeaderAddressCode (slot : ℕ) : MachineCode := linearCode (levelHeaderAddressInstructions slot)

end
end NearlyOptimalPPR.Computation

-- Runtime interface from Solutions.LevelHeaderAccess

set_option autoImplicit false
namespace NearlyOptimalPPR.Computation
noncomputable section

def levelHeaderIntegerLoadCode (slot : ℕ) : MachineCode := .seq (levelHeaderAddressCode slot) (.atom (.scalar (.integerLoad 105 102)))
def levelHeaderIntegerStoreCode (slot : ℕ) : MachineCode := .seq (levelHeaderAddressCode slot) (.atom (.scalar (.integerStore 102 105)))
def levelHeaderRealLoadCode (slot : ℕ) : MachineCode := .seq (levelHeaderAddressCode slot) (coreCode (.load 10 102))
def levelHeaderRealStoreCode (slot : ℕ) : MachineCode := .seq (levelHeaderAddressCode slot) (coreCode (.store 102 10))

end
end NearlyOptimalPPR.Computation

-- Runtime interface from Solutions.LevelHeaderRealFrom

set_option autoImplicit false
namespace NearlyOptimalPPR.Computation
noncomputable section

def levelHeaderRealFromCode (slot source : ℕ) : MachineCode :=
  .seq (coreCode (.mul 10 source 31)) (levelHeaderRealStoreCode slot)
end
end NearlyOptimalPPR.Computation

-- Runtime interface from Solutions.LevelHeaderSet

set_option autoImplicit false
namespace NearlyOptimalPPR.Computation
noncomputable section

def levelHeaderIntegerSetCode (slot : ℕ) (value : ℤ) : MachineCode :=
  .seq (coreCode (.pset 105 value)) (levelHeaderIntegerStoreCode slot)
def levelHeaderRealZeroCode (slot : ℕ) : MachineCode :=
  .seq (coreCode (.const 10 0)) (levelHeaderRealStoreCode slot)

end
end NearlyOptimalPPR.Computation

-- Runtime interface from Solutions.LevelHeaderSets

set_option autoImplicit false
open scoped ENNReal
namespace NearlyOptimalPPR.Computation
noncomputable section

def levelHeaderIntegerSetsCode (assignments : List (ℕ × ℤ)) : MachineCode :=
  sequenceCode (assignments.map (fun kv => levelHeaderIntegerSetCode kv.1 kv.2))
end
end NearlyOptimalPPR.Computation

-- Runtime interface from Solutions.LevelHeaderRealZeros

set_option autoImplicit false
open scoped ENNReal
namespace NearlyOptimalPPR.Computation
noncomputable section

def levelHeaderRealZerosCode (slots : List ℕ) : MachineCode :=
  sequenceCode (slots.map levelHeaderRealZeroCode)
end
end NearlyOptimalPPR.Computation

-- Runtime interface from Solutions.FreshHeaderDefaults

set_option autoImplicit false
namespace NearlyOptimalPPR.Computation
noncomputable section

def freshHeaderIntegerDefaults : List (ℕ × ℤ) :=
  [(0,0),(1,0),(2,0),(3,0),(4,0),(5,0),(6,0),(9,0),(10,1),(11,0)]
def freshHeaderDefaultsCode : MachineCode := .seq (levelHeaderIntegerSetsCode freshHeaderIntegerDefaults)
  (levelHeaderRealZerosCode [3,4,5])
end
end NearlyOptimalPPR.Computation

-- Runtime interface from Solutions.FrameScalarParameters

set_option autoImplicit false
namespace NearlyOptimalPPR.Computation
noncomputable section

def frameScalarParametersCode : MachineCode := .seq (levelHeaderRealFromCode 0 12) (levelHeaderRealFromCode 1 13)
end
end NearlyOptimalPPR.Computation

-- Runtime interface from Solutions.LevelHeaderIntegerFrom

set_option autoImplicit false
namespace NearlyOptimalPPR.Computation
noncomputable section

def levelHeaderIntegerFromCode (slot source : ℕ) : MachineCode :=
  .seq (coreCode (.pcopy 105 source)) (levelHeaderIntegerStoreCode slot)
end
end NearlyOptimalPPR.Computation

-- Runtime interface from Solutions.BlockCandidatePower

set_option autoImplicit false
open scoped ENNReal
namespace NearlyOptimalPPR.Computation
noncomputable section

def blockCandidatePrefixInstructions : List Instruction := [
  .scalar (.core (.pcopy 1 84)),.scalar (.core (.pinc 1)),.scalar (.core (.pinc 1)),
  .scalar (.core (.pcopy 86 85)),.scalar (.core (.pinc 86)),.scalar (.pointerReal 0 86)]

def blockCandidatePrefixCode : MachineCode := linearCode blockCandidatePrefixInstructions

def blockCandidatePowerCode : MachineCode := .seq blockCandidatePrefixCode powerCode

end
end NearlyOptimalPPR.Computation

-- Runtime interface from Solutions.BlockCandidateDecision

set_option autoImplicit false
open scoped ENNReal
namespace NearlyOptimalPPR.Computation
noncomputable section

def blockCandidateDecisionCode : MachineCode := .seq (.atom (RealOperation.sub.instruction 22 1 21))
  (.branchReal 22 (coreCode (.pinc 85)) (coreCode (.const 24 0)))

def blockCandidateTestCode : MachineCode := .seq blockCandidatePowerCode blockCandidateDecisionCode

def blockSearchLoopCode : MachineCode := .whileReal 24 blockCandidateTestCode

end
end NearlyOptimalPPR.Computation

-- Runtime interface from Solutions.BlockTargetPreparation

set_option autoImplicit false
open scoped ENNReal
namespace NearlyOptimalPPR.Computation
noncomputable section

def blockTargetPrefixInstructions : List Instruction := [
  .scalar (.core (.const 30 1)),RealOperation.mul.instruction 0 20 30,
  .scalar (.core (.pcopy 1 84)),.scalar (.core (.pinc 1))]

def blockTargetTailInstructions : List Instruction := [
  RealOperation.mul.instruction 21 1 30,.scalar (.core (.pset 85 0)),.scalar (.core (.const 24 1))]

def blockTargetPrefixCode : MachineCode := linearCode blockTargetPrefixInstructions

def blockTargetTailCode : MachineCode := linearCode blockTargetTailInstructions

def blockTargetPreparationCode : MachineCode := .seq blockTargetPrefixCode (.seq powerCode blockTargetTailCode)

end
end NearlyOptimalPPR.Computation

-- Runtime interface from Solutions.BalancedBlockExecution

set_option autoImplicit false
open scoped ENNReal
namespace NearlyOptimalPPR.Computation
noncomputable section

def balancedBlockCode : MachineCode := .seq blockTargetPreparationCode
  (.seq blockSearchLoopCode (coreCode (.pset 0 0)))

end
end NearlyOptimalPPR.Computation

-- Runtime interface from Solutions.FrameBlockCode

set_option autoImplicit false
namespace NearlyOptimalPPR.Computation
noncomputable section

def frameBlockPrepInstructions : List Instruction := [
  .scalar (.core (.pset 105 2)),.scalar (.integerLoad 84 105),
  .scalar (.core (.pdec 84)),.scalar (.core (.pdec 84)),.scalar (.pointerSub 84 84 100),
  .scalar (.core (.mul 20 10 31))]
def frameBlockPrepCode : MachineCode := linearCode frameBlockPrepInstructions

def frameThresholdRestoreCode : MachineCode := .seq (levelHeaderRealLoadCode 1) (coreCode (.mul 20 10 31))
def frameBlockPreparationCode : MachineCode := .seq (levelHeaderRealLoadCode 0)
  (.seq frameBlockPrepCode (.seq balancedBlockCode
    (.seq (levelHeaderIntegerFromCode 14 85) frameThresholdRestoreCode)))

end
end NearlyOptimalPPR.Computation

-- Runtime interface from Solutions.GraphRecordAddress

set_option autoImplicit false
namespace NearlyOptimalPPR.Computation


def vertexRecordAddress (width vertex offset : ℕ) : ℤ :=
  -1-((vertex*width+offset : ℕ) : ℤ)

end NearlyOptimalPPR.Computation

-- Runtime interface from Solutions.FreshAllocation

set_option autoImplicit false
namespace NearlyOptimalPPR.Computation
namespace SparseQueue
noncomputable section

def reserveArrayCode : MachineCode :=
  .seq (coreCode (.pcopy 13 20)) (.atom (.scalar (.pointerAdd 20 20 18)))

end
end SparseQueue
end NearlyOptimalPPR.Computation

-- Runtime interface from Solutions.RankArrayInitialize

set_option autoImplicit false
open scoped ENNReal
namespace NearlyOptimalPPR.Computation
namespace SparseQueue
noncomputable section

def rankZeroInstructions : List Instruction := [
  .scalar (.pointerAdd 16 13 17),.scalar (.integerStore 16 0),.scalar (.core (.pinc 17))]

def rankZeroBodyCode : MachineCode := linearCode rankZeroInstructions

def rankZeroLoopCode : MachineCode := .whilePointer 18 17 rankZeroBodyCode

def rankArrayInitializeCode : MachineCode := .seq (coreCode (.pset 0 0))
  (.seq (coreCode (.pset 17 0)) rankZeroLoopCode)

end
end SparseQueue
end NearlyOptimalPPR.Computation

-- Runtime interface from Solutions.RankQueueAllocation

set_option autoImplicit false
open scoped ENNReal
namespace NearlyOptimalPPR.Computation
namespace SparseQueue
noncomputable section

def rankQueueAllocationCode : MachineCode := .seq reserveArrayCode rankArrayInitializeCode

end
end SparseQueue
end NearlyOptimalPPR.Computation

-- Runtime interface from Solutions.HeaderQueueAllocation

set_option autoImplicit false
set_option maxRecDepth 10000
open scoped ENNReal
namespace NearlyOptimalPPR.Computation
open SparseQueue
noncomputable section

def headerQueueAllocationCode (slot : ℕ) : MachineCode := .seq rankQueueAllocationCode (levelHeaderIntegerFromCode slot 13)
end
end NearlyOptimalPPR.Computation

-- Runtime interface from Solutions.FreshQueuePair

set_option autoImplicit false
set_option maxRecDepth 10000
open scoped ENNReal
namespace NearlyOptimalPPR.Computation
open SparseQueue
noncomputable section

def freshQueuePairCode : MachineCode := .seq (headerQueueAllocationCode 7) (headerQueueAllocationCode 8)
end
end NearlyOptimalPPR.Computation

-- Runtime interface from Solutions.LevelContextPreparation

set_option autoImplicit false
namespace NearlyOptimalPPR.Computation
noncomputable section

def levelContextInstructions : List Instruction := [
  .scalar (.core (.pcopy 87 100)),.scalar (.core (.pinc 87)),
  .scalar (.pointerAdd 87 87 87),.scalar (.pointerAdd 87 87 87),
  .scalar (.pointerAdd 87 87 87),.scalar (.pointerAdd 87 87 87),
  .scalar (.core (.pcopy 89 87)),.scalar (.core (.pcopy 41 50))]
def levelContextCode : MachineCode := linearCode levelContextInstructions
def frameRankLoadInstructions : List Instruction := [
  .scalar (.core (.pset 105 5)),.scalar (.integerLoad 18 105),.scalar (.core (.pcopy 25 18))]
def frameRankLoadCode : MachineCode := linearCode frameRankLoadInstructions
end
end NearlyOptimalPPR.Computation

-- Runtime interface from Solutions.FreshHeaderCode

set_option autoImplicit false
namespace NearlyOptimalPPR.Computation
open SparseQueue
noncomputable section

def freshHeaderCode : MachineCode := .seq frameScalarParametersCode
  (.seq freshHeaderDefaultsCode (.seq frameBlockPreparationCode
    (.seq frameRankLoadCode (.seq freshQueuePairCode levelContextCode))))
end
end NearlyOptimalPPR.Computation

-- Runtime interface from Solutions.VertexAddressExecution

set_option autoImplicit false
open scoped ENNReal
namespace NearlyOptimalPPR.Computation
noncomputable section

def vertexAddressTailCode : MachineCode := sequenceCode [
  .atom (.scalar (.pointerAdd 45 42 44)),.atom (.scalar (.pointerSub 45 0 45)),coreCode (.pdec 45)]

def vertexAddressCode : MachineCode := .seq integerScaleCode vertexAddressTailCode

end
end NearlyOptimalPPR.Computation

-- Runtime interface from Solutions.VertexRecordAccess

set_option autoImplicit false
open scoped ENNReal
namespace NearlyOptimalPPR.Computation
noncomputable section

def vertexRealLoadCode : MachineCode := .seq vertexAddressCode (coreCode (.load 10 45))
def vertexRealStoreCode : MachineCode := .seq vertexAddressCode (coreCode (.store 45 10))
def vertexIntegerLoadCode : MachineCode := .seq vertexAddressCode (.atom (.scalar (.integerLoad 51 45)))
def vertexIntegerStoreCode : MachineCode := .seq vertexAddressCode (.atom (.scalar (.integerStore 45 51)))

end
end NearlyOptimalPPR.Computation

-- Runtime interface from Solutions.VertexFieldWrite

set_option autoImplicit false
open scoped ENNReal
namespace NearlyOptimalPPR.Computation
noncomputable section

def fieldWritePrepRoutine (field source : ℕ) : PointerRoutine := .sequence [
  .atom (.copy 51 source),.atom (.set 44 field)]

def vertexFieldWriteCode (field source : ℕ) : MachineCode :=
  .seq (fieldWritePrepRoutine field source).code vertexIntegerStoreCode

end
end NearlyOptimalPPR.Computation

-- Runtime interface from Solutions.AdjacencyMetadata

set_option autoImplicit false
open scoped ENNReal
namespace NearlyOptimalPPR.Computation
noncomputable section

def adjacencyMetadataCode : MachineCode := .seq (vertexFieldWriteCode 0 60)
  (.seq (vertexFieldWriteCode 1 61) (.seq (coreCode (.pset 51 1)) (vertexFieldWriteCode 2 51)))

end
end NearlyOptimalPPR.Computation

-- Runtime interface from Solutions.AdjacencyFetchCode

set_option autoImplicit false
namespace NearlyOptimalPPR.Computation
noncomputable section


def adjacencyFetchBodyCode : MachineCode := sequenceCode [
  .atom (.scalar (.nbr 63 40 62)),.atom (.scalar (.pointerAdd 64 61 62)),
  .atom (.scalar (.integerStore 64 63)),coreCode (.pinc 62)]

def adjacencyFetchLoopCode : MachineCode := .whilePointer 60 62 adjacencyFetchBodyCode

end
end NearlyOptimalPPR.Computation

-- Runtime interface from Solutions.AdjacencyFetchLoop

set_option autoImplicit false
open scoped ENNReal
namespace NearlyOptimalPPR.Computation
open SparseQueue
noncomputable section

def AdjacencyStored {n : ℕ} (I : ℤ → ℤ) (base : ℤ) (neighbors : List (Fin n)) (upto : ℕ) : Prop :=
  ∀ i < upto, ∀ hi : i < neighbors.length, I (base+(i : ℤ))=(neighbors[i].val : ℤ)

end
end NearlyOptimalPPR.Computation

-- Runtime interface from Solutions.AdjacencyStorage

set_option autoImplicit false
open scoped ENNReal
namespace NearlyOptimalPPR.Computation
open SparseQueue
noncomputable section

def adjacencyReserveRoutine : PointerRoutine := .sequence [
  .atom (.copy 61 20),.atom (.add 20 20 60),.atom (.set 62 0)]

def adjacencyStorageCode : MachineCode := .seq (.atom (.scalar (.deg 60 40)))
  (.seq adjacencyReserveRoutine.code adjacencyFetchLoopCode)

end
end NearlyOptimalPPR.Computation

-- Runtime interface from Solutions.AdjacencyMetadataSemantics

set_option autoImplicit false
namespace NearlyOptimalPPR.Computation
open SparseQueue
noncomputable section

structure GraphCache {n : ℕ} (g : InputGraph n) (I : ℤ → ℤ) (width : ℕ)
    (stored : Finset (Fin n)) (free : ℤ) : Prop where
  widthBound : 3 ≤ width
  freeBound : 128 ≤ free
  flag : ∀ v : Fin n, I (vertexRecordAddress width v.val 2)=if v ∈ stored then 1 else 0
  degree : ∀ v ∈ stored, I (vertexRecordAddress width v.val 0)=((g.neighbors v).length : ℤ)
  basePositive : ∀ v ∈ stored, 128 ≤ I (vertexRecordAddress width v.val 1)
  adjacency : ∀ v ∈ stored, AdjacencyStored I (I (vertexRecordAddress width v.val 1)) (g.neighbors v) (g.neighbors v).length
  belowFree : ∀ v ∈ stored, ∀ i < (g.neighbors v).length,
    I (vertexRecordAddress width v.val 1)+(i : ℤ) < free

end
end NearlyOptimalPPR.Computation

-- Runtime interface from Solutions.VertexFieldMemory

set_option autoImplicit false
namespace NearlyOptimalPPR.Computation
noncomputable section

def QueuedFlags {n : ℕ} (I : ℤ → ℤ) (width offset : ℕ) (domain : Finset (Fin n)) (queued : Finset ℕ) : Prop :=
  ∀ v ∈ domain, I (vertexRecordAddress width v.val offset)=if v.val ∈ queued then 1 else 0

end
end NearlyOptimalPPR.Computation

-- Runtime interface from Solutions.HeapDetachCode

set_option autoImplicit false
namespace NearlyOptimalPPR.Computation
noncomputable section


def heapDetachCode : MachineCode := sequenceCode [
  coreCode (.pset 0 0),coreCode (.pcopy 23 5),coreCode (.pinc 23),coreCode (.pinc 23),
  .atom (.scalar (.integerLoad 22 23)),.atom (.scalar (.integerStore 23 0))]

end
end NearlyOptimalPPR.Computation

-- Runtime interface from Solutions.RankQueueMass

set_option autoImplicit false
namespace NearlyOptimalPPR.Computation
namespace SparseQueue
open Batteries.BinomialHeap.Imp
noncomputable section
open Finset

def slotKeySet (slots : RankSlots) (length : ℕ) : Finset ℕ :=
  (range length).biUnion (fun r => (slots r).elim ∅ RankedTree.support)

def slotMass (slots : RankSlots) (length : ℕ) : ℕ :=
  ∑ r ∈ range length, (slots r).elim 0 RankedTree.size

end
end SparseQueue
end NearlyOptimalPPR.Computation

-- Runtime interface from Solutions.HeapDrainCode

set_option autoImplicit false
namespace NearlyOptimalPPR.Computation
noncomputable section

def heapDrainPrefixCode : MachineCode := sequenceCode [
  coreCode (.pcopy 5 22),coreCode (.pdec 24),coreCode (.pcopy 14 24)]

def heapDrainBodyCode : MachineCode := sequenceCode [heapDrainPrefixCode,heapDetachCode,heapCarryCode]

def heapDrainCode : MachineCode := .whilePointer 22 0 heapDrainBodyCode

end
end NearlyOptimalPPR.Computation

-- Runtime interface from Solutions.HeapDeletePreparation

set_option autoImplicit false
namespace NearlyOptimalPPR.Computation
namespace SparseQueue
noncomputable section

def heapDeletePrefixRoutine : PointerRoutine := .sequence [
  .atom (.copy 5 27),.atom (.copy 24 28),.atom (.copy 23 5),.atom (.inc 23),
  .atom (.load 22 23),.atom (.add 15 13 28)]

def heapDeletePrepareCode : MachineCode := .seq heapDeletePrefixRoutine.code (.atom (.scalar (.integerStore 15 0)))

def heapDeleteOccupiedCode : MachineCode := .seq heapDeletePrepareCode heapDrainCode

def heapPopCode : MachineCode := .seq heapMinScanCode (.branchPointer 27 0 .skip heapDeleteOccupiedCode)

end
end SparseQueue
end NearlyOptimalPPR.Computation

-- Runtime interface from Solutions.VertexFieldRead

set_option autoImplicit false
open scoped ENNReal
namespace NearlyOptimalPPR.Computation
noncomputable section

def vertexFieldReadCode (field destination : ℕ) : MachineCode := .seq (coreCode (.pset 44 field))
  (.seq vertexIntegerLoadCode (coreCode (.pcopy destination 51)))

end
end NearlyOptimalPPR.Computation

-- Runtime interface from Solutions.GraphCacheRead

set_option autoImplicit false
open scoped ENNReal
namespace NearlyOptimalPPR.Computation
noncomputable section

def cacheReadCode : MachineCode := .seq (vertexFieldReadCode 0 60) (vertexFieldReadCode 1 61)

end
end NearlyOptimalPPR.Computation

-- Runtime interface from Solutions.ExteriorEligibility

set_option autoImplicit false
open scoped ENNReal
namespace NearlyOptimalPPR.Computation
noncomputable section

def exteriorActiveOffsetRoutine : PointerRoutine := .sequence [
  .atom (.copy 44 87),.atom (.inc 44),.atom (.inc 44)]

def exteriorResidualOffsetRoutine : PointerRoutine := .sequence [
  .atom (.copy 44 87),.atom (.inc 44)]

def exteriorDegreeProductInstructions : List Instruction := [
  .scalar (.pointerReal 10 60),RealOperation.mul.instruction 22 20 10]

def exteriorDegreeProductCode : MachineCode := linearCode exteriorDegreeProductInstructions

def exteriorInactiveCode : MachineCode := .seq (vertexFieldReadCode 0 60)
  (.seq exteriorDegreeProductCode (.seq exteriorResidualOffsetRoutine.code
    (.seq vertexRealLoadCode (.atom (RealOperation.sub.instruction 23 10 22)))))


def exteriorEligibilityCode : MachineCode := .seq exteriorActiveOffsetRoutine.code
  (.seq vertexIntegerLoadCode (.branchPointer 51 0 exteriorInactiveCode (coreCode (.const 23 0))))

end
end NearlyOptimalPPR.Computation

-- Runtime interface from Solutions.VertexFlagClear

set_option autoImplicit false
open scoped ENNReal
namespace NearlyOptimalPPR.Computation
open SparseQueue
noncomputable section

def vertexFlagClearCode : MachineCode := .seq (coreCode (.pcopy 44 88))
  (.seq (coreCode (.pcopy 51 0)) vertexIntegerStoreCode)

end
end NearlyOptimalPPR.Computation

-- Runtime interface from Solutions.HeapCleanCode

set_option autoImplicit false
namespace NearlyOptimalPPR.Computation
namespace SparseQueue
noncomputable section


def heapCleanEmptyCode : MachineCode := .seq (coreCode (.const 24 0)) (coreCode (.pset 97 0))

def heapCleanFoundCode : MachineCode := .seq (coreCode (.const 24 0)) (coreCode (.pset 97 1))

def heapCleanDecisionCode : MachineCode := .branchReal 23 .skip heapCleanFoundCode

def heapCleanBodyCode (test : MachineCode) : MachineCode := .seq heapPopCode
  (.seq (coreCode (.pset 0 0)) (.branchPointer 27 0 heapCleanEmptyCode
    (.seq (coreCode (.pcopy 40 31)) (.seq test heapCleanDecisionCode))))

def heapCleanCode (test : MachineCode) : MachineCode := .seq (coreCode (.const 24 1))
  (.whileReal 24 (heapCleanBodyCode test))

def exteriorQueuedTestCode : MachineCode := .seq (coreCode (.pcopy 41 50))
  (.seq exteriorEligibilityCode vertexFlagClearCode)

def exteriorQueueCleanCode : MachineCode := heapCleanCode exteriorQueuedTestCode

end
end SparseQueue
end NearlyOptimalPPR.Computation

-- Runtime interface from Solutions.ExteriorQueueMemory

set_option autoImplicit false
namespace NearlyOptimalPPR.Computation
namespace SparseQueue
noncomputable section

structure ExteriorQueueMemory {n : ℕ} (I : ℤ → ℤ) (R : ℤ → ℝ)
    (width levelBase flagOffset : ℕ) (q : ℝ) (domain : Finset (Fin n)) (valid queued : Finset ℕ) : Prop where
  queuedDomain : queued ⊆ domain.image Fin.val
  flags : QueuedFlags I width flagOffset domain queued
  activeNonnegative : ∀ v ∈ domain, 0 ≤ I (vertexRecordAddress width v.val (levelBase+2))
  eligibility : ∀ v ∈ domain, v.val ∈ valid ↔
    I (vertexRecordAddress width v.val (levelBase+2))=0 ∧
      q*(I (vertexRecordAddress width v.val 0) : ℝ) < R (vertexRecordAddress width v.val (levelBase+1))

end
end SparseQueue
end NearlyOptimalPPR.Computation

-- Runtime interface from Solutions.HighQueueMemory

set_option autoImplicit false
namespace NearlyOptimalPPR.Computation
namespace SparseQueue
noncomputable section


def HighBooleanRecords {n : ℕ} (I : ℤ → ℤ) (R : ℤ → ℝ) (width levelBase : ℕ)
    (theta : ℝ) (domain : Finset (Fin n)) : Prop :=
  ∀ v ∈ domain, R (vertexRecordAddress width v.val (levelBase+4))=
    if I (vertexRecordAddress width v.val (levelBase+2))=0 then 0 else
      if 3*theta*(I (vertexRecordAddress width v.val 0) : ℝ) ≤ R (vertexRecordAddress width v.val (levelBase+1)) then 1 else 0

end
end SparseQueue
end NearlyOptimalPPR.Computation

-- Runtime interface from Solutions.RankQueueObject

set_option autoImplicit false
namespace NearlyOptimalPPR.Computation
namespace SparseQueue
noncomputable section


structure RankQueueObject (I : ℤ → ℤ) (base : ℤ) (length : ℕ) (free floor : ℤ) where
  slots : RankSlots
  roots : ℕ → ℤ
  feet : ℕ → Finset ℤ
  representation : RankArrayRep I base length slots roots feet
  unique : (slotKeySet slots length).card=slotMass slots length
  below : ∀ z ∈ queueCells base length feet, z < free
  above : ∀ z ∈ queueCells base length feet, floor ≤ z

namespace RankQueueObject

def cells {I : ℤ → ℤ} {base : ℤ} {length : ℕ} {free floor : ℤ}
    (obj : RankQueueObject I base length free floor) : Finset ℤ := queueCells base length obj.feet
def keys {I : ℤ → ℤ} {base : ℤ} {length : ℕ} {free floor : ℤ}
    (obj : RankQueueObject I base length free floor) : Finset ℕ := slotKeySet obj.slots length
def mass {I : ℤ → ℤ} {base : ℤ} {length : ℕ} {free floor : ℤ}
    (obj : RankQueueObject I base length free floor) : ℕ := slotMass obj.slots length

end RankQueueObject

end
end SparseQueue
end NearlyOptimalPPR.Computation

-- Runtime interface from Solutions.KeyListRepresentation

set_option autoImplicit false
namespace NearlyOptimalPPR.Computation
namespace SparseQueue
open Batteries.BinomialHeap.Imp
noncomputable section


def keyListForest : List ℕ → HeapNode ℕ
  | [] => .nil
  | k::ks => .node k .nil (keyListForest ks)

def KeyListRep (I : ℤ → ℤ) (head : ℤ) (keys : List ℕ) (F : Finset ℤ) : Prop :=
  ForestRep I head (keyListForest keys) F

end
end SparseQueue
end NearlyOptimalPPR.Computation

-- Runtime interface from Solutions.IndexMarkCode

set_option autoImplicit false
open scoped ENNReal
namespace NearlyOptimalPPR.Computation
noncomputable section


def indexMarkCode : MachineCode := .seq (vertexFieldWriteCode 7 53)
  (.seq (coreCode (.pcopy 51 75)) (.seq (coreCode (.pinc 51)) (vertexFieldWriteCode 8 51)))

end
end NearlyOptimalPPR.Computation

-- Runtime interface from Solutions.IndexMarkBody

set_option autoImplicit false
open scoped ENNReal
namespace NearlyOptimalPPR.Computation
noncomputable section


def indexMarkBodyCode : MachineCode := .seq (.atom (.scalar (.pointerAdd 81 80 75)))
  (.seq (.atom (.scalar (.integerLoad 40 81))) (.seq indexMarkCode (coreCode (.pinc 75))))

def indexMarkLoopCode : MachineCode := .whilePointer 77 75 indexMarkBodyCode

end
end NearlyOptimalPPR.Computation

-- Runtime interface from Solutions.IndexMarkLoop

set_option autoImplicit false
open scoped ENNReal
namespace NearlyOptimalPPR.Computation
noncomputable section

def EnumerationStored {n k : ℕ} (I : ℤ → ℤ) (base : ℤ) (e : Fin k → Fin n) : Prop :=
  ∀ j : Fin k, I (base+(j.val : ℤ))=(e j).val

end
end NearlyOptimalPPR.Computation

-- Runtime interface from Solutions.VertexListRepresentation

set_option autoImplicit false
namespace NearlyOptimalPPR.Computation
open SparseQueue
noncomputable section

def VertexListRep {n : ℕ} (I : ℤ → ℤ) (head : ℤ) (vertices : List (Fin n)) (F : Finset ℤ) : Prop :=
  KeyListRep I head (vertices.map Fin.val) F

def vertexEnumeration {n : ℕ} (vertices : List (Fin n)) : Fin vertices.length → Fin n := fun i => vertices[i]

end
end NearlyOptimalPPR.Computation

-- Runtime interface from Solutions.RecursiveMachineMemory

set_option autoImplicit false
namespace NearlyOptimalPPR.Computation
open SparseQueue
noncomputable section

def normalizePCNumber : NormalizePC → ℕ
  | .initialDrain => 0 | .beginEpisode => 1 | .fullSolve => 2 | .normalize => 3 | .leafDrain => 4
  | .afterChild => 5 | .finishEpisode => 6 | .restartDrain => 7 | .normal => 8 | .interrupted => 9

def recursiveDegreeDomain {n : ℕ} (g : InputGraph n) (s : Fin n) (logical : RecursiveState n) : Finset (Fin n) :=
  insert s (touchedBy g logical.stored)

def cachedRowCells {n : ℕ} (g : InputGraph n) (I : ℤ → ℤ) (width : ℕ)
    (stored : Finset (Fin n)) : Finset ℤ :=
  stored.biUnion (fun v => arrayCells (I (vertexRecordAddress width v.val 1)) (g.neighbors v).length)


structure RecursiveFrameMemory {n : ℕ} (g : InputGraph n) (logical : RecursiveState n)
    (j width length : ℕ) (machine : MachineState) (floor : ℤ) where
  N : machine.scalar.core.mem (levelHeaderAddress j 0)=(logical.frames j).N
  q : machine.scalar.core.mem (levelHeaderAddress j 1)=(logical.frames j).q
  Q : machine.scalar.core.mem (levelHeaderAddress j 3)=(logical.frames j).Q
  W : machine.scalar.core.mem (levelHeaderAddress j 4)=(logical.frames j).W
  theta : machine.scalar.core.mem (levelHeaderAddress j 5)=(logical.frames j).theta
  block : machine.scalar.integerMemory (levelHeaderAddress j 14)=((logical.frames j).block : ℤ)
  pc : machine.scalar.integerMemory (levelHeaderAddress j 0)=(normalizePCNumber (logical.frames j).pc : ℤ)
  openBudget : machine.scalar.integerMemory (levelHeaderAddress j 9)=if (logical.frames j).openBudget then 1 else 0
  needFull : machine.scalar.integerMemory (levelHeaderAddress j 10)=if (logical.frames j).needFull then 1 else 0
  children : machine.scalar.integerMemory (levelHeaderAddress j 11)=((logical.frames j).childrenThisEpisode : ℤ)
  reference : ∀ v ∈ parentDomain logical j,
    machine.scalar.core.mem (vertexRecordAddress width v.val (16*(j+1)))=(logical.frames j).reference v
  residual : ∀ v ∈ parentDomain logical j,
    machine.scalar.core.mem (vertexRecordAddress width v.val (16*(j+1)+1))=(logical.frames j).residual v
  activeFlags : ∀ v ∈ parentDomain logical j,
    machine.scalar.integerMemory (vertexRecordAddress width v.val (16*(j+1)+2))=if v ∈ (logical.frames j).active then 1 else 0
  cacheFlags : ∀ v ∈ parentDomain logical j,
    machine.scalar.integerMemory (vertexRecordAddress width v.val (16*(j+1)+4))=if v ∈ (logical.frames j).cache then 1 else 0
  activeVertices : List (Fin n)
  activeFoot : Finset ℤ
  activeRep : VertexListRep machine.scalar.integerMemory (machine.scalar.integerMemory (levelHeaderAddress j 1)) activeVertices activeFoot
  activeNodup : activeVertices.Nodup
  activeSet : activeVertices.toFinset=(logical.frames j).active
  activeCount : machine.scalar.integerMemory (levelHeaderAddress j 3)=((logical.frames j).active.card : ℤ)
  activeVolume : machine.scalar.integerMemory (levelHeaderAddress j 2)=(volumeNat g (logical.frames j).active : ℤ)
  activeBelow : ∀ z ∈ activeFoot, z < machine.scalar.core.ptrs 20
  activeAbove : ∀ z ∈ activeFoot, floor ≤ z
  cacheVertices : List (Fin n)
  cacheFoot : Finset ℤ
  cacheRep : VertexListRep machine.scalar.integerMemory (machine.scalar.integerMemory (levelHeaderAddress j 4)) cacheVertices cacheFoot
  cacheNodup : cacheVertices.Nodup
  cacheSet : cacheVertices.toFinset=(logical.frames j).cache
  cacheCount : machine.scalar.integerMemory (levelHeaderAddress j 5)=((logical.frames j).cache.card : ℤ)
  cacheVolume : machine.scalar.integerMemory (levelHeaderAddress j 6)=(volumeNat g (logical.frames j).cache : ℤ)
  cacheBelow : ∀ z ∈ cacheFoot, z < machine.scalar.core.ptrs 20
  cacheAbove : ∀ z ∈ cacheFoot, floor ≤ z
  exteriorBase : ℤ
  highBase : ℤ
  exteriorPointer : machine.scalar.integerMemory (levelHeaderAddress j 7)=exteriorBase
  highPointer : machine.scalar.integerMemory (levelHeaderAddress j 8)=highBase
  exteriorObject : RankQueueObject machine.scalar.integerMemory exteriorBase length (machine.scalar.core.ptrs 20) floor
  highObject : RankQueueObject machine.scalar.integerMemory highBase length (machine.scalar.core.ptrs 20) floor
  exteriorData : ExteriorQueueMemory machine.scalar.integerMemory machine.scalar.core.mem width
    (16*(j+1)) (16*(j+1)+3) (logical.frames j).q (parentDomain logical j)
    ((logical.frames j).exterior.image Fin.val) exteriorObject.keys
  exteriorCover : (logical.frames j).exterior.image Fin.val ⊆ exteriorObject.keys
  highBoolean : HighBooleanRecords machine.scalar.integerMemory machine.scalar.core.mem width (16*(j+1))
    (logical.frames j).theta (parentDomain logical j)
  virtualExcluded : ∀ v ∈ parentDomain logical j,
    machine.scalar.integerMemory (vertexRecordAddress width v.val (16*(j+1)+5))=0
  highFlags : QueuedFlags machine.scalar.integerMemory width (16*(j+1)+6) (parentDomain logical j) highObject.keys
  highDomain : highObject.keys ⊆ (parentDomain logical j).image Fin.val
  highValid : ∀ v ∈ parentDomain logical j, v.val ∈ (logical.frames j).high.image Fin.val ↔
    machine.scalar.integerMemory (vertexRecordAddress width v.val (16*(j+1)+2)) ≠ 0 ∧
      3*(logical.frames j).theta*(machine.scalar.integerMemory (vertexRecordAddress width v.val 0) : ℝ) ≤
        machine.scalar.core.mem (vertexRecordAddress width v.val (16*(j+1)+1))
  highCover : (logical.frames j).high.image Fin.val ⊆ highObject.keys

namespace RecursiveFrameMemory

def owned {n : ℕ} {g : InputGraph n} {logical : RecursiveState n} {j width length : ℕ}
    {machine : MachineState} {floor : ℤ} (f : RecursiveFrameMemory g logical j width length machine floor) : Finset ℤ :=
  f.activeFoot ∪ f.cacheFoot ∪ f.exteriorObject.cells ∪ f.highObject.cells

def pieces {n : ℕ} {g : InputGraph n} {logical : RecursiveState n} {j width length : ℕ}
    {machine : MachineState} {floor : ℤ} (f : RecursiveFrameMemory g logical j width length machine floor) : List (Finset ℤ) :=
  [f.activeFoot,f.cacheFoot,f.exteriorObject.cells,f.highObject.cells]

end RecursiveFrameMemory

structure RecursiveMachineMemory {n : ℕ} (g : InputGraph n) (s : Fin n) (α ε : ℝ) (ell length : ℕ)
    (logical : RecursiveState n) (machine : MachineState) where
  zero : machine.scalar.core.ptrs 0=0
  top : machine.scalar.core.ptrs 100=(logical.top : ℤ)
  width : machine.scalar.core.ptrs 50=((16*(ell+3) : ℕ) : ℤ)
  alphaRegister : machine.scalar.core.regs 30=α
  one : machine.scalar.core.regs 31=1
  alphaMemory : machine.scalar.core.mem 0=α
  epsilonMemory : machine.scalar.core.mem 1=ε
  depthMemory : machine.scalar.integerMemory 2=((ell+2 : ℕ) : ℤ)
  lengthMemory : machine.scalar.integerMemory 5=(length : ℤ)
  seedMemory : machine.scalar.integerMemory 0=(s.val : ℤ)
  allocator : 128+32*((ell+2 : ℕ) : ℤ) ≤ machine.scalar.core.ptrs 20
  potential : ∀ v : Fin n, machine.scalar.core.mem (vertexRecordAddress (16*(ell+3)) v.val 0)=logical.x v
  seedMarker : ∀ v : Fin n, machine.scalar.core.mem (vertexRecordAddress (16*(ell+3)) v.val 2)=LocalPush.e s v
  boundary : machine.scalar.integerMemory 7=logical.boundaryEdges
  graphCache : GraphCache g machine.scalar.integerMemory (16*(ell+3)) logical.stored (machine.scalar.core.ptrs 20)
  rowAbove : ∀ v ∈ logical.stored,
    128+32*((ell+2 : ℕ) : ℤ) ≤ machine.scalar.integerMemory (vertexRecordAddress (16*(ell+3)) v.val 1)
  knownDegree : ∀ v ∈ recursiveDegreeDomain g s logical,
    machine.scalar.integerMemory (vertexRecordAddress (16*(ell+3)) v.val 0)=((g.neighbors v).length : ℤ)
  unknownDegree : ∀ v ∉ recursiveDegreeDomain g s logical,
    machine.scalar.integerMemory (vertexRecordAddress (16*(ell+3)) v.val 0)=0
  frames : ∀ j ≤ logical.top, RecursiveFrameMemory g logical j (16*(ell+3)) length machine (128+32*((ell+2 : ℕ) : ℤ))
  pieceSeparation : ∀ j, ∀ hj : j ≤ logical.top,
    ((frames j hj).pieces).Pairwise Disjoint
  frameSeparation : ∀ i, ∀ hi : i ≤ logical.top, ∀ j, ∀ hj : j ≤ logical.top, i ≠ j →
    Disjoint (frames i hi).owned (frames j hj).owned
  cacheSeparation : ∀ j, ∀ hj : j ≤ logical.top,
    Disjoint (frames j hj).owned (cachedRowCells g machine.scalar.integerMemory (16*(ell+3)) logical.stored)
  output : machine.output=[]

end
end NearlyOptimalPPR.Computation

-- Runtime interface from Solutions.ChildState

set_option autoImplicit false
namespace NearlyOptimalPPR.Computation
noncomputable section


def spawnChildState {n : ℕ} (g : InputGraph n) (ell : ℕ) (logical : RecursiveState n) : RecursiveState n :=
  let j := logical.top
  let f := logical.frames j
  let c := freshFrame g [] ell (j+1) logical.nextId f.block f.theta f.active logical.x f.residual
  let u := debit logical j (16*(volumeNat g f.active+1)*keyCost logical+8*(ell+2)*(f.block+2) : ℕ)
  let u := changeFrame u j (fun fc => {fc with pc := .afterChild,childrenThisEpisode := fc.childrenThisEpisode+1})
  {u with
    top := j+1
    nextId := logical.nextId+1
    frames := Function.update u.frames (j+1) c
    information := Function.update u.information c.id (some ⟨j+1,f.block,c.block⟩)}

end
end NearlyOptimalPPR.Computation

-- Runtime interface from Solutions.QueuePotential

set_option autoImplicit false
namespace NearlyOptimalPPR.Computation
noncomputable section

def RecursiveFrameMemory.queueMass {n : ℕ} {g : InputGraph n} {logical : RecursiveState n}
    {j width length : ℕ} {machine : MachineState} {floor : ℤ}
    (frame : RecursiveFrameMemory g logical j width length machine floor) : ℕ :=
  frame.exteriorObject.mass+frame.highObject.mass

def RecursiveMachineMemory.queueMass {n : ℕ} {g : InputGraph n} {s : Fin n} {α ε : ℝ}
    {ell length : ℕ} {logical : RecursiveState n} {machine : MachineState}
    (memory : RecursiveMachineMemory g s α ε ell length logical machine) : ℕ :=
  ∑ i ∈ Finset.range (logical.top+1), if hi : i ≤ logical.top then (memory.frames i hi).queueMass else 0

end
end NearlyOptimalPPR.Computation

-- Runtime interface from Solutions.ExteriorQueueCleanLoop

set_option autoImplicit false
set_option maxRecDepth 10000
open scoped ENNReal
namespace NearlyOptimalPPR.Computation
namespace SparseQueue
noncomputable section

def cleanBodyBound (width length R : ℕ) : ℕ := 14*length+(21*R+16)*R+15+16*width+50

end
end SparseQueue
end NearlyOptimalPPR.Computation

-- Runtime interface from Solutions.ExteriorCleanObject

set_option autoImplicit false
set_option maxRecDepth 10000
open scoped ENNReal
namespace NearlyOptimalPPR.Computation
namespace SparseQueue
noncomputable section

def exteriorCleanObjectCode : MachineCode := .seq exteriorQueueCleanCode (coreCode (.pset 0 0))
end
end SparseQueue
end NearlyOptimalPPR.Computation

-- Runtime interface from Solutions.HeapNodeAllocation

set_option autoImplicit false
namespace NearlyOptimalPPR.Computation
namespace SparseQueue
noncomputable section

def heapNodeAllocCode : MachineCode := sequenceCode [
  coreCode (.pset 0 0),coreCode (.pcopy 5 20),.atom (.scalar (.integerStore 5 4)),
  coreCode (.pinc 20),.atom (.scalar (.integerStore 20 0)),
  coreCode (.pinc 20),.atom (.scalar (.integerStore 20 0)),coreCode (.pinc 20)]

end
end SparseQueue
end NearlyOptimalPPR.Computation

-- Runtime interface from Solutions.HeapInsertExecution

set_option autoImplicit false
open scoped ENNReal
namespace NearlyOptimalPPR.Computation
namespace SparseQueue
noncomputable section

def heapInsertCode : MachineCode := .seq heapNodeAllocCode
  (.seq (coreCode (.pcopy 14 0)) heapCarryCode)

end
end SparseQueue
end NearlyOptimalPPR.Computation

-- Runtime interface from Solutions.VertexFlagSet

set_option autoImplicit false
open scoped ENNReal
namespace NearlyOptimalPPR.Computation
noncomputable section

def vertexFlagSetCode : MachineCode := .seq (coreCode (.pcopy 44 88))
  (.seq (coreCode (.pset 51 1)) vertexIntegerStoreCode)

end
end NearlyOptimalPPR.Computation

-- Runtime interface from Solutions.FlaggedHeapInsert

set_option autoImplicit false
set_option maxRecDepth 10000
open scoped ENNReal
namespace NearlyOptimalPPR.Computation
namespace SparseQueue
noncomputable section

def flaggedHeapInsertCode : MachineCode := .seq (coreCode (.pcopy 4 40))
  (.seq heapInsertCode (.seq (coreCode (.pset 0 0)) vertexFlagSetCode))

end
end SparseQueue
end NearlyOptimalPPR.Computation

-- Runtime interface from Solutions.QueuedFlagRead

set_option autoImplicit false
open scoped ENNReal
namespace NearlyOptimalPPR.Computation
noncomputable section

def queuedFlagReadCode : MachineCode := .seq (coreCode (.pcopy 44 88)) vertexIntegerLoadCode

end
end NearlyOptimalPPR.Computation

-- Runtime interface from Solutions.QueuedInsertCode

set_option autoImplicit false
set_option maxRecDepth 10000
open scoped ENNReal
namespace NearlyOptimalPPR.Computation
namespace SparseQueue
noncomputable section

def queuedInsertCode : MachineCode := .seq queuedFlagReadCode (.branchPointer 51 0 flaggedHeapInsertCode .skip)

end
end SparseQueue
end NearlyOptimalPPR.Computation

-- Runtime interface from Solutions.ExteriorQueueRefreshCode

set_option autoImplicit false
namespace NearlyOptimalPPR.Computation
namespace SparseQueue
noncomputable section

def exteriorQueueRefreshCode : MachineCode := .seq (coreCode (.pcopy 41 50))
  (.seq exteriorEligibilityCode (.branchReal 23 .skip queuedInsertCode))

end
end SparseQueue
end NearlyOptimalPPR.Computation

-- Runtime interface from Solutions.ExteriorPeekObject

set_option autoImplicit false
set_option maxRecDepth 10000
open scoped ENNReal
namespace NearlyOptimalPPR.Computation
namespace SparseQueue
noncomputable section

def exteriorPeekObjectCode : MachineCode := .seq exteriorCleanObjectCode
  (.branchPointer 97 0 .skip exteriorQueueRefreshCode)
end
end SparseQueue
end NearlyOptimalPPR.Computation

-- Runtime interface from Solutions.LevelHeaderTo

set_option autoImplicit false
namespace NearlyOptimalPPR.Computation
noncomputable section

def levelHeaderIntegerToCode (slot target : ℕ) : MachineCode :=
  .seq (levelHeaderIntegerLoadCode slot) (coreCode (.pcopy target 105))
def levelHeaderRealToCode (slot target : ℕ) : MachineCode :=
  .seq (levelHeaderRealLoadCode slot) (coreCode (.mul target 10 31))
end
end NearlyOptimalPPR.Computation

-- Runtime interface from Solutions.LevelVertexFlagClear

set_option autoImplicit false
open scoped ENNReal
namespace NearlyOptimalPPR.Computation
noncomputable section

def levelVertexOffsetInstructions (offset : ℕ) : List Instruction := [
  .scalar (.core (.pset 88 offset)),.scalar (.pointerAdd 88 87 88)]
def levelVertexOffsetCode (offset : ℕ) : MachineCode := linearCode (levelVertexOffsetInstructions offset)
def levelVertexFlagClearCode (offset : ℕ) : MachineCode := .seq (levelVertexOffsetCode offset) vertexFlagClearCode
end
end NearlyOptimalPPR.Computation

-- Runtime interface from Solutions.FrameQueueContext

set_option autoImplicit false
namespace NearlyOptimalPPR.Computation
noncomputable section

def frameQueueContextCode (queueSlot scalarSlot : ℕ) : MachineCode := .seq levelContextCode
  (.seq (levelHeaderIntegerToCode queueSlot 13) (.seq frameRankLoadCode (levelHeaderRealToCode scalarSlot 20)))
def exteriorFrameContextCode : MachineCode := .seq (frameQueueContextCode 7 1) (levelVertexOffsetCode 3)
end
end NearlyOptimalPPR.Computation

-- Runtime interface from Solutions.PeekLevelExecution

set_option autoImplicit false
set_option maxRecDepth 10000
open scoped ENNReal
namespace NearlyOptimalPPR.Computation
open SparseQueue
noncomputable section

def peekLevelPrefixInstructions : List Instruction := [
  .scalar (.core (.pcopy 108 100)),.scalar (.core (.pcopy 100 109))]
def peekLevelPrefixCode : MachineCode := linearCode peekLevelPrefixInstructions
def peekLevelCode : MachineCode := .seq peekLevelPrefixCode
  (.seq exteriorFrameContextCode (.seq exteriorPeekObjectCode (coreCode (.pcopy 100 108))))
end
end NearlyOptimalPPR.Computation

-- Runtime interface from Solutions.PriorityAdvance

set_option autoImplicit false
set_option maxRecDepth 10000
open scoped ENNReal
namespace NearlyOptimalPPR.Computation
noncomputable section

def priorityFoundCode : MachineCode := .seq (coreCode (.pcopy 112 109)) (coreCode (.pcopy 109 111))
def priorityAdvanceCode : MachineCode := .branchPointer 97 0 (coreCode (.pinc 109)) priorityFoundCode
def priorityBodyCode : MachineCode := .seq peekLevelCode priorityAdvanceCode
def priorityLoopCode : MachineCode := .whilePointer 111 109 priorityBodyCode
def priorityInitInstructions : List Instruction := [
  .scalar (.core (.pcopy 111 100)),.scalar (.core (.pinc 111)),
  .scalar (.core (.pset 109 0)),.scalar (.core (.pset 112 (-1))),.scalar (.core (.pset 97 0))]
def priorityInitCode : MachineCode := linearCode priorityInitInstructions
def priorityCode : MachineCode := .seq priorityInitCode priorityLoopCode

end
end NearlyOptimalPPR.Computation

-- Runtime interface from Solutions.FIFOTailLink

set_option autoImplicit false
open scoped ENNReal
namespace NearlyOptimalPPR.Computation
namespace SparseQueue
noncomputable section

def fifoTailLinkInstructions : List Instruction := [
  .scalar (.core (.pcopy 7 91)),.scalar (.core (.pinc 7)),.scalar (.core (.pinc 7)),.scalar (.integerStore 7 5)]

def fifoTailLinkCode : MachineCode := linearCode fifoTailLinkInstructions

def fifoAppendBranchCode : MachineCode := .branchPointer 90 0 (coreCode (.pcopy 90 5)) fifoTailLinkCode

end
end SparseQueue
end NearlyOptimalPPR.Computation

-- Runtime interface from Solutions.FIFOAppendExecution

set_option autoImplicit false
open scoped ENNReal
namespace NearlyOptimalPPR.Computation
namespace SparseQueue
noncomputable section

def fifoAppendCode : MachineCode := .seq heapNodeAllocCode (.seq fifoAppendBranchCode (coreCode (.pcopy 91 5)))

end
end SparseQueue
end NearlyOptimalPPR.Computation

-- Runtime interface from Solutions.FIFOPopExecution

set_option autoImplicit false
open scoped ENNReal
namespace NearlyOptimalPPR.Computation
namespace SparseQueue
noncomputable section

def fifoPopHeadInstructions : List Instruction := [
  .scalar (.integerLoad 40 90),.scalar (.core (.pcopy 7 90)),.scalar (.core (.pinc 7)),
  .scalar (.core (.pinc 7)),.scalar (.integerLoad 90 7)]

def fifoPopHeadCode : MachineCode := linearCode fifoPopHeadInstructions

def fifoPopCode : MachineCode := .seq fifoPopHeadCode (.branchPointer 90 0 (coreCode (.pset 91 0)) .skip)

end
end SparseQueue
end NearlyOptimalPPR.Computation

-- Runtime interface from Solutions.PriorityLoopExecution

set_option autoImplicit false
set_option maxRecDepth 10000
open scoped ENNReal
namespace NearlyOptimalPPR.Computation
open SparseQueue
noncomputable section

def PendingSelectionSpec {n : ℕ} (logical : RecursiveState n) (out : MachineState) : Prop :=
  match pendingPush logical with
  | none => out.scalar.core.ptrs 97=0 ∧ out.scalar.core.ptrs 112=(-1)
  | some (t,v) => out.scalar.core.ptrs 97=1 ∧ out.scalar.core.ptrs 112=(t : ℤ) ∧ out.scalar.core.ptrs 40=(v.val : ℤ)

end
end NearlyOptimalPPR.Computation

-- Runtime interface from Solutions.EpochInvariant

set_option autoImplicit false
namespace NearlyOptimalPPR.Computation
noncomputable section

def EpochInvariant {n : ℕ} (width : ℕ) (st : MachineState) : Prop :=
  ∀ v : Fin n, st.scalar.integerMemory (vertexRecordAddress width v.val 7) ≤ st.scalar.core.ptrs 53

end
end NearlyOptimalPPR.Computation

-- Runtime interface from Solutions.ControllerMemory

set_option autoImplicit false
namespace NearlyOptimalPPR.Computation
noncomputable section


structure ControllerMemory {n : ℕ} (g : InputGraph n) (s : Fin n) (α ε : ℝ) (ell length : ℕ)
    (logical : RecursiveState n) (st : MachineState) where
  one : st.scalar.core.ptrs 151=1
  doneFlag : st.scalar.core.ptrs 150=if logical.done then 1 else 0
  halted : st.scalar.halted=false
  live : ∀ h : logical.done=false, RecursiveMachineMemory g s α ε ell length logical st
  epoch : logical.done=false → EpochInvariant (n:=n) (16*(ell+3)) st
  output : logical.done=true → outputVector (n:=n) st.output=outputVector (n:=n) logical.output

def ControllerMemory.mass {n : ℕ} {g : InputGraph n} {s : Fin n} {α ε : ℝ} {ell length : ℕ}
    {logical : RecursiveState n} {st : MachineState} (memory : ControllerMemory g s α ε ell length logical st) : ℕ :=
  if h : logical.done=false then (memory.live h).queueMass else 0

end
end NearlyOptimalPPR.Computation

-- Runtime interface from Solutions.ControllerCachePotential

set_option autoImplicit false
namespace NearlyOptimalPPR.Computation
noncomputable section

def recursiveCacheMass {n : ℕ} (logical : RecursiveState n) : ℕ :=
  ∑ i ∈ Finset.range (logical.top+1), (logical.frames i).cache.card

def ControllerMemory.potential {n : ℕ} {g : InputGraph n} {s : Fin n} {α ε : ℝ} {ell length : ℕ}
    {logical : RecursiveState n} {st : MachineState} (memory : ControllerMemory g s α ε ell length logical st)
    (P Q : ℕ) : ℕ := P*memory.mass+(if logical.done then 0 else Q*recursiveCacheMass logical)

end
end NearlyOptimalPPR.Computation

-- Runtime interface from Solutions.BudgetScanCode

set_option autoImplicit false
namespace NearlyOptimalPPR.Computation
noncomputable section

def budgetScanMarkCode : MachineCode := .seq (levelHeaderRealToCode 3 60)
  (.seq (levelHeaderRealToCode 4 61) (.seq (coreCode (.sub 62 60 61))
    (.branchReal 62 (coreCode (.pset 160 1)) .skip)))
def budgetScanBodyCode : MachineCode := .seq (levelHeaderIntegerToCode 9 166)
  (.seq (.branchPointer 166 0 .skip budgetScanMarkCode) (coreCode (.pinc 100)))
def budgetScanLoopCode : MachineCode := .whilePointer 164 100 budgetScanBodyCode

def budgetScanInitRoutine : PointerRoutine := .sequence [
  .atom (.copy 165 100),.atom (.set 100 0),.atom (.set 160 0)]
def budgetScanCode : MachineCode := .seq budgetScanInitRoutine.code
  (.seq budgetScanLoopCode (coreCode (.pcopy 100 165)))

end
end NearlyOptimalPPR.Computation

-- Runtime interface from Solutions.BudgetCheckExecution

set_option autoImplicit false
set_option maxRecDepth 10000
namespace NearlyOptimalPPR.Computation
noncomputable section
attribute [local instance] Classical.propDecidable

def budgetCheckPrefixRoutine (ancestorsOnly : Bool) : PointerRoutine := .sequence
  ([.atom (.copy 164 100)] ++ if ancestorsOnly then [] else [.atom (.inc 164)])
def budgetCheckCode (ancestorsOnly : Bool) : MachineCode := .seq (budgetCheckPrefixRoutine ancestorsOnly).code budgetScanCode

end
end NearlyOptimalPPR.Computation

-- Runtime interface from Solutions.BudgetStatusExecution

set_option autoImplicit false
set_option maxRecDepth 10000
namespace NearlyOptimalPPR.Computation
noncomputable section
attribute [local instance] Classical.propDecidable

def budgetStatusCode : MachineCode := .seq (budgetCheckCode true)
  (.seq (coreCode (.pcopy 170 160)) (budgetCheckCode false))
end
end NearlyOptimalPPR.Computation

-- Runtime interface from Solutions.ControllerBudgetFlags

set_option autoImplicit false
namespace NearlyOptimalPPR.Computation
noncomputable section
attribute [local instance] Classical.propDecidable

def ControllerBudgetFlags {n : ℕ} (logical : RecursiveState n) (st : MachineState) : Prop :=
  st.scalar.core.ptrs 160=(if anyExhausted logical then 1 else 0) ∧
  st.scalar.core.ptrs 170=(if ancestorExhausted logical then 1 else 0)

end
end NearlyOptimalPPR.Computation

-- Runtime interface from Solutions.ControllerPriorityChoice

set_option autoImplicit false
set_option maxRecDepth 10000
open scoped ENNReal
namespace NearlyOptimalPPR.Computation
open SparseQueue
noncomputable section

def compilerPriorityChoice {n : ℕ} (logical no yes : RecursiveState n) : RecursiveState n :=
  if (pendingPush logical).isSome then yes else no

def controllerPriorityCharge {n : ℕ} (logical : RecursiveState n) (ell length rank : ℕ) (no yes : ℝ≥0∞) : ℝ≥0∞ :=
  let P := cleanBodyBound (16*(ell+3)) length rank+2
  let T := (logical.top+1)*(2*P+(21*rank+20*(16*(ell+3))+70)+50)+6
  ((T : ℕ) : ℝ≥0∞)+(if (pendingPush logical).isSome then yes else no)+2

end
end NearlyOptimalPPR.Computation

-- Runtime interface from Solutions.CompilerBeginEpisodeSource

set_option autoImplicit false
set_option maxRecDepth 10000
namespace NearlyOptimalPPR.Computation
noncomputable section

def compilerBeginEpisode {n : ℕ} (m : SolveModel) (g : InputGraph n) (logical : RecursiveState n) : RecursiveState n :=
  let j := logical.top
  let f := logical.frames j
  let Q := max (∑ v ∈ f.active, f.residual v) (f.q*(f.block : ℝ))
  let theta := Q/(f.block : ℝ)
  let charged := debit logical j (16*(volumeNat g f.active+1)*keyCost logical : ℕ)
  changeFrame {charged with episodes := Function.update charged.episodes f.id (charged.episodes f.id+1)} j
    (fun fc => {fc with Q := Q,W := 0,theta := theta,openBudget := true,childrenThisEpisode := 0,cache := ∅,high := f.active.filter (fun v => 3*theta*LocalPush.deg g.graph v ≤ f.residual v),pc := if f.needFull then .fullSolve else .normalize})

end
end NearlyOptimalPPR.Computation

-- Runtime interface from Solutions.GraphCacheFresh

set_option autoImplicit false
open scoped ENNReal
namespace NearlyOptimalPPR.Computation
open SparseQueue
noncomputable section

def cacheFreshCode : MachineCode := .seq adjacencyStorageCode adjacencyMetadataCode

end
end NearlyOptimalPPR.Computation

-- Runtime interface from Solutions.GraphCacheCheck

set_option autoImplicit false
open scoped ENNReal
namespace NearlyOptimalPPR.Computation
noncomputable section

def cacheCheckPrepRoutine : PointerRoutine := .sequence [.atom (.copy 41 50),.atom (.set 44 2)]
def cacheCheckCode : MachineCode := .seq cacheCheckPrepRoutine.code vertexIntegerLoadCode

end
end NearlyOptimalPPR.Computation

-- Runtime interface from Solutions.GraphCacheExecution

set_option autoImplicit false
open scoped ENNReal
namespace NearlyOptimalPPR.Computation
open SparseQueue
noncomputable section

def cacheRowCode : MachineCode := .seq cacheCheckCode (.branchPointer 51 0 cacheFreshCode cacheReadCode)

end
end NearlyOptimalPPR.Computation

-- Runtime interface from Solutions.SetNeedFullSource

set_option autoImplicit false
namespace NearlyOptimalPPR.Computation
noncomputable section

def compilerSetNeedFull {n : ℕ} (logical : RecursiveState n) (need : Bool) : RecursiveState n :=
  changeFrame logical logical.top (fun f => {f with needFull := need})

end
end NearlyOptimalPPR.Computation

-- Runtime interface from Solutions.CompilerFinishRequestSource

set_option autoImplicit false
namespace NearlyOptimalPPR.Computation
noncomputable section

def compilerFinishRequest {n : ℕ} (g : InputGraph n) (logical : RecursiveState n) : RecursiveState n :=
  let f := logical.frames logical.top
  let mu := ∑ v ∈ f.active, f.residual v
  let charged := debit logical logical.top (16*(volumeNat g f.active+1) : ℕ)
  let finished := finishEpisode charged
  changePC (compilerSetNeedFull finished (decide (f.Q/2 ≤ mu)))
    (if f.theta=f.q then .normal else .beginEpisode)

end
end NearlyOptimalPPR.Computation

-- Runtime interface from Solutions.CompilerCacheUnionSource

set_option autoImplicit false
namespace NearlyOptimalPPR.Computation
noncomputable section

def compilerCacheUnion {n : ℕ} (logical : RecursiveState n) : RecursiveState n :=
  changeFrame logical logical.top (fun f => {f with cache := f.cache ∪ f.high})

end
end NearlyOptimalPPR.Computation

-- Runtime interface from Solutions.CompilerLeafSolveSource

set_option autoImplicit false
namespace NearlyOptimalPPR.Computation
noncomputable section

def compilerLeafUpdate {n : ℕ} (g : InputGraph n) (α : ℝ) (logical : RecursiveState n) : RecursiveState n :=
  let f := logical.frames logical.top
  let C := f.cache ∪ f.high
  let h := solveOn g α C (fun v => f.residual v-f.theta*LocalPush.deg g.graph v)
  refreshKeys g (jointUpdate g α (compilerCacheUnion logical) h) (touchedBy g C)

def compilerLeafSolve {n : ℕ} (m : SolveModel) (g : InputGraph n) (α : ℝ)
    (logical : RecursiveState n) : RecursiveState n :=
  let f := logical.frames logical.top
  debit (compilerLeafUpdate g α logical) logical.top (jointCost m g logical (f.cache ∪ f.high))

end
end NearlyOptimalPPR.Computation

-- Runtime interface from Solutions.CompilerFullSolveSource

set_option autoImplicit false
namespace NearlyOptimalPPR.Computation
noncomputable section

def compilerFullUpdate {n : ℕ} (g : InputGraph n) (α : ℝ) (logical : RecursiveState n) : RecursiveState n :=
  let f := logical.frames logical.top
  refreshKeys g (jointUpdate g α logical (solveOn g α f.active f.residual)) (touchedBy g f.active)

def compilerFullCharged {n : ℕ} (m : SolveModel) (g : InputGraph n) (α : ℝ)
    (logical : RecursiveState n) : RecursiveState n :=
  let f := logical.frames logical.top
  let u := debit (compilerFullUpdate g α logical) logical.top (jointCost m g logical f.active)
  { u with fullSolves := Function.update u.fullSolves f.id (u.fullSolves f.id+1) }

def compilerFullSolve {n : ℕ} (m : SolveModel) (g : InputGraph n) (α : ℝ)
    (logical : RecursiveState n) : RecursiveState n :=
  changePC (compilerFullCharged m g α logical) .normalize

end
end NearlyOptimalPPR.Computation

-- Runtime interface from Solutions.HighQueueContext

set_option autoImplicit false
open scoped ENNReal
namespace NearlyOptimalPPR.Computation
noncomputable section

def highQueueContextInstructions : List Instruction := [
  .scalar (.core (.pcopy 87 89)),.scalar (.core (.pinc 87)),.scalar (.core (.pinc 87)),.scalar (.core (.pinc 87)),
  .scalar (.core (.pcopy 88 87)),.scalar (.core (.pinc 88)),.scalar (.core (.pinc 88)),.scalar (.core (.pinc 88)),
  .scalar (.core (.const 20 0))]

def highQueueContextCode : MachineCode := linearCode highQueueContextInstructions

end
end NearlyOptimalPPR.Computation

-- Runtime interface from Solutions.HighCleanPreparation

set_option autoImplicit false
set_option maxRecDepth 10000
namespace NearlyOptimalPPR.Computation
open SparseQueue
noncomputable section

def highCleanPrepareCode : MachineCode := .seq (levelHeaderIntegerToCode 8 13)
  (.seq levelContextCode (.seq frameRankLoadCode highQueueContextCode))
end
end NearlyOptimalPPR.Computation

-- Runtime interface from Solutions.HighPeekExecution

set_option autoImplicit false
set_option maxRecDepth 10000
namespace NearlyOptimalPPR.Computation
open SparseQueue
noncomputable section

def highPeekCode : MachineCode := .seq highCleanPrepareCode exteriorPeekObjectCode
end
end NearlyOptimalPPR.Computation

-- Runtime interface from Solutions.KeyListPrepend

set_option autoImplicit false
open scoped ENNReal
namespace NearlyOptimalPPR.Computation
namespace SparseQueue
noncomputable section

def listLinkPrepRoutine : PointerRoutine := .sequence [
  .atom (.copy 7 5),.atom (.inc 7),.atom (.inc 7)]

end
end SparseQueue
end NearlyOptimalPPR.Computation

-- Runtime interface from Solutions.SupportListPrepend

set_option autoImplicit false
open scoped ENNReal
namespace NearlyOptimalPPR.Computation
namespace SparseQueue
noncomputable section

def supportListPrependCode : MachineCode := .seq heapNodeAllocCode
  (.seq listLinkPrepRoutine.code (.seq (.atom (.scalar (.integerStore 7 92))) (coreCode (.pcopy 92 5))))

end
end SparseQueue
end NearlyOptimalPPR.Computation

-- Runtime interface from Solutions.FrameListPrepend

set_option autoImplicit false
open scoped ENNReal
namespace NearlyOptimalPPR.Computation
open SparseQueue
noncomputable section

def frameListPrependCode (headSlot : ℕ) : MachineCode := .seq (levelHeaderIntegerToCode headSlot 92)
  (.seq (coreCode (.pcopy 4 40)) (.seq supportListPrependCode (levelHeaderIntegerFromCode headSlot 92)))
end
end NearlyOptimalPPR.Computation

-- Runtime interface from Solutions.LevelHeaderIntegerAddFrom

set_option autoImplicit false
namespace NearlyOptimalPPR.Computation
noncomputable section

def levelHeaderIntegerAddFromCode (slot source : ℕ) : MachineCode := .seq (levelHeaderIntegerLoadCode slot)
  (.seq (.atom (.scalar (.pointerAdd 105 105 source))) (levelHeaderIntegerStoreCode slot))
end
end NearlyOptimalPPR.Computation

-- Runtime interface from Solutions.LevelHeaderArithmetic

set_option autoImplicit false
namespace NearlyOptimalPPR.Computation
noncomputable section

def levelHeaderIncrementCode (slot : ℕ) : MachineCode := .seq (levelHeaderIntegerLoadCode slot)
  (.seq (coreCode (.pinc 105)) (levelHeaderIntegerStoreCode slot))
def levelHeaderIntegerRealCode (slot target : ℕ) : MachineCode := .seq (levelHeaderIntegerLoadCode slot)
  (.atom (.scalar (.pointerReal target 105)))

end
end NearlyOptimalPPR.Computation

-- Runtime interface from Solutions.FrameListMetadata

set_option autoImplicit false
open scoped ENNReal
namespace NearlyOptimalPPR.Computation
noncomputable section

def frameFlagOffsetInstructions (field : ℕ) : List Instruction := [
  .scalar (.core (.pset 88 (field : ℤ))),.scalar (.pointerAdd 88 87 88)]
def frameFlagOffsetCode (field : ℕ) : MachineCode := linearCode (frameFlagOffsetInstructions field)

def frameListMetadataCode (cardSlot volumeSlot field : ℕ) : MachineCode :=
  .seq (levelHeaderIncrementCode cardSlot) (.seq (levelHeaderIntegerAddFromCode volumeSlot 120)
    (.seq (frameFlagOffsetCode field) vertexFlagSetCode))
end
end NearlyOptimalPPR.Computation

-- Runtime interface from Solutions.FrameListInsert

set_option autoImplicit false
open scoped ENNReal
namespace NearlyOptimalPPR.Computation
open SparseQueue
noncomputable section

def frameListInsertCode (headSlot cardSlot volumeSlot field : ℕ) : MachineCode :=
  .seq (frameListPrependCode headSlot) (frameListMetadataCode cardSlot volumeSlot field)
end
end NearlyOptimalPPR.Computation

-- Runtime interface from Solutions.CacheInsertPrelude

set_option autoImplicit false
set_option maxRecDepth 10000
namespace NearlyOptimalPPR.Computation
noncomputable section

def cacheInsertPreludeCode : MachineCode := .seq levelContextCode
  (.seq (coreCode (.pset 44 0)) (.seq vertexIntegerLoadCode (coreCode (.pcopy 120 51))))
end
end NearlyOptimalPPR.Computation

-- Runtime interface from Solutions.CacheInsertExecution

set_option autoImplicit false
set_option maxRecDepth 10000
namespace NearlyOptimalPPR.Computation
noncomputable section

def cacheInsertCode : MachineCode := .seq cacheInsertPreludeCode (frameListInsertCode 4 5 6 4)
end
end NearlyOptimalPPR.Computation

-- Runtime interface from Solutions.FrameVertexIntegerRead

set_option autoImplicit false
set_option maxRecDepth 10000
namespace NearlyOptimalPPR.Computation
noncomputable section

def frameVertexReadOffsetRoutine (field : ℕ) : PointerRoutine := .sequence [
  .atom (.set 44 (field : ℤ)),.atom (.add 44 87 44)]
def frameVertexIntegerReadCode (field : ℕ) : MachineCode :=
  .seq levelContextCode (.seq (frameVertexReadOffsetRoutine field).code vertexIntegerLoadCode)
end
end NearlyOptimalPPR.Computation

-- Runtime interface from Solutions.EnsureCacheExecution

set_option autoImplicit false
set_option maxRecDepth 10000
namespace NearlyOptimalPPR.Computation
noncomputable section

def ensureCacheCode : MachineCode := .seq (frameVertexIntegerReadCode 4)
  (.branchPointer 51 0 cacheInsertCode .skip)
end
end NearlyOptimalPPR.Computation

-- Runtime interface from Solutions.HighBitClearRawExecution

set_option autoImplicit false
set_option maxRecDepth 10000
namespace NearlyOptimalPPR.Computation
noncomputable section

def highBitClearCode : MachineCode := .seq (frameVertexIntegerReadCode 4)
  (.seq (coreCode (.const 10 0)) vertexRealStoreCode)
end
end NearlyOptimalPPR.Computation

-- Runtime interface from Solutions.HighCollectPointExecution

set_option autoImplicit false
set_option maxRecDepth 10000
namespace NearlyOptimalPPR.Computation
noncomputable section

def highCollectPointCode : MachineCode := .seq ensureCacheCode highBitClearCode
end
end NearlyOptimalPPR.Computation

-- Runtime interface from Solutions.HighCleanExecution

set_option autoImplicit false
set_option maxRecDepth 10000
namespace NearlyOptimalPPR.Computation
open SparseQueue
noncomputable section

def highCleanCode : MachineCode := .seq highCleanPrepareCode exteriorCleanObjectCode
end
end NearlyOptimalPPR.Computation

-- Runtime interface from Solutions.HighCollectLoopExecution

set_option autoImplicit false
set_option maxRecDepth 10000
namespace NearlyOptimalPPR.Computation
open SparseQueue
noncomputable section

def highCollectBodyCode : MachineCode := .seq highCleanCode
  (.branchPointer 97 0 .skip highCollectPointCode)
def highCollectLoopCode : MachineCode := .whilePointer 97 0 highCollectBodyCode
end
end NearlyOptimalPPR.Computation

-- Runtime interface from Solutions.HighCollectExecution

set_option autoImplicit false
set_option maxRecDepth 10000
namespace NearlyOptimalPPR.Computation
open SparseQueue
noncomputable section

def highCollectCode : MachineCode := .seq (coreCode (.pset 97 1)) highCollectLoopCode
end
end NearlyOptimalPPR.Computation

-- Runtime interface from Solutions.VertexListCopyBody

set_option autoImplicit false
namespace NearlyOptimalPPR.Computation
noncomputable section

def vertexListCopyInstructions : List Instruction := [
  .scalar (.integerLoad 40 94),.scalar (.integerStore 20 40),.scalar (.core (.pinc 20)),
  .scalar (.core (.pcopy 96 94)),.scalar (.core (.pinc 96)),.scalar (.core (.pinc 96)),
  .scalar (.integerLoad 94 96),.scalar (.core (.pinc 75))]

def vertexListCopyBodyCode : MachineCode := linearCode vertexListCopyInstructions

def vertexListCopyLoopCode : MachineCode := .whilePointer 94 0 vertexListCopyBodyCode

end
end NearlyOptimalPPR.Computation

-- Runtime interface from Solutions.VertexEnumerationCreation

set_option autoImplicit false
open scoped ENNReal
namespace NearlyOptimalPPR.Computation
noncomputable section

def vertexEnumerationInit : PointerRoutine := .sequence [
  .atom (.copy 80 20),.atom (.copy 94 90),.atom (.set 75 0)]

def vertexEnumerationCode : MachineCode :=
  .seq vertexEnumerationInit.code (.seq vertexListCopyLoopCode (coreCode (.pcopy 77 75)))

end
end NearlyOptimalPPR.Computation

-- Runtime interface from Solutions.PendingArrayRefreshRead

set_option autoImplicit false
namespace NearlyOptimalPPR.Computation
noncomputable section

def pendingArrayRefreshReadInstructions : List Instruction := [
  .scalar (.pointerAdd 144 140 143),.scalar (.integerLoad 40 144)]
def pendingArrayRefreshReadCode : MachineCode := linearCode pendingArrayRefreshReadInstructions
end
end NearlyOptimalPPR.Computation

-- Runtime interface from Solutions.QueuePairFrameContext

set_option autoImplicit false
set_option maxRecDepth 10000
open scoped ENNReal
namespace NearlyOptimalPPR.Computation
open SparseQueue
noncomputable section

def queuePairFrameContextCode : MachineCode := .seq (levelHeaderIntegerToCode 8 128)
  (.seq (levelHeaderRealToCode 5 47) (.seq exteriorFrameContextCode (coreCode (.pcopy 89 87))))
end
end NearlyOptimalPPR.Computation

-- Runtime interface from Solutions.HighBooleanCode

set_option autoImplicit false
namespace NearlyOptimalPPR.Computation
noncomputable section

def highDegreeProductInstructions : List Instruction := [
  .scalar (.pointerReal 10 60),RealOperation.mul.instruction 22 20 10,
  .scalar (.core (.const 21 3)),RealOperation.mul.instruction 22 22 21]

def highDegreeProductCode : MachineCode := linearCode highDegreeProductInstructions

def highResidualDecisionCode : MachineCode := .seq (.atom (RealOperation.sub.instruction 23 22 10))
  (.branchReal 23 (coreCode (.const 10 1)) (coreCode (.const 10 0)))

def highActiveCode : MachineCode := .seq (vertexFieldReadCode 0 60)
  (.seq highDegreeProductCode (.seq exteriorResidualOffsetRoutine.code
    (.seq vertexRealLoadCode highResidualDecisionCode)))

def highBooleanValueCode : MachineCode := .seq exteriorActiveOffsetRoutine.code
  (.seq vertexIntegerLoadCode (.branchPointer 51 0 (coreCode (.const 10 0)) highActiveCode))

def highBooleanStoreOffsetRoutine : PointerRoutine := .sequence [
  .atom (.copy 44 87),.atom (.inc 44),.atom (.inc 44),.atom (.inc 44),.atom (.inc 44)]

def highBooleanUpdateCode : MachineCode := .seq highBooleanValueCode
  (.seq highBooleanStoreOffsetRoutine.code vertexRealStoreCode)

end
end NearlyOptimalPPR.Computation

-- Runtime interface from Solutions.HighQueueRefreshExecution

set_option autoImplicit false
set_option maxRecDepth 10000
open scoped ENNReal
namespace NearlyOptimalPPR.Computation
namespace SparseQueue
noncomputable section

def highQueueRefreshInit : PointerRoutine := .sequence [.atom (.copy 41 50),.atom (.copy 87 89)]

def highQueueRefreshCode : MachineCode := .seq highQueueRefreshInit.code
  (.seq highBooleanUpdateCode (.seq highQueueContextCode exteriorQueueRefreshCode))

end
end SparseQueue
end NearlyOptimalPPR.Computation

-- Runtime interface from Solutions.QueuePairRefreshCode

set_option autoImplicit false
set_option maxRecDepth 10000
open scoped ENNReal
namespace NearlyOptimalPPR.Computation
open SparseQueue
noncomputable section

def queuePairHighPrepInstructions : List Instruction := [
  .scalar (.core (.pcopy 13 128)),.scalar (.core (.mul 20 47 31))]
def queuePairHighPrepCode : MachineCode := linearCode queuePairHighPrepInstructions
def queuePairRefreshCode : MachineCode := .seq exteriorQueueRefreshCode (.seq queuePairHighPrepCode highQueueRefreshCode)
end
end NearlyOptimalPPR.Computation

-- Runtime interface from Solutions.PendingLevelRefresh

set_option autoImplicit false
set_option maxRecDepth 10000
open scoped ENNReal
namespace NearlyOptimalPPR.Computation
open SparseQueue
noncomputable section

def pendingLevelRefreshCode : MachineCode := .seq (coreCode (.pcopy 100 109))
  (.seq queuePairFrameContextCode (.seq queuePairRefreshCode (coreCode (.pcopy 100 108))))
end
end NearlyOptimalPPR.Computation

-- Runtime interface from Solutions.PendingLevelGuard

set_option autoImplicit false
set_option maxRecDepth 10000
open scoped ENNReal
namespace NearlyOptimalPPR.Computation
noncomputable section

def pendingLevelGuardCode : MachineCode := .branchPointer 118 0 .skip pendingLevelRefreshCode
end
end NearlyOptimalPPR.Computation

-- Runtime interface from Solutions.DomainAdvance

set_option autoImplicit false
set_option maxRecDepth 10000
open scoped ENNReal
namespace NearlyOptimalPPR.Computation
noncomputable section

def domainAdvanceBodyCode : MachineCode := .seq (levelVertexOffsetCode 2)
  (.seq queuedFlagReadCode (coreCode (.pcopy 118 51)))
def domainAdvanceCode : MachineCode := .branchPointer 118 0 .skip domainAdvanceBodyCode
end
end NearlyOptimalPPR.Computation

-- Runtime interface from Solutions.PendingDomainAdvance

set_option autoImplicit false
set_option maxRecDepth 10000
open scoped ENNReal
namespace NearlyOptimalPPR.Computation
noncomputable section

def pendingDomainAdvanceInitInstructions : List Instruction := [
  .scalar (.core (.pcopy 87 109)),.scalar (.core (.pinc 87)),
  .scalar (.pointerAdd 87 87 87),.scalar (.pointerAdd 87 87 87),
  .scalar (.pointerAdd 87 87 87),.scalar (.pointerAdd 87 87 87),.scalar (.core (.pcopy 41 50))]
def pendingDomainAdvanceInitCode : MachineCode := linearCode pendingDomainAdvanceInitInstructions
def pendingDomainAdvanceCode : MachineCode := .seq pendingDomainAdvanceInitCode domainAdvanceCode
end
end NearlyOptimalPPR.Computation

-- Runtime interface from Solutions.PendingVertexLevelBody

set_option autoImplicit false
set_option maxRecDepth 10000
open scoped ENNReal
namespace NearlyOptimalPPR.Computation
noncomputable section

def pendingVertexLevelBodyCode : MachineCode := .seq pendingLevelGuardCode
  (.seq pendingDomainAdvanceCode (coreCode (.pinc 109)))
end
end NearlyOptimalPPR.Computation

-- Runtime interface from Solutions.PendingVertexLevelLoop

set_option autoImplicit false
set_option maxRecDepth 10000
open scoped ENNReal
namespace NearlyOptimalPPR.Computation
noncomputable section

def pendingVertexLevelLoopCode : MachineCode := .whilePointer 111 109 pendingVertexLevelBodyCode
end
end NearlyOptimalPPR.Computation

-- Runtime interface from Solutions.PendingVertexRefresh

set_option autoImplicit false
set_option maxRecDepth 10000
open scoped ENNReal
namespace NearlyOptimalPPR.Computation
noncomputable section

def pendingVertexRefreshInitInstructions : List Instruction := [
  .scalar (.core (.pcopy 108 100)),.scalar (.core (.pcopy 111 108)),.scalar (.core (.pinc 111)),
  .scalar (.core (.pset 109 0)),.scalar (.core (.pset 118 1))]
def pendingVertexRefreshInitCode : MachineCode := linearCode pendingVertexRefreshInitInstructions
def pendingVertexRefreshCode : MachineCode := .seq pendingVertexRefreshInitCode pendingVertexLevelLoopCode
end
end NearlyOptimalPPR.Computation

-- Runtime interface from Solutions.PendingArrayRefreshBody

set_option autoImplicit false
set_option maxRecDepth 10000
namespace NearlyOptimalPPR.Computation
noncomputable section

def pendingArrayRefreshBodyCode : MachineCode := .seq pendingArrayRefreshReadCode
  (.seq pendingVertexRefreshCode (coreCode (.pinc 143)))
def pendingArrayRefreshLoopCode : MachineCode := .whilePointer 142 143 pendingArrayRefreshBodyCode
end
end NearlyOptimalPPR.Computation

-- Runtime interface from Solutions.PendingArrayRefreshExecution

set_option autoImplicit false
set_option maxRecDepth 10000
namespace NearlyOptimalPPR.Computation
noncomputable section

def pendingArrayRefreshInitRoutine : PointerRoutine := .sequence [
  .atom (.copy 140 80),.atom (.copy 142 77),.atom (.set 143 0)]
def pendingArrayRefreshCode : MachineCode := .seq pendingArrayRefreshInitRoutine.code pendingArrayRefreshLoopCode
end
end NearlyOptimalPPR.Computation

-- Runtime interface from Solutions.PendingCacheRestoreExecution

set_option autoImplicit false
set_option maxRecDepth 10000
namespace NearlyOptimalPPR.Computation
noncomputable section

def pendingCacheRestoreCode : MachineCode := .seq (levelHeaderIntegerToCode 4 90)
  (.seq vertexEnumerationCode pendingArrayRefreshCode)
end
end NearlyOptimalPPR.Computation

-- Runtime interface from Solutions.LeafCachePreparationExecution

set_option autoImplicit false
set_option maxRecDepth 10000
namespace NearlyOptimalPPR.Computation
open SparseQueue
noncomputable section

def leafCachePreparationCode : MachineCode := .seq highCollectCode pendingCacheRestoreCode
end
end NearlyOptimalPPR.Computation

-- Runtime interface from Solutions.LeafRHSArithmetic

set_option autoImplicit false
open scoped ENNReal
namespace NearlyOptimalPPR.Computation
noncomputable section

def leafRHSArithmeticInstructions : List Instruction := [
  .scalar (.pointerReal 72 120),.scalar (.core (.mul 74 73 72)),
  .scalar (.core (.sub 10 71 74)),.scalar (.core (.pset 44 1))]
def leafRHSArithmeticCode : MachineCode := linearCode leafRHSArithmeticInstructions
end
end NearlyOptimalPPR.Computation

-- Runtime interface from Solutions.VertexRealReadTo

set_option autoImplicit false
open scoped ENNReal
namespace NearlyOptimalPPR.Computation
noncomputable section

def vertexRealReadToCode (target : ℕ) : MachineCode := .seq vertexRealLoadCode (coreCode (.mul target 10 31))
end
end NearlyOptimalPPR.Computation

-- Runtime interface from Solutions.LeafRHSPointRawExecution

set_option autoImplicit false
set_option maxRecDepth 10000
namespace NearlyOptimalPPR.Computation
noncomputable section

def leafRHSPointCode : MachineCode := .seq cacheInsertPreludeCode
  (.seq (frameVertexReadOffsetRoutine 1).code (.seq (vertexRealReadToCode 71)
    (.seq (levelHeaderRealToCode 5 73) (.seq leafRHSArithmeticCode vertexRealStoreCode))))
end
end NearlyOptimalPPR.Computation

-- Runtime interface from Solutions.PushOutputRead

set_option autoImplicit false
namespace NearlyOptimalPPR.Computation
noncomputable section

def pushOutputReadInstructions : List Instruction := [
  .scalar (.integerLoad 40 94),.scalar (.core (.pcopy 96 94)),.scalar (.core (.pinc 96)),
  .scalar (.core (.pinc 96)),.scalar (.integerLoad 94 96),.scalar (.core (.pset 44 0))]
def pushOutputReadCode : MachineCode := linearCode pushOutputReadInstructions
end
end NearlyOptimalPPR.Computation

-- Runtime interface from Solutions.LeafRHSBodyExecution

set_option autoImplicit false
set_option maxRecDepth 10000
namespace NearlyOptimalPPR.Computation
noncomputable section

def leafRHSBodyCode : MachineCode := .seq pushOutputReadCode leafRHSPointCode
def leafRHSLoopCode : MachineCode := .whilePointer 94 0 leafRHSBodyCode
end
end NearlyOptimalPPR.Computation

-- Runtime interface from Solutions.LeafRHSExecution

set_option autoImplicit false
set_option maxRecDepth 10000
namespace NearlyOptimalPPR.Computation
noncomputable section

def leafRHSCode : MachineCode := .seq (levelHeaderIntegerToCode 4 94) leafRHSLoopCode
end
end NearlyOptimalPPR.Computation

-- Runtime interface from Solutions.SparseEncoding

set_option autoImplicit false
open Finset Matrix
namespace NearlyOptimalPPR.Computation
noncomputable section

structure SparseEntry where
  row : ℤ
  column : ℤ
  value : ℝ


end
end NearlyOptimalPPR.Computation

-- Runtime interface from Solutions.TripletAppendCode

set_option autoImplicit false
namespace NearlyOptimalPPR.Computation
noncomputable section


def tripletAppendInstructions : List Instruction := [
  .scalar (.pointerAdd 70 71 74),.scalar (.integerStore 70 75),
  .scalar (.pointerAdd 70 72 74),.scalar (.integerStore 70 76),
  .scalar (.pointerAdd 70 73 74),.scalar (.core (.store 70 10)),.scalar (.core (.pinc 74))]

def tripletAppendCode : MachineCode := linearCode tripletAppendInstructions

end
end NearlyOptimalPPR.Computation

-- Runtime interface from Solutions.SolveBufferAllocation

set_option autoImplicit false
open scoped ENNReal
namespace NearlyOptimalPPR.Computation
open SparseQueue
noncomputable section

def preparedSolveRegisters : SolveRegisters := ⟨77,74,71,72,73,78,79⟩


def solveBufferRoutine : PointerRoutine := .sequence [
  .atom (.copy 71 20),.atom (.add 20 20 82),
  .atom (.copy 72 20),.atom (.add 20 20 82),
  .atom (.copy 73 20),.atom (.add 20 20 82),
  .atom (.copy 78 20),.atom (.add 20 20 77),
  .atom (.copy 79 20),.atom (.add 20 20 77),.atom (.set 74 0)]

end
end NearlyOptimalPPR.Computation

-- Runtime interface from Solutions.PrincipalEntries

set_option autoImplicit false
open Finset Matrix
namespace NearlyOptimalPPR.Computation
noncomputable section


def enumerationIndex {n k : ℕ} (e : Fin k → Fin n) (v : Fin n) : Option (Fin k) :=
  if h : ∃ i, e i=v then some (Classical.choose h) else none

def principalRowEntries {n k : ℕ} (g : InputGraph n) (α : ℝ) (e : Fin k → Fin n) (i : Fin k) : List SparseEntry :=
  ⟨i.val,i.val,LocalPush.deg g.graph (e i)⟩ ::
    ((g.neighbors (e i)).filterMap fun v => (enumerationIndex e v).map fun j => ⟨i.val,j.val,α-1⟩)

def principalEntries {n k : ℕ} (g : InputGraph n) (α : ℝ) (e : Fin k → Fin n) : List SparseEntry :=
  (List.finRange k).flatMap (principalRowEntries g α e)

end
end NearlyOptimalPPR.Computation

-- Runtime interface from Solutions.IndexLookupCode

set_option autoImplicit false
open scoped ENNReal
namespace NearlyOptimalPPR.Computation
noncomputable section

def indexLookupPresentCode : MachineCode := .seq (vertexFieldReadCode 8 76)
  (.seq (coreCode (.pdec 76)) (coreCode (.pset 68 1)))

def indexLookupCode : MachineCode := .seq (coreCode (.pset 68 0))
  (.seq (vertexFieldReadCode 7 65) (.branchPointer 53 65 indexLookupPresentCode .skip))

end
end NearlyOptimalPPR.Computation

-- Runtime interface from Solutions.OffDiagonalAppend

set_option autoImplicit false
open scoped ENNReal
namespace NearlyOptimalPPR.Computation
noncomputable section

def offDiagonalEntryCode : MachineCode := .seq indexLookupCode (.branchPointer 68 0 .skip tripletAppendCode)

end
end NearlyOptimalPPR.Computation

-- Runtime interface from Solutions.NeighborAssemblyBody

set_option autoImplicit false
open scoped ENNReal
namespace NearlyOptimalPPR.Computation
noncomputable section

def neighborAssemblyBodyCode : MachineCode := .seq (.atom (.scalar (.pointerAdd 64 61 62)))
  (.seq (.atom (.scalar (.integerLoad 40 64))) (.seq offDiagonalEntryCode (coreCode (.pinc 62))))

def neighborAssemblyLoopCode : MachineCode := .whilePointer 60 62 neighborAssemblyBodyCode

end
end NearlyOptimalPPR.Computation

-- Runtime interface from Solutions.DiagonalAppend

set_option autoImplicit false
open scoped ENNReal
namespace NearlyOptimalPPR.Computation
noncomputable section

def diagonalAppendCode : MachineCode := .seq (coreCode (.pcopy 76 75))
  (.seq (.atom (.scalar (.pointerReal 10 60))) tripletAppendCode)

end
end NearlyOptimalPPR.Computation

-- Runtime interface from Solutions.PrincipalRowAssembly

set_option autoImplicit false
open scoped ENNReal
namespace NearlyOptimalPPR.Computation
noncomputable section


def principalRowAssemblyCode : MachineCode := .seq cacheReadCode (.seq diagonalAppendCode
  (.seq (.atom (RealOperation.mul.instruction 10 12 11))
    (.seq (coreCode (.pset 62 0)) neighborAssemblyLoopCode)))

end
end NearlyOptimalPPR.Computation

-- Runtime interface from Solutions.DegreeSumCode

set_option autoImplicit false
open scoped ENNReal
namespace NearlyOptimalPPR.Computation
noncomputable section

def degreeSumTailRoutine : PointerRoutine := .sequence [
  .atom (.add 82 82 60),.atom (.inc 82),.atom (.inc 75)]

def degreeSumBodyCode : MachineCode := .seq (.atom (.scalar (.pointerAdd 81 80 75)))
  (.seq (.atom (.scalar (.integerLoad 40 81))) (.seq (vertexFieldReadCode 0 60) degreeSumTailRoutine.code))

def degreeSumLoopCode : MachineCode := .whilePointer 77 75 degreeSumBodyCode

def degreeSumInitRoutine : PointerRoutine := .sequence [
  .atom (.copy 41 50),.atom (.set 75 0),.atom (.set 82 0)]

def degreeSumCode : MachineCode := .seq degreeSumInitRoutine.code degreeSumLoopCode

end
end NearlyOptimalPPR.Computation

-- Runtime interface from Solutions.IndexPreparation

set_option autoImplicit false
open scoped ENNReal
namespace NearlyOptimalPPR.Computation
noncomputable section

def indexInitRoutine : PointerRoutine := .sequence [
  .atom (.copy 41 50),.atom (.set 75 0),.atom (.inc 53)]

def indexPreparationCode : MachineCode := .seq indexInitRoutine.code indexMarkLoopCode

end
end NearlyOptimalPPR.Computation

-- Runtime interface from Solutions.LocalSolvePreparation

set_option autoImplicit false
open scoped ENNReal
namespace NearlyOptimalPPR.Computation
noncomputable section

def localSolvePreparationCode : MachineCode := .seq degreeSumCode
  (.seq indexPreparationCode (.seq solveBufferRoutine.code (coreCode (.pcopy 41 50))))

end
end NearlyOptimalPPR.Computation

-- Runtime interface from Solutions.PrincipalAssemblyBody

set_option autoImplicit false
open scoped ENNReal
namespace NearlyOptimalPPR.Computation
noncomputable section

def principalAssemblyBodyCode : MachineCode := .seq (.atom (.scalar (.pointerAdd 81 80 75)))
  (.seq (.atom (.scalar (.integerLoad 40 81))) (.seq principalRowAssemblyCode (coreCode (.pinc 75))))

def principalAssemblyLoopCode : MachineCode := .whilePointer 77 75 principalAssemblyBodyCode

end
end NearlyOptimalPPR.Computation

-- Runtime interface from Solutions.MatrixAssemblyInit

set_option autoImplicit false
namespace NearlyOptimalPPR.Computation
noncomputable section

def matrixAssemblyInitInstructions : List Instruction := [
  .scalar (.core (.load 12 0)),.scalar (.core (.const 11 1)),
  RealOperation.sub.instruction 12 12 11,.scalar (.core (.pset 75 0))]

def matrixAssemblyInitCode : MachineCode := linearCode matrixAssemblyInitInstructions

end
end NearlyOptimalPPR.Computation

-- Runtime interface from Solutions.PrincipalMatrixAssembly

set_option autoImplicit false
open scoped ENNReal
namespace NearlyOptimalPPR.Computation
noncomputable section

def principalMatrixAssemblyCode : MachineCode := .seq matrixAssemblyInitCode principalAssemblyLoopCode

end
end NearlyOptimalPPR.Computation

-- Runtime interface from Solutions.RightHandSideBody

set_option autoImplicit false
open scoped ENNReal
namespace NearlyOptimalPPR.Computation
noncomputable section

def rightHandSideTailInstructions : List Instruction := [
  .scalar (.pointerAdd 70 78 75),.scalar (.core (.store 70 10)),.scalar (.core (.pinc 75))]

def rightHandSideTailCode : MachineCode := linearCode rightHandSideTailInstructions

def rightHandSideBodyCode : MachineCode := .seq (.atom (.scalar (.pointerAdd 81 80 75)))
  (.seq (.atom (.scalar (.integerLoad 40 81))) (.seq vertexRealLoadCode rightHandSideTailCode))

def rightHandSideLoopCode : MachineCode := .whilePointer 77 75 rightHandSideBodyCode

end
end NearlyOptimalPPR.Computation

-- Runtime interface from Solutions.RightHandSidePreparation

set_option autoImplicit false
open scoped ENNReal
namespace NearlyOptimalPPR.Computation
noncomputable section

def rightHandSidePreparationCode : MachineCode := .seq (coreCode (.pset 75 0)) rightHandSideLoopCode

end
end NearlyOptimalPPR.Computation

-- Runtime interface from Solutions.AssembledPrincipalSolve

set_option autoImplicit false
open scoped ENNReal
namespace NearlyOptimalPPR.Computation
noncomputable section

def assembledPrincipalSolveCode : MachineCode :=
  .seq rightHandSidePreparationCode (.atom (.solve preparedSolveRegisters))

end
end NearlyOptimalPPR.Computation

-- Runtime interface from Solutions.PrincipalSolvePipeline

set_option autoImplicit false
open scoped ENNReal
namespace NearlyOptimalPPR.Computation
noncomputable section

def principalSolvePipelineCode : MachineCode := .seq principalMatrixAssemblyCode
  (.seq (coreCode (.pcopy 44 83)) assembledPrincipalSolveCode)

end
end NearlyOptimalPPR.Computation

-- Runtime interface from Solutions.CachedPrincipalSolve

set_option autoImplicit false
open scoped ENNReal
namespace NearlyOptimalPPR.Computation
noncomputable section

def cachedPrincipalSolveCode : MachineCode := .seq localSolvePreparationCode principalSolvePipelineCode

end
end NearlyOptimalPPR.Computation

-- Runtime interface from Solutions.ExteriorScalarPrefix

set_option autoImplicit false
set_option maxRecDepth 10000
open scoped ENNReal
namespace NearlyOptimalPPR.Computation
noncomputable section

def exteriorScalarPrefixInstructions : List Instruction := [
  .scalar (.core (.pcopy 108 100)),.scalar (.core (.pcopy 116 40)),.scalar (.core (.pcopy 100 112))]
def exteriorScalarPrefixCode : MachineCode := .seq (linearCode exteriorScalarPrefixInstructions)
  (.seq levelContextCode (levelHeaderRealToCode 1 20))
end
end NearlyOptimalPPR.Computation

-- Runtime interface from Solutions.ExteriorInputsCode

set_option autoImplicit false
set_option maxRecDepth 10000
open scoped ENNReal
namespace NearlyOptimalPPR.Computation
noncomputable section

def exteriorRootReferenceCode : MachineCode := .branchPointer 112 0 (coreCode (.const 5 0)) .skip
def exteriorResidualOffsetInstructions : List Instruction := [
  .scalar (.core (.pset 86 1)),.scalar (.pointerAdd 44 87 86)]
def exteriorResidualOffsetCode : MachineCode := linearCode exteriorResidualOffsetInstructions
def exteriorInputsTailCode : MachineCode := .seq (.atom (.scalar (.deg 60 40)))
  (.seq (.atom (.scalar (.pointerReal 11 60))) (coreCode (.sub 12 4 5)))
def exteriorInputsCode : MachineCode := .seq (coreCode (.pset 44 0))
  (.seq (vertexRealReadToCode 4) (.seq (coreCode (.pcopy 44 87)) (.seq (vertexRealReadToCode 5)
    (.seq exteriorRootReferenceCode (.seq exteriorResidualOffsetCode (.seq vertexRealLoadCode exteriorInputsTailCode))))))

end
end NearlyOptimalPPR.Computation

-- Runtime interface from Solutions.ExteriorAmountCode

set_option autoImplicit false
open scoped ENNReal
namespace NearlyOptimalPPR.Computation
noncomputable section

def exteriorAmountPrefixInstructions : List Instruction := [
  .scalar (.core (.const 14 5)),.scalar (.core (.const 15 (3/8))),
  RealOperation.mul.instruction 16 14 11,RealOperation.div.instruction 17 10 16,
  RealOperation.mul.instruction 18 15 20,RealOperation.sub.instruction 19 18 12,
  RealOperation.sub.instruction 22 19 17]
def exteriorAmountPrefixCode : MachineCode := linearCode exteriorAmountPrefixInstructions
def exteriorAmountChoiceCode (sourceReg : ℕ) (activated : ℤ) : MachineCode :=
  .seq (coreCode (.mul 40 sourceReg 31)) (coreCode (.pset 114 activated))
def exteriorAmountDecisionCode : MachineCode := .branchReal 22 (exteriorAmountChoiceCode 19 1) (exteriorAmountChoiceCode 17 0)
def exteriorAmountTailInstructions : List Instruction := [
  RealOperation.sub.instruction 47 31 30,RealOperation.mul.instruction 41 47 40,
  RealOperation.mul.instruction 42 11 40,.scalar (.core (.const 14 (1/2))),
  RealOperation.mul.instruction 43 20 11,RealOperation.mul.instruction 43 43 14,
  RealOperation.mul.instruction 44 18 31,RealOperation.mul.instruction 45 20 31,
  RealOperation.mul.instruction 46 47 42]
def exteriorAmountTailCode : MachineCode := linearCode exteriorAmountTailInstructions
def exteriorAmountCode : MachineCode := .seq exteriorAmountPrefixCode (.seq exteriorAmountDecisionCode exteriorAmountTailCode)

end
end NearlyOptimalPPR.Computation

-- Runtime interface from Solutions.ExteriorScalarExecution

set_option autoImplicit false
set_option maxRecDepth 10000
open scoped ENNReal
namespace NearlyOptimalPPR.Computation
noncomputable section

def exteriorScalarCode : MachineCode := .seq exteriorScalarPrefixCode (.seq exteriorInputsCode exteriorAmountCode)
end
end NearlyOptimalPPR.Computation

-- Runtime interface from Solutions.VertexRealAdd

set_option autoImplicit false
open scoped ENNReal
namespace NearlyOptimalPPR.Computation
noncomputable section

def realAddAtPointerInstructions : List Instruction := [
  .scalar (.core (.load 11 45)),RealOperation.add.instruction 10 11 10,.scalar (.core (.store 45 10))]

def realAddAtPointerCode : MachineCode := linearCode realAddAtPointerInstructions

def vertexRealAddCode : MachineCode := .seq vertexAddressCode realAddAtPointerCode

end
end NearlyOptimalPPR.Computation

-- Runtime interface from Solutions.VertexRealAddFrom

set_option autoImplicit false
open scoped ENNReal
namespace NearlyOptimalPPR.Computation
noncomputable section

def vertexRealAddFromCode (source : ℕ) : MachineCode := .seq (coreCode (.mul 10 source 31)) vertexRealAddCode
end
end NearlyOptimalPPR.Computation

-- Runtime interface from Solutions.ExteriorSelfUpdate

set_option autoImplicit false
set_option maxRecDepth 10000
open scoped ENNReal
namespace NearlyOptimalPPR.Computation
noncomputable section

def exteriorSelfCoefficientInstructions (coefficient : ℤ) : List Instruction := [
  .scalar (.core (.const 49 (coefficient : ℝ))),RealOperation.mul.instruction 48 49 42]
def exteriorSelfCoefficientCode (coefficient : ℤ) : MachineCode := linearCode (exteriorSelfCoefficientInstructions coefficient)
def exteriorSelfChoiceCode : MachineCode := .branchPointer 112 100 (exteriorSelfCoefficientCode (-5)) (exteriorSelfCoefficientCode (-1))
def exteriorSelfCode : MachineCode := .branchPointer 100 112
  (.seq exteriorSelfChoiceCode (.seq exteriorResidualOffsetCode (vertexRealAddFromCode 48))) .skip

end
end NearlyOptimalPPR.Computation

-- Runtime interface from Solutions.LevelHeaderAddFrom

set_option autoImplicit false
open scoped ENNReal
namespace NearlyOptimalPPR.Computation
noncomputable section

def levelHeaderAddFromCode (slot source : ℕ) : MachineCode := .seq (levelHeaderRealLoadCode slot)
  (.seq (coreCode (.add 10 10 source)) (levelHeaderRealStoreCode slot))
end
end NearlyOptimalPPR.Computation

-- Runtime interface from Solutions.ExteriorBudgetUpdate

set_option autoImplicit false
set_option maxRecDepth 10000
open scoped ENNReal
namespace NearlyOptimalPPR.Computation
noncomputable section

def exteriorBudgetBodyCode : MachineCode := .seq (levelHeaderIntegerLoadCode 9)
  (.branchPointer 105 0 .skip (levelHeaderAddFromCode 4 46))
def exteriorBudgetCode : MachineCode := .branchPointer 112 100 exteriorBudgetBodyCode .skip
end
end NearlyOptimalPPR.Computation

-- Runtime interface from Solutions.ExteriorSelfBudget

set_option autoImplicit false
set_option maxRecDepth 10000
open scoped ENNReal
namespace NearlyOptimalPPR.Computation
noncomputable section

def exteriorSelfBudgetCode : MachineCode := .seq exteriorSelfCode exteriorBudgetCode
end
end NearlyOptimalPPR.Computation

-- Runtime interface from Solutions.ExteriorSelfBudgetLoop

set_option autoImplicit false
set_option maxRecDepth 10000
open scoped ENNReal
namespace NearlyOptimalPPR.Computation
noncomputable section

def exteriorSelfBudgetBodyCode : MachineCode := .seq (coreCode (.pcopy 100 109))
  (.seq levelContextCode (.seq exteriorSelfBudgetCode (coreCode (.pinc 109))))
def exteriorSelfBudgetInitInstructions : List Instruction := [
  .scalar (.core (.pcopy 111 108)),.scalar (.core (.pinc 111)),.scalar (.core (.pset 109 0))]
def exteriorSelfBudgetInitCode : MachineCode := linearCode exteriorSelfBudgetInitInstructions
def exteriorSelfBudgetLoopCode : MachineCode := .seq exteriorSelfBudgetInitCode
  (.seq (.whilePointer 111 109 exteriorSelfBudgetBodyCode) (coreCode (.pcopy 100 108)))
end
end NearlyOptimalPPR.Computation

-- Runtime interface from Solutions.StoredNeighborRead

set_option autoImplicit false
open scoped ENNReal
namespace NearlyOptimalPPR.Computation
noncomputable section

def storedNeighborReadInstructions : List Instruction := [
  .scalar (.core (.pcopy 122 109)),.scalar (.pointerAdd 123 121 122),
  .scalar (.integerLoad 40 123),.scalar (.core (.pcopy 41 50))]
def storedNeighborReadCode : MachineCode := linearCode storedNeighborReadInstructions
end
end NearlyOptimalPPR.Computation

-- Runtime interface from Solutions.DegreeRecordStore

set_option autoImplicit false
open scoped ENNReal
namespace NearlyOptimalPPR.Computation
noncomputable section

def degreeRecordStoreCode : MachineCode := .seq (.atom (.scalar (.deg 60 40))) (vertexFieldWriteCode 0 60)

end
end NearlyOptimalPPR.Computation

-- Runtime interface from Solutions.DomainResidualUpdate

set_option autoImplicit false
set_option maxRecDepth 10000
open scoped ENNReal
namespace NearlyOptimalPPR.Computation
noncomputable section

def domainResidualAddCode : MachineCode := .branchPointer 118 0 .skip
  (.seq exteriorResidualOffsetCode (vertexRealAddFromCode 41))
def domainResidualStepCode : MachineCode := .seq domainResidualAddCode domainAdvanceCode
end
end NearlyOptimalPPR.Computation

-- Runtime interface from Solutions.DomainResidualBody

set_option autoImplicit false
set_option maxRecDepth 10000
open scoped ENNReal
namespace NearlyOptimalPPR.Computation
noncomputable section

def domainResidualBodyCode : MachineCode := .seq (coreCode (.pcopy 100 109))
  (.seq levelContextCode (.seq domainResidualStepCode (coreCode (.pinc 109))))
end
end NearlyOptimalPPR.Computation

-- Runtime interface from Solutions.DomainResidualLoop

set_option autoImplicit false
set_option maxRecDepth 10000
open scoped ENNReal
namespace NearlyOptimalPPR.Computation
noncomputable section

def domainResidualInitInstructions : List Instruction := [
  .scalar (.core (.pcopy 111 108)),.scalar (.core (.pinc 111)),
  .scalar (.core (.pset 109 0)),.scalar (.core (.pset 118 1))]
def domainResidualInitCode : MachineCode := linearCode domainResidualInitInstructions
def domainResidualLoopCode : MachineCode := .seq domainResidualInitCode
  (.seq (.whilePointer 111 109 domainResidualBodyCode) (coreCode (.pcopy 100 108)))
end
end NearlyOptimalPPR.Computation

-- Runtime interface from Solutions.StoredNeighborBody

set_option autoImplicit false
set_option maxRecDepth 10000
open scoped ENNReal
namespace NearlyOptimalPPR.Computation
noncomputable section

def storedNeighborTailInstructions : List Instruction := [
  .scalar (.core (.pcopy 109 122)),.scalar (.core (.pinc 109)),.scalar (.core (.pcopy 111 120))]
def storedNeighborTailCode : MachineCode := linearCode storedNeighborTailInstructions

def storedNeighborBodyCode : MachineCode := .seq storedNeighborReadCode
  (.seq degreeRecordStoreCode (.seq domainResidualLoopCode storedNeighborTailCode))
end
end NearlyOptimalPPR.Computation

-- Runtime interface from Solutions.StoredNeighborLoop

set_option autoImplicit false
set_option maxRecDepth 10000
open scoped ENNReal
namespace NearlyOptimalPPR.Computation
noncomputable section

def storedNeighborInitInstructions : List Instruction := [
  .scalar (.core (.pcopy 120 60)),.scalar (.core (.pcopy 121 61)),
  .scalar (.core (.pcopy 111 120)),.scalar (.core (.pset 109 0))]
def storedNeighborInitCode : MachineCode := linearCode storedNeighborInitInstructions

def storedNeighborRestoreInstructions : List Instruction := [
  .scalar (.core (.pcopy 40 116)),.scalar (.core (.pcopy 100 108))]
def storedNeighborRestoreCode : MachineCode := linearCode storedNeighborRestoreInstructions

def storedNeighborLoopCode : MachineCode := .seq storedNeighborInitCode
  (.seq (.whilePointer 111 109 storedNeighborBodyCode) storedNeighborRestoreCode)
end
end NearlyOptimalPPR.Computation

-- Runtime interface from Solutions.StoredActiveCountBody

set_option autoImplicit false
set_option maxRecDepth 10000
open scoped ENNReal
namespace NearlyOptimalPPR.Computation
noncomputable section

def storedActiveDecisionRoutine : PointerRoutine := .branch 60 0 .skip (.atom (.inc 124))
def storedActiveCountBodyCode : MachineCode := .seq storedNeighborReadCode
  (.seq (vertexFieldReadCode 18 60) (.seq storedActiveDecisionRoutine.code (coreCode (.pinc 109))))
end
end NearlyOptimalPPR.Computation

-- Runtime interface from Solutions.StoredActiveCountLoop

set_option autoImplicit false
set_option maxRecDepth 10000
open scoped ENNReal
namespace NearlyOptimalPPR.Computation
noncomputable section

def storedActiveCountInitInstructions : List Instruction := [
  .scalar (.core (.pcopy 111 120)),.scalar (.core (.pset 109 0)),.scalar (.core (.pset 124 0))]
def storedActiveCountInitCode : MachineCode := linearCode storedActiveCountInitInstructions
def storedActiveCountLoopCode : MachineCode := .seq storedActiveCountInitCode
  (.seq (.whilePointer 111 109 storedActiveCountBodyCode) (coreCode (.pcopy 40 116)))
end
end NearlyOptimalPPR.Computation

-- Runtime interface from Solutions.RootBoundaryUpdate

set_option autoImplicit false
open scoped ENNReal
namespace NearlyOptimalPPR.Computation
noncomputable section

def rootBoundaryUpdateInstructions : List Instruction := [
  .scalar (.core (.pset 127 7)),.scalar (.integerLoad 125 127),
  .scalar (.pointerAdd 125 125 120),.scalar (.pointerAdd 126 124 124),
  .scalar (.pointerSub 125 125 126)]
def rootBoundaryUpdatePrefixCode : MachineCode := linearCode rootBoundaryUpdateInstructions
def rootBoundaryClipRoutine : PointerRoutine := .branch 125 0 (.atom (.set 125 0)) .skip
def rootBoundaryUpdateCode : MachineCode := .seq rootBoundaryUpdatePrefixCode
  (.seq rootBoundaryClipRoutine.code (.atom (.scalar (.integerStore 127 125))))
end
end NearlyOptimalPPR.Computation

-- Runtime interface from Solutions.ActivationBoundary

set_option autoImplicit false
set_option maxRecDepth 10000
open scoped ENNReal
namespace NearlyOptimalPPR.Computation
noncomputable section

def activationBoundaryCode : MachineCode := .branchPointer 112 0
  (.seq storedActiveCountLoopCode rootBoundaryUpdateCode) .skip
end
end NearlyOptimalPPR.Computation

-- Runtime interface from Solutions.ActivationBudget

set_option autoImplicit false
open scoped ENNReal
namespace NearlyOptimalPPR.Computation
noncomputable section

def activationBudgetFactorInstructions : List Instruction := [
  .scalar (.core (.pcopy 126 100)),.scalar (.core (.pinc 126)),
  .scalar (.core (.pinc 126)),.scalar (.core (.pinc 126)),
  .scalar (.pointerReal 49 126),.scalar (.core (.mul 48 49 43))]
def activationBudgetFactorCode : MachineCode := linearCode activationBudgetFactorInstructions
def activationBudgetApplyCode : MachineCode := .seq activationBudgetFactorCode (levelHeaderAddFromCode 4 48)
def activationBudgetCode : MachineCode := .seq (levelHeaderIntegerLoadCode 9)
  (.branchPointer 105 0 .skip activationBudgetApplyCode)
end
end NearlyOptimalPPR.Computation

-- Runtime interface from Solutions.ActivationScalars

set_option autoImplicit false
open scoped ENNReal
namespace NearlyOptimalPPR.Computation
noncomputable section

def activationResidualOffsetInstructions : List Instruction := [
  .scalar (.core (.pcopy 44 87)),.scalar (.core (.pinc 44))]
def activationResidualOffsetCode : MachineCode := linearCode activationResidualOffsetInstructions
def activationScalarsCode : MachineCode := .seq activationResidualOffsetCode
  (.seq (vertexRealAddFromCode 43) activationBudgetCode)
end
end NearlyOptimalPPR.Computation

-- Runtime interface from Solutions.VertexRealCopy

set_option autoImplicit false
open scoped ENNReal
namespace NearlyOptimalPPR.Computation
noncomputable section


def vertexRealCopyCode : MachineCode := .seq (coreCode (.pcopy 44 89))
  (.seq vertexRealLoadCode (.seq (coreCode (.pcopy 44 88)) vertexRealStoreCode))
end
end NearlyOptimalPPR.Computation

-- Runtime interface from Solutions.VertexRealZero

set_option autoImplicit false
open scoped ENNReal
namespace NearlyOptimalPPR.Computation
noncomputable section

def vertexRealZeroCode : MachineCode := .seq (coreCode (.pcopy 44 88))
  (.seq (coreCode (.const 10 0)) vertexRealStoreCode)
end
end NearlyOptimalPPR.Computation

-- Runtime interface from Solutions.LevelVertexFlagsClear

set_option autoImplicit false
open scoped ENNReal
namespace NearlyOptimalPPR.Computation
noncomputable section

def levelVertexFlagsClearCode (offsets : List ℕ) : MachineCode :=
  sequenceCode (offsets.map levelVertexFlagClearCode)
end
end NearlyOptimalPPR.Computation

-- Runtime interface from Solutions.FreshVertexCode

set_option autoImplicit false
namespace NearlyOptimalPPR.Computation
noncomputable section

def freshReferencePrepInstructions : List Instruction := [
  .scalar (.core (.pset 89 0)),.scalar (.core (.pcopy 88 87))]
def freshReferencePrepCode : MachineCode := linearCode freshReferencePrepInstructions

def freshResidualPrepInstructions : List Instruction := [
  .scalar (.core (.pset 89 (-15))),.scalar (.pointerAdd 89 87 89),
  .scalar (.core (.pcopy 88 87)),.scalar (.core (.pinc 88))]
def freshResidualPrepCode : MachineCode := linearCode freshResidualPrepInstructions

def freshReferenceCode : MachineCode := .seq freshReferencePrepCode vertexRealCopyCode
def freshResidualCode : MachineCode := .seq freshResidualPrepCode vertexRealCopyCode
def freshHighZeroCode : MachineCode := .seq (levelVertexOffsetCode 4) vertexRealZeroCode

def freshVertexCode : MachineCode := .seq freshReferenceCode
  (.seq freshResidualCode (.seq freshHighZeroCode (levelVertexFlagsClearCode [2,3,4,5,6])))

end
end NearlyOptimalPPR.Computation

-- Runtime interface from Solutions.ActivationChildAdmit

set_option autoImplicit false
set_option maxRecDepth 10000
open scoped ENNReal
namespace NearlyOptimalPPR.Computation
noncomputable section

def activationChildAdmitApplyCode : MachineCode := .seq (coreCode (.pinc 100))
  (.seq levelContextCode (.seq freshVertexCode (.seq (coreCode (.pcopy 100 112)) levelContextCode)))
def activationChildAdmitCode : MachineCode := .branchPointer 108 112 .skip activationChildAdmitApplyCode
end
end NearlyOptimalPPR.Computation

-- Runtime interface from Solutions.CachedSourceNeighborRead

set_option autoImplicit false
set_option maxRecDepth 10000
open scoped ENNReal
namespace NearlyOptimalPPR.Computation
noncomputable section

def cachedSourceNeighborPrefixInstructions : List Instruction := [
  .scalar (.core (.pcopy 122 109)),.scalar (.core (.pcopy 40 116)),.scalar (.core (.pcopy 41 50))]
def cachedSourceNeighborPrefixCode : MachineCode := linearCode cachedSourceNeighborPrefixInstructions
def cachedSourceNeighborSuffixInstructions : List Instruction := [
  .scalar (.pointerAdd 123 121 122),.scalar (.integerLoad 40 123)]
def cachedSourceNeighborSuffixCode : MachineCode := linearCode cachedSourceNeighborSuffixInstructions
def cachedSourceNeighborReadCode : MachineCode := .seq cachedSourceNeighborPrefixCode
  (.seq (vertexFieldReadCode 1 121) cachedSourceNeighborSuffixCode)
end
end NearlyOptimalPPR.Computation

-- Runtime interface from Solutions.PendingNeighborRefreshBody

set_option autoImplicit false
set_option maxRecDepth 10000
open scoped ENNReal
namespace NearlyOptimalPPR.Computation
noncomputable section

def pendingNeighborRefreshTailInstructions : List Instruction := [
  .scalar (.core (.pcopy 109 122)),.scalar (.core (.pinc 109)),.scalar (.core (.pcopy 111 120))]
def pendingNeighborRefreshTailCode : MachineCode := linearCode pendingNeighborRefreshTailInstructions

def pendingNeighborRefreshBodyCode : MachineCode := .seq cachedSourceNeighborReadCode
  (.seq pendingVertexRefreshCode pendingNeighborRefreshTailCode)
end
end NearlyOptimalPPR.Computation

-- Runtime interface from Solutions.PendingNeighborRefreshLoop

set_option autoImplicit false
set_option maxRecDepth 10000
open scoped ENNReal
namespace NearlyOptimalPPR.Computation
open SparseQueue
noncomputable section

def pendingNeighborRefreshLoopCode : MachineCode := .whilePointer 111 109 pendingNeighborRefreshBodyCode
end
end NearlyOptimalPPR.Computation

-- Runtime interface from Solutions.PendingNeighborRefresh

set_option autoImplicit false
set_option maxRecDepth 10000
open scoped ENNReal
namespace NearlyOptimalPPR.Computation
open SparseQueue
noncomputable section

def pendingNeighborRefreshInitInstructions : List Instruction := [
  .scalar (.core (.pcopy 111 120)),.scalar (.core (.pset 109 0))]
def pendingNeighborRefreshInitCode : MachineCode := linearCode pendingNeighborRefreshInitInstructions
def pendingNeighborRefreshCode : MachineCode := .seq pendingNeighborRefreshInitCode
  (.seq pendingNeighborRefreshLoopCode (coreCode (.pcopy 40 116)))
end
end NearlyOptimalPPR.Computation

-- Runtime interface from Solutions.PendingTouchedRefresh

set_option autoImplicit false
set_option maxRecDepth 10000
open scoped ENNReal
namespace NearlyOptimalPPR.Computation
open SparseQueue
noncomputable section

def pendingTouchedRefreshCode : MachineCode := .seq pendingVertexRefreshCode pendingNeighborRefreshCode
end
end NearlyOptimalPPR.Computation

-- Runtime interface from Solutions.ExteriorPushProgramCode

set_option autoImplicit false
set_option maxRecDepth 10000
namespace NearlyOptimalPPR.Computation
noncomputable section

def exteriorPotentialPrepInstructions : List Instruction := [
  .scalar (.core (.pcopy 41 50)),.scalar (.core (.pset 44 0))]
def exteriorPotentialPrepCode : MachineCode := linearCode exteriorPotentialPrepInstructions
def exteriorPotentialAddCode : MachineCode := .seq exteriorPotentialPrepCode (vertexRealAddFromCode 40)

def exteriorActivationPrepareCode : MachineCode := .seq (coreCode (.pcopy 100 112)) levelContextCode

def exteriorActivationApplyCode : MachineCode := .seq activationBoundaryCode
  (.seq exteriorActivationPrepareCode (.seq (frameListInsertCode 1 3 2 2)
    (.seq activationScalarsCode (.seq activationChildAdmitCode (coreCode (.pcopy 100 108))))))
def exteriorActivationCode : MachineCode := .branchPointer 114 0 .skip exteriorActivationApplyCode

def exteriorNumericPrefixCode : MachineCode := .seq exteriorScalarCode
  (.seq cacheRowCode (.seq exteriorPotentialAddCode (.seq exteriorSelfBudgetLoopCode storedNeighborLoopCode)))
def exteriorNumericRawCode : MachineCode := .seq exteriorNumericPrefixCode exteriorActivationCode
def exteriorPushProgramCode : MachineCode := .seq exteriorNumericRawCode pendingTouchedRefreshCode

end
end NearlyOptimalPPR.Computation

-- Runtime interface from Solutions.JointCoordinateCode

set_option autoImplicit false
set_option maxRecDepth 10000
namespace NearlyOptimalPPR.Computation
noncomputable section

def jointCoordinatePreludeInstructions : List Instruction := [
  .scalar (.core (.pcopy 108 100)),.scalar (.core (.pcopy 116 40)),.scalar (.core (.pcopy 41 50))]
def jointCoordinatePreludeCode : MachineCode := linearCode jointCoordinatePreludeInstructions

def jointCoordinateSelfInstructions : List Instruction := [
  .scalar (.pointerReal 44 60),.scalar (.core (.mul 42 44 40)),
  .scalar (.core (.sub 45 31 31)),.scalar (.core (.sub 41 45 42))]
def jointCoordinateSelfCode : MachineCode := linearCode jointCoordinateSelfInstructions

def jointCoordinateNeighborInstructions : List Instruction := [
  .scalar (.core (.sub 41 31 30)),.scalar (.core (.mul 41 41 40))]
def jointCoordinateNeighborCode : MachineCode := linearCode jointCoordinateNeighborInstructions

def jointCoordinateNumericCode : MachineCode := .seq jointCoordinatePreludeCode
  (.seq cacheReadCode (.seq exteriorPotentialAddCode (.seq jointCoordinateSelfCode
    (.seq domainResidualLoopCode (.seq jointCoordinateNeighborCode storedNeighborLoopCode)))))
def jointCoordinateProgramCode : MachineCode := .seq jointCoordinateNumericCode pendingTouchedRefreshCode

end
end NearlyOptimalPPR.Computation

-- Runtime interface from Solutions.JointSolveIterationCode

set_option autoImplicit false
set_option maxRecDepth 10000
namespace NearlyOptimalPPR.Computation
noncomputable section

def jointSolveIterationInitInstructions : List Instruction := [
  .scalar (.core (.pcopy 140 80)),.scalar (.core (.pcopy 141 79)),
  .scalar (.core (.pcopy 142 77)),.scalar (.core (.pset 143 0))]
def jointSolveIterationInitCode : MachineCode := linearCode jointSolveIterationInitInstructions

def jointSolveIterationReadInstructions : List Instruction := [
  .scalar (.pointerAdd 144 140 143),.scalar (.integerLoad 40 144),
  .scalar (.pointerAdd 144 141 143),.scalar (.core (.load 40 144))]
def jointSolveIterationReadCode : MachineCode := linearCode jointSolveIterationReadInstructions

def jointSolveIterationBodyCode : MachineCode := .seq jointSolveIterationReadCode
  (.seq jointCoordinateProgramCode (coreCode (.pinc 143)))
def jointSolveIterationLoopCode : MachineCode := .whilePointer 142 143 jointSolveIterationBodyCode
def jointSolveIterationCode : MachineCode := .seq jointSolveIterationInitCode jointSolveIterationLoopCode

end
end NearlyOptimalPPR.Computation

-- Runtime interface from Solutions.JointSolveIterationBound

set_option autoImplicit false
set_option maxRecDepth 10000
namespace NearlyOptimalPPR.Computation

def jointSolveIterationFactor (ell top rank : ℕ) : ℕ := (top+1)*(42*rank+88*(16*(ell+3))+442)

end NearlyOptimalPPR.Computation

-- Runtime interface from Solutions.CachedJointSolveExecution

set_option autoImplicit false
set_option maxRecDepth 10000
open scoped ENNReal
namespace NearlyOptimalPPR.Computation
noncomputable section

def cachedJointSolveCode : MachineCode := .seq cachedPrincipalSolveCode jointSolveIterationCode

end
end NearlyOptimalPPR.Computation

-- Runtime interface from Solutions.ListJointSolveExecution

set_option autoImplicit false
set_option maxRecDepth 10000
open scoped ENNReal
namespace NearlyOptimalPPR.Computation
noncomputable section

def listJointSolveCode : MachineCode := .seq vertexEnumerationCode cachedJointSolveCode
end
end NearlyOptimalPPR.Computation

-- Runtime interface from Solutions.CacheJointSolveExecution

set_option autoImplicit false
set_option maxRecDepth 10000
open scoped ENNReal
namespace NearlyOptimalPPR.Computation
noncomputable section

def cacheJointSolvePreludeCode : MachineCode := .seq (levelHeaderIntegerToCode 4 90) (coreCode (.pset 83 1))
def cacheJointSolveCode : MachineCode := .seq cacheJointSolvePreludeCode listJointSolveCode
end
end NearlyOptimalPPR.Computation

-- Runtime interface from Solutions.LeafCachedSolveExecution

set_option autoImplicit false
set_option maxRecDepth 10000
open scoped ENNReal
namespace NearlyOptimalPPR.Computation
noncomputable section

def leafCachedSolveCode : MachineCode := .seq leafRHSCode cacheJointSolveCode
end
end NearlyOptimalPPR.Computation

-- Runtime interface from Solutions.LeafJointSolveExecution

set_option autoImplicit false
set_option maxRecDepth 10000
open scoped ENNReal
namespace NearlyOptimalPPR.Computation
open SparseQueue
noncomputable section

def leafPreparationFactor (ell top length rank : ℕ) : ℕ :=
  let P := cleanBodyBound (16*(ell+3)) length rank+2
  P+20*(16*(ell+3))+190+((top+1)*(42*rank+60*(16*(ell+3))+284)+21)+P*(2*(top+1))+21
def leafSolveUnitCost (ell top rank card size : ℕ) : ℕ :=
  ((12*(16*(ell+3))+56)*card+11)+
    ((10*card+5)+((24*(16*(ell+3))+100)*size+28)+(jointSolveIterationFactor ell top rank*size+5)+11)
def leafJointSolveCode : MachineCode := .seq leafCachePreparationCode leafCachedSolveCode
end
end NearlyOptimalPPR.Computation

-- Runtime interface from Solutions.ChangePCExecution

set_option autoImplicit false
set_option maxRecDepth 10000
namespace NearlyOptimalPPR.Computation
noncomputable section

def changePCCode (pc : NormalizePC) : MachineCode := levelHeaderIntegerSetCode 0 (normalizePCNumber pc : ℤ)
end
end NearlyOptimalPPR.Computation

-- Runtime interface from Solutions.LeafDecisionExecution

set_option autoImplicit false
set_option maxRecDepth 10000
open scoped ENNReal
namespace NearlyOptimalPPR.Computation
open SparseQueue
noncomputable section

def compilerLeafDecision {n : ℕ} (m : SolveModel) (g : InputGraph n) (α : ℝ) (logical : RecursiveState n) : RecursiveState n :=
  if (logical.frames logical.top).high=∅ then changePC (debit logical logical.top 1) .afterChild
  else compilerLeafSolve m g α logical

def leafDecisionCode : MachineCode := .seq highPeekCode
  (.branchPointer 97 0 (changePCCode .afterChild) leafJointSolveCode)
end
end NearlyOptimalPPR.Computation

-- Runtime interface from Solutions.InitialEmptyExecution

set_option autoImplicit false
set_option maxRecDepth 10000
namespace NearlyOptimalPPR.Computation
noncomputable section

def compilerInitialEmpty {n : ℕ} (logical : RecursiveState n) : RecursiveState n :=
  changePC (debit logical logical.top 1) (if (logical.frames logical.top).active=∅ then .normal else .beginEpisode)

def initialEmptyCode : MachineCode := .seq (levelHeaderIntegerToCode 3 175)
  (.branchPointer 175 0 (changePCCode .normal) (changePCCode .beginEpisode))
end
end NearlyOptimalPPR.Computation

-- Runtime interface from Solutions.FrameResidualSumPrelude

set_option autoImplicit false
set_option maxRecDepth 10000
namespace NearlyOptimalPPR.Computation
noncomputable section

def frameResidualSumPointerRoutine : PointerRoutine := .sequence [
  .atom (.copy 83 100),.atom (.inc 83),.atom (.add 83 83 83),.atom (.add 83 83 83),
  .atom (.add 83 83 83),.atom (.add 83 83 83),.atom (.inc 83),.atom (.copy 41 50)]
def frameResidualSumPreludeCode : MachineCode := .seq (levelHeaderIntegerToCode 1 94)
  (.seq frameResidualSumPointerRoutine.code (coreCode (.const 70 0)))

end
end NearlyOptimalPPR.Computation

-- Runtime interface from Solutions.VertexResidualSumBody

set_option autoImplicit false
set_option maxRecDepth 10000
namespace NearlyOptimalPPR.Computation
noncomputable section

def vertexResidualSumBodyCode : MachineCode := .seq pushOutputReadCode
  (.seq (coreCode (.pcopy 44 83)) (.seq vertexRealLoadCode (coreCode (.add 70 70 10))))
def vertexResidualSumLoopCode : MachineCode := .whilePointer 94 0 vertexResidualSumBodyCode

end
end NearlyOptimalPPR.Computation

-- Runtime interface from Solutions.FrameResidualSumExecution

set_option autoImplicit false
set_option maxRecDepth 10000
namespace NearlyOptimalPPR.Computation
noncomputable section

def frameResidualSumCode : MachineCode := .seq frameResidualSumPreludeCode vertexResidualSumLoopCode
end
end NearlyOptimalPPR.Computation

-- Runtime interface from Solutions.EpisodeMaximumExecution

set_option autoImplicit false
set_option maxRecDepth 10000
namespace NearlyOptimalPPR.Computation
noncomputable section

def episodeMaximumCode : MachineCode := .seq (coreCode (.sub 74 70 73))
  (.branchReal 74 (coreCode (.mul 75 73 31)) (coreCode (.mul 75 70 31)))
end
end NearlyOptimalPPR.Computation

-- Runtime interface from Solutions.EpisodeBudgetScalarExecution

set_option autoImplicit false
set_option maxRecDepth 10000
namespace NearlyOptimalPPR.Computation
noncomputable section

def episodeBudgetProductInstructions : List Instruction := [
  .scalar (.pointerReal 72 180),.scalar (.core (.mul 73 71 72))]
def episodeBudgetProductCode : MachineCode := linearCode episodeBudgetProductInstructions

def episodeBudgetScalarCode : MachineCode := .seq (levelHeaderRealToCode 1 71)
  (.seq (levelHeaderIntegerToCode 14 180) (.seq episodeBudgetProductCode
    (.seq episodeMaximumCode (coreCode (.div 76 75 72)))))
end
end NearlyOptimalPPR.Computation

-- Runtime interface from Solutions.FrameEpisodeParametersExecution

set_option autoImplicit false
set_option maxRecDepth 10000
namespace NearlyOptimalPPR.Computation
noncomputable section

def frameEpisodeParametersCode : MachineCode := .seq frameResidualSumCode episodeBudgetScalarCode
end
end NearlyOptimalPPR.Computation

-- Runtime interface from Solutions.FrameCacheClearPrelude

set_option autoImplicit false
set_option maxRecDepth 10000
namespace NearlyOptimalPPR.Computation
noncomputable section

def frameCacheClearPointerRoutine : PointerRoutine := .sequence [
  .atom (.copy 182 100),.atom (.inc 182),.atom (.add 182 182 182),.atom (.add 182 182 182),
  .atom (.add 182 182 182),.atom (.add 182 182 182),.atom (.set 183 4),.atom (.add 182 182 183),.atom (.copy 41 50)]
def frameCacheClearPreludeCode : MachineCode := .seq (levelHeaderIntegerToCode 1 94) frameCacheClearPointerRoutine.code
end
end NearlyOptimalPPR.Computation

-- Runtime interface from Solutions.ClearVertexFieldBody

set_option autoImplicit false
set_option maxRecDepth 10000
namespace NearlyOptimalPPR.Computation
noncomputable section

def clearVertexFieldPrepRoutine : PointerRoutine := .sequence [.atom (.copy 44 182),.atom (.copy 51 0)]
def clearVertexFieldBodyCode : MachineCode := .seq pushOutputReadCode
  (.seq clearVertexFieldPrepRoutine.code vertexIntegerStoreCode)
def clearVertexFieldLoopCode : MachineCode := .whilePointer 94 0 clearVertexFieldBodyCode
end
end NearlyOptimalPPR.Computation

-- Runtime interface from Solutions.FrameCacheClearExecution

set_option autoImplicit false
set_option maxRecDepth 10000
namespace NearlyOptimalPPR.Computation
noncomputable section

def frameCacheClearCode : MachineCode := .seq frameCacheClearPreludeCode clearVertexFieldLoopCode
end
end NearlyOptimalPPR.Computation

-- Runtime interface from Solutions.EpisodePCExecution

set_option autoImplicit false
set_option maxRecDepth 10000
namespace NearlyOptimalPPR.Computation
noncomputable section

def episodePCCode : MachineCode := .seq (levelHeaderIntegerToCode 10 181)
  (.branchPointer 181 0 (levelHeaderIntegerSetCode 0 (normalizePCNumber .normalize : ℤ))
    (levelHeaderIntegerSetCode 0 (normalizePCNumber .fullSolve : ℤ)))
end
end NearlyOptimalPPR.Computation

-- Runtime interface from Solutions.EpisodeHeaderExecution

set_option autoImplicit false
set_option maxRecDepth 10000
namespace NearlyOptimalPPR.Computation
noncomputable section

def episodeIntegerAssignments : List (ℕ × ℤ) := [(4,0),(5,0),(6,0),(9,1),(11,0)]
def episodeHeaderCode : MachineCode := .seq (levelHeaderRealFromCode 3 75)
  (.seq (levelHeaderRealZeroCode 4) (.seq (levelHeaderRealFromCode 5 76)
    (.seq (levelHeaderIntegerSetsCode episodeIntegerAssignments) episodePCCode)))
end
end NearlyOptimalPPR.Computation

-- Runtime interface from Solutions.EpisodeRawExecution

set_option autoImplicit false
set_option maxRecDepth 10000
namespace NearlyOptimalPPR.Computation
noncomputable section

def episodeRawCode : MachineCode := .seq frameEpisodeParametersCode (.seq frameCacheClearCode episodeHeaderCode)
end
end NearlyOptimalPPR.Computation

-- Runtime interface from Solutions.EnumeratedEpisodePendingExecution

set_option autoImplicit false
set_option maxRecDepth 10000
namespace NearlyOptimalPPR.Computation
noncomputable section

def enumeratedEpisodePendingCode : MachineCode := .seq (levelHeaderIntegerToCode 1 90)
  (.seq vertexEnumerationCode episodeRawCode)
end
end NearlyOptimalPPR.Computation

-- Runtime interface from Solutions.BeginEpisodeExecution

set_option autoImplicit false
set_option maxRecDepth 10000
namespace NearlyOptimalPPR.Computation
noncomputable section

def beginEpisodeCode : MachineCode :=
  .seq enumeratedEpisodePendingCode pendingArrayRefreshCode

end
end NearlyOptimalPPR.Computation

-- Runtime interface from Solutions.ActiveJointSolvePrelude

set_option autoImplicit false
set_option maxRecDepth 10000
namespace NearlyOptimalPPR.Computation
noncomputable section

def activeJointOffsetRoutine : PointerRoutine := .sequence [.atom (.copy 83 87),.atom (.inc 83)]
def activeJointSolvePreludeCode : MachineCode := .seq (levelHeaderIntegerToCode 1 90)
  (.seq levelContextCode activeJointOffsetRoutine.code)
end
end NearlyOptimalPPR.Computation

-- Runtime interface from Solutions.ActiveJointSolveExecution

set_option autoImplicit false
set_option maxRecDepth 10000
open scoped ENNReal
namespace NearlyOptimalPPR.Computation
noncomputable section

def activeJointSolveCode : MachineCode := .seq activeJointSolvePreludeCode listJointSolveCode
end
end NearlyOptimalPPR.Computation

-- Runtime interface from Solutions.FullJointSolveExecution

set_option autoImplicit false
set_option maxRecDepth 10000
open scoped ENNReal
namespace NearlyOptimalPPR.Computation
noncomputable section

def fullJointSolveCode : MachineCode := .seq activeJointSolveCode (changePCCode .normalize)
end
end NearlyOptimalPPR.Computation

-- Runtime interface from Solutions.FullSolveDecisionExecution

set_option autoImplicit false
set_option maxRecDepth 10000
open scoped ENNReal
namespace NearlyOptimalPPR.Computation
noncomputable section

def fullSolveDecisionCode : MachineCode := .seq (levelHeaderIntegerToCode 3 175)
  (.branchPointer 175 0 (changePCCode .normalize) fullJointSolveCode)
end
end NearlyOptimalPPR.Computation

-- Runtime interface from Solutions.FreshVertexList

set_option autoImplicit false
set_option maxRecDepth 10000
open scoped ENNReal
namespace NearlyOptimalPPR.Computation
open SparseQueue
noncomputable section

def freshVertexListBodyCode : MachineCode := .seq pushOutputReadCode freshVertexCode
def freshVertexListCode : MachineCode := .whilePointer 94 0 freshVertexListBodyCode

end
end NearlyOptimalPPR.Computation

-- Runtime interface from Solutions.ExteriorPopulateCode

set_option autoImplicit false
set_option maxRecDepth 10000
namespace NearlyOptimalPPR.Computation
namespace SparseQueue
noncomputable section

def exteriorPopulateBodyCode : MachineCode := .seq pushOutputReadCode exteriorQueueRefreshCode
def exteriorPopulateCode : MachineCode := .whilePointer 94 0 exteriorPopulateBodyCode
end
end SparseQueue
end NearlyOptimalPPR.Computation

-- Runtime interface from Solutions.FreshCallCode

set_option autoImplicit false
namespace NearlyOptimalPPR.Computation
noncomputable section


def freshCallSetupCode : MachineCode := .seq freshHeaderCode
  (.seq (coreCode (.pcopy 94 113)) (.seq freshVertexListCode
    (.seq (coreCode (.pcopy 94 113)) exteriorFrameContextCode)))
def freshCallCode : MachineCode := .seq freshCallSetupCode SparseQueue.exteriorPopulateCode
end
end NearlyOptimalPPR.Computation

-- Runtime interface from Solutions.FreshChildPreparation

set_option autoImplicit false
set_option maxRecDepth 10000
open scoped ENNReal
namespace NearlyOptimalPPR.Computation
noncomputable section

def freshChildPreparationCode : MachineCode := .seq (levelHeaderIntegerToCode 1 113)
  (.seq (levelHeaderIntegerRealCode 14 12) (.seq (levelHeaderRealToCode 5 13)
    (.seq (levelHeaderIncrementCode 11) (.seq (levelHeaderIntegerSetCode 0 5) (coreCode (.pinc 100))))))
def freshChildRawCode : MachineCode := .seq freshChildPreparationCode freshCallCode
def freshChildCode : MachineCode := .seq freshChildRawCode (coreCode (.load 30 0))

end
end NearlyOptimalPPR.Computation

-- Runtime interface from Solutions.FrameCacheListClearPrelude

set_option autoImplicit false
set_option maxRecDepth 10000
namespace NearlyOptimalPPR.Computation
noncomputable section

def frameCacheListClearPointerRoutine : PointerRoutine := .sequence [
  .atom (.copy 182 100),.atom (.inc 182),.atom (.add 182 182 182),.atom (.add 182 182 182),
  .atom (.add 182 182 182),.atom (.add 182 182 182),.atom (.set 183 4),.atom (.add 182 182 183),.atom (.copy 41 50)]
def frameCacheListClearPreludeCode : MachineCode := .seq (levelHeaderIntegerToCode 4 94) frameCacheListClearPointerRoutine.code
end
end NearlyOptimalPPR.Computation

-- Runtime interface from Solutions.FrameCacheListClearExecution

set_option autoImplicit false
set_option maxRecDepth 10000
namespace NearlyOptimalPPR.Computation
noncomputable section

def frameCacheListClearCode : MachineCode := .seq frameCacheListClearPreludeCode clearVertexFieldLoopCode
end
end NearlyOptimalPPR.Computation

-- Runtime interface from Solutions.FinishEpisodeRawExecution

set_option autoImplicit false
set_option maxRecDepth 10000
namespace NearlyOptimalPPR.Computation
noncomputable section

def finishEpisodeAssignments : List (ℕ × ℤ) := [(4,0),(5,0),(6,0),(9,0)]
def finishEpisodeCode : MachineCode := .seq frameCacheListClearCode
  (levelHeaderIntegerSetsCode finishEpisodeAssignments)
end
end NearlyOptimalPPR.Computation

-- Runtime interface from Solutions.NeedFullArithmetic

set_option autoImplicit false
open scoped ENNReal
namespace NearlyOptimalPPR.Computation
noncomputable section

def needFullArithmeticInstructions : List Instruction := [
  .scalar (.core (.const 74 (1/2))),.scalar (.core (.mul 73 75 74)),.scalar (.core (.sub 76 73 70))]
def needFullArithmeticCode : MachineCode := linearCode needFullArithmeticInstructions
end
end NearlyOptimalPPR.Computation

-- Runtime interface from Solutions.SetNeedFullExecution

set_option autoImplicit false
set_option maxRecDepth 10000
namespace NearlyOptimalPPR.Computation
noncomputable section

def setNeedFullCode (need : Bool) : MachineCode := levelHeaderIntegerSetCode 10 (if need then 1 else 0)
end
end NearlyOptimalPPR.Computation

-- Runtime interface from Solutions.NeedFullDecisionExecution

set_option autoImplicit false
set_option maxRecDepth 10000
namespace NearlyOptimalPPR.Computation
noncomputable section

def needFullPrepareCode : MachineCode := .seq (levelHeaderRealToCode 3 75) needFullArithmeticCode
def needFullDecisionCode : MachineCode := .seq needFullPrepareCode
  (.branchReal 76 (setNeedFullCode true) (setNeedFullCode false))
end
end NearlyOptimalPPR.Computation

-- Runtime interface from Solutions.ReturnPCPreparation

set_option autoImplicit false
set_option maxRecDepth 10000
namespace NearlyOptimalPPR.Computation
noncomputable section

def returnPCPrepareCode : MachineCode := .seq (levelHeaderRealToCode 5 77)
  (.seq (levelHeaderRealToCode 1 78) (coreCode (.sub 79 77 78)))
end
end NearlyOptimalPPR.Computation

-- Runtime interface from Solutions.ReturnPCGuardExecution

set_option autoImplicit false
set_option maxRecDepth 10000
namespace NearlyOptimalPPR.Computation
noncomputable section

def returnPCGuardCode : MachineCode := .branchReal 79
  (.seq (coreCode (.sub 80 78 77)) (.branchReal 80 (changePCCode .normal) (changePCCode .beginEpisode)))
  (changePCCode .beginEpisode)
end
end NearlyOptimalPPR.Computation

-- Runtime interface from Solutions.ReturnPCExecution

set_option autoImplicit false
set_option maxRecDepth 10000
namespace NearlyOptimalPPR.Computation
noncomputable section

def returnPCCode : MachineCode := .seq returnPCPrepareCode returnPCGuardCode
end
end NearlyOptimalPPR.Computation

-- Runtime interface from Solutions.FinishRequestExecution

set_option autoImplicit false
set_option maxRecDepth 10000
namespace NearlyOptimalPPR.Computation
noncomputable section

def finishRequestCode : MachineCode := .seq frameResidualSumCode
  (.seq finishEpisodeCode (.seq needFullDecisionCode returnPCCode))
end
end NearlyOptimalPPR.Computation

-- Runtime interface from Solutions.InterruptEpisodeExecution

set_option autoImplicit false
set_option maxRecDepth 10000
namespace NearlyOptimalPPR.Computation
noncomputable section

def interruptEpisodeCode (pc : NormalizePC) : MachineCode := .seq finishEpisodeCode (changePCCode pc)
end
end NearlyOptimalPPR.Computation

-- Runtime interface from Solutions.RestartRequestExecution

set_option autoImplicit false
set_option maxRecDepth 10000
namespace NearlyOptimalPPR.Computation
noncomputable section

def compilerRestartRequest {n : ℕ} (logical : RecursiveState n) : RecursiveState n :=
  changePC (compilerSetNeedFull (debit logical logical.top 1) true) .beginEpisode

def restartRequestCode : MachineCode := .seq (setNeedFullCode true) (changePCCode .beginEpisode)
end
end NearlyOptimalPPR.Computation

-- Runtime interface from Solutions.ExteriorPushBound

set_option autoImplicit false
set_option maxRecDepth 10000
namespace NearlyOptimalPPR.Computation
noncomputable section

def exteriorPushBound (ell top rank degree : ℕ) : ℕ :=
  let width := 16*(ell+3)
  84*width+452+(top+1)*(4*width+60)+degree*((top+1)*(8*width+39)+8*width+50)+
    (degree+1)*((top+1)*(42*rank+60*width+284)+4*width+25)

end
end NearlyOptimalPPR.Computation

-- Runtime interface from Solutions.DrainDecisionExecution

set_option autoImplicit false
set_option maxRecDepth 10000
namespace NearlyOptimalPPR.Computation
open SparseQueue
noncomputable section

def compilerDrain {n : ℕ} (g : InputGraph n) (α : ℝ) (logical : RecursiveState n) (pc : NormalizePC) : RecursiveState n :=
  match pendingPush logical with
  | none => changePC (debit logical logical.top 1) pc
  | some (t,v) => exteriorPush g α logical t v

def drainDegree {n : ℕ} (g : InputGraph n) (logical : RecursiveState n) : ℕ :=
  match pendingPush logical with
  | none => 0
  | some (_,v) => (g.neighbors v).length

def drainDecisionCode (pc : NormalizePC) : MachineCode := .seq priorityCode
  (.branchPointer 97 0 (changePCCode pc) exteriorPushProgramCode)
end
end NearlyOptimalPPR.Computation

-- Runtime interface from Solutions.RootSparseOutputPrelude

set_option autoImplicit false
namespace NearlyOptimalPPR.Computation
noncomputable section

def rootSparseOutputPreludeInstructions : List Instruction := [
  .scalar (.core (.pset 94 129)),.scalar (.integerLoad 94 94),
  .scalar (.core (.pset 40 129)),.scalar (.core (.load 32 40)),
  .scalar (.core (.const 33 3)),.scalar (.core (.mul 32 32 33)),
  .scalar (.core (.const 33 8)),.scalar (.core (.div 32 32 33)),
  .scalar (.core (.pcopy 41 50))]
def rootSparseOutputPreludeCode : MachineCode := linearCode rootSparseOutputPreludeInstructions

end
end NearlyOptimalPPR.Computation

-- Runtime interface from Solutions.PushOutputScalar

set_option autoImplicit false
namespace NearlyOptimalPPR.Computation
noncomputable section

def pushOutputScalarInstructions : List Instruction := [
  .scalar (.pointerReal 11 60), .scalar (.core (.mul 10 10 11)), .scalar (.core (.mul 10 30 10)), .emit 40 10]
def pushOutputScalarCode : MachineCode := linearCode pushOutputScalarInstructions

end
end NearlyOptimalPPR.Computation

-- Runtime interface from Solutions.PruneOutputScalar

set_option autoImplicit false
namespace NearlyOptimalPPR.Computation
noncomputable section

def pruneOutputClipCode : MachineCode := .seq (coreCode (.sub 10 10 32))
  (.branchReal 10 (coreCode (.const 10 0)) .skip)

end
end NearlyOptimalPPR.Computation

-- Runtime interface from Solutions.PrunedOutputBody

set_option autoImplicit false
set_option maxRecDepth 10000
namespace NearlyOptimalPPR.Computation
noncomputable section

def prunedOutputBodyCode : MachineCode := .seq pushOutputReadCode
  (.seq vertexRealLoadCode (.seq (vertexFieldReadCode 0 60) (.seq pruneOutputClipCode pushOutputScalarCode)))
def prunedOutputLoopCode : MachineCode := .whilePointer 94 0 prunedOutputBodyCode

end
end NearlyOptimalPPR.Computation

-- Runtime interface from Solutions.RootSparseOutputExecution

set_option autoImplicit false
set_option maxRecDepth 10000
namespace NearlyOptimalPPR.Computation
noncomputable section

def rootSparseOutputCode : MachineCode := .seq rootSparseOutputPreludeCode prunedOutputLoopCode
end
end NearlyOptimalPPR.Computation

-- Runtime interface from Solutions.RootComponentPrelude

set_option autoImplicit false
namespace NearlyOptimalPPR.Computation
noncomputable section

def rootComponentPreludeRoutine : PointerRoutine := .sequence [
  .atom (.set 90 129),.atom (.load 90 90),.atom (.set 83 2)]

end
end NearlyOptimalPPR.Computation

-- Runtime interface from Solutions.SolveAnswerOutputBody

set_option autoImplicit false
set_option maxRecDepth 10000
namespace NearlyOptimalPPR.Computation
noncomputable section

def solveAnswerOutputBodyCode : MachineCode := .seq jointSolveIterationReadCode
  (.seq (vertexFieldReadCode 0 60) (.seq (coreCode (.mul 10 40 31))
    (.seq pushOutputScalarCode (coreCode (.pinc 143)))))
def solveAnswerOutputLoopCode : MachineCode := .whilePointer 142 143 solveAnswerOutputBodyCode

end
end NearlyOptimalPPR.Computation

-- Runtime interface from Solutions.SolveAnswerOutputExecution

set_option autoImplicit false
set_option maxRecDepth 10000
namespace NearlyOptimalPPR.Computation
noncomputable section

def solveAnswerOutputInitRoutine : PointerRoutine := .sequence [
  .atom (.copy 140 80),.atom (.copy 141 79),.atom (.copy 142 77),.atom (.set 143 0),.atom (.copy 41 50)]
def solveAnswerOutputCode : MachineCode := .seq solveAnswerOutputInitRoutine.code solveAnswerOutputLoopCode

end
end NearlyOptimalPPR.Computation

-- Runtime interface from Solutions.CachedSolveOutputExecution

set_option autoImplicit false
set_option maxRecDepth 10000
open scoped ENNReal
namespace NearlyOptimalPPR.Computation
noncomputable section

def cachedSolveOutputCode : MachineCode := .seq cachedPrincipalSolveCode solveAnswerOutputCode
end
end NearlyOptimalPPR.Computation

-- Runtime interface from Solutions.ListSolveOutputExecution

set_option autoImplicit false
set_option maxRecDepth 10000
open scoped ENNReal
namespace NearlyOptimalPPR.Computation
noncomputable section

def listSolveOutputCode : MachineCode := .seq vertexEnumerationCode cachedSolveOutputCode
end
end NearlyOptimalPPR.Computation

-- Runtime interface from Solutions.RootComponentSolveExecution

set_option autoImplicit false
set_option maxRecDepth 10000
open scoped ENNReal
namespace NearlyOptimalPPR.Computation
noncomputable section

def rootComponentSolveCode : MachineCode := .seq rootComponentPreludeRoutine.code listSolveOutputCode
end
end NearlyOptimalPPR.Computation

-- Runtime interface from Solutions.RecursiveControllerCode

set_option autoImplicit false
set_option maxRecDepth 10000
namespace NearlyOptimalPPR.Computation
noncomputable section

def stopControllerCode : MachineCode := coreCode (.pset 150 1)
def controllerRootReturnCode : MachineCode := .seq rootSparseOutputCode stopControllerCode
def controllerComponentCode : MachineCode := .seq rootComponentSolveCode stopControllerCode
def controllerReturnCode : MachineCode := .branchPointer 100 0 controllerRootReturnCode (coreCode (.pdec 100))
def controllerInitialCode : MachineCode := .branchPointer 170 0
  (.seq priorityCode (.branchPointer 97 0 initialEmptyCode
    (.branchPointer 160 0 exteriorPushProgramCode (changePCCode .initialDrain)))) (changePCCode .interrupted)
def controllerFullCode : MachineCode := .branchPointer 160 0 fullSolveDecisionCode (changePCCode .afterChild)
def controllerDepthRoutine : PointerRoutine := .sequence [.atom (.set 171 2),.atom (.load 171 171)]
def controllerDepthCode : MachineCode := .seq controllerDepthRoutine.code
  (.seq (coreCode (.pdec 171)) (coreCode (.pdec 171)))
def controllerNormalizeCode : MachineCode := .branchPointer 160 0
  (.seq controllerDepthCode (.branchPointer 171 100 (changePCCode .leafDrain) freshChildCode)) (changePCCode .afterChild)
def controllerLeafCode : MachineCode := .branchPointer 160 0
  (.seq priorityCode (.branchPointer 97 0 leafDecisionCode exteriorPushProgramCode)) (changePCCode .afterChild)
def controllerAfterChildCode : MachineCode := .branchPointer 170 0
  (.branchPointer 160 0 (drainDecisionCode .finishEpisode) (interruptEpisodeCode .restartDrain)) (interruptEpisodeCode .interrupted)
def controllerFinishCode : MachineCode := .branchPointer 170 0
  (.branchPointer 160 0 finishRequestCode (interruptEpisodeCode .restartDrain)) (interruptEpisodeCode .interrupted)
def controllerRestartCode : MachineCode := .branchPointer 170 0
  (.seq priorityCode (.branchPointer 97 0 restartRequestCode
    (.branchPointer 160 0 exteriorPushProgramCode (changePCCode .restartDrain)))) (changePCCode .interrupted)

def numberedDispatchCode (start : ℕ) (branches : List MachineCode) : MachineCode :=
  match branches with
  | [] => .skip
  | b::bs => .seq (coreCode (.pset 153 (start : ℤ))) (.branchPointer 152 153 b (numberedDispatchCode (start+1) bs))
def controllerBranches : List MachineCode := [controllerInitialCode,beginEpisodeCode,controllerFullCode,
  controllerNormalizeCode,controllerLeafCode,controllerAfterChildCode,controllerFinishCode,controllerRestartCode,
  controllerReturnCode,controllerReturnCode]
def controllerOrdinaryCode : MachineCode := .seq budgetStatusCode
  (.seq (levelHeaderIntegerToCode 0 152) (numberedDispatchCode 0 controllerBranches))
def controllerComponentTestRoutine : PointerRoutine := .sequence [
  .atom (.set 176 131),.atom (.load 176 176),.atom (.set 177 7),.atom (.load 177 177)]
def controllerBodyCode : MachineCode := .seq controllerComponentTestRoutine.code
  (.branchPointer 176 0 controllerOrdinaryCode (.branchPointer 177 0 controllerComponentCode controllerOrdinaryCode))
def recursiveControllerCode : MachineCode := .whilePointer 151 150 controllerBodyCode

end
end NearlyOptimalPPR.Computation

-- Runtime interface from Solutions.ControllerFullExecution

set_option autoImplicit false
set_option maxRecDepth 10000
open scoped ENNReal
namespace NearlyOptimalPPR.Computation
noncomputable section
attribute [local instance] Classical.propDecidable

def compilerFullDecision {n : ℕ} (m : SolveModel) (g : InputGraph n) (α : ℝ) (logical : RecursiveState n) : RecursiveState n :=
  if anyExhausted logical then changePC (debit logical logical.top 1) .afterChild else compilerFullSolve m g α logical

end
end NearlyOptimalPPR.Computation

-- Runtime interface from Solutions.ControllerSelectedDrain

set_option autoImplicit false
set_option maxRecDepth 10000
open scoped ENNReal
namespace NearlyOptimalPPR.Computation
noncomputable section
attribute [local instance] Classical.propDecidable

def compilerSelectedDrain {n : ℕ} (g : InputGraph n) (α : ℝ) (logical : RecursiveState n) (pc : NormalizePC) : RecursiveState n :=
  if ¬anyExhausted logical then compilerDrain g α logical pc else changePC (debit logical logical.top 1) pc

def selectedExteriorCharge {n : ℕ} (g : InputGraph n) (logical : RecursiveState n) (ell rank P : ℕ) : ℝ≥0∞ :=
  (((logical.top+1)*(drainDegree g logical+1)*(42*rank+168*(16*(ell+3))+910)+P*(2*(logical.top+1)*(drainDegree g logical+1)) : ℕ) : ℝ≥0∞)

end
end NearlyOptimalPPR.Computation

-- Runtime interface from Solutions.ControllerInitialRestart

set_option autoImplicit false
set_option maxRecDepth 10000
open scoped ENNReal
namespace NearlyOptimalPPR.Computation
open SparseQueue
noncomputable section
attribute [local instance] Classical.propDecidable

def compilerInitialRestart {n : ℕ} (g : InputGraph n) (α : ℝ) (logical : RecursiveState n)
    (pc : NormalizePC) (noPending : RecursiveState n) : RecursiveState n :=
  if ¬ancestorExhausted logical then compilerPriorityChoice logical noPending (compilerSelectedDrain g α logical pc)
  else changePC (debit logical logical.top 1) .interrupted

def initialRestartGrowth {n : ℕ} (g : InputGraph n) (logical : RecursiveState n) : ℕ :=
  if ¬ancestorExhausted logical then
    if (pendingPush logical).isSome then
      if ¬anyExhausted logical then 2*(logical.top+1)*(drainDegree g logical+1) else 0
    else 0
  else 0

def initialRestartCharge {n : ℕ} (g : InputGraph n) (logical : RecursiveState n)
    (ell length rank : ℕ) (noCharge : ℝ≥0∞) : ℝ≥0∞ :=
  let P := cleanBodyBound (16*(ell+3)) length rank+2
  (if ¬ancestorExhausted logical then controllerPriorityCharge logical ell length rank noCharge
    ((if ¬anyExhausted logical then selectedExteriorCharge g logical ell rank P else 10)+2)
  else 10)+2

end
end NearlyOptimalPPR.Computation

-- Runtime interface from Solutions.ControllerNormalizeDecision

set_option autoImplicit false
set_option maxRecDepth 10000
open scoped ENNReal
namespace NearlyOptimalPPR.Computation
noncomputable section
attribute [local instance] Classical.propDecidable

def controllerChildCharge {n : ℕ} (logical : RecursiveState n) (ell length rank P : ℕ) : ℝ≥0∞ :=
  ((((logical.frames logical.top).block+2)*(4*(ell-(logical.top+1))+22)+10*length+324+
    (logical.frames logical.top).active.card*(21*rank+60*(16*(ell+3))+190)+P*(logical.frames logical.top).active.card : ℕ) : ℝ≥0∞)

def compilerNormalizeInner {n : ℕ} (g : InputGraph n) (ell : ℕ) (logical : RecursiveState n) : RecursiveState n :=
  if logical.top=ell then changePC (debit logical logical.top 1) .leafDrain else spawnChildState g ell logical

def compilerNormalizeDecision {n : ℕ} (g : InputGraph n) (ell : ℕ) (logical : RecursiveState n) : RecursiveState n :=
  if ¬anyExhausted logical then compilerNormalizeInner g ell logical else changePC (debit logical logical.top 1) .afterChild

end
end NearlyOptimalPPR.Computation

-- Runtime interface from Solutions.ControllerPendingExecution

set_option autoImplicit false
set_option maxRecDepth 10000
open scoped ENNReal
namespace NearlyOptimalPPR.Computation
open SparseQueue
noncomputable section

def compilerPendingDecision {n : ℕ} (g : InputGraph n) (α : ℝ) (logical noPending : RecursiveState n) : RecursiveState n :=
  match pendingPush logical with
  | none => noPending
  | some (t,v) => exteriorPush g α logical t v

def controllerPendingGrowth {n : ℕ} (g : InputGraph n) (logical : RecursiveState n) (noneGrowth : ℕ) : ℕ :=
  match pendingPush logical with
  | none => noneGrowth
  | some (_,v) => 2*(logical.top+1)*((g.neighbors v).length+1)

def controllerPendingCharge {n : ℕ} (g : InputGraph n) (logical : RecursiveState n) (ell length rank : ℕ) (noneCharge : ℝ≥0∞) : ℝ≥0∞ :=
  let P := cleanBodyBound (16*(ell+3)) length rank+2
  let T := (logical.top+1)*(2*P+(21*rank+20*(16*(ell+3))+70)+50)+6
  ((T : ℕ) : ℝ≥0∞)+(match pendingPush logical with
  | none => noneCharge
  | some (_,v) => (((logical.top+1)*((g.neighbors v).length+1)*(42*rank+168*(16*(ell+3))+910)+
      P*(2*(logical.top+1)*((g.neighbors v).length+1)) : ℕ) : ℝ≥0∞))+2

end
end NearlyOptimalPPR.Computation

-- Runtime interface from Solutions.ControllerLeafTight

set_option autoImplicit false
set_option maxRecDepth 10000
open scoped ENNReal
namespace NearlyOptimalPPR.Computation
open SparseQueue
noncomputable section
attribute [local instance] Classical.propDecidable

def leafTightGrowth {n : ℕ} (g : InputGraph n) (logical : RecursiveState n) : ℕ :=
  if (logical.frames logical.top).high=∅ then 0 else
    let C := (logical.frames logical.top).cache ∪ (logical.frames logical.top).high
    2*(logical.top+1)*(C.card+(volumeNat g C+C.card))

def leafTightCharge {n : ℕ} (m : SolveModel) (g : InputGraph n) (logical : RecursiveState n) (ell length rank Q : ℕ) : ℝ≥0∞ :=
  let P := cleanBodyBound (16*(ell+3)) length rank+2
  let H := 2*P+(21*rank+20*(16*(ell+3))+70)+36
  if (logical.frames logical.top).high=∅ then ((H+12 : ℕ) : ℝ≥0∞) else
    let C := (logical.frames logical.top).cache ∪ (logical.frames logical.top).high
    let size := volumeNat g C+C.card
    let A := (C.card+1)*leafPreparationFactor ell logical.top length rank
    let B := leafSolveUnitCost ell logical.top rank C.card size
    let S := A+B+P*(2*(logical.top+1)*size)
    ((H+S+12+Q*C.card : ℕ) : ℝ≥0∞)+solveCharge m C.card size

end
end NearlyOptimalPPR.Computation

-- Runtime interface from Solutions.ControllerLeafDecision

set_option autoImplicit false
set_option maxRecDepth 10000
open scoped ENNReal
namespace NearlyOptimalPPR.Computation
open SparseQueue
noncomputable section
attribute [local instance] Classical.propDecidable

def leafControllerGrowth {n : ℕ} (g : InputGraph n) (logical : RecursiveState n) : ℕ :=
  leafTightGrowth g logical

def leafControllerCharge {n : ℕ} (m : SolveModel) (g : InputGraph n) (logical : RecursiveState n) (ell length rank Q : ℕ) : ℝ≥0∞ :=
  leafTightCharge m g logical ell length rank Q

def compilerLeafController {n : ℕ} (m : SolveModel) (g : InputGraph n) (α : ℝ) (logical : RecursiveState n) : RecursiveState n :=
  if ¬anyExhausted logical then compilerPendingDecision g α logical (compilerLeafDecision m g α logical)
  else changePC (debit logical logical.top 1) .afterChild

end
end NearlyOptimalPPR.Computation

-- Runtime interface from Solutions.ControllerFinishDecision

set_option autoImplicit false
set_option maxRecDepth 10000
open scoped ENNReal
namespace NearlyOptimalPPR.Computation
noncomputable section
attribute [local instance] Classical.propDecidable

def compilerFinishDecision {n : ℕ} (g : InputGraph n) (logical : RecursiveState n) : RecursiveState n :=
  if ¬ancestorExhausted logical then
    if ¬anyExhausted logical then compilerFinishRequest g logical
    else changePC (finishEpisode (debit logical logical.top 1)) .restartDrain
  else changePC (finishEpisode (debit logical logical.top 1)) .interrupted

def controllerFinishCharge {n : ℕ} (logical : RecursiveState n) (ell : ℕ) : ℝ≥0∞ :=
  (if ¬ancestorExhausted logical then
    (if ¬anyExhausted logical then (((4*(16*(ell+3))+17)*(logical.frames logical.top).active.card+140 : ℕ) : ℝ≥0∞) else 70)+2
  else 70)+2

end
end NearlyOptimalPPR.Computation

-- Runtime interface from Solutions.ControllerAfterDecision

set_option autoImplicit false
set_option maxRecDepth 10000
open scoped ENNReal
namespace NearlyOptimalPPR.Computation
open SparseQueue
noncomputable section
attribute [local instance] Classical.propDecidable

def compilerAfterDecision {n : ℕ} (g : InputGraph n) (α : ℝ) (logical : RecursiveState n) : RecursiveState n :=
  if ¬ancestorExhausted logical then
    if ¬anyExhausted logical then compilerDrain g α logical .finishEpisode
    else changePC (finishEpisode (debit logical logical.top 1)) .restartDrain
  else changePC (finishEpisode (debit logical logical.top 1)) .interrupted

def controllerDrainCharge {n : ℕ} (g : InputGraph n) (logical : RecursiveState n) (ell length rank : ℕ) : ℝ≥0∞ :=
  let P := cleanBodyBound (16*(ell+3)) length rank+2
  let T := (logical.top+1)*(2*P+(21*rank+20*(16*(ell+3))+70)+50)+6
  let D := drainDegree g logical+1
  let E := (logical.top+1)*D*(42*rank+168*(16*(ell+3))+910)
  ((T+E+P*(2*(logical.top+1)*D)+12 : ℕ) : ℝ≥0∞)

def controllerAfterGrowth {n : ℕ} (g : InputGraph n) (logical : RecursiveState n) : ℕ :=
  if ¬ancestorExhausted logical then
    if ¬anyExhausted logical then 2*(logical.top+1)*(drainDegree g logical+1) else 0
  else 0

def controllerAfterCharge {n : ℕ} (g : InputGraph n) (logical : RecursiveState n) (ell length rank : ℕ) : ℝ≥0∞ :=
  (if ¬ancestorExhausted logical then
    (if ¬anyExhausted logical then controllerDrainCharge g logical ell length rank else 70)+2
  else 70)+2

end
end NearlyOptimalPPR.Computation

-- Runtime interface from Solutions.ControllerOrdinaryExecution

set_option autoImplicit false
set_option maxRecDepth 10000
open scoped ENNReal
namespace NearlyOptimalPPR.Computation
noncomputable section

def controllerPCCode : NormalizePC → MachineCode
  | .initialDrain => controllerInitialCode
  | .beginEpisode => beginEpisodeCode
  | .fullSolve => controllerFullCode
  | .normalize => controllerNormalizeCode
  | .leafDrain => controllerLeafCode
  | .afterChild => controllerAfterChildCode
  | .finishEpisode => controllerFinishCode
  | .restartDrain => controllerRestartCode
  | .normal | .interrupted => controllerReturnCode

end
end NearlyOptimalPPR.Computation

-- Runtime interface from Solutions.ControllerStepData

set_option autoImplicit false
namespace NearlyOptimalPPR.Computation
open SparseQueue
noncomputable section
attribute [local instance] Classical.propDecidable
open scoped ENNReal

def controllerNext {n : ℕ} (m : SolveModel) (g : InputGraph n) (α : ℝ) (ell : ℕ) (logical : RecursiveState n) : RecursiveState n :=
  match (logical.frames logical.top).pc with
  | .initialDrain => compilerInitialRestart g α logical .initialDrain (compilerInitialEmpty logical)
  | .beginEpisode => compilerBeginEpisode m g logical
  | .fullSolve => compilerFullDecision m g α logical
  | .normalize => compilerNormalizeDecision g ell logical
  | .leafDrain => compilerLeafController m g α logical
  | .afterChild => compilerAfterDecision g α logical
  | .finishEpisode => compilerFinishDecision g logical
  | .restartDrain => compilerInitialRestart g α logical .restartDrain (compilerRestartRequest logical)
  | .normal | .interrupted => endCall g α (debit logical logical.top 1)

def controllerStepGrowth {n : ℕ} (g : InputGraph n) (ell : ℕ) (logical : RecursiveState n) : ℕ :=
  match (logical.frames logical.top).pc with
  | .initialDrain | .restartDrain => initialRestartGrowth g logical
  | .beginEpisode => 2*(logical.top+1)*(logical.frames logical.top).active.card
  | .fullSolve => if anyExhausted logical then 0 else 2*(logical.top+1)*(volumeNat g (logical.frames logical.top).active+(logical.frames logical.top).active.card)
  | .normalize => if ¬anyExhausted logical then (if logical.top=ell then 0 else (logical.frames logical.top).active.card) else 0
  | .leafDrain => if ¬anyExhausted logical then controllerPendingGrowth g logical (leafControllerGrowth g logical) else 0
  | .afterChild => controllerAfterGrowth g logical
  | .finishEpisode | .normal | .interrupted => 0

def controllerPCCharge {n : ℕ} (m : SolveModel) (g : InputGraph n) (logical : RecursiveState n) (ell length rank Q : ℕ) : ℝ≥0∞ :=
  let P := cleanBodyBound (16*(ell+3)) length rank+2
  let C := (logical.frames logical.top).active
  let size := volumeNat g C+C.card
  match (logical.frames logical.top).pc with
  | .initialDrain => initialRestartCharge g logical ell length rank 22
  | .beginEpisode =>
    (((((2*(4*(16*(ell+3))+17)+10)+((logical.top+1)*(42*rank+60*(16*(ell+3))+284)+11))*C.card+188)+P*(2*(logical.top+1)*C.card) : ℕ) : ℝ≥0∞)
  | .fullSolve =>
    if anyExhausted logical then 12 else
      ((((10*C.card+5)+((24*(16*(ell+3))+100)*size+28)+(jointSolveIterationFactor ell logical.top rank*size+5)+42)+P*(2*(logical.top+1)*size)+12 : ℕ) : ℝ≥0∞)+solveCharge m C.card size
  | .normalize =>
    (if ¬anyExhausted logical then (if logical.top=ell then 10 else controllerChildCharge logical ell length rank P)+6 else 10)+2
  | .leafDrain =>
    (if ¬anyExhausted logical then controllerPendingCharge g logical ell length rank (leafControllerCharge m g logical ell length rank Q) else 10)+2
  | .afterChild => controllerAfterCharge g logical ell length rank
  | .finishEpisode => controllerFinishCharge logical ell
  | .restartDrain => initialRestartCharge g logical ell length rank 20
  | .normal | .interrupted => ((if logical.top=0 then (8*(16*(ell+3))+31)*(logical.frames 0).active.card+12 else 3 : ℕ) : ℝ≥0∞)


structure ControllerCapacities {n : ℕ} (g : InputGraph n) (logical : RecursiveState n) (ell M N : ℕ) : Prop where
  base : M ≤ N
  begin : (logical.frames logical.top).pc=.beginEpisode → M+2*(logical.top+1)*(logical.frames logical.top).active.card ≤ N
  full : (logical.frames logical.top).pc=.fullSolve → ¬anyExhausted logical →
    M+2*(logical.top+1)*(volumeNat g (logical.frames logical.top).active+(logical.frames logical.top).active.card) ≤ N
  child : (logical.frames logical.top).pc=.normalize → ¬anyExhausted logical → logical.top≠ell →
    M+(logical.frames logical.top).active.card ≤ N
  leaf : (logical.frames logical.top).pc=.leafDrain → ¬anyExhausted logical → M+leafControllerGrowth g logical ≤ N
  push : (logical.frames logical.top).pc ∈ [NormalizePC.initialDrain,.leafDrain,.afterChild,.restartDrain] →
    ¬anyExhausted logical → (pendingPush logical).isSome=true → M+2*(logical.top+1)*(drainDegree g logical+1) ≤ N
  drain : (logical.frames logical.top).pc=.afterChild → ¬anyExhausted logical →
    M+2*(logical.top+1)*(drainDegree g logical+1) ≤ N

end
end NearlyOptimalPPR.Computation

-- Runtime interface from Solutions.ControllerStepExecution

set_option autoImplicit false
set_option maxRecDepth 20000
open scoped ENNReal
namespace NearlyOptimalPPR.Computation
open SparseQueue
noncomputable section
attribute [local instance] Classical.propDecidable

def controllerOrdinaryCharge {n : ℕ} (m : SolveModel) (g : InputGraph n) (logical : RecursiveState n) (ell length rank Q : ℕ) : ℝ≥0∞ :=
  ((76*(logical.top+1)+25+(3*normalizePCNumber (logical.frames logical.top).pc+2) : ℕ) : ℝ≥0∞)+controllerPCCharge m g logical ell length rank Q

def controllerComponentCharge {n : ℕ} (m : SolveModel) (g : InputGraph n) (logical : RecursiveState n) (ell : ℕ) : ℝ≥0∞ :=
  let C := (logical.frames 0).active
  let size := volumeNat g C+C.card
  (((10*C.card+5)+((24*(16*(ell+3))+100)*size+28)+((4*(16*(ell+3))+21)*C.card+6)+4 : ℕ) : ℝ≥0∞)+solveCharge m C.card size

def controllerSourceGrowth {n : ℕ} (g : InputGraph n) (ell : ℕ) (logical : RecursiveState n) : ℕ :=
  if componentComplete logical then 0 else controllerStepGrowth g ell logical

def controllerBodyCharge {n : ℕ} (m : SolveModel) (g : InputGraph n) (logical : RecursiveState n) (ell length rank Q : ℕ) : ℝ≥0∞ :=
  (if componentComplete logical then controllerComponentCharge m g logical ell else controllerOrdinaryCharge m g logical ell length rank Q)+8

end
end NearlyOptimalPPR.Computation

-- Runtime interface from Solutions.RootInitializedExecution

set_option autoImplicit false
set_option maxRecDepth 10000
namespace NearlyOptimalPPR.Computation
noncomputable section

def rootInitializedCode : MachineCode := .seq freshCallCode (coreCode (.load 30 0))
end
end NearlyOptimalPPR.Computation

-- Runtime interface from Solutions.RootRegisterPreparation

set_option autoImplicit false
set_option maxRecDepth 10000
namespace NearlyOptimalPPR.Computation
noncomputable section

def rootRegisterPreparationRoutine : PointerRoutine := .sequence [
  .atom (.copy 20 2),.atom (.add 20 20 20),.atom (.add 20 20 20),
  .atom (.add 20 20 20),.atom (.add 20 20 20),.atom (.add 20 20 20),
  .atom (.set 201 128),.atom (.add 20 20 201),
  .atom (.set 100 0),.atom (.set 53 0),.atom (.set 150 0),.atom (.set 151 1),
  .atom (.load 40 0),.atom (.copy 4 40),.atom (.copy 41 50),.atom (.set 92 0)]
end
end NearlyOptimalPPR.Computation

-- Runtime interface from Solutions.RootSeedRealExecution

set_option autoImplicit false
set_option maxRecDepth 10000
namespace NearlyOptimalPPR.Computation
noncomputable section

def rootSeedRealCode : MachineCode := .seq (coreCode (.const 10 1))
  (.seq (coreCode (.pset 44 1)) (.seq vertexRealStoreCode (.seq (coreCode (.pset 44 2)) vertexRealStoreCode)))
end
end NearlyOptimalPPR.Computation

-- Runtime interface from Solutions.RootSeedMemoryExecution

set_option autoImplicit false
set_option maxRecDepth 10000
namespace NearlyOptimalPPR.Computation
noncomputable section

def rootSeedMemoryCode : MachineCode := .seq degreeRecordStoreCode rootSeedRealCode
end
end NearlyOptimalPPR.Computation

-- Runtime interface from Solutions.RootSeedListExecution

set_option autoImplicit false
set_option maxRecDepth 10000
namespace NearlyOptimalPPR.Computation
open SparseQueue
noncomputable section

def rootSeedListPrefixRoutine : PointerRoutine := .sequence [.atom (.copy 4 40),.atom (.set 92 0)]
def rootSeedListCode : MachineCode := .seq rootSeedListPrefixRoutine.code
  (.seq supportListPrependCode (coreCode (.pcopy 113 92)))
end
end NearlyOptimalPPR.Computation

-- Runtime interface from Solutions.RootCallParameters

set_option autoImplicit false
set_option maxRecDepth 10000
namespace NearlyOptimalPPR.Computation
noncomputable section

def rootCallParameterInstructions : List Instruction := [
  .scalar (.core (.pset 10 2)),.scalar (.core (.load 13 10)),.scalar (.core (.const 31 1)),
  .scalar (.core (.div 12 31 13)),.scalar (.core (.load 30 0))]
def rootCallParameterCode : MachineCode := linearCode rootCallParameterInstructions
end
end NearlyOptimalPPR.Computation

-- Runtime interface from Solutions.RootPreparationExecution

set_option autoImplicit false
set_option maxRecDepth 10000
namespace NearlyOptimalPPR.Computation
open SparseQueue
noncomputable section

def rootPreparationCode : MachineCode := .seq rootRegisterPreparationRoutine.code
  (.seq rootSeedMemoryCode (.seq rootSeedListCode rootCallParameterCode))
end
end NearlyOptimalPPR.Computation

-- Runtime interface from Solutions.RootInitializationExecution

set_option autoImplicit false
set_option maxRecDepth 10000
namespace NearlyOptimalPPR.Computation
noncomputable section

def rootInitializationCode : MachineCode := .seq rootPreparationCode rootInitializedCode
end
end NearlyOptimalPPR.Computation

-- Runtime interface from Solutions.RootThresholdExecution

set_option autoImplicit false
open scoped ENNReal
namespace NearlyOptimalPPR.Computation
noncomputable section


def rootThresholdInstructions : List Instruction := [
  .scalar (.core (.pcopy 49 2)),.scalar (.core (.pinc 49)),.scalar (.pointerReal 7 49),
  .scalar (.core (.const 8 32)),RealOperation.mul.instruction 7 7 8,
  .scalar (.core (.pset 1 1)),.scalar (.core (.load 8 1)),RealOperation.div.instruction 0 8 7]

def rootThresholdCode : MachineCode := linearCode rootThresholdInstructions

end
end NearlyOptimalPPR.Computation

-- Runtime interface from Solutions.PositiveThresholdSearch

set_option autoImplicit false
open scoped ENNReal
namespace NearlyOptimalPPR.Computation
noncomputable section

def thresholdBodyCode : MachineCode := .seq (.atom (RealOperation.sub.instruction 6 6 0))
  (coreCode (.pinc 44))

def thresholdLoopCode : MachineCode := .whileReal 6 thresholdBodyCode

def rootCapacitySearchCode : MachineCode := sequenceCode [
  coreCode (.const 6 8),coreCode (.pset 44 0),thresholdLoopCode]

end
end NearlyOptimalPPR.Computation

-- Runtime interface from Solutions.BinaryCapacityCode

set_option autoImplicit false
namespace NearlyOptimalPPR.Computation
noncomputable section

lemma binary_capacity_exists (N : ℕ) : ∃ r : ℕ, N < 2^r :=
  ⟨Nat.log 2 N+1,Nat.lt_pow_succ_log_self (by decide) N⟩

def binaryCapacity (N : ℕ) : ℕ := Nat.find (binary_capacity_exists N)

def binaryCapacityBodyRoutine : PointerRoutine := .sequence [
  .atom (.add 46 46 46),.atom (.inc 45)]

def binaryCapacityLoopCode : MachineCode := .whilePointer 48 46 binaryCapacityBodyRoutine.code

def binaryCapacityInitRoutine : PointerRoutine := .sequence [
  .atom (.copy 48 44),.atom (.inc 48),.atom (.set 45 0),.atom (.set 46 1)]


def binaryCapacityCode : MachineCode := .seq binaryCapacityInitRoutine.code binaryCapacityLoopCode

end
end NearlyOptimalPPR.Computation

-- Runtime interface from Solutions.ParameterPreparation

set_option autoImplicit false
open scoped ENNReal
namespace NearlyOptimalPPR.Computation
noncomputable section

def parameterTailRoutine : PointerRoutine := .sequence [
  .atom (.set 0 0),.atom (.set 20 128),.atom (.add 50 49 49),
  .atom (.add 50 50 50),.atom (.add 50 50 50),.atom (.add 50 50 50)]

def parameterPreparationCode : MachineCode := .seq depthSearchCode (.seq rootThresholdCode
  (.seq rootCapacitySearchCode (.seq binaryCapacityCode parameterTailRoutine.code)))

end
end NearlyOptimalPPR.Computation

-- Runtime interface from Solutions.ParameterHeader

set_option autoImplicit false
namespace NearlyOptimalPPR.Computation
noncomputable section


def parameterHeaderInstructions : List Instruction := [
  .scalar (.core (.pset 10 2)),.scalar (.core (.store 10 0)),.scalar (.integerStore 10 2),
  .scalar (.core (.pinc 10)),.scalar (.integerStore 10 50),
  .scalar (.core (.pinc 10)),.scalar (.integerStore 10 44),
  .scalar (.core (.pinc 10)),.scalar (.integerStore 10 45),
  .scalar (.core (.pinc 10)),.scalar (.integerStore 10 49)]

def parameterHeaderCode : MachineCode := linearCode parameterHeaderInstructions

end
end NearlyOptimalPPR.Computation

-- Runtime interface from Solutions.AmplifiedQueueRank

set_option autoImplicit false
set_option maxRecDepth 10000
namespace NearlyOptimalPPR.Computation
noncomputable section


def amplifiedQueueRank (B r : ℕ) : ℕ := B*(r+binaryCapacity B)+1

def amplifiedQueueRankRoutine (B : ℕ) : PointerRoutine := .sequence
  ([.atom (.set 47 (binaryCapacity B : ℤ)),.atom (.add 47 47 45),.atom (.set 45 2)] ++
    List.replicate B (.atom (.add 45 45 47)))

end
end NearlyOptimalPPR.Computation

-- Runtime interface from Solutions.VertexFIFOEnqueue

set_option autoImplicit false
open scoped ENNReal
namespace NearlyOptimalPPR.Computation
open SparseQueue
noncomputable section

def vertexFIFOEnqueueCode : MachineCode := .seq (coreCode (.pcopy 4 40))
  (.seq fifoAppendCode (.seq (coreCode (.pset 88 3)) vertexFlagSetCode))

end
end NearlyOptimalPPR.Computation

-- Runtime interface from Solutions.PushInitCode

set_option autoImplicit false
namespace NearlyOptimalPPR.Computation
noncomputable section

def pushInitInstructions : List Instruction := [
  .scalar (.core (.pset 0 0)),.scalar (.core (.pset 41 16)),.scalar (.core (.pset 50 16)),
  .scalar (.core (.pset 20 128)),.scalar (.core (.pset 90 0)),.scalar (.core (.pset 91 0)),.scalar (.core (.pset 92 0)),
  .scalar (.core (.load 30 0)),.scalar (.core (.pset 1 1)),.scalar (.core (.load 20 1)),
  .scalar (.core (.const 31 1)),.scalar (.integerLoad 40 0),.scalar (.core (.pset 44 1)),.scalar (.core (.const 10 1))]

def pushInitPrefixCode : MachineCode := linearCode pushInitInstructions

def pushInitCode : MachineCode := .seq pushInitPrefixCode (.seq vertexRealStoreCode vertexFIFOEnqueueCode)

end
end NearlyOptimalPPR.Computation

-- Runtime interface from Solutions.VertexFIFODequeue

set_option autoImplicit false
open scoped ENNReal
namespace NearlyOptimalPPR.Computation
open SparseQueue
noncomputable section

def vertexFIFODequeueCode : MachineCode := .seq fifoPopCode (.seq (coreCode (.pset 88 3)) vertexFlagClearCode)

end
end NearlyOptimalPPR.Computation

-- Runtime interface from Solutions.PushEligibilityExecution

set_option autoImplicit false
open scoped ENNReal
namespace NearlyOptimalPPR.Computation
noncomputable section

def pushEligibilityCode : MachineCode := .seq (coreCode (.pset 87 0)) exteriorInactiveCode

end
end NearlyOptimalPPR.Computation

-- Runtime interface from Solutions.PushScalarCode

set_option autoImplicit false
open scoped ENNReal
namespace NearlyOptimalPPR.Computation
noncomputable section

def pushValueCalcInstructions : List Instruction := [
  .scalar (.pointerReal 11 60),RealOperation.div.instruction 12 10 11,
  RealOperation.sub.instruction 13 31 30,RealOperation.mul.instruction 13 13 12,
  RealOperation.mul.instruction 10 12 31,.scalar (.core (.pset 44 0))]

def pushValueCalcCode : MachineCode := linearCode pushValueCalcInstructions

def pushResidualResetInstructions : List Instruction := [.scalar (.core (.const 10 0)),.scalar (.core (.pset 44 1))]

def pushResidualResetCode : MachineCode := linearCode pushResidualResetInstructions

def pushScalarUpdateCode : MachineCode := .seq (coreCode (.pset 44 1))
  (.seq vertexRealLoadCode (.seq pushValueCalcCode (.seq vertexRealAddCode (.seq pushResidualResetCode vertexRealStoreCode))))

end
end NearlyOptimalPPR.Computation

-- Runtime interface from Solutions.SupportInsertCode

set_option autoImplicit false
open scoped ENNReal
namespace NearlyOptimalPPR.Computation
open SparseQueue
noncomputable section

def supportInsertCode : MachineCode := .seq (coreCode (.pcopy 4 40))
  (.seq supportListPrependCode (.seq (coreCode (.pset 88 4)) vertexFlagSetCode))

end
end NearlyOptimalPPR.Computation

-- Runtime interface from Solutions.SupportEnsureExecution

set_option autoImplicit false
set_option maxRecDepth 10000
open scoped ENNReal
namespace NearlyOptimalPPR.Computation
open SparseQueue
noncomputable section

def supportEnsureCode : MachineCode := .seq (coreCode (.pset 88 4))
  (.seq queuedFlagReadCode (.branchPointer 51 0 supportInsertCode .skip))

end
end NearlyOptimalPPR.Computation

-- Runtime interface from Solutions.PushNeighborsPreparation

set_option autoImplicit false
namespace NearlyOptimalPPR.Computation
noncomputable section

def pushNeighborsPrepareInstructions : List Instruction := [
  .scalar (.core (.pcopy 63 40)), .scalar (.core (.pcopy 67 60)), .scalar (.core (.pset 62 0))]
def pushNeighborsPrepareCode : MachineCode := linearCode pushNeighborsPrepareInstructions

end
end NearlyOptimalPPR.Computation

-- Runtime interface from Solutions.PushResidualCode

set_option autoImplicit false
open scoped ENNReal
namespace NearlyOptimalPPR.Computation
noncomputable section

def pushResidualPrepareInstructions : List Instruction := [
  .scalar (.core (.pset 44 1)), .scalar (.core (.mul 10 13 31))]
def pushResidualPrepareCode : MachineCode := linearCode pushResidualPrepareInstructions

def pushResidualAddCode : MachineCode := .seq pushResidualPrepareCode vertexRealAddCode

end
end NearlyOptimalPPR.Computation

-- Runtime interface from Solutions.FIFOEnsureCode

set_option autoImplicit false
namespace NearlyOptimalPPR.Computation
noncomputable section

def fifoEnsureCode : MachineCode := .seq (coreCode (.pset 88 3))
  (.seq queuedFlagReadCode (.branchPointer 51 0 vertexFIFOEnqueueCode .skip))

end
end NearlyOptimalPPR.Computation

-- Runtime interface from Solutions.PushRefreshCode

set_option autoImplicit false
open scoped ENNReal
namespace NearlyOptimalPPR.Computation
noncomputable section

def pushRefreshCode : MachineCode := .seq pushEligibilityCode (.branchReal 23 .skip fifoEnsureCode)

end
end NearlyOptimalPPR.Computation

-- Runtime interface from Solutions.PushNeighborUpdate

set_option autoImplicit false
set_option maxRecDepth 10000
open scoped ENNReal
namespace NearlyOptimalPPR.Computation
noncomputable section

def pushNeighborUpdateCode : MachineCode := .seq degreeRecordStoreCode (.seq pushResidualAddCode pushRefreshCode)

end
end NearlyOptimalPPR.Computation

-- Runtime interface from Solutions.PushNeighborLoopCode

set_option autoImplicit false
namespace NearlyOptimalPPR.Computation
noncomputable section

def pushNeighborBodyCode : MachineCode := .seq (.atom (.scalar (.nbr 40 63 62)))
  (.seq pushNeighborUpdateCode (coreCode (.pinc 62)))
def pushNeighborLoopCode : MachineCode := .whilePointer 67 62 pushNeighborBodyCode

end
end NearlyOptimalPPR.Computation

-- Runtime interface from Solutions.PushPositiveCode

set_option autoImplicit false
namespace NearlyOptimalPPR.Computation
noncomputable section

def pushPositiveCode : MachineCode := .seq pushScalarUpdateCode
  (.seq supportEnsureCode (.seq pushNeighborsPrepareCode pushNeighborLoopCode))

end
end NearlyOptimalPPR.Computation

-- Runtime interface from Solutions.PushIterationCode

set_option autoImplicit false
namespace NearlyOptimalPPR.Computation
noncomputable section

def pushIterationCode : MachineCode := .seq vertexFIFODequeueCode
  (.seq degreeRecordStoreCode (.seq pushEligibilityCode (.branchReal 23 .skip pushPositiveCode)))
end
end NearlyOptimalPPR.Computation

-- Runtime interface from Solutions.PushWhileExecution

set_option autoImplicit false
set_option maxRecDepth 10000
open scoped ENNReal
namespace NearlyOptimalPPR.Computation
open SparseQueue
noncomputable section

def pushWhileCode : MachineCode := .whilePointer 90 0 pushIterationCode
end
end NearlyOptimalPPR.Computation

-- Runtime interface from Solutions.PushOutputBody

set_option autoImplicit false
set_option maxRecDepth 10000
namespace NearlyOptimalPPR.Computation
noncomputable section

def pushOutputBodyCode : MachineCode := .seq pushOutputReadCode
  (.seq vertexRealLoadCode (.seq (vertexFieldReadCode 0 60) pushOutputScalarCode))
def pushOutputLoopCode : MachineCode := .whilePointer 94 0 pushOutputBodyCode

def pushOutputCode : MachineCode := .seq (coreCode (.pcopy 94 92)) pushOutputLoopCode

end
end NearlyOptimalPPR.Computation

-- Runtime interface from Solutions.PushCoreCode

set_option autoImplicit false
namespace NearlyOptimalPPR.Computation
noncomputable section

def pushCoreCode : MachineCode := .seq pushInitCode (.seq pushWhileCode pushOutputCode)
end
end NearlyOptimalPPR.Computation

-- Runtime interface from Solutions.UniformProgramCode

set_option autoImplicit false
set_option maxRecDepth 10000
namespace NearlyOptimalPPR.Computation
noncomputable section

def recursivePreparationCode (B : ℕ) : MachineCode := .seq parameterPreparationCode
  (.seq (amplifiedQueueRankRoutine B).code (.seq parameterHeaderCode rootInitializationCode))
end
end NearlyOptimalPPR.Computation

-- Runtime interface from Solutions.PushInputMemory

set_option autoImplicit false
namespace NearlyOptimalPPR.Computation
noncomputable section

structure PushInputMemory {n : ℕ} (s : Fin n) (α ε : ℝ) (st : MachineState) : Prop where
  seed : st.scalar.integerMemory 0=(s.val : ℤ)
  alpha : st.scalar.core.mem 0=α
  epsilon : st.scalar.core.mem 1=ε
  integerZero : ∀ z, z < 0 → st.scalar.integerMemory z=0
  realZero : ∀ z, z < 0 → st.scalar.core.mem z=0
  output : st.output=[]

end
end NearlyOptimalPPR.Computation

-- Runtime interface from Solutions.CompilerOverheadCoefficients

set_option autoImplicit false
set_option maxRecDepth 10000
namespace NearlyOptimalPPR.Computation
open SparseQueue
noncomputable section

def compilerOverheadBase (ell length rank Q : ℕ) : ℕ :=
  1000+16*(ell+3)+ell+length+rank+Q+(cleanBodyBound (16*(ell+3)) length rank+2)

def compilerOverheadFactor (ell length rank Q : ℕ) : ℕ := 4096*(compilerOverheadBase ell length rank Q)^2

end
end NearlyOptimalPPR.Computation


