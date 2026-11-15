-- Prove2me | Definitions.Def_QMAPerfectCompleteness_Proof_RawControlGadgets
-- name    : QMAPerfectCompleteness_Proof_RawControlGadgets
-- status  : Definition
-- author  : @Dorian Rudolph
-- created : 2026-11-14T14:56:03.666365+00:00
-- url     : https://prove2.me/theorems/3a47c4a7-2f63-486d-aa2c-bfdd4ffe28ef
-- title:
--   Raw controls, comparisons and clock gadgets
-- statement:
--   Defines literal instruction templates for fixed comparisons, prefix controls, modular increment, phase gates and paired Hadamards. Their address arguments are natural numbers, so these compiler templates do not require complex matrix data.
-- source:
--   Formalization auxiliary for ~/research/qma1z/main.tex, the uniform circuit implementation supporting Section 3.3 and the proof of Theorem 1.1. Original Lean source: commit bbe19efbde567e5c8f7fe21655fd0c4da3573e4d, Solutions/RawControlGadgets.lean, retained declaration span lines 10–103.

/- Generated from Solutions.RawControlGadgets by authoritative Stage-2 skeleton subtraction.
Original explanatory text, declaration names and scoped commands are retained.
Only selected proof cuts, import rewrites and fact-indexed platform edits are applied. -/
import Definitions.Def_QMAPerfectCompleteness_Main_Classes
import Definitions.Def_QMAPerfectCompleteness_Main_Compiler
import Definitions.Def_QMAPerfectCompleteness_Main_Cyclic
import Init.Data.BitVec.Bitblast
import Definitions.Def_QMAPerfectCompleteness_Main_BlockEncoding
import Definitions.Def_QMAPerfectCompleteness_Proof_BlockEncoding
import Definitions.Def_QMAPerfectCompleteness_Proof_BooleanCircuits
import Definitions.Def_QMAPerfectCompleteness_Proof_CircuitUnitary
import Definitions.Def_QMAPerfectCompleteness_Proof_ClockCircuits
import Definitions.Def_QMAPerfectCompleteness_Proof_ComparisonCircuits
import Definitions.Def_QMAPerfectCompleteness_Proof_ControlCircuits
import Definitions.Def_QMAPerfectCompleteness_Proof_Cyclic
import Definitions.Def_QMAPerfectCompleteness_Proof_EqualityCircuits
import Definitions.Def_QMAPerfectCompleteness_Proof_EuclideanStates
import Definitions.Def_QMAPerfectCompleteness_Proof_IndexHadamards
import Definitions.Def_QMAPerfectCompleteness_Proof_RawCircuitEncoding
import Definitions.Def_QMAPerfectCompleteness_Proof_RawG2Gadgets
import Definitions.Def_QMAPerfectCompleteness_Proof_ReversibleGadgets
import Definitions.Def_QMAPerfectCompleteness_Proof_VerifierEncoding



/-! Executable bounded-loop control, comparison, clock and phase circuit templates. -/
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
namespace QMAPerfectCompleteness.Main.RawG2
open RawEncoding

def prefixLayout {r : ℕ} (L : AndLayout r) (t : ℕ) (ht : t≤r) : AndLayout t where
  controls j := L.controls ⟨j,Nat.lt_of_lt_of_le j.isLt ht⟩
  flags j := L.flags ⟨j,by have := j.isLt; omega⟩

def reverseLayout {r : ℕ} (L : AndLayout r) : AndLayout r :=
  ⟨fun j=>L.controls j.rev,L.flags⟩




def stageGates {r : ℕ} (L : AndLayout r) (p : Fin r → Bool) (target : ℕ)
    (t : ℕ) (ht : t<r) : List Instruction :=
  if p ⟨t,ht⟩ then patternControlledX (prefixLayout L (t+1) (by omega))
    (ComparisonCircuits.stagePattern p t ht) target else []

def comparePrefix {r : ℕ} (L : AndLayout r) (p : Fin r → Bool) (target : ℕ) :
    (t : ℕ) → t≤r → List Instruction
  | 0,_ => []
  | t+1,ht => comparePrefix L p target t (by omega) ++ stageGates L p target t (by omega)

def compareGates {r : ℕ} (L : AndLayout r) (p : Fin r → Bool) (target : ℕ) :=
  comparePrefix (reverseLayout L) (fun j=>p j.rev) target r le_rfl

def compareNatGates {r : ℕ} (L : AndLayout r) (a target : ℕ) :=
  if a<2^r then compareGates L (fun j=>a.testBit j.val) target else [x target]









def incrementStep {r : ℕ} (L : AndLayout (r+1)) (t : ℕ) (ht : t<r) : List Instruction :=
  multiControlledX (prefixLayout L (t+1) (by omega)) (L.controls ⟨t+1,by omega⟩)

def incrementPrefix {r : ℕ} (L : AndLayout (r+1)) :
    (t : ℕ) → t≤r → List Instruction
  | 0,_ => []
  | t+1,ht => incrementStep L t (by omega) ++ incrementPrefix L t (by omega)

def increment {r : ℕ} (L : AndLayout (r+1)) := incrementPrefix L r le_rfl







def phase (a b : ℕ) : List Instruction := [hh a b,x a,hh a b]
def tripleControlledX (e : Fin 5 → ℕ) : List Instruction :=
  [tof (e 0) (e 1) (e 4),tof (e 4) (e 2) (e 3),tof (e 0) (e 1) (e 4)]




def pairedHadamards {k : ℕ} (e : Fin k → ℕ) : List Instruction :=
  (List.finRange (k/2)).map fun j=>hh (e ⟨2*j.val,by have := j.isLt; omega⟩)
    (e ⟨2*j.val+1,by have := j.isLt; omega⟩)



end QMAPerfectCompleteness.Main.RawG2


