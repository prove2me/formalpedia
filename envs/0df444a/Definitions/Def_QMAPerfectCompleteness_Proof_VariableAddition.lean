-- Prove2me | Definitions.Def_QMAPerfectCompleteness_Proof_VariableAddition
-- name    : QMAPerfectCompleteness_Proof_VariableAddition
-- status  : Definition
-- author  : @Dorian Rudolph
-- created : 2026-11-14T14:57:57.525445+00:00
-- url     : https://prove2.me/theorems/675f7e5a-c08f-48dc-9665-4366af7c47c5
-- title:
--   Reversible addition of variable binary registers
-- statement:
--   Defines a ripple-carry adder layout and literal classical commands for two variable input words. The construction separates carry computation, copying of sum bits into the output register and uncomputation of the carry workspace.
-- source:
--   Formalization auxiliary for ~/research/qma1z/main.tex, the uniform circuit implementation supporting Section 3.3 and the proof of Theorem 1.1. Original Lean source: commit bbe19efbde567e5c8f7fe21655fd0c4da3573e4d, Solutions/VariableAddition.lean, retained declaration span lines 11–322.

/- Generated from Solutions.VariableAddition by authoritative Stage-2 skeleton subtraction.
Original explanatory text, declaration names and scoped commands are retained.
Only selected proof cuts, import rewrites and fact-indexed platform edits are applied. -/
import Definitions.Def_QMAPerfectCompleteness_Main_Compiler
import Definitions.Def_QMAPerfectCompleteness_Main_Cyclic
import Init.Data.BitVec.Bitblast
import Definitions.Def_QMAPerfectCompleteness_Proof_BlockEncoding
import Definitions.Def_QMAPerfectCompleteness_Proof_BooleanCircuits
import Definitions.Def_QMAPerfectCompleteness_Proof_BooleanFraming
import Definitions.Def_QMAPerfectCompleteness_Proof_CircuitUnitary
import Definitions.Def_QMAPerfectCompleteness_Proof_ClockCircuits
import Definitions.Def_QMAPerfectCompleteness_Proof_ComparisonCircuits
import Definitions.Def_QMAPerfectCompleteness_Proof_ControlCircuits
import Definitions.Def_QMAPerfectCompleteness_Proof_Cyclic
import Definitions.Def_QMAPerfectCompleteness_Proof_EqualityCircuits
import Definitions.Def_QMAPerfectCompleteness_Proof_EuclideanStates
import Definitions.Def_QMAPerfectCompleteness_Proof_ReversibleGadgets



/-! Literal variable-register addition using a ripple carry, copied sums, and uncomputation. -/
open Matrix
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
namespace QMAPerfectCompleteness.Main.VariableAddition
open BooleanCircuits ComparisonCircuits ClockCircuits

/-- Carry generate and propagate are disjoint, hence XOR is OR in this formula. -/
def carryBit (a b c : Bool) : Bool := xor (a && b) ((xor a b) && c)

def carryCommands {n : ℕ} (e : Fin 5 ↪ Fin n) : List (Command n) :=
  [.conj (e 0) (e 1) (e 3) (e.injective.ne (by decide)) (e.injective.ne (by decide)),
   .copy (e 0) (e 4) (e.injective.ne (by decide)),
   .copy (e 1) (e 4) (e.injective.ne (by decide)),
   .conj (e 4) (e 2) (e 3) (e.injective.ne (by decide)) (e.injective.ne (by decide)),
   .copy (e 1) (e 4) (e.injective.ne (by decide)),
   .copy (e 0) (e 4) (e.injective.ne (by decide))]









/-- Inputs a,b, r+1 carry bits, r output bits, and one reusable temporary. -/
structure Layout (r n : ℕ) where
  slots : Fin (4*r+2) ↪ Fin n

namespace Layout
variable {r n : ℕ} (L : Layout r n)

def left (j : Fin r) : Fin n := L.slots ⟨j,by omega⟩
def right (j : Fin r) : Fin n := L.slots ⟨r+j,by omega⟩
def carry (j : Fin (r+1)) : Fin n := L.slots ⟨2*r+j,by omega⟩
def output (j : Fin r) : Fin n := L.slots ⟨3*r+1+j,by omega⟩
def temp : Fin n := L.slots ⟨4*r+1,by omega⟩









lemma output_ne_carry (i : Fin r) (j : Fin (r+1)) : L.output i ≠ L.carry j := by
  intro h
  have hv := congrArg Fin.val (L.slots.injective h)
  have hj := j.isLt
  change 3*r+1+i.val = 2*r+j.val at hv
  omega

/-- a_i,b_i,c_i,c_(i+1),temporary occupy five distinct wires. -/
def step (j : Fin r) : Fin 5 ↪ Fin n :=
  ⟨fun i => L.slots ⟨(![j.val,r+j.val,2*r+j.val,2*r+(j.val+1),4*r+1] : Fin 5 → ℕ) i,by
      have hj := j.isLt
      fin_cases i <;> simp <;> omega⟩,by
    intro a b h
    have h' : (![j.val,r+j.val,2*r+j.val,2*r+(j.val+1),4*r+1] : Fin 5 → ℕ) a =
        (![j.val,r+j.val,2*r+j.val,2*r+(j.val+1),4*r+1] : Fin 5 → ℕ) b :=
      congrArg Fin.val (L.slots.injective h)
    have hj := j.isLt
    fin_cases a <;> fin_cases b <;> first | rfl | (norm_num at h' <;> omega)⟩







def carryPrefix (L : Layout r n) : (t : ℕ) → t ≤ r → List (Command n)
  | 0,_ => []
  | t+1,ht => L.carryPrefix t (by omega) ++ carryCommands (L.step ⟨t,by omega⟩)


















def leftWord (x : Basis n) : BitVec r :=
  BitVec.ofNatLT (littleValue (fun j => x (L.left j))) (littleValue_lt_two_pow _)
def rightWord (x : Basis n) : BitVec r :=
  BitVec.ofNatLT (littleValue (fun j => x (L.right j))) (littleValue_lt_two_pow _)









lemma left_ne_output (i j : Fin r) : L.left i ≠ L.output j := by
  intro h
  have hv := congrArg Fin.val (L.slots.injective h)
  have hi := i.isLt
  change i.val = 3*r+1+j.val at hv
  omega

lemma right_ne_output (i j : Fin r) : L.right i ≠ L.output j := by
  intro h
  have hv := congrArg Fin.val (L.slots.injective h)
  have hi := i.isLt
  change r+i.val = 3*r+1+j.val at hv
  omega



def sumStep (j : Fin r) : List (Command n) :=
  [.copy (L.left j) (L.output j) (L.left_ne_output j j),
    .copy (L.right j) (L.output j) (L.right_ne_output j j),
    .copy (L.carry j.castSucc) (L.output j) (L.output_ne_carry j j.castSucc).symm]





def sumCommands (js : List (Fin r)) : List (Command n) := js.flatMap L.sumStep









def inputFrame : Set (Fin n) := {w | ∀ j, w ≠ L.output j}







/-- Compute all carries, copy sum bits, and erase every carry. -/
def commands : List (Command n) :=
  L.carryPrefix r le_rfl ++ L.sumCommands (List.finRange r) ++ (L.carryPrefix r le_rfl).reverse



















end Layout
end QMAPerfectCompleteness.Main.VariableAddition


