-- Prove2me | Definitions.Def_QMAPerfectCompleteness_Proof_RawArithmeticGadgets
-- name    : QMAPerfectCompleteness_Proof_RawArithmeticGadgets
-- status  : Definition
-- author  : @Dorian Rudolph
-- created : 2026-11-14T15:04:33.243585+00:00
-- url     : https://prove2.me/theorems/ace6e9d8-f85b-4133-8c2e-873fe4271427
-- title:
--   Raw ripple-addition and comparison circuits
-- statement:
--   Defines matrix-free raw layouts and instruction lists for variable addition, borrow-based comparison and equality. Their erasure interfaces match the corresponding typed reversible circuits and specify the carry, sum and cleanup passes.
-- source:
--   Formalization auxiliary for ~/research/qma1z/main.tex, the uniform circuit implementation supporting Section 3.3 and the proof of Theorem 1.1. Original Lean source: commit bbe19efbde567e5c8f7fe21655fd0c4da3573e4d, Solutions/RawArithmeticGadgets.lean, retained declaration span lines 11–107.

/- Generated from Solutions.RawArithmeticGadgets by authoritative Stage-2 skeleton subtraction.
Original explanatory text, declaration names and scoped commands are retained.
Only selected proof cuts, import rewrites and fact-indexed platform edits are applied. -/
import Definitions.Def_QMAPerfectCompleteness_Main_Classes
import Definitions.Def_QMAPerfectCompleteness_Main_Compiler
import Definitions.Def_QMAPerfectCompleteness_Main_Cyclic
import Init.Data.BitVec.Bitblast
import Definitions.Def_QMAPerfectCompleteness_Main_BlockEncoding
import Definitions.Def_QMAPerfectCompleteness_Proof_BlockCompiler
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
import Definitions.Def_QMAPerfectCompleteness_Proof_IndexHadamards
import Definitions.Def_QMAPerfectCompleteness_Proof_RawCircuitEncoding
import Definitions.Def_QMAPerfectCompleteness_Proof_RawG2Gadgets
import Definitions.Def_QMAPerfectCompleteness_Proof_ReversibleGadgets
import Definitions.Def_QMAPerfectCompleteness_Proof_VariableAddition
import Definitions.Def_QMAPerfectCompleteness_Proof_VariableComparison
import Definitions.Def_QMAPerfectCompleteness_Proof_VariableEquality
import Definitions.Def_QMAPerfectCompleteness_Proof_VerifierEncoding



/-! Executable linear ripple circuits, with exact erasure of their proved typed counterparts. -/
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000
namespace QMAPerfectCompleteness.Main.RawG2
open RawEncoding

structure BorrowLayout (r : ℕ) where
  left : Fin r → ℕ
  right : Fin r → ℕ
  carry : Fin (r+1) → ℕ
  temp : ℕ

def eraseBorrow {r n : ℕ} (e : Fin (3*r+2) ↪ Fin n) : BorrowLayout r :=
  ⟨fun j=>(VariableComparison.leftWire e j).val,fun j=>(VariableComparison.rightWire e j).val,
    fun j=>(VariableComparison.carryWire e j).val,(VariableComparison.tempWire e).val⟩

def borrowCommands (e : Fin 5 → ℕ) : List Command :=
  [.copy (e 0) (e 4),.copy (e 1) (e 4),.flip (e 4),.flip (e 0),
   .conj (e 0) (e 1) (e 3),.flip (e 0),.conj (e 4) (e 2) (e 3),
   .flip (e 4),.copy (e 1) (e 4),.copy (e 0) (e 4)]

def borrowPrefix {r : ℕ} (L : BorrowLayout r) : (t : ℕ) → t≤r → List Command
  | 0,_ => []
  | t+1,ht => borrowPrefix L t (by omega) ++ borrowCommands
      ![L.left ⟨t,by omega⟩,L.right ⟨t,by omega⟩,
        L.carry ⟨t,by omega⟩,L.carry ⟨t+1,by omega⟩,L.temp]

def comparator {r : ℕ} (L : BorrowLayout r) (target : ℕ) : List Instruction :=
  computeUseUncompute (compile (borrowPrefix L r le_rfl)) [cn (L.carry (Fin.last r)) target]









def swapBorrow {r : ℕ} (L : BorrowLayout r) : BorrowLayout r := ⟨L.right,L.left,L.carry,L.temp⟩



def equality {r : ℕ} (L : BorrowLayout r) (target : ℕ) :=
  comparator L target ++ comparator (swapBorrow L) target ++ [x target]



structure AdditionLayout (r : ℕ) where
  left : Fin r → ℕ
  right : Fin r → ℕ
  carry : Fin (r+1) → ℕ
  output : Fin r → ℕ
  temp : ℕ

def eraseAddition {r n : ℕ} (L : VariableAddition.Layout r n) : AdditionLayout r :=
  ⟨fun j=>(L.left j).val,fun j=>(L.right j).val,fun j=>(L.carry j).val,
    fun j=>(L.output j).val,L.temp.val⟩

def carryCommands (e : Fin 5 → ℕ) : List Command :=
  [.conj (e 0) (e 1) (e 3),.copy (e 0) (e 4),.copy (e 1) (e 4),
   .conj (e 4) (e 2) (e 3),.copy (e 1) (e 4),.copy (e 0) (e 4)]

def carryPrefix {r : ℕ} (L : AdditionLayout r) : (t : ℕ) → t≤r → List Command
  | 0,_ => []
  | t+1,ht => carryPrefix L t (by omega) ++ carryCommands
      ![L.left ⟨t,by omega⟩,L.right ⟨t,by omega⟩,
        L.carry ⟨t,by omega⟩,L.carry ⟨t+1,by omega⟩,L.temp]

def sumStep {r : ℕ} (L : AdditionLayout r) (j : Fin r) : List Command :=
  [.copy (L.left j) (L.output j),.copy (L.right j) (L.output j),.copy (L.carry j.castSucc) (L.output j)]

def additionCommands {r : ℕ} (L : AdditionLayout r) :=
  carryPrefix L r le_rfl ++ (List.finRange r).flatMap (sumStep L) ++ (carryPrefix L r le_rfl).reverse

def addition {r : ℕ} (L : AdditionLayout r) := compile (additionCommands L)











end QMAPerfectCompleteness.Main.RawG2


