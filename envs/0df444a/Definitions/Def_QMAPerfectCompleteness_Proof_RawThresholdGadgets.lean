-- Prove2me | Definitions.Def_QMAPerfectCompleteness_Proof_RawThresholdGadgets
-- name    : QMAPerfectCompleteness_Proof_RawThresholdGadgets
-- status  : Definition
-- author  : @Dorian Rudolph
-- created : 2026-11-14T15:05:43.968355+00:00
-- url     : https://prove2.me/theorems/80d07943-5623-45a0-849e-bf40c072c5da
-- title:
--   Raw preparation of certificate thresholds
-- statement:
--   Defines the raw copy and addition templates that prepare padded certificate words and their range thresholds. The layout and erasure interfaces agree with the typed threshold-preparation circuit.
-- source:
--   Formalization auxiliary for ~/research/qma1z/main.tex, the uniform circuit implementation supporting Section 3.3 and the proof of Theorem 1.1. Original Lean source: commit bbe19efbde567e5c8f7fe21655fd0c4da3573e4d, Solutions/RawThresholdGadgets.lean, retained declaration span lines 10–66.

/- Generated from Solutions.RawThresholdGadgets by authoritative Stage-2 skeleton subtraction.
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
import Definitions.Def_QMAPerfectCompleteness_Proof_RawArithmeticGadgets
import Definitions.Def_QMAPerfectCompleteness_Proof_RawCircuitEncoding
import Definitions.Def_QMAPerfectCompleteness_Proof_RawG2Gadgets
import Definitions.Def_QMAPerfectCompleteness_Proof_RegisterCopies
import Definitions.Def_QMAPerfectCompleteness_Proof_ReversibleGadgets
import Definitions.Def_QMAPerfectCompleteness_Proof_ThresholdPreparation
import Definitions.Def_QMAPerfectCompleteness_Proof_VariableAddition
import Definitions.Def_QMAPerfectCompleteness_Proof_VariableComparison
import Definitions.Def_QMAPerfectCompleteness_Proof_VariableEquality
import Definitions.Def_QMAPerfectCompleteness_Proof_VerifierEncoding



/-! Executable certificate threshold preparation, independent of quantum matrix data. -/
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
namespace QMAPerfectCompleteness.Main.RawG2
open RawEncoding

structure ThresholdLayout (k : ℕ) where
  certificate : Fin 2 → Fin k → ℕ
  word : Fin 6 → Fin (k+2) → ℕ
  carry : Fin (k+3) → ℕ
  temp : ℕ

def eraseThreshold {k n : ℕ} (L : ThresholdPreparation.Layout k n) : ThresholdLayout k :=
  ⟨fun d j=>(L.wire (.certificate d j)).val,fun d j=>(L.wire (.word d j)).val,
    fun j=>(L.wire (.carry j)).val,(L.wire .temp).val⟩

def threeLayout {k : ℕ} (L : ThresholdLayout k) : AdditionLayout (k+2) :=
  ⟨L.word 0,L.word 1,L.carry,L.word 4,L.temp⟩
def upperLayout {k : ℕ} (L : ThresholdLayout k) : AdditionLayout (k+2) :=
  ⟨L.word 4,L.word 2,L.carry,L.word 5,L.temp⟩







def thresholdCopies {k : ℕ} (L : ThresholdLayout k) : List Command :=
  (ThresholdPreparation.Layout.copyIndices (k:=k)).map fun i=>
    .copy (L.certificate (if i.1.val<2 then 0 else 1) i.2)
      (L.word ⟨i.1.val,by have := i.1.isLt; omega⟩ (ThresholdPreparation.Layout.targetPosition i))

def thresholdCommands {k : ℕ} (L : ThresholdLayout k) :=
  thresholdCopies L ++ additionCommands (threeLayout L) ++ additionCommands (upperLayout L)

def threshold {k : ℕ} (L : ThresholdLayout k) := compile (thresholdCommands L)







end QMAPerfectCompleteness.Main.RawG2


