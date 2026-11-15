-- Prove2me | Definitions.Def_QMAPerfectCompleteness_Proof_CertificateClosingCircuit
-- name    : QMAPerfectCompleteness_Proof_CertificateClosingCircuit
-- status  : Definition
-- author  : @Dorian Rudolph
-- created : 2026-11-14T15:10:48.843659+00:00
-- url     : https://prove2.me/theorems/194b0ecc-4f90-4790-9198-6f1dd52b38a4
-- title:
--   Closing gadget on the coherent verifier layout
-- statement:
--   Instantiates the clean variable-history closing gadget on the master physical layout. The chosen closing-range tag, history-test registers and block flag satisfy the required wire-disjointness conditions, giving a literal controlled closing gate list.
-- source:
--   Auxiliary formalization source for ~/research/qma1z/main.tex: commit bbe19efbde567e5c8f7fe21655fd0c4da3573e4d, Solutions/CertificateClosingCircuit.lean, lines 11–63.

/- Generated from Solutions.CertificateClosingCircuit by authoritative Stage-2 skeleton subtraction.
Original explanatory text, declaration names and scoped commands are retained.
Only selected proof cuts, import rewrites and fact-indexed platform edits are applied. -/
import Definitions.Def_QMAPerfectCompleteness_Main_Compiler
import Definitions.Def_QMAPerfectCompleteness_Main_Cyclic
import Init.Data.BitVec.Bitblast
import Definitions.Def_QMAPerfectCompleteness_Main_BlockEncoding
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Definitions.Def_QMAPerfectCompleteness_Proof_BlockCompiler
import Definitions.Def_QMAPerfectCompleteness_Proof_BlockCoordinates
import Definitions.Def_QMAPerfectCompleteness_Proof_BlockEncoding
import Definitions.Def_QMAPerfectCompleteness_Proof_BooleanCircuits
import Definitions.Def_QMAPerfectCompleteness_Proof_CertificateCoordinates
import Definitions.Def_QMAPerfectCompleteness_Proof_CertificateHistoryPrograms
import Definitions.Def_QMAPerfectCompleteness_Proof_CertificateMasterHistory
import Definitions.Def_QMAPerfectCompleteness_Proof_CertificateMasterLayout
import Definitions.Def_QMAPerfectCompleteness_Proof_CertificateMixture
import Definitions.Def_QMAPerfectCompleteness_Proof_CertificateReadout
import Definitions.Def_QMAPerfectCompleteness_Proof_CertificateVerifierLayout
import Definitions.Def_QMAPerfectCompleteness_Proof_CircuitUnitary
import Definitions.Def_QMAPerfectCompleteness_Proof_ClockCircuits
import Definitions.Def_QMAPerfectCompleteness_Proof_CoherentCertificate
import Definitions.Def_QMAPerfectCompleteness_Proof_ComparisonCircuits
import Definitions.Def_QMAPerfectCompleteness_Proof_ControlCircuits
import Definitions.Def_QMAPerfectCompleteness_Proof_Cyclic
import Definitions.Def_QMAPerfectCompleteness_Proof_Dyadic
import Definitions.Def_QMAPerfectCompleteness_Proof_EqualityCircuits
import Definitions.Def_QMAPerfectCompleteness_Proof_EuclideanStates
import Definitions.Def_QMAPerfectCompleteness_Proof_IndexHadamards
import Definitions.Def_QMAPerfectCompleteness_Proof_PointwiseSetup
import Definitions.Def_QMAPerfectCompleteness_Proof_ReversibleGadgets
import Definitions.Def_QMAPerfectCompleteness_Proof_VariableComparison
import Definitions.Def_QMAPerfectCompleteness_Proof_VariableEquality
import Definitions.Def_QMAPerfectCompleteness_Proof_VariableHistoryEquality
import Definitions.Def_QMAPerfectCompleteness_Proof_VerifierAnalysis

/- Namespace registrations retained from original proof-only imports. -/
namespace QMAPerfectCompleteness.Main.Certificate
end QMAPerfectCompleteness.Main.Certificate
namespace QMAPerfectCompleteness.Main.DiagonalProof
end QMAPerfectCompleteness.Main.DiagonalProof



/-! Actual variable-certificate closing branch on the master physical layout. -/
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
namespace QMAPerfectCompleteness.Main.CertificateClosingCircuit
open CertificateMasterLayout BlockCompiler CertificateHistoryPrograms
variable (V : Verifier gatesG2)

def flag : Fin (total V) := oldEmbedding V (layoutOf V).flagWire

lemma flag_value : (flag V).val = BlockCircuit.bodyWires V-1 := by
  change indexQubits V+BlockCircuit.clockWires V+(V.proofQubits+V.ancillaQubits) = _
  dsimp only [BlockCircuit.bodyWires]
  omega

lemma flag_ne_tag (i : Fin 11) : flag V ≠ oldTags V i := by
  intro h
  have hv := congrArg Fin.val h
  have hf := flag_value V
  have hb : 0 < BlockCircuit.bodyWires V := by dsimp only [BlockCircuit.bodyWires]; omega
  rw [oldTags_val] at hv
  omega

lemma flag_ne_equality (j : Fin (3*V.proofQubits+2)) : flag V ≠ historyEquality V j := by
  intro h
  have hv := congrArg Fin.val h
  change indexQubits V+BlockCircuit.clockWires V+(V.proofQubits+V.ancillaQubits) =
    (if j.val<V.proofQubits then indexQubits V+BlockCircuit.clockWires V+j.val else
      if j.val<2*V.proofQubits then BlockCircuit.bodyWires V+work V+(j.val-V.proofQubits) else
      if j.val<3*V.proofQubits+1 then BlockCircuit.bodyWires V+11+(j.val-2*V.proofQubits)
      else BlockCircuit.bodyWires V+10) at hv
  dsimp only [BlockCircuit.bodyWires] at hv
  split_ifs at hv <;> omega

noncomputable def layout : ClosingLayout V.proofQubits (BlockCircuit.clockWires V) (total V) where
  history := historyLayout V
  range := oldTags V 4
  flag := flag V
  range_history := by
    intro h
    have hv := congrArg Fin.val h
    change BlockCircuit.bodyWires V+4 = BlockCircuit.bodyWires V+7 at hv
    omega
  range_flag := (flag_ne_tag V 4).symm
  flag_tags i := flag_ne_tag V (historyTagChoice i)
  flag_eq := flag_ne_equality V
  flag_clock j := by
    intro h
    have hv := congrArg Fin.val h
    change indexQubits V+BlockCircuit.clockWires V+(V.proofQubits+V.ancillaQubits) = indexQubits V+j.val at hv
    have hj := j.isLt
    omega
  flag_scratch j := by
    intro h
    have hv := congrArg Fin.val h
    change indexQubits V+BlockCircuit.clockWires V+(V.proofQubits+V.ancillaQubits) =
      BlockCircuit.bodyWires V+(11+j.val) at hv
    dsimp only [BlockCircuit.bodyWires] at hv
    omega

noncomputable def gates : List (Instr gatesG2 (total V)) := (layout V).gates



end QMAPerfectCompleteness.Main.CertificateClosingCircuit


