-- Prove2me | Definitions.Def_QMAPerfectCompleteness_Proof_CertificateMasterReadout
-- name    : QMAPerfectCompleteness_Proof_CertificateMasterReadout
-- status  : Definition
-- author  : @Dorian Rudolph
-- created : 2026-11-14T15:09:47.906379+00:00
-- url     : https://prove2.me/theorems/eae7a8c8-a870-408d-9a91-d681499354f4
-- title:
--   Physical zero test and acceptance-output layout
-- statement:
--   Instantiates the final readout on the index, original verifier ancillas and block flag. The validity bit, zero-test bit, acceptance output and zero-test scratch are placed on disjoint wires, yielding the literal acceptance-flag circuit used by the coherent verifier.
-- source:
--   Auxiliary formalization source for ~/research/qma1z/main.tex: commit bbe19efbde567e5c8f7fe21655fd0c4da3573e4d, Solutions/CertificateMasterReadout.lean, lines 9–77.

/- Generated from Solutions.CertificateMasterReadout by authoritative Stage-2 skeleton subtraction.
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



/-! Instantiation of the final physical acceptance flag on the coherent verifier layout. -/
set_option backward.isDefEq.respectTransparency false
namespace QMAPerfectCompleteness.Main.CertificateMasterLayout
open BlockCircuit CertificateReadout
variable (V : Verifier gatesG2)

abbrev zeroBits : ℕ := k V+(V.ancillaQubits+1)

/-- The measured Z register is precisely index, verifier Y ancillas, and the block flag. -/
def zeroControls : Fin (zeroBits V) ↪ Fin (total V) :=
  ⟨fun j => ⟨if j.val<k V then j.val else k V+clockWires V+V.proofQubits+(j.val-k V),by
      have hj : j.val<k V+(V.ancillaQubits+1) := j.isLt
      change (if j.val<k V then j.val else k V+clockWires V+V.proofQubits+(j.val-k V)) <
        (bodyWires V+work V)+CertificateCoordinates.claimQubits V
      dsimp only [bodyWires]
      split_ifs <;> dsimp only [k] at * <;> omega⟩,
    by intro i j h
       have hv := congrArg Fin.val h
       change (if i.val<k V then i.val else k V+clockWires V+V.proofQubits+(i.val-k V)) =
         (if j.val<k V then j.val else k V+clockWires V+V.proofQubits+(j.val-k V)) at hv
       apply Fin.ext
       split_ifs at hv <;> omega⟩

lemma zeroControls_lt_body (j : Fin (zeroBits V)) : (zeroControls V j).val<bodyWires V := by
  have hj : j.val<k V+(V.ancillaQubits+1) := j.isLt
  change (if j.val<k V then j.val else k V+clockWires V+V.proofQubits+(j.val-k V)) < _
  dsimp only [bodyWires]
  split_ifs <;> dsimp only [k] at * <;> omega

def readoutOffsets : Fin 3 → ℕ :=
  ![oldWork V+prepWork V+7,oldWork V+prepWork V+8+readoutWork V,oldWork V+prepWork V+9+readoutWork V]

def readoutTagTriple : Fin 3 ↪ Fin (total V) :=
  ⟨fun j => ⟨bodyWires V+readoutOffsets V j,by
      change bodyWires V+readoutOffsets V j < (bodyWires V+work V)+CertificateCoordinates.claimQubits V
      fin_cases j <;> norm_num [readoutOffsets] <;> dsimp only [work] <;> omega⟩,by
    intro i j h
    have hv := congrArg Fin.val h
    change bodyWires V+readoutOffsets V i = bodyWires V+readoutOffsets V j at hv
    fin_cases i <;> fin_cases j <;> first |rfl| (norm_num [readoutOffsets] at hv <;> omega)⟩

lemma readoutTag_ge_body (j : Fin 3) : bodyWires V ≤ (readoutTagTriple V j).val := by
  change bodyWires V ≤ bodyWires V+readoutOffsets V j
  omega

def readoutAndLayout : ControlCircuits.AndLayout (zeroBits V) (total V) where
  controls := zeroControls V
  flags := (finCongr (show zeroBits V+1=readoutWork V by dsimp [zeroBits,readoutWork,k]; omega)).toEmbedding.trans (readoutFlags V)
  disjoint i j := by
    intro h
    have hv := congrArg Fin.val h
    have hi := zeroControls_lt_body V i
    change (zeroControls V i).val = bodyWires V+(oldWork V+prepWork V+2+6)+j.val at hv
    omega

/-- Validity bit, all-zero work bit and acceptance output are disjoint from Z and test scratch. -/
def readoutLayout : CertificateReadout.Layout (zeroBits V) (total V) where
  zeros := readoutAndLayout V
  tags := readoutTagTriple V
  disjoint_controls i j := by
    intro h
    have hv := congrArg Fin.val h
    have hi := readoutTag_ge_body V i
    have hj := zeroControls_lt_body V j
    change (readoutTagTriple V i).val = (zeroControls V j).val at hv
    omega
  disjoint_flags i j := by
    intro h
    have hv := congrArg Fin.val h
    have hj : j.val < readoutWork V := by have := j.isLt; dsimp [zeroBits,readoutWork,k] at *; omega
    change (readoutTagTriple V i).val = bodyWires V+(oldWork V+prepWork V+2+6)+j.val at hv
    change bodyWires V+readoutOffsets V i = bodyWires V+(oldWork V+prepWork V+2+6)+j.val at hv
    fin_cases i <;> norm_num [readoutOffsets] at hv <;> omega

noncomputable def readoutGates := (readoutLayout V).gates







end QMAPerfectCompleteness.Main.CertificateMasterLayout


