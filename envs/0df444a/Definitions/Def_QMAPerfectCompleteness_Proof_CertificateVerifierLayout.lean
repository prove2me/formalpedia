-- Prove2me | Definitions.Def_QMAPerfectCompleteness_Proof_CertificateVerifierLayout
-- name    : QMAPerfectCompleteness_Proof_CertificateVerifierLayout
-- status  : Definition
-- author  : @Dorian Rudolph
-- created : 2026-11-14T15:06:59.067018+00:00
-- url     : https://prove2.me/theorems/7b9bb799-f3f5-469a-b7b2-fd3897293532
-- title:
--   Contiguous proof and ancillary layout for the final verifier
-- statement:
--   Constructs the wire permutation that places history and certificate qubits first, followed by index, original verifier ancillas, flag and workspace. Relabeling a physical gate list and output wire through this permutation produces an ordinary verifier with a contiguous proof register and the standard zero-ancilla initialization.
-- source:
--   Auxiliary formalization source for ~/research/qma1z/main.tex: commit bbe19efbde567e5c8f7fe21655fd0c4da3573e4d, Solutions/CertificateVerifierLayout.lean, lines 11–125.

/- Generated from Solutions.CertificateVerifierLayout by authoritative Stage-2 skeleton subtraction.
Original explanatory text, declaration names and scoped commands are retained.
Only selected proof cuts, import rewrites and fact-indexed platform edits are applied. -/
import Definitions.Def_QMAPerfectCompleteness_Main_Compiler
import Definitions.Def_QMAPerfectCompleteness_Main_Cyclic
import Init.Data.BitVec.Bitblast
import Definitions.Def_QMAPerfectCompleteness_Main_BlockEncoding
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Definitions.Def_QMAPerfectCompleteness_Proof_BlockCoordinates
import Definitions.Def_QMAPerfectCompleteness_Proof_BlockEncoding
import Definitions.Def_QMAPerfectCompleteness_Proof_CertificateCoordinates
import Definitions.Def_QMAPerfectCompleteness_Proof_CertificateMixture
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
import Definitions.Def_QMAPerfectCompleteness_Proof_VerifierAnalysis

/- Namespace registrations retained from original proof-only imports. -/
namespace QMAPerfectCompleteness.Main.Certificate
end QMAPerfectCompleteness.Main.Certificate
namespace QMAPerfectCompleteness.Main.DiagonalProof
end QMAPerfectCompleteness.Main.DiagonalProof



/-! Reordering the actual coherent-certificate wires into the published verifier convention:
history and certificate first, followed by index, verifier ancillas, flag and workspace. -/
open Matrix
set_option backward.isDefEq.respectTransparency false
namespace QMAPerfectCompleteness.Main.CertificateVerifierLayout
open CertificateCoordinates BlockCircuit ReversibleGadgets

/-- Physical order index/history/ancillas/certificate becomes history/certificate/index/ancillas. -/
def reorder (k h a c : ℕ) : Fin (k+h+a+c) ≃ Fin (h+c+k+a) where
  toFun i := ⟨if i.val<k then h+c+i.val else if i.val<k+h then i.val-k else
    if i.val<k+h+a then h+c+k+(i.val-(k+h)) else h+(i.val-(k+h+a)),by
      have hi := i.isLt
      split_ifs <;> omega⟩
  invFun i := ⟨if i.val<h then k+i.val else if i.val<h+c then k+h+a+(i.val-h) else
    if i.val<h+c+k then i.val-(h+c) else k+h+(i.val-(h+c+k)),by
      have hi := i.isLt
      split_ifs <;> omega⟩
  left_inv i := by
    apply Fin.ext
    have hi := i.isLt
    dsimp
    split_ifs <;> omega
  right_inv i := by
    apply Fin.ext
    have hi := i.isLt
    dsimp
    split_ifs <;> omega

abbrev ancillaQubits (V : Verifier gatesG2) (w : ℕ) : ℕ :=
  indexQubits V + (V.ancillaQubits + 1 + w)

/-- Exact permutation into a verifier with a contiguous history-and-certificate proof. -/
def wireEquiv (V : Verifier gatesG2) (w : ℕ) :
    Fin ((bodyWires V+w)+claimQubits V) ≃ Fin (proofQubits V+ancillaQubits V w) :=
  (finCongr (show (bodyWires V+w)+claimQubits V =
      indexQubits V+(clockWires V+V.proofQubits)+(V.ancillaQubits+1+w)+claimQubits V by
        dsimp [bodyWires]; omega)).trans
    ((reorder (indexQubits V) (clockWires V+V.proofQubits) (V.ancillaQubits+1+w) (claimQubits V)).trans
      (finCongr (by dsimp [proofQubits,ancillaQubits]; omega)))

def basisEquiv (V : Verifier gatesG2) (w : ℕ) :
    Basis (proofQubits V+ancillaQubits V w) ≃ Basis ((bodyWires V+w)+claimQubits V) :=
  Equiv.arrowCongr (wireEquiv V w).symm (Equiv.refl Bool)

noncomputable def verifier (V : Verifier gatesG2) (w : ℕ)
    (gs : List (Instr gatesG2 ((bodyWires V+w)+claimQubits V)))
    (output : Fin ((bodyWires V+w)+claimQubits V)) : Verifier gatesG2 where
  proofQubits := CertificateCoordinates.proofQubits V
  ancillaQubits := ancillaQubits V w
  gates := gs.map (Instr.mapWires (wireEquiv V w).toEmbedding)
  output := wireEquiv V w output







def physicalIndex (V : Verifier gatesG2) (w : ℕ) (i : Fin (indexQubits V)) :
    Fin ((bodyWires V+w)+claimQubits V) := ⟨i,by have := i.isLt; dsimp [bodyWires]; omega⟩
def physicalHistory (V : Verifier gatesG2) (w : ℕ) (i : Fin (clockWires V+V.proofQubits)) :
    Fin ((bodyWires V+w)+claimQubits V) :=
  ⟨indexQubits V+i,by have := i.isLt; dsimp [bodyWires]; omega⟩
def physicalAncilla (V : Verifier gatesG2) (w : ℕ) (i : Fin (V.ancillaQubits+1+w)) :
    Fin ((bodyWires V+w)+claimQubits V) :=
  ⟨indexQubits V+(clockWires V+V.proofQubits)+i,by have := i.isLt; dsimp [bodyWires]; omega⟩
def physicalClaim (V : Verifier gatesG2) (w : ℕ) (i : Fin (claimQubits V)) :
    Fin ((bodyWires V+w)+claimQubits V) := Fin.natAdd (bodyWires V+w) i









/-- The standard verifier initialization expressed in physical circuit coordinates. -/
def prepared (V : Verifier gatesG2) (w : ℕ) (p : Basis (proofQubits V)) :
    Basis ((bodyWires V+w)+claimQubits V) :=
  basisEquiv V w (Fin.append p (fun _ : Fin (ancillaQubits V w) => false))






end QMAPerfectCompleteness.Main.CertificateVerifierLayout


