-- Prove2me | Definitions.Def_QMAPerfectCompleteness_Proof_CertificateVerifierCoordinates
-- name    : QMAPerfectCompleteness_Proof_CertificateVerifierCoordinates
-- status  : Definition
-- author  : @Dorian Rudolph
-- created : 2026-11-14T15:06:27.259361+00:00
-- url     : https://prove2.me/theorems/8c7f707c-bc31-40fc-b7b1-5c60532e18e7
-- title:
--   Verifier operators with certificate spectators
-- statement:
--   Defines logical and physical placements of an arbitrary operator on the original verifier wires, tensored with identity on the certificate. It also gives the literal forward and reversed verifier calls and the index-and-certificate key used to describe invariant workspace fibers.
-- source:
--   Auxiliary formalization source for ~/research/qma1z/main.tex: commit bbe19efbde567e5c8f7fe21655fd0c4da3573e4d, Solutions/CertificateVerifierCoordinates.lean, lines 12–106.

/- Generated from Solutions.CertificateVerifierCoordinates by authoritative Stage-2 skeleton subtraction.
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
import Definitions.Def_QMAPerfectCompleteness_Proof_BlockVerifierCoordinates
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
namespace QMAPerfectCompleteness.Main.CoordinateFibers
end QMAPerfectCompleteness.Main.CoordinateFibers
namespace QMAPerfectCompleteness.Main.BlockComposition
end QMAPerfectCompleteness.Main.BlockComposition



/-! Lift the two quantum calls through retained certificate and workspace coordinates. -/
open Matrix
open scoped Kronecker
set_option backward.isDefEq.respectTransparency false
namespace QMAPerfectCompleteness.Main.CertificateVerifierCoordinates
open BlockCircuit BlockCoordinates CertificateCoordinates BlockVerifierCoordinates ReversibleGadgets

/-- Prefix embedding, leaving the appended certificate unchanged. -/
def prefixEmbedding (n q : ℕ) : Fin n ↪ Fin (n+q) :=
  ⟨Fin.castAdd q,by intro i j h; exact Fin.ext (congrArg (fun z : Fin (n+q) => z.val) h)⟩







noncomputable def logicalCall (V : Verifier gatesG2) (M : Matrix V.Wire V.Wire ℂ) :
    Matrix (CoherentCertificate.ComputationReg V) (CoherentCertificate.ComputationReg V) ℂ :=
  logicalVerifier V M ⊗ₖ (1 : Matrix (CertificateMixture.Claim V) (CertificateMixture.Claim V) ℂ)

noncomputable def physicalCall (V : Verifier gatesG2) (w : ℕ) (M : Matrix V.Wire V.Wire ℂ) :=
  placeMatrix (prefixEmbedding (bodyWires V+w) (claimQubits V))
    (placeMatrix (verifierEmbedding w) M)



/-- The workspace key contains only the index and the retained certificate. -/
def key (V : Verifier gatesG2) (p : CoherentCertificate.ComputationReg V) :
    Fin (2^indexQubits V) × CertificateMixture.Claim V := (p.1.1,p.2)





noncomputable def forward (V : Verifier gatesG2) (w : ℕ) :=
  (forwardGates V w).map (Instr.mapWires (prefixEmbedding (bodyWires V+w) (claimQubits V)))
noncomputable def backward (V : Verifier gatesG2) (w : ℕ) :=
  (backwardGates V w).map (Instr.mapWires (prefixEmbedding (bodyWires V+w) (claimQubits V)))





end QMAPerfectCompleteness.Main.CertificateVerifierCoordinates


