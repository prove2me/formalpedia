-- Prove2me | Definitions.Def_QMAPerfectCompleteness_Proof_CertificateEtaTransport
-- name    : QMAPerfectCompleteness_Proof_CertificateEtaTransport
-- status  : Definition
-- author  : @Dorian Rudolph
-- created : 2026-11-14T15:11:39.972208+00:00
-- url     : https://prove2.me/theorems/1c774fdc-8bd0-4c22-a8a2-abfd2c1c5214
-- title:
--   Initial flag flip and zero-workspace embedding
-- statement:
--   Defines the physical embedding of a logical body and certificate with all additional workspace zero. The singleton NOT gate on the distinguished flag wire is the actual initialization step used to obtain the logical input isometry with flag one.
-- source:
--   Auxiliary formalization source for ~/research/qma1z/main.tex: commit bbe19efbde567e5c8f7fe21655fd0c4da3573e4d, Solutions/CertificateEtaTransport.lean, lines 28–33.

/- Generated from Solutions.CertificateEtaTransport by authoritative Stage-2 skeleton subtraction.
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
import Definitions.Def_QMAPerfectCompleteness_Proof_CertificateInitialization
import Definitions.Def_QMAPerfectCompleteness_Proof_CertificateMixture
import Definitions.Def_QMAPerfectCompleteness_Proof_CertificateVerifierLayout
import Definitions.Def_QMAPerfectCompleteness_Proof_CircuitUnitary
import Definitions.Def_QMAPerfectCompleteness_Proof_ClockCircuits
import Definitions.Def_QMAPerfectCompleteness_Proof_CoherentAcceptance
import Definitions.Def_QMAPerfectCompleteness_Proof_CoherentCertificate
import Definitions.Def_QMAPerfectCompleteness_Proof_CoherentReadout
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



/-! The actual initial X gate transports initialized verifier columns to the logical η isometry. -/
open Matrix
open scoped Classical
set_option backward.isDefEq.respectTransparency false
namespace QMAPerfectCompleteness.Main.CertificateEtaTransport
open BlockCircuit CertificateCoordinates CertificateVerifierLayout CertificateInitialization CoherentCertificate





noncomputable def rawEncoding (V : Verifier gatesG2) (w : ℕ) (q : ComputationReg V) :
    Basis ((bodyWires V+w)+claimQubits V) := (computationEquiv V w).symm (q,fun _=>false)

noncomputable def gates (V : Verifier gatesG2) (w : ℕ) :
    List (Instr gatesG2 ((bodyWires V+w)+claimQubits V)) :=
  [ReversibleGadgets.xAt (physicalFlag V w)]



end QMAPerfectCompleteness.Main.CertificateEtaTransport


