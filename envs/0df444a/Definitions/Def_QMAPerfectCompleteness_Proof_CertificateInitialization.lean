-- Prove2me | Definitions.Def_QMAPerfectCompleteness_Proof_CertificateInitialization
-- name    : QMAPerfectCompleteness_Proof_CertificateInitialization
-- status  : Definition
-- author  : @Dorian Rudolph
-- created : 2026-11-14T15:08:20.281425+00:00
-- url     : https://prove2.me/theorems/7d8fac4d-5090-45a5-aff0-d6156ffb1fa8
-- title:
--   Initialized history, certificate and block-flag coordinates
-- statement:
--   Splits the physical proof into clock, original proof and certificate bits, and embeds these data with index zero, original verifier ancillas zero and clean workspace. The logical initial state retains an explicit flag value; the distinguished physical flag is the qubit set to one for the block-test input.
-- source:
--   Auxiliary formalization source for ~/research/qma1z/main.tex: commit bbe19efbde567e5c8f7fe21655fd0c4da3573e4d, Solutions/CertificateInitialization.lean, lines 10–176.

/- Generated from Solutions.CertificateInitialization by authoritative Stage-2 skeleton subtraction.
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
import Definitions.Def_QMAPerfectCompleteness_Proof_VerifierAnalysis

/- Namespace registrations retained from original proof-only imports. -/
namespace QMAPerfectCompleteness.Main.Certificate
end QMAPerfectCompleteness.Main.Certificate
namespace QMAPerfectCompleteness.Main.DiagonalProof
end QMAPerfectCompleteness.Main.DiagonalProof



/-! Exact initialized history/certificate registers in the physical coherent-verifier layout. -/
open Matrix
set_option backward.isDefEq.respectTransparency false
namespace QMAPerfectCompleteness.Main.CertificateInitialization
open CertificateCoordinates CertificateVerifierLayout BlockCircuit BlockCoordinates

variable (V : Verifier gatesG2) (w : ℕ)
def historyBits (p : Basis (proofQubits V)) : Basis (clockWires V+V.proofQubits) :=
  (splitBasis (clockWires V+V.proofQubits) (claimQubits V) p).1
def claimBits (p : Basis (proofQubits V)) : Basis (claimQubits V) :=
  (splitBasis (clockWires V+V.proofQubits) (claimQubits V) p).2
def clockBits (p : Basis (proofQubits V)) : Basis (clockWires V) :=
  (splitBasis (clockWires V) V.proofQubits (historyBits V p)).1
def proofBits (p : Basis (proofQubits V)) : V.Proof :=
  (splitBasis (clockWires V) V.proofQubits (historyBits V p)).2

noncomputable def logicalInitial (f : Bool) (p : CoherentCertificate.ProofReg V) : CoherentCertificate.ComputationReg V :=
  ((0,p.1.1,V.initialState p.1.2,f),p.2)












/-- The single physical flag initialized to one for η. -/
def physicalFlag : Fin ((bodyWires V+w)+claimQubits V) := Fin.castAdd (claimQubits V) (flagWire (V:=V) (w:=w))









/-- The fully prepared η basis state before certificate arithmetic. -/
noncomputable def etaState (p : Basis (proofQubits V)) : Basis ((bodyWires V+w)+claimQubits V) :=
  (computationEquiv V w).symm (logicalInitial V true (proofEquiv V p),fun _=>false)



end QMAPerfectCompleteness.Main.CertificateInitialization


