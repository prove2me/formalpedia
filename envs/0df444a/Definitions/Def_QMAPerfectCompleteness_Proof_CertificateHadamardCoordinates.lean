-- Prove2me | Definitions.Def_QMAPerfectCompleteness_Proof_CertificateHadamardCoordinates
-- name    : QMAPerfectCompleteness_Proof_CertificateHadamardCoordinates
-- status  : Definition
-- author  : @Dorian Rudolph
-- created : 2026-11-14T15:07:52.158201+00:00
-- url     : https://prove2.me/theorems/061d06c6-e7b3-4316-9c01-87820401dd15
-- title:
--   Index Hadamards with certificate-dependent workspace
-- statement:
--   Places an operator on the logical index register while acting identically on the body and certificate registers. It also defines the corresponding physical placement and the literal paired-Hadamard gate list, allowing the uniform index superposition to be created and reversed without changing prepared certificate arithmetic.
-- source:
--   Auxiliary formalization source for ~/research/qma1z/main.tex: commit bbe19efbde567e5c8f7fe21655fd0c4da3573e4d, Solutions/CertificateHadamardCoordinates.lean, lines 11–77.

/- Generated from Solutions.CertificateHadamardCoordinates by authoritative Stage-2 skeleton subtraction.
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
import Definitions.Def_QMAPerfectCompleteness_Proof_BlockVerifierCoordinates
import Definitions.Def_QMAPerfectCompleteness_Proof_CertificateCoordinates
import Definitions.Def_QMAPerfectCompleteness_Proof_CertificateMixture
import Definitions.Def_QMAPerfectCompleteness_Proof_CertificateVerifierCoordinates
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
namespace QMAPerfectCompleteness.Main.BlockHadamardCoordinates
end QMAPerfectCompleteness.Main.BlockHadamardCoordinates



/-! The index Hadamards preserve certificate-dependent arithmetic workspace. -/
open Matrix
open scoped Kronecker
set_option backward.isDefEq.respectTransparency false
namespace QMAPerfectCompleteness.Main.CertificateHadamardCoordinates
open BlockCircuit BlockCoordinates CertificateCoordinates CertificateVerifierCoordinates ReversibleGadgets

def indexEmbedding (V : Verifier gatesG2) (w : ℕ) :
    Fin (indexQubits V) ↪ Fin (bodyWires V+w) :=
  ⟨indexWire,by intro i j h; exact Fin.ext (congrArg (fun z : Fin (bodyWires V+w) => z.val) h)⟩



noncomputable def logicalH (V : Verifier gatesG2)
    (H : Matrix (Fin (2^indexQubits V)) (Fin (2^indexQubits V)) ℂ) :
    Matrix (CoherentCertificate.ComputationReg V) (CoherentCertificate.ComputationReg V) ℂ :=
  (H ⊗ₖ (1 : Matrix V.Body V.Body ℂ)) ⊗ₖ
    (1 : Matrix (CertificateMixture.Claim V) (CertificateMixture.Claim V) ℂ)

noncomputable def physicalH (V : Verifier gatesG2) (w : ℕ)
    (H : Matrix (Fin (2^indexQubits V)) (Fin (2^indexQubits V)) ℂ) :=
  placeMatrix (prefixEmbedding (bodyWires V+w) (claimQubits V))
    (placeMatrix (indexEmbedding V w)
      (H.submatrix (IndexHadamards.bitsEquiv _) (IndexHadamards.bitsEquiv _)))





noncomputable def gates (V : Verifier gatesG2) (w : ℕ) :=
  (IndexHadamards.pairedHadamards (indexEmbedding V w)).map
    (Instr.mapWires (prefixEmbedding (bodyWires V+w) (claimQubits V)))



end QMAPerfectCompleteness.Main.CertificateHadamardCoordinates


