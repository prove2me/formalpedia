-- Prove2me | Definitions.Def_QMAPerfectCompleteness_Proof_CertificateBlockCorrectness
-- name    : QMAPerfectCompleteness_Proof_CertificateBlockCorrectness
-- status  : Definition
-- author  : @Dorian Rudolph
-- created : 2026-11-14T15:12:36.479503+00:00
-- url     : https://prove2.me/theorems/6cc623aa-fece-4e8b-9ac5-1cb256c58101
-- title:
--   Prepared workspace fibers for coherent block transport
-- statement:
--   Encodes a logical body and certificate together with workspace that may depend on the index and certificate. The prepared-fiber invariant requires clean comparator and old-work registers and agreement of computed range predicates with their intended numerical truth values; tagged fibers replace only the six branch tags.
-- source:
--   Auxiliary formalization source for ~/research/qma1z/main.tex: commit bbe19efbde567e5c8f7fe21655fd0c4da3573e4d, Solutions/CertificateBlockCorrectness.lean, lines 18–186.

/- Generated from Solutions.CertificateBlockCorrectness by authoritative Stage-2 skeleton subtraction.
Original explanatory text, declaration names and scoped commands are retained.
Only selected proof cuts, import rewrites and fact-indexed platform edits are applied. -/
import Definitions.Def_QMAPerfectCompleteness_Main_Compiler
import Definitions.Def_QMAPerfectCompleteness_Main_Cyclic
import Init.Data.BitVec.Bitblast
import Definitions.Def_QMAPerfectCompleteness_Main_BlockEncoding
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Definitions.Def_QMAPerfectCompleteness_Proof_BlockClockCoordinates
import Definitions.Def_QMAPerfectCompleteness_Proof_BlockCompiler
import Definitions.Def_QMAPerfectCompleteness_Proof_BlockCoordinates
import Definitions.Def_QMAPerfectCompleteness_Proof_BlockEncoding
import Definitions.Def_QMAPerfectCompleteness_Proof_BlockImplements
import Definitions.Def_QMAPerfectCompleteness_Proof_BlockLogicalActions
import Definitions.Def_QMAPerfectCompleteness_Proof_BlockLogicalSelect
import Definitions.Def_QMAPerfectCompleteness_Proof_BlockProgramPlacement
import Definitions.Def_QMAPerfectCompleteness_Proof_BlockStateCoordinates
import Definitions.Def_QMAPerfectCompleteness_Proof_BlockTaggedActions
import Definitions.Def_QMAPerfectCompleteness_Proof_BlockVerifierCoordinates
import Definitions.Def_QMAPerfectCompleteness_Proof_BooleanCircuits
import Definitions.Def_QMAPerfectCompleteness_Proof_CertificateCoordinates
import Definitions.Def_QMAPerfectCompleteness_Proof_CertificateHadamardCoordinates
import Definitions.Def_QMAPerfectCompleteness_Proof_CertificateMasterHistory
import Definitions.Def_QMAPerfectCompleteness_Proof_CertificateMasterLayout
import Definitions.Def_QMAPerfectCompleteness_Proof_CertificateMixture
import Definitions.Def_QMAPerfectCompleteness_Proof_CertificateRangeCircuit
import Definitions.Def_QMAPerfectCompleteness_Proof_CertificateReadout
import Definitions.Def_QMAPerfectCompleteness_Proof_CertificateValidity
import Definitions.Def_QMAPerfectCompleteness_Proof_CertificateValidityCircuit
import Definitions.Def_QMAPerfectCompleteness_Proof_CertificateVerifierCoordinates
import Definitions.Def_QMAPerfectCompleteness_Proof_CertificateVerifierLayout
import Definitions.Def_QMAPerfectCompleteness_Proof_CircuitUnitary
import Definitions.Def_QMAPerfectCompleteness_Proof_ClockCircuits
import Definitions.Def_QMAPerfectCompleteness_Proof_CoherentCertificate
import Definitions.Def_QMAPerfectCompleteness_Proof_ComparisonCircuits
import Definitions.Def_QMAPerfectCompleteness_Proof_ControlCircuits
import Definitions.Def_QMAPerfectCompleteness_Proof_Cyclic
import Definitions.Def_QMAPerfectCompleteness_Proof_Dyadic
import Definitions.Def_QMAPerfectCompleteness_Proof_DynamicBlockCompiler
import Definitions.Def_QMAPerfectCompleteness_Proof_DynamicRangeLayout
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
namespace QMAPerfectCompleteness.Main.BlockComposition
end QMAPerfectCompleteness.Main.BlockComposition
namespace QMAPerfectCompleteness.Main.BlockTransport
end QMAPerfectCompleteness.Main.BlockTransport
namespace QMAPerfectCompleteness.Main.BlockHistoryCoordinates
end QMAPerfectCompleteness.Main.BlockHistoryCoordinates
namespace QMAPerfectCompleteness.Main.BlockHadamardCoordinates
end QMAPerfectCompleteness.Main.BlockHadamardCoordinates
namespace QMAPerfectCompleteness.Main.Certificate
end QMAPerfectCompleteness.Main.Certificate
namespace QMAPerfectCompleteness.Main.DiagonalProof
end QMAPerfectCompleteness.Main.DiagonalProof
namespace QMAPerfectCompleteness.Main.CoordinateFibers
end QMAPerfectCompleteness.Main.CoordinateFibers



/-! Exact coherent block SELECT on the master certificate register layout. -/
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
open Matrix
open scoped Kronecker
namespace QMAPerfectCompleteness.Main.CertificateBlockCorrectness
open CertificateMasterLayout CertificateCoordinates BlockCoordinates BlockCompiler
open ReversibleGadgets BlockImplements
variable (V : Verifier gatesG2)

abbrev Logical := CoherentCertificate.ComputationReg V
abbrev Physical := Basis (total V)
abbrev Key := Fin (2^k V) × CertificateMixture.Claim V
abbrev coords := computationEquiv V (work V)
noncomputable instance logicalDecidable : DecidableEq (Logical V) := Classical.decEq _
def key (p : Logical V) : Key V := (p.1.1,p.2)

/-- Prepared arithmetic workspace may depend on the coherent index/certificate control. -/
noncomputable def embed (s : Key V → Basis (work V)) (p : Logical V) : Physical V :=
  (coords V).symm (p,s (key V p))



def old (x : Physical V) : Basis (layoutOf V).total := x ∘ oldEmbedding V

def workWire (i : Fin (work V)) : Fin (total V) :=
  Fin.castAdd (claimQubits V) (BlockCircuit.workspaceWire i)



































def taggedSpace (s : Key V → Basis (work V)) (q : Key V) : Basis (work V) :=
  fun i => if hi : i.val<6 then Layout.rangeTruth q.2.2.1.val q.2.2.2.val q.1.val ⟨i.val,hi⟩ else s q i

/-- Interface discharged by coherent threshold preparation and zero old-work initialization. -/
structure Prepared (s : Key V → Basis (work V)) : Prop where
  range_clean : ∀ p, (CertificateRangeCircuit.layout V).Clean (embed V s p)
  old_clean : ∀ p, BlockCircuit.WorkspaceClean (old V (embed V s p))
  range_truth : ∀ p, (CertificateRangeCircuit.layout V).truth (embed V s p) =
    Layout.rangeTruth p.2.2.1.val p.2.2.2.val p.1.1.val









end QMAPerfectCompleteness.Main.CertificateBlockCorrectness


