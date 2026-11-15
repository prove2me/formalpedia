-- Prove2me | Definitions.Def_QMAPerfectCompleteness_Proof_CertificateOldPrograms
-- name    : QMAPerfectCompleteness_Proof_CertificateOldPrograms
-- status  : Definition
-- author  : @Dorian Rudolph
-- created : 2026-11-14T15:11:10.263672+00:00
-- url     : https://prove2.me/theorems/2535e331-6c10-462d-8921-c937b2d2890c
-- title:
--   Original block gadgets inside the master register
-- statement:
--   Lifts the original middle-stage program, controlled clock increment, identity flag update and active-range phase into the master coherent-certificate register. The original-state projection and flag address retain the published block layout while appended arithmetic and certificate wires act as spectators.
-- source:
--   Auxiliary formalization source for ~/research/qma1z/main.tex: commit bbe19efbde567e5c8f7fe21655fd0c4da3573e4d, Solutions/CertificateOldPrograms.lean, lines 12–57.

/- Generated from Solutions.CertificateOldPrograms by authoritative Stage-2 skeleton subtraction.
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
import Definitions.Def_QMAPerfectCompleteness_Proof_BlockProgramPlacement
import Definitions.Def_QMAPerfectCompleteness_Proof_BooleanCircuits
import Definitions.Def_QMAPerfectCompleteness_Proof_CertificateCoordinates
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



/-! Literal old block gadgets lifted into the master coherent-certificate register. -/
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
open Matrix
namespace QMAPerfectCompleteness.Main.CertificateOldPrograms
open CertificateMasterLayout BlockCompiler ReversibleGadgets
variable (V : Verifier gatesG2)
abbrev Physical := Basis (total V)
def oldState (x : Physical V) : Basis (layoutOf V).total := x ∘ oldEmbedding V

def flag : Fin (total V) := oldEmbedding V (layoutOf V).flagWire



noncomputable def midProgram := (layoutOf V).midProgram.mapWires (oldEmbedding V)
noncomputable def incrementProgram := (layoutOf V).incrementProgram.mapWires (oldEmbedding V)
noncomputable def identityFlagProgram := (layoutOf V).identityFlagProgram.mapWires (oldEmbedding V)









noncomputable def phaseGates := (phaseZAt (layoutOf V).phaseTargets).map (Instr.mapWires (oldEmbedding V))



end QMAPerfectCompleteness.Main.CertificateOldPrograms


