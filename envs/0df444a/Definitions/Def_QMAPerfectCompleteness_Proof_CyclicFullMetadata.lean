-- Prove2me | Definitions.Def_QMAPerfectCompleteness_Proof_CyclicFullMetadata
-- name    : QMAPerfectCompleteness_Proof_CyclicFullMetadata
-- status  : Definition
-- author  : @Dorian Rudolph
-- created : 2026-11-14T15:11:12.606897+00:00
-- url     : https://prove2.me/theorems/e385cc87-a7f1-4672-9a20-faf08bc8d38d
-- title:
--   Complete cyclic serializer metadata
-- statement:
--   Defines the seven-field stream k, c, ell, m, a, output and HH, followed by the original verifier gate body. It also supplies the corresponding typed-verifier values and the total metadata extraction interface.
-- source:
--   Formalization auxiliary for ~/research/qma1z/main.tex, the uniform circuit implementation supporting Section 3.3 and the proof of Theorem 1.1. Original Lean source: commit bbe19efbde567e5c8f7fe21655fd0c4da3573e4d, Solutions/CyclicFullMetadata.lean, retained declaration span lines 9–29.

/- Generated from Solutions.CyclicFullMetadata by authoritative Stage-2 skeleton subtraction.
Original explanatory text, declaration names and scoped commands are retained.
Only selected proof cuts, import rewrites and fact-indexed platform edits are applied. -/
import Definitions.Def_QMAPerfectCompleteness_Main_Cyclic
import Definitions.Def_QMAPerfectCompleteness_Main_Compiler
import Definitions.Def_QMAPerfectCompleteness_Main_Classes
import Definitions.Def_QAlgorithms_ClassicalStringComputability
import Definitions.Def_QMAPerfectCompleteness_Main_Gates
import Definitions.Def_QMAPerfectCompleteness_Proof_BinaryComposition
import Definitions.Def_QMAPerfectCompleteness_Proof_BlockEncoding
import Definitions.Def_QMAPerfectCompleteness_Proof_CircuitUnitary
import Definitions.Def_QMAPerfectCompleteness_Proof_ClassTransport
import Definitions.Def_QMAPerfectCompleteness_Proof_ConcreteUniformity
import Definitions.Def_QMAPerfectCompleteness_Proof_ControlCircuits
import Definitions.Def_QMAPerfectCompleteness_Proof_Cyclic
import Definitions.Def_QMAPerfectCompleteness_Proof_CyclicClockMetadata
import Definitions.Def_QMAPerfectCompleteness_Proof_CyclicClockPrefixTM
import Definitions.Def_QMAPerfectCompleteness_Proof_CyclicIndexMetadataCorrectness
import Definitions.Def_QMAPerfectCompleteness_Proof_CyclicIndexMetadataIO
import Definitions.Def_QMAPerfectCompleteness_Proof_CyclicIndexMetadataTM
import Definitions.Def_QMAPerfectCompleteness_Proof_CyclicMetadataTM
import Definitions.Def_QMAPerfectCompleteness_Proof_DyadicCompiler
import Definitions.Def_QMAPerfectCompleteness_Proof_DyadicEncoding
import Definitions.Def_QMAPerfectCompleteness_Proof_DyadicPreservation
import Definitions.Def_QMAPerfectCompleteness_Proof_EuclideanStates
import Definitions.Def_QMAPerfectCompleteness_Proof_FinitePlanCompilerTM
import Definitions.Def_QMAPerfectCompleteness_Proof_GateCompilation
import Definitions.Def_QMAPerfectCompleteness_Proof_HTCompiler
import Definitions.Def_QMAPerfectCompleteness_Proof_HTCompilerTM
import Definitions.Def_QMAPerfectCompleteness_Proof_HTEncoding
import Definitions.Def_QMAPerfectCompleteness_Proof_HTPreservation
import Definitions.Def_QMAPerfectCompleteness_Proof_HadamardToffoli
import Definitions.Def_QMAPerfectCompleteness_Proof_PolyTimeComposition
import Definitions.Def_QMAPerfectCompleteness_Proof_RawCircuitEncoding
import Definitions.Def_QMAPerfectCompleteness_Proof_RealSimulation
import Definitions.Def_QMAPerfectCompleteness_Proof_Repetition
import Definitions.Def_QMAPerfectCompleteness_Proof_RepetitionCircuit
import Definitions.Def_QMAPerfectCompleteness_Proof_RepetitionEncoding
import Definitions.Def_QMAPerfectCompleteness_Proof_ReversibleGadgets
import Definitions.Def_QMAPerfectCompleteness_Proof_StackTransfers
import Definitions.Def_QMAPerfectCompleteness_Proof_StructuredStackCode
import Definitions.Def_QMAPerfectCompleteness_Proof_UnaryFieldCode
import Definitions.Def_QMAPerfectCompleteness_Proof_UnaryMetadataArithmetic
import Definitions.Def_QMAPerfectCompleteness_Proof_UnaryNextPowerCorrectness
import Definitions.Def_QMAPerfectCompleteness_Proof_UnaryNextPowerPhases
import Definitions.Def_QMAPerfectCompleteness_Proof_UnaryNextPowerTM
import Definitions.Def_QMAPerfectCompleteness_Proof_UnaryStackOps
import Definitions.Def_QMAPerfectCompleteness_Proof_VerifierEncoding

/- Namespace registrations retained from original proof-only imports. -/
namespace QMAPerfectCompleteness.Main.DiagonalProof
end QMAPerfectCompleteness.Main.DiagonalProof
namespace QMAPerfectCompleteness.Uniformity.Expansion
end QMAPerfectCompleteness.Uniformity.Expansion
namespace QMAPerfectCompleteness.Uniformity.UnaryNatArithmetic
end QMAPerfectCompleteness.Uniformity.UnaryNatArithmetic


/-! A closed actual polynomial-time compiler for all cyclic serializer parameters. -/
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
namespace QMAPerfectCompleteness.Main.CyclicMetadataTM
open QAlgorithms.Complexity (Str encNat)
open QMAPerfectCompleteness.Uniformity

noncomputable def metadataValues (V : Verifier gatesG2) : CyclicIndexMetadataTM.Values :=
  CyclicIndexMetadataTM.values (clockQubits V.proofQubits) (ell V.proofQubits)
    V.proofQubits V.ancillaQubits V.output.val (hhCount V)
noncomputable def sourceBody (V : Verifier gatesG2) : Str := V.gates.flatMap Instr.encode




/-- k,c,ell,m,a,out,HH followed by the original literal gate body. -/
noncomputable def metadataCode (V : Verifier gatesG2) : Str := encNat (indexQubits V)++clockCode V

noncomputable def metadataExtract (s : Str) : Str :=
  match Encoding.decodeVerifier gatesG2 s with
  | none=>[]
  | some V=>metadataCode V




end QMAPerfectCompleteness.Main.CyclicMetadataTM


