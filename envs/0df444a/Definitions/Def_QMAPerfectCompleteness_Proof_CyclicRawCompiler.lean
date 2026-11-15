-- Prove2me | Definitions.Def_QMAPerfectCompleteness_Proof_CyclicRawCompiler
-- name    : QMAPerfectCompleteness_Proof_CyclicRawCompiler
-- status  : Definition
-- author  : @Dorian Rudolph
-- created : 2026-11-14T15:29:16.82872+00:00
-- url     : https://prove2.me/theorems/6c879ae2-745f-4b15-86f4-c75507332170
-- title:
--   Raw circuit specification of the cyclic verifier
-- statement:
--   Defines the literal raw instruction lists for certificate preparation and validity, range selection, history and closing branches, clock control and final readout. These lists specify the coherent-certificate verifier independently of matrix-valued gate records.
-- source:
--   Formalization auxiliary for ~/research/qma1z/main.tex, Section 3.3, the coherent-certificate verifier and controlled block construction. Original Lean source: commit bbe19efbde567e5c8f7fe21655fd0c4da3573e4d, Solutions/CyclicRawCompiler.lean, retained declaration span lines 15–75.

/- Generated from Solutions.CyclicRawCompiler by authoritative Stage-2 skeleton subtraction.
Original explanatory text, declaration names and scoped commands are retained.
Only selected proof cuts, import rewrites and fact-indexed platform edits are applied. -/
import Definitions.Def_QMAPerfectCompleteness_Main_Classes
import Definitions.Def_QMAPerfectCompleteness_Main_Compiler
import Definitions.Def_QMAPerfectCompleteness_Main_Cyclic
import Init.Data.BitVec.Bitblast
import Definitions.Def_QMAPerfectCompleteness_Main_BlockEncoding
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.DeriveFintype
import Definitions.Def_QAlgorithms_ClassicalStringComputability
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
import Definitions.Def_QMAPerfectCompleteness_Proof_BooleanFraming
import Definitions.Def_QMAPerfectCompleteness_Proof_CertificateBlockCompilerCorrectness
import Definitions.Def_QMAPerfectCompleteness_Proof_CertificateBlockCorrectness
import Definitions.Def_QMAPerfectCompleteness_Proof_CertificateClosingActions
import Definitions.Def_QMAPerfectCompleteness_Proof_CertificateClosingCircuit
import Definitions.Def_QMAPerfectCompleteness_Proof_CertificateCoordinates
import Definitions.Def_QMAPerfectCompleteness_Proof_CertificateEtaTransport
import Definitions.Def_QMAPerfectCompleteness_Proof_CertificateHadamardCoordinates
import Definitions.Def_QMAPerfectCompleteness_Proof_CertificateHistoryCoordinates
import Definitions.Def_QMAPerfectCompleteness_Proof_CertificateHistoryPrograms
import Definitions.Def_QMAPerfectCompleteness_Proof_CertificateInitialization
import Definitions.Def_QMAPerfectCompleteness_Proof_CertificateLogicalSelect
import Definitions.Def_QMAPerfectCompleteness_Proof_CertificateMasterHistory
import Definitions.Def_QMAPerfectCompleteness_Proof_CertificateMasterLayout
import Definitions.Def_QMAPerfectCompleteness_Proof_CertificateMasterReadout
import Definitions.Def_QMAPerfectCompleteness_Proof_CertificateMixture
import Definitions.Def_QMAPerfectCompleteness_Proof_CertificateOldPrograms
import Definitions.Def_QMAPerfectCompleteness_Proof_CertificatePostCorrectness
import Definitions.Def_QMAPerfectCompleteness_Proof_CertificatePreparation
import Definitions.Def_QMAPerfectCompleteness_Proof_CertificateQuantumTransports
import Definitions.Def_QMAPerfectCompleteness_Proof_CertificateRangeCircuit
import Definitions.Def_QMAPerfectCompleteness_Proof_CertificateReadout
import Definitions.Def_QMAPerfectCompleteness_Proof_CertificateStageActions
import Definitions.Def_QMAPerfectCompleteness_Proof_CertificateThresholdLayout
import Definitions.Def_QMAPerfectCompleteness_Proof_CertificateValidity
import Definitions.Def_QMAPerfectCompleteness_Proof_CertificateValidityCircuit
import Definitions.Def_QMAPerfectCompleteness_Proof_CertificateValidityPreparation
import Definitions.Def_QMAPerfectCompleteness_Proof_CertificateVerifierCoordinates
import Definitions.Def_QMAPerfectCompleteness_Proof_CertificateVerifierLayout
import Definitions.Def_QMAPerfectCompleteness_Proof_CircuitRecipe
import Definitions.Def_QMAPerfectCompleteness_Proof_CircuitUnitary
import Definitions.Def_QMAPerfectCompleteness_Proof_ClockCircuits
import Definitions.Def_QMAPerfectCompleteness_Proof_CoherentAcceptance
import Definitions.Def_QMAPerfectCompleteness_Proof_CoherentCertificate
import Definitions.Def_QMAPerfectCompleteness_Proof_CoherentReadout
import Definitions.Def_QMAPerfectCompleteness_Proof_ComparisonCircuits
import Definitions.Def_QMAPerfectCompleteness_Proof_ControlCircuits
import Definitions.Def_QMAPerfectCompleteness_Proof_Cyclic
import Definitions.Def_QMAPerfectCompleteness_Proof_CyclicRawLayout
import Definitions.Def_QMAPerfectCompleteness_Proof_CyclicVerifier
import Definitions.Def_QMAPerfectCompleteness_Proof_Dyadic
import Definitions.Def_QMAPerfectCompleteness_Proof_DynamicBlockCompiler
import Definitions.Def_QMAPerfectCompleteness_Proof_DynamicRangeLayout
import Definitions.Def_QMAPerfectCompleteness_Proof_EqualityCircuits
import Definitions.Def_QMAPerfectCompleteness_Proof_EuclideanStates
import Definitions.Def_QMAPerfectCompleteness_Proof_IndexHadamards
import Definitions.Def_QMAPerfectCompleteness_Proof_PointwiseSetup
import Definitions.Def_QMAPerfectCompleteness_Proof_PolyTimeComposition
import Definitions.Def_QMAPerfectCompleteness_Proof_RawArithmeticGadgets
import Definitions.Def_QMAPerfectCompleteness_Proof_RawCertificateGadgets
import Definitions.Def_QMAPerfectCompleteness_Proof_RawCircuitEncoding
import Definitions.Def_QMAPerfectCompleteness_Proof_RawControlGadgets
import Definitions.Def_QMAPerfectCompleteness_Proof_RawG2Gadgets
import Definitions.Def_QMAPerfectCompleteness_Proof_RawThresholdGadgets
import Definitions.Def_QMAPerfectCompleteness_Proof_RegisterCopies
import Definitions.Def_QMAPerfectCompleteness_Proof_ReversibleGadgets
import Definitions.Def_QMAPerfectCompleteness_Proof_ThresholdLayout
import Definitions.Def_QMAPerfectCompleteness_Proof_ThresholdPreparation
import Definitions.Def_QMAPerfectCompleteness_Proof_VariableAddition
import Definitions.Def_QMAPerfectCompleteness_Proof_VariableComparison
import Definitions.Def_QMAPerfectCompleteness_Proof_VariableEquality
import Definitions.Def_QMAPerfectCompleteness_Proof_VariableHistoryEquality
import Definitions.Def_QMAPerfectCompleteness_Proof_VerifierAnalysis
import Definitions.Def_QMAPerfectCompleteness_Proof_VerifierEncoding

/- Namespace registrations retained from original proof-only imports. -/
namespace QMAPerfectCompleteness.Main.Certificate
end QMAPerfectCompleteness.Main.Certificate
namespace QMAPerfectCompleteness.Main.DiagonalProof
end QMAPerfectCompleteness.Main.DiagonalProof
namespace QMAPerfectCompleteness.Main.BlockComposition
end QMAPerfectCompleteness.Main.BlockComposition
namespace QMAPerfectCompleteness.Main.BlockTransport
end QMAPerfectCompleteness.Main.BlockTransport
namespace QMAPerfectCompleteness.Main.BlockHistoryCoordinates
end QMAPerfectCompleteness.Main.BlockHistoryCoordinates
namespace QMAPerfectCompleteness.Main.BlockHadamardCoordinates
end QMAPerfectCompleteness.Main.BlockHadamardCoordinates
namespace QMAPerfectCompleteness.Main.CoordinateFibers
end QMAPerfectCompleteness.Main.CoordinateFibers
namespace QMAPerfectCompleteness.Main.CertificateClaimBits
end QMAPerfectCompleteness.Main.CertificateClaimBits
namespace QMAPerfectCompleteness.Main.CertificateReadoutEffect
end QMAPerfectCompleteness.Main.CertificateReadoutEffect
namespace QMAPerfectCompleteness.Main.CertificateVerifierEffect
end QMAPerfectCompleteness.Main.CertificateVerifierEffect



/-! Executable literal circuit specification for the coherent-certificate construction.
The finite recipe realization will avoid materializing the powers in validity constants. -/
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
namespace QMAPerfectCompleteness.Main.CyclicRaw
open RawEncoding RawG2

namespace Meta

def thresholds (P : Meta) : RawG2.ThresholdLayout P.k :=
  ⟨fun d j=>P.certificate d.val j.val,fun d j=>P.word d.val j.val,fun j=>P.carry j.val,P.temp⟩

def arithmeticBorrow (P : Meta) (a b : ℕ → ℕ) : BorrowLayout P.r :=
  ⟨fun j=>a j.val,fun j=>b j.val,fun j=>P.carry j.val,P.temp⟩

def ranges (P : Meta) : RawG2.RangeLayout P.r where
  comparisons d := P.arithmeticBorrow P.paddedIndex (P.word (![0,4,5] d))
  tags j := P.tag j.val

def validityLayout (P : Meta) : RawG2.ValidityLayout P.k where
  a := ⟨fun j=>P.word 0 j.val,fun j=>P.carry j.val⟩
  b := ⟨fun j=>P.word 2 j.val,fun j=>P.carry j.val⟩
  comparison := P.arithmeticBorrow (P.word 0) (P.word 3)
  tags j := P.validity j.val

def clockAnd (P : Meta) : RawG2.AndLayout P.c :=
  ⟨fun j=>P.clock j.val,fun j=>P.scratch j.val⟩

def historyLayout (P : Meta) : RawG2.HistoryLayout P.m P.c where
  equality := ⟨fun j=>P.verifier j.val,fun j=>P.certificateZ j.val,
    fun j=>P.scratch j.val,P.tag 10⟩
  clock := P.clockAnd
  tags j := P.tag (![8,6,7] j)

def incrementLayout (P : Meta) : RawG2.AndLayout (P.c+1) :=
  ⟨fun j=>if j.val=0 then P.tag 5 else P.clock (j.val-1),fun j=>P.scratch j.val⟩

def readoutLayout (P : Meta) : RawG2.ReadoutLayout (P.k+(P.a+1)) where
  zeros := ⟨fun j=>P.zeroControl j.val,fun j=>P.readoutFlag j.val⟩
  tags j := ![P.validity 5,P.readoutZero,P.readoutOutput] j

def indexH (P : Meta) := RawG2.pairedHadamards (k:=P.k) (fun j=>j.val)
def prepGates (P : Meta) := RawG2.threshold P.thresholds
def validGates (P : Meta) := RawG2.validity P.validityLayout (P.validity 5)
def prefixGates (P : Meta) := P.prepGates ++ P.validGates

def rangeGates (P : Meta) := RawG2.range P.ranges

def mid (P : Meta) :=
  let C := RawG2.compareNatGates P.clockAnd P.ell (P.tag 6)
  C ++ RawG2.tripleControlledX ![P.tag 3,P.tag 6,P.verifier P.out,P.flag,P.tag 10] ++ C.reverse

def post (P : Meta) :=
  [RawG2.cn (P.tag 0) P.flag] ++ RawG2.closing P.historyLayout (P.tag 4) P.flag ++
  RawG2.increment P.incrementLayout ++ RawG2.phase (P.tag 5) (P.tag 9)

def block (P : Meta) (src : List Instruction) :=
  P.indexH ++ (P.rangeGates ++ RawG2.place (fun j=>P.verifier j) src ++ P.mid ++
    RawG2.place (fun j=>P.verifier j) src.reverse ++ P.post ++ P.rangeGates.reverse) ++ P.indexH

def gates (P : Meta) (src : List Instruction) :=
  [RawG2.x P.flag] ++ P.prefixGates ++ P.block src ++ RawG2.readout P.readoutLayout

def compile (P : Meta) (src : List Instruction) : RawEncoding.Circuit :=
  ⟨P.proof,P.ancilla,P.permute P.readoutOutput,RawG2.place P.permute (P.gates src)⟩

end Meta

/-- Fully executable on the raw unary circuit data; no gate matrices or proof terms occur. -/
def compileRaw (V : RawEncoding.Circuit) := (ofRaw V).compile V.gates

end QMAPerfectCompleteness.Main.CyclicRaw


