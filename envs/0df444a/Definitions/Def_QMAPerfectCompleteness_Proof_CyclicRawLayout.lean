-- Prove2me | Definitions.Def_QMAPerfectCompleteness_Proof_CyclicRawLayout
-- name    : QMAPerfectCompleteness_Proof_CyclicRawLayout
-- status  : Definition
-- author  : @Dorian Rudolph
-- created : 2026-11-14T15:28:07.1882+00:00
-- url     : https://prove2.me/theorems/8a749e93-9f78-4a4c-9c62-6951bf4bda63
-- title:
--   Physical addresses of cyclic verifier registers
-- statement:
--   Defines the scalar metadata and physical wire addresses for index, clock, verifier, certificate, predicate, arithmetic and readout registers. The raw and typed layout interfaces use the same register ordering and affine offsets.
-- source:
--   Formalization auxiliary for ~/research/qma1z/main.tex, the uniform circuit implementation supporting Section 3.3 and the proof of Theorem 1.1. Original Lean source: commit bbe19efbde567e5c8f7fe21655fd0c4da3573e4d, Solutions/CyclicRawLayout.lean, retained declaration span lines 12–78.

/- Generated from Solutions.CyclicRawLayout by authoritative Stage-2 skeleton subtraction.
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
import Definitions.Def_QMAPerfectCompleteness_Proof_CyclicVerifier
import Definitions.Def_QMAPerfectCompleteness_Proof_Dyadic
import Definitions.Def_QMAPerfectCompleteness_Proof_DynamicBlockCompiler
import Definitions.Def_QMAPerfectCompleteness_Proof_DynamicRangeLayout
import Definitions.Def_QMAPerfectCompleteness_Proof_EqualityCircuits
import Definitions.Def_QMAPerfectCompleteness_Proof_EuclideanStates
import Definitions.Def_QMAPerfectCompleteness_Proof_IndexHadamards
import Definitions.Def_QMAPerfectCompleteness_Proof_PointwiseSetup
import Definitions.Def_QMAPerfectCompleteness_Proof_PolyTimeComposition
import Definitions.Def_QMAPerfectCompleteness_Proof_RawCircuitEncoding
import Definitions.Def_QMAPerfectCompleteness_Proof_RawG2Gadgets
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



/-! Executable scalar metadata and affine physical addresses for the actual cyclic compiler. -/
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
namespace QMAPerfectCompleteness.Main.CyclicRaw
open RawEncoding CertificateMasterLayout

structure Meta where
  m : ℕ
  a : ℕ
  out : ℕ
  hh : ℕ
  c : ℕ
  ell : ℕ
  k : ℕ
  deriving DecidableEq, Repr

def ofRaw (V : RawEncoding.Circuit) : Meta :=
  let hh := V.gates.countP (fun i=>i.gate==3)
  let c := Nat.clog 2 (4*(V.proofQubits+1)+1)
  let ell := 2^c-1
  let q := (2*hh+1)*ell+4
  ⟨V.proofQubits,V.ancillaQubits,V.output,hh,c,ell,q+q%2⟩

namespace Meta

def env (P : Meta) : CircuitRecipe.Environment
  | .proof => P.m | .ancilla => P.a | .output => P.out | .hadamards => P.hh
  | .clock => P.c | .ell => P.ell | .index => P.k

def r (P : Meta) := P.k+2
def oldWork (P : Meta) := P.k+P.c+P.m+15
def prepWork (P : Meta) := 6*P.r+(P.k+3)+1
def readoutWork (P : Meta) := P.k+P.a+2
def work (P : Meta) := P.oldWork+P.prepWork+2+6+P.readoutWork+2
def body (P : Meta) := P.k+P.c+(P.m+P.a)+1
def claim (P : Meta) := P.m+(P.k+P.k)
def proof (P : Meta) := (P.c+P.m)+P.claim
def ancilla (P : Meta) := P.k+(P.a+1+P.work)



def clock (P : Meta) (j : ℕ) := P.k+j
def verifier (P : Meta) (j : ℕ) := P.k+P.c+j
def flag (P : Meta) := P.k+P.c+(P.m+P.a)
def tag (P : Meta) (j : ℕ) := P.body+j
def scratch (P : Meta) (j : ℕ) := P.body+(11+j)
def word (P : Meta) (d j : ℕ) := P.body+P.oldWork+(d*P.r+j)
def carry (P : Meta) (j : ℕ) := P.body+(P.oldWork+6*P.r)+j
def temp (P : Meta) := P.body+(P.oldWork+6*P.r+(P.k+3))
def pad (P : Meta) (j : ℕ) := P.body+(P.oldWork+P.prepWork)+j
def validity (P : Meta) (j : ℕ) := P.body+(P.oldWork+P.prepWork+2)+j
def readoutFlag (P : Meta) (j : ℕ) := P.body+(P.oldWork+P.prepWork+2+6)+j
def readoutZero (P : Meta) := P.body+(P.oldWork+P.prepWork+8+P.readoutWork)
def readoutOutput (P : Meta) := P.body+(P.oldWork+P.prepWork+9+P.readoutWork)
def certificateZ (P : Meta) (j : ℕ) := P.body+P.work+j
def certificate (P : Meta) (s j : ℕ) := P.body+P.work+P.m+(s*P.k+j)
def paddedIndex (P : Meta) (j : ℕ) := if j<P.k then j else P.pad (j-P.k)
def zeroControl (P : Meta) (j : ℕ) := if j<P.k then j else P.k+P.c+P.m+(j-P.k)

/-- Index/history/ancilla/certificate is reordered to the contiguous-proof verifier convention. -/
def permute (P : Meta) (j : ℕ) :=
  if j<P.k then P.proof+j else if j<P.k+(P.c+P.m) then j-P.k else
  if j<P.k+(P.c+P.m)+(P.a+1+P.work) then P.proof+P.k+(j-(P.k+(P.c+P.m))) else
    (P.c+P.m)+(j-(P.k+(P.c+P.m)+(P.a+1+P.work)))

end Meta

@[simp] theorem ofRaw_erase (V : Verifier gatesG2) :
    ofRaw (eraseVerifier V)=⟨V.proofQubits,V.ancillaQubits,V.output.val,hhCount V,
      clockQubits V.proofQubits,ell V.proofQubits,indexQubits V⟩ := by
  simp [ofRaw,eraseVerifier,eraseInstr,hhCount,clockQubits,ell,indexQubits,List.countP_map,Function.comp_def]

noncomputable abbrev params (V : Verifier gatesG2) := ofRaw (eraseVerifier V)




























end QMAPerfectCompleteness.Main.CyclicRaw


