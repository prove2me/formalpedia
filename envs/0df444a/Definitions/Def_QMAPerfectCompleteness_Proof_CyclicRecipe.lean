-- Prove2me | Definitions.Def_QMAPerfectCompleteness_Proof_CyclicRecipe
-- name    : QMAPerfectCompleteness_Proof_CyclicRecipe
-- status  : Definition
-- author  : @Dorian Rudolph
-- created : 2026-11-14T15:30:46.265551+00:00
-- url     : https://prove2.me/theorems/023b54c9-eeac-4ba3-8e07-83c29e0802dc
-- title:
--   Finite recipe for the coherent verifier
-- statement:
--   Defines one finite, width-parameterized recipe for the complete coherent-certificate circuit. Its bounded loops assemble preparation, validity tests, index selection, history and closing operations, the block circuit and the accepting-output test.
-- source:
--   Formalization auxiliary for ~/research/qma1z/main.tex, Section 3.3, the coherent-certificate verifier and controlled block construction. Original Lean source: commit bbe19efbde567e5c8f7fe21655fd0c4da3573e4d, Solutions/CyclicRecipe.lean, retained declaration span lines 10–122.

/- Generated from Solutions.CyclicRecipe by authoritative Stage-2 skeleton subtraction.
Original explanatory text, declaration names and scoped commands are retained.
Only selected proof cuts, import rewrites and fact-indexed platform edits are applied. -/
import Mathlib.Tactic.DeriveFintype
import Definitions.Def_QMAPerfectCompleteness_Main_Classes
import Definitions.Def_QAlgorithms_ClassicalStringComputability
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
import Definitions.Def_QMAPerfectCompleteness_Proof_CyclicRawCompiler
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
import Definitions.Def_QMAPerfectCompleteness_Proof_RecipeGadgets
import Definitions.Def_QMAPerfectCompleteness_Proof_RecipeNormalization
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



/-! A single finite circuit-generator program for the literal coherent-certificate verifier.
Every loop is bounded by a register width; validity thresholds are produced as bit patterns. -/
namespace QMAPerfectCompleteness.Main.CyclicRecipe
open CircuitRecipe
open CircuitRecipe.Gadgets

abbrev m : Expr := .param .proof
abbrev a : Expr := .param .ancilla
abbrev out : Expr := .param .output
abbrev c : Expr := .param .clock
abbrev k : Expr := .param .index
abbrev r : Expr := k+2
abbrev oldWork : Expr := k+c+m+15
abbrev prepWork : Expr := .scale 6 r+(k+3)+1
abbrev readoutWork : Expr := k+a+2
abbrev work : Expr := oldWork+prepWork+2+6+readoutWork+2
abbrev body : Expr := k+c+(m+a)+1
abbrev claim : Expr := m+(k+k)
abbrev proof : Expr := (c+m)+claim
abbrev ancilla : Expr := k+(a+1+work)

def clock : Expr := k+.addr
def verifier : Expr := k+c+.addr
def flag : Expr := k+c+(m+a)
def tag (j : ℕ) : Expr := body+.lit j
def scratch : Expr := body+(11+.addr)
def word (d : ℕ) : Expr := body+oldWork+(.scale d r+.addr)
def carry : Expr := body+(oldWork+.scale 6 r)+.addr
def temp : Expr := body+(oldWork+.scale 6 r+(k+3))
def pad : Expr := body+(oldWork+prepWork)+.addr
def validTag (j : ℕ) : Expr := body+(oldWork+prepWork+2)+.lit j
def readoutFlag : Expr := body+(oldWork+prepWork+2+6)+.addr
def readoutZero : Expr := body+(oldWork+prepWork+8+readoutWork)
def readoutOutput : Expr := body+(oldWork+prepWork+9+readoutWork)
def certZ : Expr := body+work+.addr
def cert (s : ℕ) : Expr := body+work+m+(.scale s k+.addr)
def paddedIndex : Expr := .ifLt .addr k .addr (pad.plug (.addr-k))
def zeroControl : Expr := .ifLt .addr k .addr (k+c+m+(.addr-k))
def incControl : Expr := .ifLt .addr 1 (tag 5) (clock.plug (.addr-1))

def permute : Expr :=
  .ifLt .addr k (proof+.addr)
    (.ifLt .addr (k+(c+m)) (.addr-k)
      (.ifLt .addr (k+(c+m)+(a+1+work)) (proof+k+(.addr-(k+(c+m))))
        ((c+m)+(.addr-(k+(c+m)+(a+1+work))))))



def copies : Recipe := .forUp (.scale 4 k)
  (.ifLt (.bound 0) k.lift
    (cn ((cert 0).lift.plug (.bound 0)) ((word 0).lift.plug (.bound 0)))
    (.ifLt (.bound 0) (.scale 2 k.lift)
      (cn ((cert 0).lift.plug (.bound 0-k.lift)) ((word 1).lift.plug (.bound 0-k.lift+1)))
      (.ifLt (.bound 0) (.scale 3 k.lift)
        (cn ((cert 1).lift.plug (.bound 0-.scale 2 k.lift))
          ((word 2).lift.plug (.bound 0-.scale 2 k.lift)))
        (cn ((cert 1).lift.plug (.bound 0-.scale 3 k.lift))
          ((word 3).lift.plug (.bound 0-.scale 3 k.lift+1))))))

def threshold : Recipe := copies ++
  addition r (word 0) (word 1) carry (word 4) temp ++
  addition r (word 4) (word 2) carry (word 5) temp

def bitAt (p : Expr) : Expr := .ifLt .addr p 0 (.ifLt p .addr 0 1)
def upperBits : Expr := .ifLt .addr 1 1 (bitAt (k-2))

def criteria : Recipe :=
  compareBits r (word 0) carry (bitAt 0) (validTag 0) ++ x (validTag 0) ++
  compareBits r (word 2) carry (bitAt 0) (validTag 1) ++ x (validTag 1) ++
  compareBits r (word 0) carry (bitAt (k-3)) (validTag 2) ++ x (validTag 2) ++
  compareBits r (word 0) carry upperBits (validTag 3) ++
  comparator r (word 0) (word 3) carry temp (validTag 4) ++ x (validTag 4)

def validity : Recipe := criteria ++
  multiX 5 (body+(oldWork+prepWork+2)+.addr) carry (validTag 5)

def preparation : Recipe := threshold ++ validity

def andNot (a b c : Expr) : Recipe := x a ++ conj a b c ++ x a

def range : Recipe :=
  comparator r paddedIndex (word 0) carry temp (tag 0) ++
  comparator r paddedIndex (word 4) carry temp (tag 1) ++
  comparator r paddedIndex (word 5) carry temp (tag 2) ++
  andNot (tag 0) (tag 1) (tag 3) ++ andNot (tag 1) (tag 2) (tag 4) ++
  andNot (tag 0) (tag 2) (tag 5)

def indexH : Recipe := pairedH k .addr

def clockBelow : Recipe := compareBits c clock scratch 1 (tag 6)
def tripleFlag : Recipe :=
  tof (tag 3) (tag 6) (tag 10) ++ tof (tag 10) (verifier.plug out) flag ++
  tof (tag 3) (tag 6) (tag 10)
def mid : Recipe := useUncompute clockBelow tripleFlag

def proofEquality : Recipe := equality m verifier certZ scratch (tag 10) (tag 8)
def lastClock : Recipe := patternX c clock scratch 1 (tag 6)
def history : Recipe := proofEquality ++ lastClock ++ tof (tag 8) (tag 6) (tag 7) ++
  lastClock.reverse ++ proofEquality.reverse

def closing : Recipe := useUncompute history (tof (tag 4) (tag 7) flag)
def post : Recipe := cn (tag 0) flag ++ closing ++ increment c incControl scratch ++
  hh (tag 5) (tag 9) ++ x (tag 5) ++ hh (tag 5) (tag 9)

def block : Recipe := indexH ++
  (range ++ .source false verifier ++ mid ++ .source true verifier ++ post ++ range.reverse) ++ indexH

def zeroTest : Recipe := patternX (k+(a+1)) zeroControl readoutFlag 0 readoutZero
def readout : Recipe := useUncompute zeroTest
  (x readoutZero ++ conj (validTag 5) readoutZero readoutOutput ++ x readoutZero)

def physical : Recipe := x flag ++ preparation ++ block ++ readout

def program : CircuitRecipe.Circuit :=
  ⟨proof,ancilla,permute.plug readoutOutput,.mapWires permute physical⟩

def compileRaw (V : RawEncoding.Circuit) : RawEncoding.Circuit :=
  program.eval (CyclicRaw.ofRaw V).env V.gates

end QMAPerfectCompleteness.Main.CyclicRecipe


