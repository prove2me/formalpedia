-- Prove2me | Definitions.Def_QMAPerfectCompleteness_Proof_RawCertificateGadgets
-- name    : QMAPerfectCompleteness_Proof_RawCertificateGadgets
-- status  : Definition
-- author  : @Dorian Rudolph
-- created : 2026-11-14T15:11:24.157272+00:00
-- url     : https://prove2.me/theorems/cc1bc02d-1ad1-4226-a315-f428774d5880
-- title:
--   Raw certificate-control circuit templates
-- statement:
--   Defines raw layouts and gate lists for certificate validity, dynamic ranges, history equality, closing operations and readout. These templates give the literal executable instruction representation of the typed coherent-certificate gadgets.
-- source:
--   Formalization auxiliary for ~/research/qma1z/main.tex, Section 3.3, the coherent-certificate verifier and controlled block construction. Original Lean source: commit bbe19efbde567e5c8f7fe21655fd0c4da3573e4d, Solutions/RawCertificateGadgets.lean, retained declaration span lines 15–121.

/- Generated from Solutions.RawCertificateGadgets by authoritative Stage-2 skeleton subtraction.
Original explanatory text, declaration names and scoped commands are retained.
Only selected proof cuts, import rewrites and fact-indexed platform edits are applied. -/
import Definitions.Def_QMAPerfectCompleteness_Main_Classes
import Definitions.Def_QMAPerfectCompleteness_Main_Compiler
import Definitions.Def_QMAPerfectCompleteness_Main_Cyclic
import Init.Data.BitVec.Bitblast
import Definitions.Def_QMAPerfectCompleteness_Main_BlockEncoding
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
import Definitions.Def_QMAPerfectCompleteness_Proof_CertificateHistoryPrograms
import Definitions.Def_QMAPerfectCompleteness_Proof_CertificateReadout
import Definitions.Def_QMAPerfectCompleteness_Proof_CertificateValidity
import Definitions.Def_QMAPerfectCompleteness_Proof_CircuitUnitary
import Definitions.Def_QMAPerfectCompleteness_Proof_ClockCircuits
import Definitions.Def_QMAPerfectCompleteness_Proof_ComparisonCircuits
import Definitions.Def_QMAPerfectCompleteness_Proof_ControlCircuits
import Definitions.Def_QMAPerfectCompleteness_Proof_Cyclic
import Definitions.Def_QMAPerfectCompleteness_Proof_DynamicBlockCompiler
import Definitions.Def_QMAPerfectCompleteness_Proof_DynamicRangeLayout
import Definitions.Def_QMAPerfectCompleteness_Proof_EqualityCircuits
import Definitions.Def_QMAPerfectCompleteness_Proof_EuclideanStates
import Definitions.Def_QMAPerfectCompleteness_Proof_IndexHadamards
import Definitions.Def_QMAPerfectCompleteness_Proof_RawArithmeticGadgets
import Definitions.Def_QMAPerfectCompleteness_Proof_RawCircuitEncoding
import Definitions.Def_QMAPerfectCompleteness_Proof_RawControlGadgets
import Definitions.Def_QMAPerfectCompleteness_Proof_RawG2Gadgets
import Definitions.Def_QMAPerfectCompleteness_Proof_ReversibleGadgets
import Definitions.Def_QMAPerfectCompleteness_Proof_VariableAddition
import Definitions.Def_QMAPerfectCompleteness_Proof_VariableComparison
import Definitions.Def_QMAPerfectCompleteness_Proof_VariableEquality
import Definitions.Def_QMAPerfectCompleteness_Proof_VariableHistoryEquality
import Definitions.Def_QMAPerfectCompleteness_Proof_VerifierEncoding

/- Namespace registrations retained from original proof-only imports. -/
namespace QMAPerfectCompleteness.Main.BlockComposition
end QMAPerfectCompleteness.Main.BlockComposition
namespace QMAPerfectCompleteness.Main.BlockTransport
end QMAPerfectCompleteness.Main.BlockTransport
namespace QMAPerfectCompleteness.Main.BlockHistoryCoordinates
end QMAPerfectCompleteness.Main.BlockHistoryCoordinates
namespace QMAPerfectCompleteness.Main.BlockHadamardCoordinates
end QMAPerfectCompleteness.Main.BlockHadamardCoordinates



/-! Executable certificate-control templates and literal typed-erasure proofs. -/
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
namespace QMAPerfectCompleteness.Main.RawG2
open RawEncoding

structure HistoryLayout (m c : ℕ) where
  equality : BorrowLayout m
  clock : AndLayout c
  tags : Fin 3 → ℕ

def eraseHistory {m c n : ℕ} (L : VariableHistoryEquality.Layout m c n) : HistoryLayout m c :=
  ⟨eraseBorrow L.equality,eraseAnd L.clock,fun j=>(L.tags j).val⟩

def history {m c : ℕ} (L : HistoryLayout m c) :=
  let E := equality L.equality (L.tags 0)
  let C := patternControlledX L.clock (fun _=>true) (L.tags 1)
  E ++ C ++ [tof (L.tags 0) (L.tags 1) (L.tags 2)] ++ C.reverse ++ E.reverse



def closing {m c : ℕ} (L : HistoryLayout m c) (range flag : ℕ) :=
  history L ++ [tof range (L.tags 2) flag] ++ (history L).reverse



structure ReadoutLayout (r : ℕ) where
  zeros : AndLayout r
  tags : Fin 3 → ℕ

def eraseReadout {r n : ℕ} (L : CertificateReadout.Layout r n) : ReadoutLayout r :=
  ⟨eraseAnd L.zeros,fun j=>(L.tags j).val⟩

def readout {r : ℕ} (L : ReadoutLayout r) :=
  let Z := patternControlledX L.zeros (fun _=>false) (L.tags 1)
  Z ++ compile [.flip (L.tags 1),.conj (L.tags 0) (L.tags 1) (L.tags 2),.flip (L.tags 1)] ++ Z.reverse



structure RangeLayout (r : ℕ) where
  comparisons : Fin 3 → BorrowLayout r
  tags : Fin 6 → ℕ

def eraseRange {r n : ℕ} (L : DynamicBlockCompiler.RangeLayout n r) : RangeLayout r :=
  ⟨fun j=>eraseBorrow (L.comparators j),fun j=>(L.tags j).val⟩

def andNot (a b c : ℕ) := compile [.flip a,.conj a b c,.flip a]

def range {r : ℕ} (L : RangeLayout r) :=
  comparator (L.comparisons 0) (L.tags 0) ++ comparator (L.comparisons 1) (L.tags 1) ++
  comparator (L.comparisons 2) (L.tags 2) ++ andNot (L.tags 0) (L.tags 1) (L.tags 3) ++
  andNot (L.tags 1) (L.tags 2) (L.tags 4) ++ andNot (L.tags 0) (L.tags 2) (L.tags 5)





structure ValidityLayout (k : ℕ) where
  a : AndLayout (k+2)
  b : AndLayout (k+2)
  comparison : BorrowLayout (k+2)
  tags : Fin 5 → ℕ

def eraseValidity {k n : ℕ} (L : CertificateValidity.Layout k n) : ValidityLayout k :=
  ⟨eraseAnd L.a,eraseAnd L.b,eraseBorrow L.cmp,fun j=>(L.tags j).val⟩

def criteria {k : ℕ} (L : ValidityLayout k) :=
  compareNatGates L.a 1 (L.tags 0) ++ [x (L.tags 0)] ++
  compareNatGates L.b 1 (L.tags 1) ++ [x (L.tags 1)] ++
  compareNatGates L.a (2^(k-3)) (L.tags 2) ++ [x (L.tags 2)] ++
  compareNatGates L.a (2^(k-2)+1) (L.tags 3) ++
  comparator L.comparison (L.tags 4) ++ [x (L.tags 4)]



def conjunction {k : ℕ} (L : ValidityLayout k) : AndLayout 5 :=
  ⟨L.tags,fun j=>L.a.flags ⟨min j.val (k+2),by omega⟩⟩

def validity {k : ℕ} (L : ValidityLayout k) (out : ℕ) :=
  criteria L ++ multiControlledX (conjunction L) out



end QMAPerfectCompleteness.Main.RawG2


