-- Prove2me | Definitions.Def_OAIQ081S058
-- name    : OAIQ081S058
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-29T21:47:45.646978+00:00
-- url     : https://prove2.me/theorems/9b9ece02-3799-4a9c-8937-a788fb8199ed
-- title:
--   Definitions bundle OAIQ081S058 of the split of OpenAI, The Exponential Time Hypothesis is False
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.exact_count_and_sat`, carved from OpenAI's openai/math development (OpenAI, *The Exponential Time Hypothesis is False*, OpenAI Math Release, October 25, 2026, result family 378, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 113 declarations of OpenAI's Lean: 72 definitions, 3 inductive types or structures and 38 theorems. The definitions and types are `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgram.sourceCode`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgram.sourceValue`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgramScalar.cacheRecords`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutScalarEmitter.record`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutSourcePlanLookup.Local.budget`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutSourcePlanLookup.clear`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutSourcePlanLookup.pairKey`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutSourcePlanLookup.payload`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutSourcePlanLookup.records`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutSourceRowsProgram.Data`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutSourceRowsProgramInitialize.Ready`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutSourceRowsProgramInitialize.finish`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutSourceRowsProgramReadiness.Empty`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutSourceValuesProgram.loopState`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutTriplePreparationProgram.Cache`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutTriplePreparationProgram.Cache.Bword`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutTriplePreparationProgram.Cache.Fits`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutTriplePreparationProgram.Cache.Hword`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutTriplePreparationProgram.Cache.Uniform`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutTriplePreparationProgram.selectedWord`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutTriplePreparationProgram.signedPair`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutTriplePreparationProgram.wordRecord`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafAssignmentSetupProgram.clear`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafFactorDispatchProgram.clear`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafFactorDispatchProgram.compare`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafFactorDispatchProgram.lessClean`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafFactorDispatchProgram.neutralBranch`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafFactorDispatchProgram.outputStacks`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafHighContextProgram.Local.cost`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafNodeSamplesProgram.clear`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafNodeSamplesProgram.copy`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafNodeSamplesProgram.pop`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafNodeSamplesProgram.ports`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafNodeSamplesProgram.reader`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafNodeSamplesProgram.transfer`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafOuterProgram.clearWorker`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafOuterProgram.route`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafOuterProgram.routes`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafOuterProgram.stage`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafOuterProgram.startBudget` and 35 more.
--
--   **Sources.** They come from these modules of lean/OAI/Algorithms, in whole or in part: `SubexponentialSAT_SqrtLog_LayoutProgramRowCode`, `SubexponentialSAT_SqrtLog_LayoutProgramScalarCacheCell`, `SubexponentialSAT_SqrtLog_LayoutPullback`, `SubexponentialSAT_SqrtLog_LayoutScalarEmitter`, `SubexponentialSAT_SqrtLog_LayoutSourcePlanLookupBasic`, `SubexponentialSAT_SqrtLog_LayoutSourcePlanLookupLocal`, `SubexponentialSAT_SqrtLog_LayoutSourcePlanLookupSemantics`, `SubexponentialSAT_SqrtLog_LayoutSourceRowsProgramCore`, `SubexponentialSAT_SqrtLog_LayoutSourceRowsProgramInitialize`, `SubexponentialSAT_SqrtLog_LayoutSourceRowsProgramReadiness`, `SubexponentialSAT_SqrtLog_LayoutSourceValuesProgramLoop`, `SubexponentialSAT_SqrtLog_LayoutTriplePreparationProgram`, `SubexponentialSAT_SqrtLog_LayoutTriplePreparationProgramBasic`, `SubexponentialSAT_SqrtLog_LeafAssignmentSetupProgramBase`, `SubexponentialSAT_SqrtLog_LeafFactorDispatchProgram`, `SubexponentialSAT_SqrtLog_LeafFactorDispatchProgramBranches`, `SubexponentialSAT_SqrtLog_LeafFactorDispatchProgramRun`, `SubexponentialSAT_SqrtLog_LeafHeadFactorsProgramSemantics`, `SubexponentialSAT_SqrtLog_LeafHighContextProgram`, `SubexponentialSAT_SqrtLog_LeafNodeSamplesProgram`, `SubexponentialSAT_SqrtLog_LeafOuterProgramStart`, `SubexponentialSAT_SqrtLog_LeafOuterProgramStorage`, `SubexponentialSAT_SqrtLog_LeafPackingFiberBounds`, `SubexponentialSAT_SqrtLog_LeafProgramClauseCount`, `SubexponentialSAT_SqrtLog_LeafProgramCleanupWide`, `SubexponentialSAT_SqrtLog_LeafProgramHash`, `SubexponentialSAT_SqrtLog_LeafProgramHashParameters`, `SubexponentialSAT_SqrtLog_LeafProgramSourceControls`, `SubexponentialSAT_SqrtLog_LeafProgramTrivial`, `SubexponentialSAT_SqrtLog_LeafQueryFrontendHighRun`, `SubexponentialSAT_SqrtLog_LeafQueryFrontendMeasure`, `SubexponentialSAT_SqrtLog_LeafRingSetupProgramNative`, `SubexponentialSAT_SqrtLog_LeafStatisticsSemanticsEnumeration`, `SubexponentialSAT_SqrtLog_MomentsPerturbation`, `SubexponentialSAT_SqrtLog_MomentsSparse`, `SubexponentialSAT_SqrtLog_MomentsSquarefree`, `SubexponentialSAT_SqrtLog_ResidualEmbeddingStored`, `SubexponentialSAT_SqrtLog_RingProgramTableBasic`, `SubexponentialSAT_SqrtLog_SquarefreeBasic`, `SubexponentialSAT_SubexpDenseLiteralPadding`, `SubexponentialSAT_SubexpEmptyClauseProgram`, `SubexponentialSAT_SubexpGuardProgram`, `SubexponentialSAT_SubexpNodeIndexProgram`, `SubexponentialSAT_SubexpProjectedInterpreter`, `SubexponentialSAT_SubexpTaylorFrames`, `SubexponentialSAT_Subexp_AssignmentRecordViews`.
--
--   **Imports.** It imports the published bundle `Def_SubexponentialSAT`; the bundles `OAIQ081S016`, `OAIQ081S023`, `OAIQ081S024`, `OAIQ081S025`, `OAIQ081S026`, `OAIQ081S027`, `OAIQ081S028`, `OAIQ081S029`, `OAIQ081S030`, `OAIQ081S031`, `OAIQ081S032`, `OAIQ081S034`, `OAIQ081S035`, `OAIQ081S036` and `OAIQ081S037` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ081S075`, `OAIQ081S076`, `OAIQ081S077`, `OAIQ081S078`, `OAIQ081S080` and `OAIQ081S081`; the statements `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgram.SourceTyped.row_meaning` and `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgram.sourceCode_decode`; the proofs of `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighQueryCorrect.accepted`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighQueryCorrect.marked`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighQueryCount.run`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeHashQueries.accepted_replay` and `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeHashQueries.marked_replay`.
-- source:
--   OpenAI, The Exponential Time Hypothesis is False, OpenAI Math Release, October 25, 2026, https://github.com/openai/math (result family 378; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/The-Exponential-Time-Hypothesis-is-False-October-25-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Algorithms at commit 7ef5c0c

import Mathlib
import Definitions.Def_SubexponentialSAT
import Definitions.Def_OAIQ081S016
import Definitions.Def_OAIQ081S023
import Definitions.Def_OAIQ081S024
import Definitions.Def_OAIQ081S025
import Definitions.Def_OAIQ081S026
import Definitions.Def_OAIQ081S027
import Definitions.Def_OAIQ081S028
import Definitions.Def_OAIQ081S029
import Definitions.Def_OAIQ081S030
import Definitions.Def_OAIQ081S031
import Definitions.Def_OAIQ081S032
import Definitions.Def_OAIQ081S034
import Definitions.Def_OAIQ081S035
import Definitions.Def_OAIQ081S036
import Definitions.Def_OAIQ081S037

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LayoutPullback
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.labelFintype _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.variableFintype _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# Literal incidence pullback

An incidence is sent to its original variable by `owner`. The pullback
duplicates a variable value; the dual operation adds row coefficients on
each fiber. No inverse matrix or new basis is used in these definitions.
-/

namespace SubexponentialSAT.SqrtLog.LayoutPullback

open scoped BigOperators

variable {I V R : Type*} [Fintype I] [Fintype V] [DecidableEq V]

section Ring

variable [CommRing R]

theorem row_right_dot (owner : I → V) (a : V → R) (z : I → R) :
    (∑ v, a v * row owner z v) = ∑ i, a (owner i) * z i := by
  simpa only [duplicate, Function.comp_def, mul_comm] using row_dot owner z a

end Ring

end SubexponentialSAT.SqrtLog.LayoutPullback

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LayoutProgramRowCode
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree _root_.OAI.Algorithms.SubexponentialSAT.Subexp.MatrixExtendedEntryProgram.instDecidableAnchorValid
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! The literal represented source-row circuit over the target ring. Integer
numerators are lifted directly, then multiplied by the supplied inverse of the
power-of-two denominator. There is no field section or inverse in the target
ring. The bit-program realizations of these measured scalar operations and
of the cache construction are separate obligations. -/
namespace SubexponentialSAT.SqrtLog.LayoutProgram

open SubexponentialSAT.MulticolorTypes SubexponentialSAT.SubexpSymbolicCost SubexponentialSAT.SubexpRowInterpolation
open SubexponentialSAT.SubexpRepresentedRows
open LayoutScaledMatrices

variable {C O : Type*} {r Q Δ : ℕ}

def sourceValue (ops : RingProgram C) (integerWord : ℤ → C) (inverseDenominator : C)
    (A R : ℕ) (u : UniversalType r Q Δ) (i : Fin Δ)
    (y : UniversalType r Q Δ) (t : Fin Q) : C :=
  if u ∈ joint t (y.head t) i ∧ y ∈ joint t (y.head t) i then
    (ops.negRun (ops.mulRun inverseDenominator
      (integerWord (LayoutCoefficientAlgorithm.scalarEntry i t A R u y))).1).1
  else ops.zeroRun.1

def sourceCode (ops : RingProgram C) (cache : NodeCache C Q)
    (integerWord : ℤ → C) (inverseDenominator : C)
    (A R : ℕ) (u : UniversalType r Q Δ) (i : Fin Δ)
    (y : UniversalType r Q Δ) : PolynomialCode C :=
  row ops cache u (fun y => y.head) (u.slot i) R
    (sourceValue ops integerWord inverseDenominator A R u i) y

end SubexponentialSAT.SqrtLog.LayoutProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LayoutScalarEmitter
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Preserving signed-pair emission into a reverse buffer. The existing exact
pair serializer is called on paid copies, and its output is transferred once.
All source words survive; the four work stacks are restored to empty. -/
namespace SubexponentialSAT.SqrtLog.LayoutScalarEmitter
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls
open SubexponentialSAT.Subexp.MatrixProgramSupport

def record (positive negative : List Bool) : List Bool :=
  RowSelectionProgram.Entries.pairPrefix positive negative

@[simp] theorem record_length (positive negative : List Bool) :
    (record positive negative).length = 2*(positive.length+negative.length)+3 := by
  simp [record,RowSelectionProgram.Entries.pairPrefix]
  omega

end SubexponentialSAT.SqrtLog.LayoutScalarEmitter

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LayoutProgramScalarCacheCell
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! The unsigned cache recurrence is executed by a one-bit shift followed by
the original finite little-endian adder. Its representation growth is linear
in the number of cells; no canonical-word assumption is used. -/

/-! One complete cache-row transform, including record parsing and preserving
emission of every newly computed value. -/
namespace SubexponentialSAT.SqrtLog.LayoutProgramScalar

open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls
open SubexponentialSAT.SqrtLog.RowSelectionProgram

def cacheRecords (xs : List (List Bool)) : List Bool :=
  xs.flatMap fun x => LayoutScalarEmitter.record x []

@[simp] theorem cacheRecords_nil : cacheRecords [] = [] := rfl
@[simp] theorem cacheRecords_cons (x : List Bool) (xs : List (List Bool)) :
    cacheRecords (x::xs) = LayoutScalarEmitter.record x []++cacheRecords xs := rfl

end SubexponentialSAT.SqrtLog.LayoutProgramScalar

/-! Complete reusable cache pass: read one encoded row, compute and emit its
new row, append the end marker, reverse the output, and clear the carry. -/

/-! The number of coefficient-cache rows is runtime unary data. This fixed
loop invokes the complete paid row pass and preserves the current encoded row.
-/
namespace SubexponentialSAT.SqrtLog.LayoutProgramScalar

open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls
open SubexponentialSAT.SqrtLog.RowSelectionProgram

@[simp] theorem cacheIter_length (n : ℕ) (xs : List (List Bool)) :
    (cacheIter n xs).length = xs.length := by
  induction n generalizing xs with
  | zero => rfl
  | succ n ih => simp [cacheIter,ih]

end SubexponentialSAT.SqrtLog.LayoutProgramScalar

/-! The physical unsigned cache computes the original coefficient recurrence's
natural magnitudes, in ascending degree order. -/
namespace SubexponentialSAT.SqrtLog.LayoutProgramScalar

open SubexponentialSAT.BinaryArithmetic
open SubexponentialSAT.SqrtLog.LayoutCoefficientRecurrence

@[simp] theorem initialCache_length (R : ℕ) : (initialCache R).length = R := by
  simp [initialCache]

end SubexponentialSAT.SqrtLog.LayoutProgramScalar

/-! A fixed loop builds the initial all-one cache row from a runtime unary
length. The constant program contains one record, independent of that length. -/

/-! One fixed program builds the complete unsigned H cache from the unary
runtime parameters A and R. No coefficient or initial cache is free input. -/

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SubexpNodeIndexProgram
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# Physical lookup of the current field node

The fixed program copies the framed node table, parses its records in order,
compares their actual bits with the current node, and counts rejected records.
Its only visible stack change is the unary first matching index at port 116.
The source table at 125 and query at 78 are preserved.
-/

namespace SubexponentialSAT.SubexpNodeIndexProgram

open BitProgram StructuredCalls SubexpScanPrimitives

namespace Internal

def ports : RecordPrograms.Ports 5 7 where
  tag := 0
  present := 1
  found := 4
  source := 2
  payload := 3
  tag_ne_present := by decide
  found_ne_tag := by decide
  found_ne_present := by decide
  source_ne_payload := by decide

abbrev bump : Cmd 5 7 :=
  .seq (RecordPrograms.atom (.set 0 true)) (RecordPrograms.atom (.push 6 0))

abbrev normalize : Cmd 5 7 :=
  .seq (RecordPrograms.atom (.set 0 false)) (RecordPrograms.atom (.set 1 true))

abbrev finish : Cmd 5 7 := .seq (.ite 4 (.base .skip) bump) normalize

def budget (query : List Bool) (nodes : List (List Bool)) : ℕ :=
  (9 * query.length + 80) * ((ProgramEncoding.encodeRecords nodes).length + 1)

end Internal

end SubexponentialSAT.SubexpNodeIndexProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LayoutSourcePlanLookupBasic
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! A fixed twelve-stack workspace for a full pair-key lookup. -/
namespace SubexponentialSAT.SqrtLog.LayoutSourcePlanLookup
open SubexponentialSAT BitProgram StructuredCalls SubexpScanPrimitives

def clear (src : Fin 12) : Code :=
  .call (StackRoutines.clearProgram src (0 : Fin 16) 1)

/-- Exact nested record representation searched in the plan. -/
def pairKey (literal factor : List Bool) : List Bool :=
  Encoding.frame (ProgramEncoding.encodeRecords [literal,factor])

@[simp] theorem pairKey_length (literal factor : List Bool) :
    (pairKey literal factor).length=4*literal.length+4*factor.length+11 := by
  simp [pairKey,ProgramEncoding.encodeRecords,Encoding.encodeList,Encoding.length_frame]
  omega

end SubexponentialSAT.SqrtLog.LayoutSourcePlanLookup

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LayoutSourcePlanLookupLocal
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.LayoutSourcePlanLookup
open SubexponentialSAT BitProgram StructuredCalls SubexpScanPrimitives

namespace Local

def budget (literal ambient factor : List Bool) (nodes : List (List Bool)) : ℕ :=
  39*(literal.length+ambient.length+factor.length)+113+
    SubexpNodeIndexProgram.Internal.budget (pairKey literal (ambient++factor)) nodes

end Local
end SubexponentialSAT.SqrtLog.LayoutSourcePlanLookup

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LayoutSourcePlanLookupSemantics
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.LayoutSourcePlanLookup

def payload (p : ℕ × ℕ) : List Bool := pairKey (unary p.1) (unary p.2)
def records (ps : List (ℕ × ℕ)) : List (List Bool) := ps.map payload

end SubexponentialSAT.SqrtLog.LayoutSourcePlanLookup

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LayoutSourceRowsProgramCore
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Native framing and postfix accumulation for complete source rows. The
local bank is relocated as a whole by the leaf controller. No polynomial
value is an instruction or an input to these controllers. -/
namespace SubexponentialSAT.SqrtLog.LayoutSourceRowsProgram
open SubexponentialSAT BitProgram StructuredCalls

abbrev Data := State 16 340

end SubexponentialSAT.SqrtLog.LayoutSourceRowsProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LayoutSourceRowsProgramInitialize
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Fixed, width-generic initialization for the source-row executor. All
zero-array construction and copies are paid; only four output stacks change. -/
namespace SubexponentialSAT.SqrtLog.LayoutSourceRowsProgramInitialize
open SubexponentialSAT BitProgram StructuredCalls SubexpConvolutionControl
open DensePolynomialProgram

def finish (s : Store) (D W : ℕ) : Store :=
  Function.update
    (Function.update
      (Function.update (Function.update s 243 (List.replicate D true))
        242 (List.replicate (D*W) false))
      192 (List.replicate (D*W) false))
    193 (List.replicate D true)

structure Ready (s : Store) (D W : ℕ) : Prop where
  dimension : s 210 = List.replicate D true
  zeroCell : s 104 = List.replicate W false
  empty100 : s 100 = []
  empty101 : s 101 = []
  empty102 : s 102 = []
  empty107 : s 107 = []
  empty108 : s 108 = []
  empty120 : s 120 = []
  empty192 : s 192 = []
  empty193 : s 193 = []
  empty242 : s 242 = []
  empty243 : s 243 = []
  empty245 : s 245 = []

end SubexponentialSAT.SqrtLog.LayoutSourceRowsProgramInitialize

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SubexpDenseLiteralPadding
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# Padding arbitrary literal payloads for the dense interpreter

The existing five-label padding table already truncates long inputs. This
module proves that behavior without a length precondition, then connects the
table to the actual framed operand stack. The cached dense zero array supplies
the requested bit width; no dimension is baked into the program control.
-/

namespace SubexponentialSAT.SubexpDenseLiteralPadding

open BitProgram StructuredCalls ModularArithmetic ModularPrograms
open SubexpConvolutionControl (Store Code )

abbrev liftSmall (cmd : Cmd 16 128) : Code :=
  .call (ProgramLinking.liftProgram (compiled cmd 0 0) id smallPorts)

def pad : Code := .call (ProgramLinking.liftProgram paddingProgram padRegs padPorts)

end SubexponentialSAT.SubexpDenseLiteralPadding

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SubexpProjectedInterpreter
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# A finite postfix interpreter with a real literal-projection call

The literal bytes are parsed and pushed by the concrete loader, then passed to
an actual finite projection service before dispatch resumes. Arithmetic and
projection contracts refer to traces of supplied Boolean instruction tables.
-/

namespace SubexponentialSAT.SubexpProjectedInterpreter

open BitProgram
open SubexpPostfixControl (triple controlLabel literalLabel pushLoopProgram
  literalService serializeCode serializeInstr )
open SubexpPostfixInterpreter (register stack )

variable {r s a b c : ℕ}

/-- All three services are installed as finite instruction-table regions. -/
def program (add : Program (3 + r) (4 + s) a) (mul : Program (3 + r) (4 + s) b)
    (loader : Program (3 + r) (4 + s) c) :
    Program (3 + r) (4 + s) (37 + (2 + (a + (b + c)))) where
  inputStack := stack 0
  outputStack := stack 2
  entry := bootLabel 0
  code := Fin.addCases
    (fun pc : Fin 37 =>
      if pc = 16 then .goto (addLabel add.entry)
      else if pc = 17 then .goto (mulLabel mul.entry)
      else if pc = 36 then .goto (loadLabel loader.entry)
      else ProgramLinking.relocateInstr register stack baseLabel none (pushLoopProgram.code pc))
    (Fin.addCases
      (fun pc : Fin 2 => if pc = 0 then .set (register 0) false (bootLabel 1)
        else .push (stack 2) (register 0) (baseLabel 0))
      (Fin.addCases
        (fun pc : Fin a => ProgramLinking.relocateInstr id id addLabel (some (baseLabel 0)) (add.code pc))
        (Fin.addCases
          (fun pc : Fin b => ProgramLinking.relocateInstr id id mulLabel (some (baseLabel 0)) (mul.code pc))
          (fun pc : Fin c => ProgramLinking.relocateInstr id id loadLabel (some (baseLabel 0))
            (loader.code pc)))))


end SubexponentialSAT.SubexpProjectedInterpreter

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LayoutSourceRowsProgramReadiness
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Native readiness of the extracted source executor after the paid zero-array
initializer. The source dimension is the full count on210; no identification
with an earlier jet-length cache is made. -/
namespace SubexponentialSAT.SqrtLog.LayoutSourceRowsProgramReadiness
open SubexponentialSAT BitProgram StructuredCalls
open SubexponentialSAT.SubexpLiftRing SubexponentialSAT.SubexpQuarticRing
open SubexponentialSAT.SubexpRowPostfixInterpreter (ports )
open LayoutSourceRowsProgram
attribute [local simp] Fin.coe_ofNat_eq_mod

/-- Empty physical work ports required in addition to native arithmetic. -/
structure Empty (s : LayoutSourceRowsProgram.Store) : Prop where
  empty99 : s (executorPorts 99) = []
  empty121 : s (executorPorts 121) = []
  empty122 : s (executorPorts 122) = []
  empty240 : s (executorPorts 240) = []
  empty241 : s (executorPorts 241) = []
  empty244 : s (executorPorts 244) = []
  empty245 : s (executorPorts 245) = []
  buffers : ∀ i, s (executorPorts (SubexpConvolutionControl.bufferPorts i)) = []

end SubexponentialSAT.SqrtLog.LayoutSourceRowsProgramReadiness

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LayoutSourceValuesProgramLoop
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Fixed control that constructs an ordered scalar table. The callback is an
actual finite command with a measured execution contract. Runtime unary node
indices and counters do not change the command. -/
namespace SubexponentialSAT.SqrtLog.LayoutSourceValuesProgram

open SubexponentialSAT BitProgram StructuredCalls SubexpConvolutionControl

attribute [local simp] Fin.coe_ofNat_eq_mod

/-- Node37, remaining64, reversed table65; all other bytes are caller state. -/
def loopState (base : Store) (j : ℕ) (remaining acc : List Bool) : Store :=
  Function.update (Function.update (Function.update base 37 (List.replicate j true))
    64 remaining) 65 acc

end SubexponentialSAT.SqrtLog.LayoutSourceValuesProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LayoutTriplePreparationProgramBasic
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Fixed port assignments for cache access and triple serialization. -/
namespace SubexponentialSAT.SqrtLog.LayoutTriplePreparationProgram

open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls

def signedPair (negative : Bool) (p n : List Bool) : RowSelectionProgram.WordPair :=
  if negative then (n,p) else (p,n)

end SubexponentialSAT.SqrtLog.LayoutTriplePreparationProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LayoutTriplePreparationProgram
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms


-- LayoutTriplePreparationProgramLookup.lean

/-! List-level cache representation for the preserving physical array scan. -/
namespace SubexponentialSAT.SqrtLog.LayoutTriplePreparationProgram
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls

/-- All five cache inputs are preserved throughout preparation. -/
structure Cache where
  Hpositive : List (List Bool)
  Hnegative : List (List Bool)
  Bpositive : List (List Bool)
  Bnegative : List (List Bool)
  width : List Bool
  power : RowSelectionProgram.WordPair

/-- The words stored in the cache, before selecting their sign. -/
def Cache.Hword (c : Cache) (i : ℕ) : RowSelectionProgram.WordPair :=
  (c.Hpositive.getD i [],c.Hnegative.getD i [])
def Cache.Bword (c : Cache) (i : ℕ) : RowSelectionProgram.WordPair :=
  (c.Bpositive.getD i [],c.Bnegative.getD i [])

def Cache.Uniform (c : Cache) : Prop :=
  (∀ w ∈ c.Hpositive, w.length = c.width.length) ∧
  (∀ w ∈ c.Hnegative, w.length = c.width.length) ∧
  (∀ w ∈ c.Bpositive, w.length = c.width.length) ∧
  (∀ w ∈ c.Bnegative, w.length = c.width.length)

def Cache.Fits (c : Cache) (N : ℕ) : Prop :=
  N ≤ c.Hpositive.length ∧ N ≤ c.Hnegative.length ∧
  N ≤ c.Bpositive.length ∧ N ≤ c.Bnegative.length

end SubexponentialSAT.SqrtLog.LayoutTriplePreparationProgram

-- LayoutTriplePreparationProgramStep.lean

/-! One real triple-production iteration: two scans, three serializers and
paid cleanup. Only a parity bit is kept outside the subroutine registers. -/
namespace SubexponentialSAT.SqrtLog.LayoutTriplePreparationProgram
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls
open RowSelectionProgram

def selectedWord (c : Cache) (work : WordPair) (which : Fin 3) : WordPair :=
  if which = 0 then work else if which = 1 then (work.2,work.1) else c.power

def wordRecord (w : WordPair) := LayoutScalarEmitter.record w.1 w.2

end SubexponentialSAT.SqrtLog.LayoutTriplePreparationProgram

-- LayoutTriplePreparationProgramBody.lean

/-! A fixed, paid iteration producing the three real scalar operands. -/

/-! The native unary loop produces all triples in increasing binomial index. -/

/-! Initial unary copy/parity and final stream reversal are native paid calls. -/

/-! Complete cache-to-triple primitive program with all scans and copies paid. -/

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafAssignmentSetupProgramBase
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Concrete storage and framed service calls for each head assignment. -/
noncomputable section
namespace SubexponentialSAT.SqrtLog.LeafAssignmentSetupProgram
open SubexponentialSAT BitProgram StructuredCalls StackRoutines

def clear (src : Fin 768) : Code := .call (clearProgram src (0 : Fin 40) 1)

end SubexponentialSAT.SqrtLog.LeafAssignmentSetupProgram
end

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafProgramHash
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# Sparse clause-circuit evaluation for one hash row

The input is a list of supplied nonzero coefficients and width-k clause lists.
The evaluator visits those lists directly; it never builds a truth table on the
union of the clause scopes. Counters include measured variable lookup and ring
callbacks. Their primitive realization is a separate obligation, not inferred
from these counters. `Algebra` also admits canonical truncated operations, whose
decoder need not be a homomorphism into the untruncated polynomial ring.
-/

namespace SubexponentialSAT.SqrtLog.LeafProgram

open SubexponentialSAT.SubexpSymbolicCost

variable {V C A : Type*}

section PolynomialSemantics

variable {R : Type*} [CommRing R]

noncomputable def clausePolynomial (ls : List (SAT.Literal V)) : MvPolynomial V R :=
  (ls.map HashInput.falsifyingLiteral).prod

end PolynomialSemantics
end SubexponentialSAT.SqrtLog.LeafProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafFactorDispatchProgram
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Paid factor classification and source lookup. IDs are runtime data. -/
namespace SubexponentialSAT.SqrtLog.LeafFactorDispatchProgram
open SubexponentialSAT BitProgram StructuredCalls SubexpScanPrimitives

def clear (src : Fin 16) : Code := .call (StackRoutines.clearProgram src 0 1)
def compare : Code := .call (ProgramLinking.liftProgram CodeSearchProgram.unaryLessProgram cmpRegs cmpPorts)
def lessClean : Code := .seq compare (.seq (clear 8) (clear 9))

end SubexponentialSAT.SqrtLog.LeafFactorDispatchProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafFactorDispatchProgramBranches
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.LeafFactorDispatchProgram
open SubexponentialSAT BitProgram StructuredCalls SubexpScanPrimitives

def neutralBranch : Code := .seq (clear 6) (mark false false)

end SubexponentialSAT.SqrtLog.LeafFactorDispatchProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafFactorDispatchProgramRun
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Fixed native dispatcher: reverse the incoming ID, classify it, and scan
only the selected source. No selected payload is supplied as an input. -/
namespace SubexponentialSAT.SqrtLog.LeafFactorDispatchProgram
open SubexponentialSAT BitProgram StructuredCalls SubexpScanPrimitives

def outputStacks (rows clauses : List (List Bool)) (hasMarked : Bool) (m f : ℕ) : Fin 16 → List Bool :=
  Function.update (Function.update (baseStacks rows clauses m f) 2 []) 15
    (selectedPayload rows clauses hasMarked m f)

end SubexponentialSAT.SqrtLog.LeafFactorDispatchProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafHeadFactorsProgramSemantics
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! The physical row predicate selects exactly the computed factor colors. -/
namespace SubexponentialSAT.SqrtLog.LeafHeadFactorsProgram
open SubexponentialSAT BitProgram StructuredCalls MulticolorTypes

@[simp] theorem indices_length (A N : ℕ) : (indices A N).length = A + N := by
  simp [indices, Packing.headsFirst_length]

end SubexponentialSAT.SqrtLog.LeafHeadFactorsProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_Subexp_AssignmentRecordViews
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Fixed parser-based views of an actual framed word alphabet. -/

namespace SubexponentialSAT.Subexp.AssignmentRecordViews

open BitProgram StructuredCalls TupleProgram

abbrev parse : Cmd 3 3 :=
  .call (ProgramLinking.liftProgram ParserProgram.frameProgram firstTwo firstTwo)

abbrev loop : Cmd 3 3 := .while 2 (.seq parse pop)

abbrev flatten : Cmd 3 3 := .seq setFirst (.seq pop (.seq loop transfer))
def flattenProgram := compiled flatten 0 2

end SubexponentialSAT.Subexp.AssignmentRecordViews

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafHighContextProgram
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.LeafHighContextProgram.Local
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls

def cost (words : List (List Bool)) (mask : List Bool) : ℕ :=
  7*(ProgramEncoding.encodeRecords words).length+9*words.flatten.length+
    6*words.length+22*mask.length+29


end SubexponentialSAT.SqrtLog.LeafHighContextProgram.Local

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafNodeSamplesProgram
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! A fixed indexed traversal of the actual framed node table. The installed
worker is a real command; its measured, frame-preserving execution remains an
explicit producer obligation. Neither the index nor a jet is semantic advice. -/
namespace SubexponentialSAT.SqrtLog.LeafNodeSamplesProgram
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.StackRoutines

def copy (src dst : Fin 768) : Code := .call (copyProgram src dst 305 (0 : Fin 40) 1)
def transfer (src dst : Fin 768) : Code := .call (transferProgram src dst (0 : Fin 40) 1)
def clear (src : Fin 768) : Code := .call (clearProgram src (0 : Fin 40) 1)

def ports : RecordPrograms.Ports 40 768 where
  tag := 37
  present := 38
  found := 39
  source := 301
  payload := 302
  tag_ne_present := by decide
  found_ne_tag := by decide
  found_ne_present := by decide
  source_ne_payload := by decide

def reader : Code := RecordPrograms.reader ports
def pop : Code := RecordPrograms.atom (.pop 301 37 38)

end SubexponentialSAT.SqrtLog.LeafNodeSamplesProgram


end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafProgramCleanupWide
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Full cleanup for the wider leaf worker including setup pockets. -/
namespace SubexponentialSAT.SqrtLog.LeafProgram.Cleanup.Wide

open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls

abbrev command : Cmd 40 768 :=
  .seq (BankRoutines.clearCmd 767 0 1 (List.finRange 768)) (reset (List.finRange 40))

def program := compiled command 0 0

end SubexponentialSAT.SqrtLog.LeafProgram.Cleanup.Wide

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafOuterProgramStorage
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Static routing for the outer leaf. Each route clears its destination and
then calls the measured physical copy routine. The route list belongs to the
fixed program, while every copied bit and every cleanup bit is charged. -/
namespace SubexponentialSAT.SqrtLog.LeafOuterProgram

open SubexponentialSAT BitProgram StructuredCalls StackRoutines

abbrev route (p : Route) : Cmd 40 896 :=
  .seq (.call (clearProgram p.2 0 1)) (.call (copyProgram p.1 p.2 767 0 1))

def routes : List Route → Cmd 40 896
  | [] => .call (clearProgram 767 0 1)
  | p::ps => .seq (route p) (routes ps)

abbrev clearWorker : Cmd 40 896 :=
  .call (ProgramLinking.liftProgram LeafProgram.Cleanup.Wide.program id workerStack)

/-- Static input and output routing around an actual finite subprogram. -/
abbrev stage {r s l : ℕ} (inputs : List Route) (p : Program r s l)
    (register : Fin r → Fin 40) (stack : Fin s → Fin 896)
    (outputs : List Route) : Cmd 40 896 :=
  .seq (routes inputs) <| .seq (.call (ProgramLinking.liftProgram p register stack)) <|
    .seq (routes outputs) clearWorker

end SubexponentialSAT.SqrtLog.LeafOuterProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SubexpGuardProgram
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# Concrete binary guard control for the subexponential schedule

The comparator below has a fixed instruction table, reads arbitrary-width
little-endian binary words, and uses only Boolean operations and stack pops.
Schedule arithmetic is not an instruction of this program.
-/

namespace SubexponentialSAT.SubexpGuardProgram

open BitProgram BinaryArithmetic

namespace Compare

theorem round_trace_false_false (regs : Fin 8 → Bool) (xs ys : List Bool) :
    Trace program 10 (cfg (some 1) regs (false :: xs) (false :: ys))
      (cfg (some 1) (roundRegs regs (some false) (some false)) xs ys) := by
  apply Computation.Trace.of_iterate
  simp [Function.iterate_succ_apply, step, program, execInstr, cfg,
    read, roundRegs, readRegs, update_left, update_right, Function.update_apply]

theorem round_trace_false_true (regs : Fin 8 → Bool) (xs ys : List Bool) :
    Trace program 10 (cfg (some 1) regs (false :: xs) (true :: ys))
      (cfg (some 1) (roundRegs regs (some false) (some true)) xs ys) := by
  apply Computation.Trace.of_iterate
  simp [Function.iterate_succ_apply, step, program, execInstr, cfg,
    read, roundRegs, readRegs, update_left, update_right, Function.update_apply]

theorem round_trace_true_false (regs : Fin 8 → Bool) (xs ys : List Bool) :
    Trace program 10 (cfg (some 1) regs (true :: xs) (false :: ys))
      (cfg (some 1) (roundRegs regs (some true) (some false)) xs ys) := by
  apply Computation.Trace.of_iterate
  simp [Function.iterate_succ_apply, step, program, execInstr, cfg,
    read, roundRegs, readRegs, update_left, update_right, Function.update_apply]

theorem round_trace_true_true (regs : Fin 8 → Bool) (xs ys : List Bool) :
    Trace program 10 (cfg (some 1) regs (true :: xs) (true :: ys))
      (cfg (some 1) (roundRegs regs (some true) (some true)) xs ys) := by
  apply Computation.Trace.of_iterate
  simp [Function.iterate_succ_apply, step, program, execInstr, cfg,
    read, roundRegs, readRegs, update_left, update_right, Function.update_apply]

/-- A concrete nonterminal round, including its branch instruction. -/
theorem round_trace (regs : Fin 8 → Bool) (xs ys : List Bool)
    (hne : xs ≠ [] ∨ ys ≠ []) :
    Trace program 10 (cfg (some 1) regs xs ys)
      (cfg (some 1) (roundRegs regs xs.head? ys.head?) xs.tail ys.tail) := by
  cases xs with
  | nil =>
    cases ys with
    | nil => simp at hne
    | cons b ys =>
      cases b <;> apply Computation.Trace.of_iterate <;>
        simp [Function.iterate_succ_apply, step, program, execInstr, cfg,
          read, roundRegs, readRegs, update_left, update_right, Function.update_apply]
  | cons a xs =>
    cases ys with
    | nil =>
      cases a <;> apply Computation.Trace.of_iterate <;>
        simp [Function.iterate_succ_apply, step, program, execInstr, cfg,
          read, roundRegs, readRegs, update_left, update_right, Function.update_apply]
    | cons b ys =>
      cases a <;> cases b
      · exact round_trace_false_false regs xs ys
      · exact round_trace_false_true regs xs ys
      · exact round_trace_true_false regs xs ys
      · exact round_trace_true_true regs xs ys

theorem exit_trace (regs : Fin 8 → Bool) :
    Trace program 5 (cfg (some 1) regs [] []) (cfg none (exitRegs regs) [] []) := by
  apply Computation.Trace.of_iterate
  simp [Function.iterate_succ_apply, step, program, execInstr, cfg,
    read, exitRegs, readRegs, update_left, update_right,
    Function.update_apply]

/-- Exact instruction count for the data-dependent loop. -/
theorem loop_trace (regs : Fin 8 → Bool) (xs ys : List Bool) :
    ∃ rf : Fin 8 → Bool,
      Trace program (10 * max xs.length ys.length + 5)
        (cfg (some 1) regs xs ys) (cfg none rf [] []) ∧
      rf 0 = carry (regs 0) xs ys := by
  induction xs generalizing ys regs with
  | nil =>
    induction ys generalizing regs with
    | nil =>
      exact ⟨exitRegs regs, by simpa using exit_trace regs, by simp [carry]⟩
    | cons b ys ih =>
      obtain ⟨rf, hr, hb⟩ := ih (roundRegs regs none (some b))
      refine ⟨rf, ?_, ?_⟩
      · have h := (round_trace regs [] (b :: ys) (by simp)).trans hr
        simpa [cfg, Nat.mul_add, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using h
      · simpa [carry, roundRegs_borrow] using hb
  | cons a xs ih =>
    cases ys with
    | nil =>
      obtain ⟨rf, hr, hb⟩ := ih (roundRegs regs (some a) none) []
      refine ⟨rf, ?_, ?_⟩
      · have h := (round_trace regs (a :: xs) [] (by simp)).trans hr
        simpa [cfg, Nat.mul_add, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using h
      · simpa [carry, roundRegs_borrow] using hb
    | cons b ys =>
      obtain ⟨rf, hr, hb⟩ := ih (roundRegs regs (some a) (some b)) ys
      refine ⟨rf, ?_, ?_⟩
      · have h := (round_trace regs (a :: xs) (b :: ys) (by simp)).trans hr
        simpa [cfg, Nat.mul_add, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using h
      · simpa [carry, roundRegs_borrow] using hb

/-- Complete comparator contract. Leading zero bits and unequal widths are allowed. -/
theorem run (regs : Fin 8 → Bool) (xs ys : List Bool) :
    ∃ rf : Fin 8 → Bool,
      Trace program (10 * max xs.length ys.length + 6)
        (cfg (some program.entry) regs xs ys) (cfg none rf [] []) ∧
      (rf 0 = true ↔ BinaryArithmetic.toNat xs < BinaryArithmetic.toNat ys) := by
  obtain ⟨rf, hr, hb⟩ := loop_trace (Function.update regs 0 false) xs ys
  refine ⟨rf, ?_, ?_⟩
  · have he : Trace program 1 (cfg (some program.entry) regs xs ys)
        (cfg (some 1) (Function.update regs 0 false) xs ys) := by
      exact .cons (by rfl) (.refl _)
    convert he.trans hr using 1
    all_goals try with_reducible_and_instances rfl
    omega
  · rw [hb]
    simpa only [Function.update_self, bitVal_false, Nat.add_zero] using carry_iff xs ys false

end Compare

open StructuredProgram

theorem embed_restrict {R S : ℕ} (register : Fin 8 → Fin R) (stack : Fin 2 → Fin S)
    (hr : Function.Injective register) (hs : Function.Injective stack) (a : State R S) :
    StructuredCalls.embedState register stack a (restrictState register stack a) = a := by
  unfold StructuredCalls.embedState restrictState
  change State.mk (Function.extend register (a.regs ∘ register) a.regs)
    (Function.extend stack (a.stacks ∘ stack) a.stacks) = a
  rw [extend_restrict register hr, extend_restrict stack hs]


end SubexponentialSAT.SubexpGuardProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafProgramHashParameters
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Concrete placement of the selector's numerical preparation in the full
leaf bank. Formula784 and answer787 are outside this routine;782 contains the
actual binary clause count produced by ClauseCount.caller. -/
namespace SubexponentialSAT.SqrtLog.LeafProgram.HashParameters

open SubexponentialSAT BitProgram StructuredCalls

@[simp] theorem rows_port : ports.hash.stack 9 = 777 := rfl
@[simp] theorem alphabet_port : ports.hash.stack 0 = 768 := rfl
@[simp] theorem depth_port : ports.hash.stack 5 = 773 := rfl
@[simp] theorem rounds_port : ports.hash.stack 6 = 774 := rfl

end SubexponentialSAT.SqrtLog.LeafProgram.HashParameters

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafProgramClauseCount
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Count the clauses in the actual emitted leaf. Both the preserving record
scan and unary-to-binary conversion are fixed native programs. -/
namespace SubexponentialSAT.SqrtLog.LeafProgram.ClauseCount

open SubexponentialSAT BitProgram StructuredCalls

def budget (records : List (List Bool)) : ℕ :=
  SubexpScopeCountSetup.countBudget records+1+records.length*(8*records.length+10)+5

end SubexponentialSAT.SqrtLog.LeafProgram.ClauseCount

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SubexpEmptyClauseProgram
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# A preserving empty-clause test on the actual encoded leaf

The fixed program searches for the one-bit encoding of an empty clause.
The leaf on stack 9 and every other caller word are preserved.  Only the
five empty membership work ports and one empty copy port are used.
-/

namespace SubexponentialSAT.SubexpEmptyClauseProgram

open BitProgram StructuredCalls

abbrev Data := StructuredProgram.State 10 10

def result (d : Data) (answer : Bool) : Data :=
  ⟨fun i => if i = 0 then answer else if i.val < 7 then false else d.regs i,
    d.stacks⟩

end SubexponentialSAT.SubexpEmptyClauseProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafProgramTrivial
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.MulticolorTypes.decidableMemJoint _root_.OAI.Algorithms.SubexponentialSAT.MulticolorTypes.decidableMemSide _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Actual classification of the two trivial leaf cases. The empty formula
and an empty clause are detected separately on the preserved encoded leaf. -/

namespace SubexponentialSAT.SqrtLog.LeafProgram.Trivial

open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls

abbrev Data := State 10 10

def result (a : Data) (records : List (List Bool)) : Data :=
  ⟨readRegs (SubexpEmptyClauseProgram.result a (decide ([false] ∈ records))).regs 7 8
      (Encoding.encodeList id records).head?, a.stacks⟩

@[simp] theorem result_stacks (a : Data) (records : List (List Bool)) :
    (result a records).stacks = a.stacks := rfl

end SubexponentialSAT.SqrtLog.LeafProgram.Trivial

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafOuterProgramStart
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Closed outer-leaf startup: count the actual clause records, compute the
numeric hash parameters, and preserve the exact binary decoder width. -/
namespace SubexponentialSAT.SqrtLog.LeafOuterProgram
open SubexponentialSAT BitProgram StructuredCalls SubexpSetupStorage

def startBudget (W : ℕ) (records : List (List Bool)) : ℕ :=
  let c := LeafProgram.ClauseCount.budget records+1
  let h := prepareHashBudget (W+c)
  c+h+9*(W+c+h)+8

end SubexponentialSAT.SqrtLog.LeafOuterProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafStatisticsSemanticsEnumeration
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Exact owner order of the neutral factors emitted by the native scan. -/
namespace SubexponentialSAT.SqrtLog.LeafStatisticsSemantics

open PackingIncidenceInput

/-- Uncovered free owners in the order in which the native counter advances. -/
def neutralOwners (scopes : List (List ℕ)) : ℕ → List Bool → List ℕ
  | _, [] => []
  | v, high :: rest =>
      if high then neutralOwners scopes (v+1) rest
      else if Scan.indices scopes v = [] then v :: neutralOwners scopes (v+1) rest
      else neutralOwners scopes (v+1) rest

/-- The actual original-factor incidence pairs; owner blocks may be reversed. -/
def originalPairs (scopes : List (List ℕ)) : ℕ → List Bool → List (ℕ × ℕ)
  | _, [] => []
  | v, high :: rest => originalPairs scopes (v+1) rest ++
      if high then [] else (Scan.indices scopes v).map fun e => (v,e)

theorem neutralOwners_eq_filter (scopes : List (List ℕ)) (v : ℕ) (mask : List Bool) :
    neutralOwners scopes v mask =
      (lowOwners v mask).filter (fun u => decide (Scan.indices scopes u = [])) := by
  induction mask generalizing v with
  | nil => simp [neutralOwners, lowOwners]
  | cons b bs ih =>
    cases b <;> by_cases h : Scan.indices scopes v = [] <;>
      simp [neutralOwners, lowOwners, ih, h]

theorem neutralOwners_mem (scopes : List (List ℕ)) (v u : ℕ) (mask : List Bool) :
    u ∈ neutralOwners scopes v mask ↔ u ∈ lowOwners v mask ∧ Scan.indices scopes u = [] := by
  simp [neutralOwners_eq_filter]

theorem neutralOwners_nodup (scopes : List (List ℕ)) (v : ℕ) (mask : List Bool) :
    (neutralOwners scopes v mask).Nodup := by
  rw [neutralOwners_eq_filter]
  exact (lowOwners_nodup v mask).filter _

theorem originalPairs_mem (scopes : List (List ℕ)) (mask : List Bool) :
    ∀ v u e, (u,e) ∈ originalPairs scopes v mask ↔
      u ∈ lowOwners v mask ∧ e ∈ Scan.indices scopes u := by
  induction mask with
  | nil => intros; simp [originalPairs, lowOwners]
  | cons b bs ih =>
    intro v u e
    cases b <;> by_cases hu : u = v
    all_goals simp [originalPairs, lowOwners, ih, hu]
    all_goals exact fun _ h => False.elim (hu h.symm)

theorem entries_mem_split (scopes : List (List ℕ)) (mask : List Bool) :
    ∀ v z p, p ∈ Semantics.entries scopes v z mask ↔
      p ∈ originalPairs scopes v mask ∨ p ∈ numbered z (neutralOwners scopes v mask) := by
  induction mask with
  | nil => intros; simp [Semantics.entries, originalPairs, numbered, neutralOwners]
  | cons b bs ih =>
    intro v z p
    cases b <;> by_cases h : Scan.indices scopes v = [] <;>
      simp [Semantics.entries, originalPairs, numbered, neutralOwners, Step.next,
        Step.factors, h, ih, or_assoc, or_comm]

theorem counter_eq_numbered_length (scopes : List (List ℕ)) (mask : List Bool) :
    ∀ v z, Loop.finalCounter scopes v z mask = z + (neutralOwners scopes v mask).length := by
  induction mask with
  | nil => intros; simp [Loop.finalCounter, neutralOwners]
  | cons b bs ih =>
    intro v z
    cases b <;> by_cases h : Scan.indices scopes v = [] <;>
      simp [Loop.finalCounter, neutralOwners, Step.next, h, ih, Nat.add_assoc,
        Nat.add_comm]

theorem native_original_mem (scopes : List (List ℕ)) (mask : List Bool)
    (v z u e : ℕ) (hz : scopes.length ≤ z) (he : e < scopes.length) :
    (u,e) ∈ Semantics.entries scopes v z mask ↔
      u ∈ lowOwners v mask ∧ e ∈ Scan.indices scopes u := by
  rw [entries_mem_split, originalPairs_mem]
  have hn : (u,e) ∉ numbered z (neutralOwners scopes v mask) := by
    intro hp
    have := numbered_factor_ge (neutralOwners scopes v mask) z u e hp
    omega
  simp [hn]

theorem native_neutral_mem (scopes : List (List ℕ)) (mask : List Bool)
    (v z u e : ℕ) (hz : scopes.length ≤ z) (he : z ≤ e) :
    (u,e) ∈ Semantics.entries scopes v z mask ↔
      ∃ i : Fin (neutralOwners scopes v mask).length,
        (neutralOwners scopes v mask).get i = u ∧ z+i.val = e := by
  rw [entries_mem_split, numbered_mem]
  have hn : (u,e) ∉ originalPairs scopes v mask := by
    intro hp
    have hi := ((originalPairs_mem scopes mask v u e).mp hp).2
    have := Subexp.IncidencePlanSpec.incidentIndex_lt scopes u e hi
    omega
  simp [hn]

theorem entries_owner_low (scopes : List (List ℕ)) (mask : List Bool)
    (v z u e : ℕ) (h : (u,e) ∈ Semantics.entries scopes v z mask) :
    u ∈ lowOwners v mask := by
  rcases (entries_mem_split scopes mask v z (u,e)).mp h with ho | hn
  · exact ((originalPairs_mem scopes mask v u e).mp ho).1
  · obtain ⟨i, hi, _⟩ := (numbered_mem (neutralOwners scopes v mask) z u e).mp hn
    have hu := List.get_mem (neutralOwners scopes v mask) i
    rw [hi] at hu
    exact ((neutralOwners_mem scopes v u mask).mp hu).1

end SubexponentialSAT.SqrtLog.LeafStatisticsSemantics

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafPackingFiberBounds
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Raw native incidence records have no repeated owner-factor pair. Hence their
index fibers are bounded by the statistics of the actual completed scopes. -/
namespace SubexponentialSAT.SqrtLog.LeafPackingFiberBounds
open PackingIncidenceInput LeafStatisticsSemantics LeafStatisticsProgram

 theorem factors_nodup (scopes : List (List ℕ)) (v z : ℕ) :
    (Step.factors scopes v z).Nodup := by
  by_cases h : Scan.indices scopes v = []
  · simp [Step.factors,h]
  · simp only [Step.factors,ite_eq_right h]
    exact Subexp.IncidencePlanSpec.incidentIndices_nodup scopes v

 theorem entries_nodup (scopes : List (List ℕ)) (mask : List Bool) :
    ∀ v z, (Semantics.entries scopes v z mask).Nodup := by
  induction mask with
  | nil => intros; simp [Semantics.entries]
  | cons b bs ih =>
    intro v z
    cases b
    · simp only [Semantics.entries,Bool.false_eq_true,ite_false]
      apply List.nodup_append.mpr
      refine ⟨ih _ _, (factors_nodup scopes v z).map (fun x y h => Prod.mk.inj h |>.2), ?_⟩
      intro p hp q hq hpq
      subst q
      obtain ⟨e,he,rfl⟩ := List.mem_map.mp hq
      have hh := lowOwners_bounds (v+1) v bs
        (entries_owner_low scopes bs (v+1) (Step.next scopes v z) v e hp)
      omega
    · simpa [Semantics.entries] using ih (v+1) z

end SubexponentialSAT.SqrtLog.LeafPackingFiberBounds

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafProgramSourceControls
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Paid source-control copies into the isolated 340-stack worker. All inputs
come from runtime layout/ring masters; no source polynomial is supplied. -/
namespace SubexponentialSAT.SqrtLog.LeafProgram.SourceControls
open SubexponentialSAT BitProgram StructuredCalls SubexpSetupStorage
abbrev Data := State 16 768

end SubexponentialSAT.SqrtLog.LeafProgram.SourceControls

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafQueryFrontendHighRun
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! The high mask is computed from the original ambient count and actual scope
mass. The forward mask is a paid copy/reversal of that same output. -/
namespace SubexponentialSAT.SqrtLog.LeafQueryFrontend
open SubexponentialSAT BitProgram StructuredCalls
attribute [local simp] Fin.coe_ofNat_eq_mod


def highMask (rows : List (List ℕ)) (ambient : ℕ) : List Bool :=
  HighIncidenceProgram.highPrefix rows
    ((HighIncidenceProgram.Prepare.mass rows * EarlyThreshold.threshold ambient) ⌈/⌉ ambient) ambient

end SubexponentialSAT.SqrtLog.LeafQueryFrontend

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafQueryFrontendMeasure
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Actual scope/mask scans are joined before any statistic is converted. -/
namespace SubexponentialSAT.SqrtLog.LeafQueryFrontend
open SubexponentialSAT BitProgram StructuredCalls
attribute [local simp] Fin.coe_ofNat_eq_mod


def totals (rows : List (List ℕ)) (forward : List Bool) :=
  LeafStatisticsProgram.variableTotals rows 0 forward LeafStatisticsProgram.zeroTotals

def completedArity (rows : List (List ℕ)) (forward : List Bool) :=
  LeafStatisticsProgram.Finalize.neutralArity
    (LeafStatisticsProgram.Arity.arity forward rows 0) (totals rows forward).uncovered

end SubexponentialSAT.SqrtLog.LeafQueryFrontend

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_RingProgramTableBasic
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Native primitives used by the companion-table preparation machine. -/
namespace SubexponentialSAT.SqrtLog.RingProgramTable

open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.StackRoutines
open SubexponentialSAT.SubexpLiftRing SubexponentialSAT.SubexpQuarticRing

abbrev clear (dst : Fin 27) : Cmd 8 27 := .call (clearProgram dst 1 3)

end SubexponentialSAT.SqrtLog.RingProgramTable

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SubexpTaylorFrames
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Fixed-control conversion of a flat coefficient stream into an ordered
list of framed coefficients. Runtime counters determine the coefficient
width and requested count. Missing high coefficients are actually read as
zero by the existing padded-reader program. -/

namespace SubexponentialSAT.SubexpTaylorFrames

open BitProgram StructuredCalls SubexpScanPrimitives
open SubexpExponentProgram

def state (regs : Fin 5 → Bool) (w : Words) : State 5 9 := ⟨regs, store w⟩

end SubexponentialSAT.SubexpTaylorFrames

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafRingSetupProgramNative
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms


/-! The fixed executable preparation pipeline.  Its input is the actual
numerical bank emitted by `LeafParametersProgram`; no field polynomial,
modulus, multiplication table, nodes, or idempotent coefficients are inputs.
The stage-by-stage execution theorem is separate from this code definition.
-/


/-! Arithmetic consumers use the same bytes generated by the preceding
stages.  These are structural handoff lemmas; the complete production
trace must establish `NativeBytes` before invoking them. -/

namespace SubexponentialSAT.SqrtLog.LeafRingSetupProgram
open BitProgram StructuredCalls

def counterStack (s : Fin 640 → List Bool) (p : Fin 640 × Fin 640) : Fin 640 → List Bool :=
  Function.update s p.2 (List.replicate (BinaryArithmetic.toNat (s p.1)) true)

end SubexponentialSAT.SqrtLog.LeafRingSetupProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_SquarefreeBasic
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.labelFintype _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.variableFintype _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Sparse squarefree polynomials. The index monoid multiplies by support union,
so the coefficient algebra imposes X_v^2 = X_v without enumerating all supports. -/

namespace SubexponentialSAT.SqrtLog.Squarefree

open scoped BigOperators

variable {V R : Type*}

noncomputable section

variable [DecidableEq V] [CommSemiring R]

def coeffHom (s : Finset V) : Poly V R →+ R where
  toFun := coeff s
  map_zero' := rfl
  map_add' _ _ := rfl

end
end SubexponentialSAT.SqrtLog.Squarefree

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_MomentsSquarefree
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.labelFintype _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.variableFintype _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Exact coefficient extraction in the Boolean squarefree algebra, including
both formal scalar variables. No total-degree truncation is substituted for
support union. The final U coefficient sum is only an additive operation. -/

namespace SubexponentialSAT.SqrtLog.Moments

open scoped BigOperators
open _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.Squarefree

noncomputable section

section SquarefreeEvaluation

variable {V R : Type*} [DecidableEq V] [CommSemiring R]

/-- U is outermost, Z next, and Boolean squarefree X coefficients innermost. -/
abbrev SquarefreeJet (V R : Type*) [DecidableEq V] [Semiring R] :=
  Polynomial (Polynomial (Poly V R))

def jetCoeff (s : Support V) : SquarefreeJet V R →+ ScalarJet R :=
  Truncation.mapCoeffs (Truncation.mapCoeffs (coeffHom s.vars))

@[simp] theorem jetCoeff_apply (s : Support V) (f : SquarefreeJet V R) (u z : ℕ) :
    ((jetCoeff s f).coeff u).coeff z = coeff s.vars ((f.coeff u).coeff z) := rfl

def jetEval (x : V → R) (hx : ∀ v, x v * x v = x v) :
    SquarefreeJet V R →+* ScalarJet R :=
  Polynomial.mapRingHom (Polynomial.mapRingHom (evalHom x hx))

@[simp] theorem jetEval_coeff (x : V → R) (hx : ∀ v, x v * x v = x v)
    (f : SquarefreeJet V R) (u z : ℕ) :
    ((jetEval x hx f).coeff u).coeff z = evalHom x hx ((f.coeff u).coeff z) := by
  simp [jetEval]

end SquarefreeEvaluation

end
end SubexponentialSAT.SqrtLog.Moments

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_MomentsPerturbation
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.labelFintype _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.variableFintype _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Actual row perturbations, rather than an assumed support invariant.
Every formal Boolean coordinate is multiplied by a polynomial with zero
constant term in Z. The construction is valid over any commutative ring. -/

namespace SubexponentialSAT.SqrtLog.Moments

open _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.Squarefree
open scoped BigOperators

variable {V R : Type*} [DecidableEq V] [CommRing R]

@[simp] theorem eval_scalar (x : V → R) (hx : ∀ v, x v * x v = x v) (c : R) :
    Squarefree.evalHom x hx (Squarefree.scalar c) = c := by
  change Squarefree.evalHom x hx (Squarefree.monomial ∅ c) = c
  simp [Squarefree.weight]

end SubexponentialSAT.SqrtLog.Moments

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_MomentsSparse
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.labelFintype _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.variableFintype _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Executable support extraction for the normalized sparse squarefree jets.
Projection erases X after extracting one requested support, leaving U and Z.
All operations preserve the same bounded sparse representation. -/

namespace SubexponentialSAT.SqrtLog.Moments

open _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.Squarefree
open scoped BigOperators

variable {V R : Type*} [DecidableEq V] [CommSemiring R]

noncomputable def ringScalar : R →+* Jet V R :=
  Polynomial.C.comp (Polynomial.C.comp Squarefree.scalar)

@[simp] theorem scalar_empty (c : R) :
    (Squarefree.scalar c : Poly V R) = Squarefree.monomial ∅ c := rfl

@[simp] theorem monomial_zero (s : Finset V) : (Squarefree.monomial s (0 : R)) = 0 := by
  simp [Squarefree.monomial]

end SubexponentialSAT.SqrtLog.Moments

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_ResidualEmbeddingStored
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.labelFintype _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.variableFintype _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Padding a sparse dictionary preserves its exact coefficients, key
uniqueness, validity, and list length. The ambient bit representation need
not compact or renumber the residual variables. -/
namespace SubexponentialSAT.SqrtLog.ResidualEmbedding

open _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.Squarefree
variable {V W R : Type*} [DecidableEq V] [DecidableEq W] [CommSemiring R]

def index (e : V ↪ W) (a : Index V) : Index W := ⟨a.u, a.z, a.vars.map e⟩

end SubexponentialSAT.SqrtLog.ResidualEmbedding

end OAI.Algorithms
end


