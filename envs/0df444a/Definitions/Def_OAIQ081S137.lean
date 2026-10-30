-- Prove2me | Definitions.Def_OAIQ081S137
-- name    : OAIQ081S137
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-29T22:44:21.973571+00:00
-- url     : https://prove2.me/theorems/c5a13bfb-3529-41b4-ac60-9d4ff4f0a644
-- title:
--   Definitions bundle OAIQ081S137 of the split of OpenAI, The Exponential Time Hypothesis is False
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.exact_count_and_sat`, carved from OpenAI's openai/math development (OpenAI, *The Exponential Time Hypothesis is False*, OpenAI Math Release, October 25, 2026, result family 378, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 54 declarations of OpenAI's Lean: 37 definitions, 16 inductive types or structures and 1 theorem. The definitions and types are `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgramScalar.InitialInvariant`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighQueryProgram.Carried.SafeAvoids`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeLeafPreparation.Ready`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeLeafPreparation.afterCode`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeLeafSetup.saveCanonical`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.PairNativeSetup.CountFalse.state`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.PairNativeSetup.countMiddle`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.PairNativeSetup.countResult`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.PairNativeSetup.setupResult`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryKeptFrame.SafeAvoids`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryNodeEvaluation.Code`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryPairControlFrame.SafeAvoids`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QuerySelectorFrames.SafeAvoids`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryStreamFrames.SafeAvoids`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryTopFrame.SafeAvoids`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SignatureHeadLoader.MasterFrame`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SignatureHeadLoader.matrixBase`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SignatureKeyNative.Ready`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SignatureKeyNative.outputState`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SignatureTupleNative.AncestorStorage`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SignatureTupleNative.CandidateReady`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SignatureTupleNative.LeafStorage`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SignatureTupleNative.candidateInput`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SignatureTupleNative.candidateOutput`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SignatureTupleNative.initializeFreshState`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SignatureTupleNative.initializeLevelsState`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SignatureTupleProgram.Iteration`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SignatureTupleProgram.Traversal`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SignatureTupleProgram.clearState`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SignatureTupleProgram.clearWordsState`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SignatureTupleProgram.clearWordsTime`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SignatureTupleProgram.copyState`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SignatureTupleProgram.dropRepresentativeState`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SignatureTupleProgram.frameState`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SignatureTupleProgram.popWordState`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SignatureTupleProgram.pushWordState`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SignatureTupleProgram.recordRepresentativeState`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SignatureTupleProgram.restoreCursorState`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SignatureTupleProgram.saveCursorState`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SignatureTupleRefinement.descendClearState` and 13 more.
--
--   **Sources.** They come from these modules of lean/OAI/Algorithms, in whole or in part: `SubexponentialSAT_SqrtLogSpace_HighQueryProgram`, `SubexponentialSAT_SqrtLogSpace_NativeLeafPreparation`, `SubexponentialSAT_SqrtLogSpace_NativeLeafStartup`, `SubexponentialSAT_SqrtLogSpace_NativeQueryArithmetic`, `SubexponentialSAT_SqrtLogSpace_PairNativeSetup`, `SubexponentialSAT_SqrtLogSpace_QueryKeptFrame`, `SubexponentialSAT_SqrtLogSpace_QueryNodeEvaluation`, `SubexponentialSAT_SqrtLogSpace_QueryPairControlFrame`, `SubexponentialSAT_SqrtLogSpace_QuerySelectorFrames`, `SubexponentialSAT_SqrtLogSpace_QueryStreamFrames`, `SubexponentialSAT_SqrtLogSpace_QueryTopFrame`, `SubexponentialSAT_SqrtLogSpace_SignatureHeadLoaderCore`, `SubexponentialSAT_SqrtLogSpace_SignatureKeyNative`, `SubexponentialSAT_SqrtLogSpace_SignatureTupleNative`, `SubexponentialSAT_SqrtLogSpace_SignatureTupleProgram`, `SubexponentialSAT_SqrtLogSpace_SignatureTupleRefinement`, `SubexponentialSAT_SqrtLogSpace_SignatureTupleTraversal`, `SubexponentialSAT_SqrtLogSpace_SparseCodeSearch`, `SubexponentialSAT_SqrtLog_LayoutProgramScalarCacheCell`, `SubexponentialSAT_SubexpHeadColorProgram`, `SubexponentialSAT_Subexp_GlobalBasisEntryCore`, `SubexponentialSAT_Subexp_SupportSelectionPrimitives`.
--
--   **Imports.** It imports the published bundle `Def_SubexponentialSAT`; the bundles `OAIQ081S100`, `OAIQ081S102`, `OAIQ081S108`, `OAIQ081S114` and `OAIQ081S115` of this split.
--
--   **Imported by** (directly, in this split): the bundle `OAIQ081S152`; the statements `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SignatureKeyNative.run` and `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SparseCodeSearch.core_runs`; the proofs of `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SignatureKeyNative.run`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SparseCodeSearch.core_runs`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.HeadIdentifierProgram.visit_eval`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgram.EntryBank.covered_eval`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgram.EntryBank.uncovered_cleanup_eval`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgram.IntegerCache.program_runsIn`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgram.SourceBank.compareBlocks_eval`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgram.SourceBank.uncovered_cleanup` and `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafHeadFactorsProgram.test_eval`.
-- source:
--   OpenAI, The Exponential Time Hypothesis is False, OpenAI Math Release, October 25, 2026, https://github.com/openai/math (result family 378; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/The-Exponential-Time-Hypothesis-is-False-October-25-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Algorithms at commit 7ef5c0c

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_SubexponentialSAT
import Definitions.Def_OAIQ081S100
import Definitions.Def_OAIQ081S102
import Definitions.Def_OAIQ081S108
import Definitions.Def_OAIQ081S114
import Definitions.Def_OAIQ081S115

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_NativeQueryArithmetic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! Actual query arithmetic with fixed ordinary polynomial time and space. -/
namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeQueryPreparation
open OAI BitProgram StructuredCalls SqrtLog LeafParametersProgram
open LeafProgram.Query CostAssembly.Polynomial

theorem halt_trace_of_eval {r s n : ℕ} {c : Cmd r s} {a b : State r s}
    (h : Eval c n a b) (input output : Fin s) :
    Trace (compiled c input output) (n + 1)
      (a.withPC (some (compiled c input output).entry)) (b.withPC none) :=
  compiled_halt_trace h input output

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeQueryPreparation
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SubexpHeadColorProgram
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# Read a head color from its physical one-hot type encoding

Ports 0, 1, and 2 hold the flat type bytes, unary position, and unary color
width. The fixed array reader preserves these inputs. A five-label bit loop
counts the false prefix of the selected one-hot word; the remaining suffix is
cleared. Only output port 3 changes, and scratch ports 4--9 are restored.
-/

namespace SubexponentialSAT.SubexpHeadColorProgram

open BitProgram StructuredCalls SubexpScanPrimitives
open Subexp.AssignmentAlphabetSemantics

abbrev Data := State 5 10

def Clean (d : Data) : Prop :=
  ∀ i ∈ ([3,4,5,6,7,8,9] : List (Fin 10)), d.stacks i = []

def selected (d : Data) (word : List Bool) : Data :=
  ⟨readRegs d.regs 0 1 none, Function.update d.stacks 5 word⟩

end SubexponentialSAT.SubexpHeadColorProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_Subexp_GlobalBasisEntryCore
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Concrete framed-word, comparison, and scalar-cell services for the
global matrix entry callback. Register 6 is the persistent row-kind flag. -/

namespace SubexponentialSAT.Subexp.GlobalBasisEntryCore

open BitProgram StructuredCalls SubexpScanPrimitives

def popped (src : Fin 32) (bit : Bool) (tail : List Bool) (d : Data) : Data :=
  ⟨readRegs d.regs 7 0 (some bit), Function.update d.stacks src tail⟩

end SubexponentialSAT.Subexp.GlobalBasisEntryCore

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_Subexp_SupportSelectionPrimitives
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Fixed copying, comparison and record emission for support selection. -/

namespace SubexponentialSAT.Subexp.SupportSelectionProgram

open BitProgram StructuredCalls SubexpScanPrimitives

abbrev Data := State 16 64

end SubexponentialSAT.Subexp.SupportSelectionProgram

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

/-! Complete reusable cache pass: read one encoded row, compute and emit its
new row, append the end marker, reverse the output, and clear the carry. -/

/-! The number of coefficient-cache rows is runtime unary data. This fixed
loop invokes the complete paid row pass and preserves the current encoded row.
-/

/-! The physical unsigned cache computes the original coefficient recurrence's
natural magnitudes, in ascending degree order. -/

/-! A fixed loop builds the initial all-one cache row from a runtime unary
length. The constant program contains one record, independent of that length. -/
namespace SubexponentialSAT.SqrtLog.LayoutProgramScalar

open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls
open SubexponentialSAT.SqrtLog.RowSelectionProgram

def InitialInvariant (base : Data) (i : ℕ) (d : Data) : Prop :=
  d.stacks 15 = pairEncoding (List.replicate i ([true],[])) ∧
  ∀ j, j ≠ 15 → j ≠ 17 → d.stacks j = base.stacks j

end SubexponentialSAT.SqrtLog.LayoutProgramScalar

/-! One fixed program builds the complete unsigned H cache from the unary
runtime parameters A and R. No coefficient or initial cache is free input. -/

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_PairNativeSetup
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! Physical pair traversal initialization and ambient-mask expansion. The
five low scratch ports325..329 are reclaimed before the caller returns; the
pair controller and persistent node/layout words are not scratch. -/
namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.PairNativeSetup
open OAI BitProgram StructuredCalls

namespace CountFalse

def state (regs : Fin 3 → Bool) (mask out : List Bool) : Data :=
  ⟨regs, fun i => if i = 0 then mask else out⟩

end CountFalse


open SubexpSetupStorage

noncomputable def countMiddle (a : Data) (rf : Fin 3 → Bool) : Data :=
  embedState countRegister countStack (countPrepared a)
    (CountFalse.state rf [] (List.replicate ((a.stacks 338).countP (!·)) true))

noncomputable def countResult (a : Data) (rf : Fin 3 → Bool) : Data :=
  finishState scratch [(326,832)] (countMiddle a rf)

noncomputable def setupResult (a : Data) (rf : Fin 3 → Bool) : Data :=
  copyState 243 833 (clearManyState [833,834,835] (countResult a rf))

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.PairNativeSetup
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_SignatureTupleProgram
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-!
# Fixed-control interpreter for streaming signature tuples

The input-dependent depth is represented by an encoded stack of suspended
frames. `probe` tests one candidate against earlier assignments. A rejected
candidate advances at its current depth; only a fresh signature descends.
Thus this control table never traverses raw assignment tuples.

The subroutines are concrete finite commands, and all execution theorems use
their actual measured evaluations. Instantiating their frame, signature, and
counter invariants remains a separate native-program obligation.
-/

namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SignatureTupleProgram

open BitProgram StructuredCalls

/-- Concrete cases of one interpreter iteration. Their costs include every
Boolean branch, including the fresh-signature test's losing case. -/
inductive Iteration {r s : ℕ} (p : Ports r) (q : Routines r s) :
    ℕ → State r s → State r s → Prop
  | leaf {a b c nv na} : a.regs p.leaf = true →
      Eval q.visit nv a b → Eval q.ascend na b c →
      Iteration p q (nv + na + 1) a c
  | fresh {a b c np nd} : a.regs p.leaf = false →
      Eval q.probe np a b → b.regs p.available = true → b.regs p.fresh = true →
      Eval q.descend nd b c → Iteration p q (np + nd + 3) a c
  | duplicate {a b c np nn} : a.regs p.leaf = false →
      Eval q.probe np a b → b.regs p.available = true → b.regs p.fresh = false →
      Eval q.advance nn b c → Iteration p q (np + nn + 3) a c
  | exhausted {a b c np na} : a.regs p.leaf = false →
      Eval q.probe np a b → b.regs p.available = false →
      Eval q.ascend na b c → Iteration p q (np + na + 2) a c

/-- Proof-level record of actual successive iterations; no trace is stored
by the executable program. The terminal guard test costs one step. -/
inductive Traversal {r s : ℕ} (p : Ports r) (q : Routines r s) :
    ℕ → State r s → State r s → Prop
  | done {a} : a.regs p.active = false → Traversal p q 1 a a
  | step {a b c n m} : a.regs p.active = true →
      Iteration p q n a b → Traversal p q m b c → Traversal p q (n + m + 1) a c

def frameState (v present : Bool) (src dst : List Bool) : State 2 2 :=
  ⟨ParserProgram.pair v present, ParserProgram.pair src dst⟩

def copyState (src dst : Fin 896) (a : State 40 896) : State 40 896 :=
  ⟨readRegs a.regs 0 1 none, StackRoutines.copyStacks src dst a.stacks⟩

noncomputable def pushWordState (src dst : Fin 896) (h : src ≠ dst)
    (a : State 40 896) : State 40 896 :=
  embedState frameRegisters (wordPorts src dst h) a
    (frameState false false [] (Encoding.frame (a.stacks src).reverse ++ a.stacks dst))

noncomputable def popWordState (src dst : Fin 896) (h : src ≠ dst)
    (a : State 40 896) (word tail : List Bool) : State 40 896 :=
  embedState frameRegisters (wordPorts src dst h) a (frameState false true tail word)

noncomputable def saveCursorState (a : State 40 896) : State 40 896 :=
  pushWordState (tupleStacks 7) (tupleStacks 0) (by decide)
    (pushWordState (tupleStacks 2) (tupleStacks 0) (by decide) a)

noncomputable def restoreCursorState (a : State 40 896) (candidate remaining frames : List Bool) :
    State 40 896 :=
  popWordState (tupleStacks 0) (tupleStacks 2) (by decide)
    (popWordState (tupleStacks 0) (tupleStacks 7) (by decide) a remaining
      (Encoding.frame candidate.reverse ++ frames)) candidate frames

noncomputable def recordRepresentativeState (a : State 40 896) : State 40 896 :=
  pushWordState (tupleStacks 4) (tupleStacks 1) (by decide)
    (copyState (tupleStacks 2) (tupleStacks 4) a)

def clearState (src : Fin 896) (a : State 40 896) : State 40 896 :=
  ⟨readRegs a.regs 0 1 none, Function.update a.stacks src []⟩

def clearWordsState : List (Fin 896) → State 40 896 → State 40 896
  | [], a => a
  | src :: rest, a => clearWordsState rest (clearState src a)

def clearWordsTime : List (Fin 896) → State 40 896 → ℕ
  | [], _ => 0
  | src :: rest, a => 2 * (a.stacks src).length + 3 + clearWordsTime rest (clearState src a)

noncomputable def dropRepresentativeState (a : State 40 896) (word reps : List Bool) :
    State 40 896 :=
  clearState (tupleStacks 4)
    (popWordState (tupleStacks 1) (tupleStacks 4) (by decide) a word reps)

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SignatureTupleProgram
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_SignatureKeyNative
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-!
# One full integer signature on the leaf ABI

All port numbers here are leaf-local. The actual key-only machine preserves
the assignment, shifted matrix and every unrelated caller word; it has no
predecessor, countdown, or signature-table input.
-/

namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SignatureKeyNative

open BitProgram StructuredCalls AttainedSignatureProgram
open OAI.Algorithms.SubexponentialSAT.SqrtLog.BucketProgram OAI.Algorithms.SubexponentialSAT.Subexp.MatrixProgramSupport

structure Ready (a : State 40 896) (W bits : List Bool)
    (rows : List (List (List Bool))) : Prop where
  offset : a.stacks (stackPorts 0) = W
  assignment : a.stacks (stackPorts 12) = bits
  output : a.stacks (stackPorts 14) = []
  matrix : a.stacks (stackPorts 15) = words (rows.map words)
  scratch : ∀ i : Fin 16, i ≠ 0 → i ≠ 12 → i ≠ 14 → i ≠ 15 →
    a.stacks (stackPorts i) = []

noncomputable def outputState (a : State 40 896) (out : Fin 8 → Bool)
    (W bits : List Bool) (rows : List (List (List Bool))) : State 40 896 :=
  embedState registers stackPorts a (state out W bits rows (signatureValue W bits rows))

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SignatureKeyNative
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_SignatureHeadLoaderCore
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! The fixed head-loader table uses the actual integer entry program. Its
physical matrix view follows LeafHeadSetupProgramHead/MatrixRun exactly, while
its controller emits one matrix and never constructs assignment tables. -/
noncomputable section
namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SignatureHeadLoader
open OAI BitProgram StructuredCalls OAI.Algorithms.SubexponentialSAT.SqrtLog
open OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafHeadSetupProgram
open OAI.Algorithms.SubexponentialSAT.SubexpSetupStorage

def matrixBase (a : Data) : Fin 288 → List Bool := fun i =>
  if i=0 then a.stacks 141 else if i=17 then a.stacks 650 else if i=18 then a.stacks 128 else
  if i=23 then a.stacks 651 else if i=225 then a.stacks 135 else if i=226 then a.stacks 136 else
  if i=227 then a.stacks 640 else if i=228 then a.stacks 641 else if i=229 then a.stacks 140 else
  if i=230 then a.stacks 642 else if i=231 then a.stacks 138 else if i=232 then a.stacks 139 else
  if i=233 then a.stacks 130 else if i=234 then a.stacks 131 else if i=235 then a.stacks 307 else
  if i=236 then a.stacks 132 else []

structure MasterFrame (base b : Data) : Prop where
  stored : ∀ i∈masters,b.stacks i=base.stacks i

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SignatureHeadLoader
end
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_SignatureTupleTraversal
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-!
# Cursor semantics for the attained-signature tuple controller

The cursor stores an attained prefix and one numeric candidate. Suspended
ancestors are first occurrences, so the tree branches over attained keys only.
The traces and finite sums below are mathematical specifications; the actual
controller retains neither a trace nor a family of assignments or tuples.
-/

namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SignatureTupleTraversal

open scoped BigOperators
open SignatureTupleDFS

open Classical

variable {N : ℕ → ℕ} {κ : ℕ → Type*}

/-- Weighted native iterations before the final loop-guard test. This is a
proof relation over actual evaluations, not an executable trace container. -/
inductive Iterations {r s : ℕ} (p : SignatureTupleProgram.Ports r)
    (q : SignatureTupleProgram.Routines r s) :
    ℕ → StructuredProgram.State r s → StructuredProgram.State r s → Prop
  | refl (a) : Iterations p q 0 a a
  | step {a b c n m} : a.regs p.active = true →
      SignatureTupleProgram.Iteration p q n a b → Iterations p q m b c →
      Iterations p q (n + m + 1) a c

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SignatureTupleTraversal
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_SignatureTupleNative
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-!
# Concrete adapters for the attained-signature tuple controller

The cursor primitives are fixed in `SignatureTupleProgram`. This module
installs the actual head loader and predecessor predicate on the shared leaf
ABI, and relates their physical state to the attained-prefix traversal.
-/

namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SignatureTupleNative

open BitProgram StructuredCalls SignatureTupleProgram

def initializeLevelsState (a : State 40 896) : State 40 896 :=
  (StructuredProgram.Atom.set controllerPorts.active true).eval
    ((StructuredProgram.Atom.bnot controllerPorts.leaf 1).eval
      ((StructuredProgram.Atom.peek (tupleStacks 6) 0 1).eval
        (copyState 649 (tupleStacks 9) (copyState 130 (tupleStacks 6) a))))

def initializeFreshState (a : State 40 896) : State 40 896 :=
  (StructuredProgram.Atom.push (rescanStacks 22) 0).eval
    ((StructuredProgram.Atom.set 0 false).eval (clearState (rescanStacks 22) a))

noncomputable def candidateInput (frame : State 40 896) (regs : Fin 16 → Bool)
    (W : List Bool) (rows : List (List (List Bool))) (h : ℕ)
    (candidate : Fin (2 ^ h)) (fresh : Bool) : State 40 896 :=
  embedState rescanRegisters rescanStacks frame
    (AttainedSignatureProgram.Rescan.workState regs W rows
      (ExecCNFTupleEnumeration.fixedBits h candidate) []
      (ExecCNFTupleEnumeration.fixedBits h 0) [] fresh [] [])

noncomputable def candidateOutput (frame : State 40 896) (regs : Fin 16 → Bool)
    (W : List Bool) (rows : List (List (List Bool))) (h : ℕ)
    (candidate : Fin (2 ^ h)) : State 40 896 :=
  embedState rescanRegisters rescanStacks frame
    (AttainedSignatureProgram.Rescan.workState regs W rows
      (ExecCNFTupleEnumeration.fixedBits h candidate)
      (AttainedSignatureProgram.Rescan.naturalKey W rows h candidate)
      (List.replicate h false) []
      (!(AttainedSignatures.duplicateScan
        (AttainedSignatureProgram.Rescan.naturalKey W rows h) candidate candidate)) [] [])


/-- Exact physical data needed by the rescan. The predicate itself supplies
its evaluation; these are byte descriptions of its input tapes. The latch
may initially contain any word because `probeWith` initializes it. -/
structure CandidateReady (a : State 40 896) (W : List Bool)
    (rows : List (List (List Bool))) (h : ℕ) (candidate : Fin (2 ^ h)) : Prop where
  offset : a.stacks (rescanStacks 0) = W
  matrix : a.stacks (rescanStacks 15) =
    Subexp.MatrixProgramSupport.words (rows.map Subexp.MatrixProgramSupport.words)
  current : a.stacks (rescanStacks 16) = ExecCNFTupleEnumeration.fixedBits h candidate
  saved : a.stacks (rescanStacks 17) = []
  predecessor : a.stacks (rescanStacks 18) = ExecCNFTupleEnumeration.fixedBits h 0
  scratch : ∀ i : Fin 24, i ≠ 0 → i ≠ 15 → i ≠ 16 → i ≠ 17 → i ≠ 18 → i ≠ 22 →
    a.stacks (rescanStacks i) = []


section CursorStorage

open SignatureTupleDFS SignatureTupleTraversal

variable (h : ℕ → ℕ) {κ : ℕ → Type*}
  (key : (d : ℕ) → Fin (2 ^ h d) → κ d)

/-- These are actual retained controller words at an attained prefix. The
prefix is proof data, while the run stores only the two framed bit stacks. -/
structure AncestorStorage (levels base depth : ℕ)
    (ancestors : Prefix (Representatives key) depth) (a : State 40 896) : Prop where
  depth_le : depth ≤ levels
  cursors : a.stacks (tupleStacks 0) = cursorFrames h key depth ancestors
  representatives : a.stacks (tupleStacks 1) = representativeFrames h key depth ancestors
  heads : a.stacks (tupleStacks 6) = List.replicate (levels - depth) true
  address : a.stacks (tupleStacks 9) = List.replicate (base + depth) true
  active : a.regs controllerPorts.active = true

structure LeafStorage (levels base : ℕ)
    (ancestors : Prefix (Representatives key) levels) (a : State 40 896) : Prop extends
      AncestorStorage h key levels base levels ancestors a where
  leaf : a.regs controllerPorts.leaf = true
  cleared : ∀ i ∈ currentHeadPorts, a.stacks i = []


end CursorStorage

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SignatureTupleNative
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_QueryStreamFrames
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! Syntactic read and write exclusion for the actual streaming query.
The collector's remaining records and accumulated count stay opaque to the
conditioned query, so replay after changing those words uses the same steps. -/
namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryStreamFrames

open OAI BitProgram StructuredCalls SqrtLog.ProgramTapeReplay
open SignatureTupleProgram SignatureTupleNative

local notation "H" => (fun i : Fin 896 => Fin.val i = 320 ∨ Fin.val i = 322)

structure SafeAvoids (c : Cmd 40 896) : Prop where
  proof : AvoidsCmd H c

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryStreamFrames
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_QuerySelectorFrames
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! The conditioned query also excludes the entire retained selector bank.
This accounts for arbitrary incumbent and remaining-round words in the
actual greedy callback's time quantifiers. -/
namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QuerySelectorFrames

open OAI BitProgram StructuredCalls SqrtLog.ProgramTapeReplay
open SignatureTupleProgram SignatureTupleNative

local notation "H" => (fun i : Fin 896 => 768 ≤ Fin.val i ∧ Fin.val i ≤ 831)

structure SafeAvoids (c : Cmd 40 896) : Prop where
  proof : AvoidsCmd H c

open OAI.Algorithms.SubexponentialSAT.SubexpSetupStorage

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QuerySelectorFrames
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_HighQueryProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! Fixed finite syntax for both marked and final accepted queries. The only
program parameter is the fixed clause width. Every mark regenerates its own
physical high mask and zero counter. The semantic proof must establish that
the actual frontend guard holds on every reachable input. -/
namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighQueryProgram

open OAI BitProgram StructuredCalls HighQueryAdapter
noncomputable section

open HashGreedyProgram.NativeRound

namespace Carried

open SqrtLog.ProgramTapeReplay

local notation "H" => (fun i : Fin 896 => i ∈ words)

structure SafeAvoids (c : Cmd 40 896) : Prop where
  proof : AvoidsCmd H c

attribute [local irreducible] HashMarkedReturn.upperClear

end Carried

end
end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighQueryProgram
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_SparseCodeSearch
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SparseCodeSearch

open BitProgram StructuredCalls CodeCandidateProgram


/-- Logical invariant of actual stored data. Only the counter and its scratch
are excluded from the boundary bound because their exact shapes are supplied
by the iterator. A saved tuple certifies the retained physical matrix. -/
structure Invariant (matrix : Fin 48) (Ready : State 16 48 → Prop)
    (Good : List Bool → Prop) (base : State 16 48) (B : ℕ) (a : State 16 48) : Prop where
  ready : Ready a
  bound : ∀ i, i ≠ 40 → i ≠ 41 → (a.stacks i).length ≤ B
  sound : a.stacks 42 ≠ [] → Good (a.stacks matrix)
  frame : ∀ i, i ≠ matrix → i ≠ 40 → i ≠ 41 → i ≠ 42 → a.stacks i = base.stacks i


open OAI.Algorithms.SubexponentialSAT.SqrtLog OAI.Algorithms.SubexponentialSAT.SqrtLog.CodeSearchProgram CodeChecks

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SparseCodeSearch
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_NativeLeafStartup
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! Actual loaded-leaf startup and canonical saved selector parameters. -/

namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeLeafSetup

open BitProgram StructuredCalls SqrtLog SqrtLog.LeafOuterProgram

/-- Save the selector parameters and physically replace both row widths by
its canonical modulus word before any code rows are serialized. -/
def saveCanonical : Cmd 40 896 :=
  .seq HashGreedyProgram.Initialize.command NativeLeaf.canonicalRowWidth

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeLeafSetup
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_NativeLeafPreparation
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! Actual physical preparation of the streamed greedy selector. The final
suffix clears the argmin bank, preserves the serialized code history, and
constructs the single retained zero candidate using the runtime depth word. -/
namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeLeafPreparation

open BitProgram StructuredCalls SqrtLog SqrtLog.LeafOuterProgram
open HashGreedyProgram

/-- This runs after actual serialization, while the saved modulus and round
words are still intact. It neither repeats parameter arithmetic nor searches. -/
def afterCode : Cmd 40 896 :=
  .seq Initialize.finishSetup
    (.seq Initialize.zeroCommand (.call (StackRoutines.clearProgram 779 0 1)))

/-- Physical entry condition for the streamed selector. Every field records
an actual stack word; none supplies an evaluator, trace, or resource oracle. -/
structure Ready (n m B : ℕ) (initial : List (List Bool)) (a : Data) : Prop where
  worker : WorkerEmpty a
  core : ∀ i ∈ Initialize.corePorts, a.stacks i = []
  history : a.stacks 777 = encodedHistory initial
  counter : a.stacks 778 = Encoding.encodeList id
    [List.replicate (HashCandidates.payloadWidth m (SparseCode.distanceDenom m B)) false]
  scratch : a.stacks 779 = []
  modulus : BinaryArithmetic.toNat (a.stacks 780) = 3 * m
  modulus_length : (a.stacks 780).length = HashCandidates.digitWidth m
  rounds : a.stacks 781 = List.replicate (HashSelect.loopCap n m) true
  clauses : BinaryArithmetic.toNat (a.stacks 782) = m
  width : a.stacks 783 = a.stacks 780
  depth : BinaryArithmetic.toNat (a.stacks 817) = SparseCode.distanceDenom m B
  shape : a.stacks 818 = List.replicate (HashSelect.loopCap n m) true

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeLeafPreparation
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_QueryTopFrame
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! The actual conditioned stream never reads, peeks or writes stack895.
The fixed source-table, factor, head, loader and controller maps are checked
explicitly; no callback footprint or successful execution is assumed. -/

namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryTopFrame

open OAI BitProgram StructuredCalls SqrtLog.ProgramTapeReplay
open SignatureTupleProgram SignatureTupleNative

local notation "H" => (fun i : Fin 896 => Fin.val i = 895)

structure SafeAvoids (c : Cmd 40 896) : Prop where
  proof : AvoidsCmd H c


open OAI.Algorithms.SubexponentialSAT.SubexpSetupStorage

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryTopFrame
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_QueryKeptFrame
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! Concrete preservation of the retained interval744..767 by the fixed
conditioned query. Every certificate examines actual call ports. -/

namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryKeptFrame

open OAI BitProgram StructuredCalls SqrtLog.ProgramTapeReplay
open SignatureTupleProgram SignatureTupleNative

local notation "H" => (fun i : Fin 896 => 744 ≤ Fin.val i ∧ Fin.val i < 768)

structure SafeAvoids (c : Cmd 40 896) : Prop where
  proof : AvoidsCmd H c

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryKeptFrame
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_SignatureTupleRefinement
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! Actual state refinements for the fixed attained-signature controller.
Each lemma follows concrete commands already installed in the native ABI. -/

namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SignatureTupleRefinement

open BitProgram StructuredCalls SignatureTupleProgram SignatureTupleNative
open SignatureTupleDFS SignatureTupleTraversal

noncomputable def retainedState (a : State 40 896) : State 40 896 :=
  saveCursorState (recordRepresentativeState a)

noncomputable def descendClearState (a : State 40 896) : State 40 896 :=
  clearWordsState currentHeadPorts (descendLevelState (retainedState a))


noncomputable def rootAscendState (a : State 40 896) : State 40 896 :=
  testParentState (clearWordsState currentHeadPorts a)


noncomputable def initialClearState (a : State 40 896) : State 40 896 :=
  clearWordsState (List.ofFn tupleStacks) a

noncomputable def initialControlState (a : State 40 896) : State 40 896 :=
  initializeLevelsState (initialClearState a)

section ParentReturn

variable (h : ℕ → ℕ) {κ : ℕ → Type*}
  (key : (d : ℕ) → Fin (2 ^ h d) → κ d)

noncomputable def parentWordsState (depth : ℕ)
    (ancestors : Prefix (Representatives key) (depth + 1)) (a : State 40 896) : State 40 896 :=
  restoreCursorState
    (dropRepresentativeState (rootAscendState a)
      (ExecCNFTupleEnumeration.fixedBits (h depth) (ancestors (Fin.last depth)).val.val)
      (representativeFrames h key depth (Fin.init ancestors)))
    (ExecCNFTupleEnumeration.fixedBits (h depth) (ancestors (Fin.last depth)).val.val)
    (ExecCNFTupleEnumeration.fixedBits (h depth + 1)
      (2 ^ h depth - (ancestors (Fin.last depth)).val.val))
    (cursorFrames h key depth (Fin.init ancestors))

noncomputable def parentReturnState (depth : ℕ)
    (ancestors : Prefix (Representatives key) (depth + 1)) (a : State 40 896) : State 40 896 :=
  ascendLevelState (parentWordsState h key depth ancestors a)

end ParentReturn


end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SignatureTupleRefinement
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_QueryPairControlFrame
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! The actual emitted-pair callback excludes reads, peeks and writes on832/833.
The mask words834/835 remain real callback inputs. This certificate does not
cover the enclosing pair controller, which operates on its own traversal words. -/

namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryPairControlFrame

open OAI BitProgram StructuredCalls SqrtLog.ProgramTapeReplay
open SignatureTupleProgram SignatureTupleNative

local notation "H" => (fun i : Fin 896 => (Fin.val i = 832 ∨ Fin.val i = 833))

structure SafeAvoids (c : Cmd 40 896) : Prop where
  proof : AvoidsCmd H c


open OAI.Algorithms.SubexponentialSAT.SubexpSetupStorage

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryPairControlFrame
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_QueryNodeEvaluation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! Concrete initialization of a node evaluation. The paid node read, layout
load, native cache bootstrap and pair setup are the fixed commands used by the
streaming query; no evaluator is supplied to these constructions. -/
namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryNodeEvaluation

open OAI BitProgram StructuredCalls SqrtLog SubexpSetupStorage
open LeafHeadSetupProgram QueryTupleState

abbrev Code := Cmd 40 896

open LeafParametersProgram LeafProgram LeafProgram.PreparedSource

open SubexpLiftRing SubexpQuarticRing
open scoped BigOperators


end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryNodeEvaluation
end


