-- Prove2me | Definitions.Def_OAIQ081S069
-- name    : OAIQ081S069
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-29T21:53:34.412925+00:00
-- url     : https://prove2.me/theorems/cbae4a66-2d97-4bfd-9a62-8e926b9b1ca1
-- title:
--   Definitions bundle OAIQ081S069 of the split of OpenAI, The Exponential Time Hypothesis is False
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.exact_count_and_sat`, carved from OpenAI's openai/math development (OpenAI, *The Exponential Time Hypothesis is False*, OpenAI Math Release, October 25, 2026, result family 378, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 95 declarations of OpenAI's Lean: 55 definitions and 40 theorems. The definitions and types are `OAI.Algorithms.SubexponentialSAT.SqrtLog.CodeRowsProgram.Compare.command`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.CodeRowsProgram.Compare.core`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.CodeRowsProgram.Compare.program`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.CodeSearchProgram.graphCountsCommand`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.CodeSearchProgram.graphWordCommand`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.CodeSearchProgram.graphWordProgram`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.CodeSearchProgram.wordCommand`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.CodeSearchProgram.wordProgram`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.CodeSearchWalshProgram.arithmetic`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.CodeSearchWalshProgram.command`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.CodeSearchWalshProgram.prepare`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.HashCircuitProgram.Constant.program`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.HashScopeProgram.MarkedFrame.command`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.HashScopeProgram.MarkedFrame.emit`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.HashScopeProgram.RawFrame.command`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.HashScopeProgram.RawFrame.emit`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.HashSelectProgram.parse`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.HashSelectProgram.state`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.HashSelectProgram.update`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.HashSelectProgram.updateProgram`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.HeadScatterProgram.finishWidth`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.HeadScatterProgram.initCommand`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.HeadScatterProgram.scanBody`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.HeadScatterProgram.scanCommand`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.HeadScatterProgram.scanLoop`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.HeadScatterProgram.scatterStep`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearchBootstrap.totalCost`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearchCandidateControl.candidateCost`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearchCandidateControl.searchCost`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearchFactorControl.factorRecords`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearchFactorControl.pairEncode`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearchFactorControl.scanCost`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearchProgram.paddedPrefix`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafParameterArithmetic.quotientAt`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.MomentsProgram.Product.keyPhase`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.Setup.logSucc`, `OAI.Algorithms.SubexponentialSAT.Subexp.MatrixProgram.dot`, `OAI.Algorithms.SubexponentialSAT.Subexp.MatrixProgram.dotBody`, `OAI.Algorithms.SubexponentialSAT.Subexp.MatrixProgram.dotLoop`, `OAI.Algorithms.SubexponentialSAT.Subexp.MatrixProgram.dotProgram` and 15 more.
--
--   **Sources.** They come from these modules of lean/OAI/Algorithms, in whole or in part: `SubexponentialSAT_SqrtLog_CodeRowsProgramCompare`, `SubexponentialSAT_SqrtLog_CodeSearchProgramGraphCounts`, `SubexponentialSAT_SqrtLog_CodeSearchProgramGraphWord`, `SubexponentialSAT_SqrtLog_CodeSearchProgramWord`, `SubexponentialSAT_SqrtLog_CodeSearchWalshProgram`, `SubexponentialSAT_SqrtLog_CodeSearchWalshProgramArithmetic`, `SubexponentialSAT_SqrtLog_CodeSearchWalshProgramChecks`, `SubexponentialSAT_SqrtLog_HashCircuitProgramConstant`, `SubexponentialSAT_SqrtLog_HashScopeProgramMarkedFrame`, `SubexponentialSAT_SqrtLog_HashScopeProgramRawFrame`, `SubexponentialSAT_SqrtLog_HashSelectProgramCore`, `SubexponentialSAT_SqrtLog_HeadScatterProgram`, `SubexponentialSAT_SqrtLog_HeadScatterProgramInit`, `SubexponentialSAT_SqrtLog_HeadScatterProgramRun`, `SubexponentialSAT_SqrtLog_HeadScatterProgramScan`, `SubexponentialSAT_SqrtLog_IdempotentPreparationProgram`, `SubexponentialSAT_SqrtLog_IdempotentProgramCompleteCost`, `SubexponentialSAT_SqrtLog_IrreducibleSearchBootstrap`, `SubexponentialSAT_SqrtLog_IrreducibleSearchBootstrapCost`, `SubexponentialSAT_SqrtLog_IrreducibleSearchEnumerationCost`, `SubexponentialSAT_SqrtLog_IrreducibleSearchNativeScan`, `SubexponentialSAT_SqrtLog_IrreducibleSearchProgramDot`, `SubexponentialSAT_SqrtLog_IrreducibleSearchProgramPrefix`, `SubexponentialSAT_SqrtLog_IrreducibleSearchProgramScalar`, `SubexponentialSAT_SqrtLog_IrreducibleSearchProgramStorage`, `SubexponentialSAT_SqrtLog_LeafParameterArithmeticQuotient`, `SubexponentialSAT_SqrtLog_MomentsProgramProduct`, `SubexponentialSAT_SqrtLog_RingScanServiceBasic`, `SubexponentialSAT_SqrtLog_SetupPrimitives`, `SubexponentialSAT_SubexpConvolutionPair`, `SubexponentialSAT_SubexpEnumerationProgram`, `SubexponentialSAT_SubexpNodeCost`, `SubexponentialSAT_SubexpOrderedTupleProgram`, `SubexponentialSAT_SubexpSetupStorage`, `SubexponentialSAT_Subexp_MatrixProgram`, `SubexponentialSAT_Subexp_MatrixScalarProgram`, `SubexponentialSAT_Subexp_MatrixVectorProgram`, `SubexponentialSAT_Subexp_PairScoreProgram`, `SubexponentialSAT_Subexp_TupleProgram`.
--
--   **Imports.** It imports the bundles `OAIQ081S045`, `OAIQ081S047`, `OAIQ081S048`, `OAIQ081S049`, `OAIQ081S050`, `OAIQ081S051`, `OAIQ081S052` and `OAIQ081S053` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ081S084`, `OAIQ081S085`, `OAIQ081S086`, `OAIQ081S087`, `OAIQ081S088`, `OAIQ081S092`, `OAIQ081S093`, `OAIQ081S095`, `OAIQ081S096`, `OAIQ081S097` and `OAIQ081S099`; the statements `OAI.Algorithms.SubexponentialSAT.SqrtLog.CodeSearchProgram.matrix_apply_trace` and `OAI.Algorithms.SubexponentialSAT.Subexp.MatrixVectorProgram.matrix_trace`; the proofs of `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.ReconstructionSpace.readback_run_space` and `OAI.Algorithms.SubexponentialSAT.SqrtLog.CodeSearchProgram.matrix_apply_trace`.
-- source:
--   OpenAI, The Exponential Time Hypothesis is False, OpenAI Math Release, October 25, 2026, https://github.com/openai/math (result family 378; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/The-Exponential-Time-Hypothesis-is-False-October-25-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Algorithms at commit 7ef5c0c

import Mathlib
import Definitions.Def_OAIQ081S045
import Definitions.Def_OAIQ081S047
import Definitions.Def_OAIQ081S048
import Definitions.Def_OAIQ081S049
import Definitions.Def_OAIQ081S050
import Definitions.Def_OAIQ081S051
import Definitions.Def_OAIQ081S052
import Definitions.Def_OAIQ081S053

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_Subexp_TupleProgram
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# Fixed-control Cartesian tuple generation

Alphabet words, tuple payloads, and iteration depths are stack data.  The
instruction tables below do not depend on any of their lengths.
-/

namespace SubexponentialSAT.Subexp.TupleProgram

open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls

/-! The fixed ABI uses ten Boolean registers and nine Boolean stacks:
0 prior tuples, 1 saved alphabet, 2 current reversed tuple, 3 alphabet cursor,
4 reversed word, 5 output, 6 copied tuple, 7 copy scratch, 8 unary depth.
Registers 0--2 and 3--5 belong to the two framed iterators, 6--7 are scratch,
and 8--9 belong to the eventual depth loop. -/

theorem readDepth_eval (a : State 10 9) : Eval readDepth 1 a (readDepthState a) := by
  exact .base (.atom _ _)

end SubexponentialSAT.Subexp.TupleProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_CodeRowsProgramCompare
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Preserving binary comparison for filtering the shortened code's columns.
The instruction table uses padding and borrow, with no numeric comparison
primitive and no traversal of the original column universe. -/
namespace SubexponentialSAT.SqrtLog.CodeRowsProgram.Compare
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.BinaryArithmetic SubexponentialSAT.ModularArithmetic
open SubexponentialSAT.SaturatingSubtractionProgram

abbrev core : Cmd 8 8 :=
  .seq prepare (.seq (padAt leftPorts) (.seq (padAt rightPorts)
    (.seq setBorrow (subtractAt subtractPorts))))

abbrev command : Cmd 8 8 :=
  .seq core (.seq (.base (.atom (.copy 7 0))) clearOutput)
abbrev program := compiled command 0 1

end SubexponentialSAT.SqrtLog.CodeRowsProgram.Compare

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_Subexp_PairScoreProgram
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# Aggregating the actual collision streams of all vertex pairs

The fixed program consumes framed pairs of already selected read plans.
Producing those selected plans from original plans and the remaining-index
table is a separate preparation step.  Every pair invokes the actual tuple
generator and collision machine; a final fixed unary tally produces the score.
-/

namespace SubexponentialSAT.Subexp.PairScoreProgram

open BitProgram StackRoutines StructuredCalls

/-- Runtime list framing around the public pair payloads. -/
def pairRecords (pairs : List PlanPair) : List Bool :=
  ProgramEncoding.encodeRecords (pairs.map pairBytes)

@[simp] theorem readPlan_planBytes (plan : List ℕ) :
    readPlan (CollisionStreamProgram.planBytes plan) = plan := by
  simp [readPlan, CollisionStreamProgram.planBytes, GatherProgram.indexRecords,
    List.map_map, Function.comp_def]

end SubexponentialSAT.Subexp.PairScoreProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_Subexp_MatrixScalarProgram
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# Scalar subroutines with the matrix checker's surrounding data preserved

These are calls to the actual finite modular-arithmetic instruction tables.
The eight additional ports carry vector streams, output, and runtime metadata.
-/

namespace SubexponentialSAT.Subexp.MatrixScalarProgram

open BitProgram StructuredCalls BinaryArithmetic ModularRingPrograms
open MatrixProgramSupport

abbrev multiply : Cmd 8 16 :=
  .call (ProgramLinking.liftProgram wordMulProgram id servicePort)

abbrev accumulate : Cmd 8 16 :=
  .seq multiply (.seq (move 8 1 9) (.seq add (move 0 8 9)))

end SubexponentialSAT.Subexp.MatrixScalarProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_Subexp_MatrixProgram
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# Fixed encoded modular dot products

Vectors are streams of framed, fixed-width little-endian scalar words. The
loop reads the two streams itself and calls the measured multiply-add routine.
Its finite control is independent of the modulus, width, and vector length.
-/

namespace SubexponentialSAT.Subexp.MatrixProgram

open BitProgram StructuredCalls BinaryArithmetic
open MatrixProgramSupport MatrixScalarProgram

abbrev term : Cmd 8 16 :=
  .seq (readWord 10 0 9 (by decide))
    (.seq (readWord 11 1 9 (by decide)) accumulate)

abbrev dotBody : Cmd 8 16 := .seq term peekLeft
abbrev dotLoop : Cmd 8 16 := .while 1 dotBody
abbrev dot : Cmd 8 16 := .seq peekLeft dotLoop
def dotProgram := compiled dot 10 8

end SubexponentialSAT.Subexp.MatrixProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_Subexp_MatrixVectorProgram
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! A fixed row controller for encoded matrix-vector multiplication. -/

namespace SubexponentialSAT.Subexp.MatrixVectorProgram

open BitProgram StructuredCalls BinaryArithmetic
open MatrixProgramSupport MatrixScalarProgram MatrixProgram

abbrev row : Cmd 8 16 :=
  .seq (MatrixProgramSupport.copy 12 10 9)
    (.seq (MatrixProgramSupport.copy 14 8 9)
      (.seq (.call dotProgram)
        (.seq (emitFrame 8 0 9 (by decide)) (transfer 0 13))))

abbrev matrixBody : Cmd 8 16 := .seq row popRow
abbrev matrixLoop : Cmd 8 16 := .while 1 matrixBody
abbrev matrixCommand : Cmd 8 16 := .seq popRow (.seq matrixLoop (transfer 13 8))
def matrixProgram := compiled matrixCommand 11 8

end SubexponentialSAT.Subexp.MatrixVectorProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_CodeSearchProgramWord
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! A complete fixed-code test of one proposed short nonzero kernel word.
Matrix and word bytes, the row count, and the distance threshold are runtime
inputs. The protected stack 17 survives the call. -/
namespace SubexponentialSAT.SqrtLog.CodeSearchProgram
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.Subexp
open scoped BigOperators

abbrev wordCommand : Cmd 8 18 :=
  .seq (.call (ProgramLinking.liftProgram MatrixVectorProgram.matrixProgram
    id matrixWordStacks)) wordTailCommand

def wordProgram := compiled wordCommand 11 10

end SubexponentialSAT.SqrtLog.CodeSearchProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_CodeSearchProgramGraphCounts
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Fixed bit-code for one Walsh query up to the scalar inequalities: compute
all dot products mod2, count their support, and recognize the zero character. -/
namespace SubexponentialSAT.SqrtLog.CodeSearchProgram
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.Subexp
open scoped BigOperators

abbrev graphCountsCommand : Cmd 8 18 :=
  .seq (.call (ProgramLinking.liftProgram MatrixVectorProgram.matrixProgram id matrixWordStacks))
    graphCountTail

end SubexponentialSAT.SqrtLog.CodeSearchProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_CodeSearchWalshProgramArithmetic
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.CodeSearchWalshProgram
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.ArithmeticCalls

abbrev arithmetic : Cmd 8 14 := .seq count (.seq (multiplyAt (ports 0))
  (.seq (multiplyAt (ports 1)) (.seq (Subexp.TupleProgram.pushConst 5 0 false)
    (.seq (addAt (ports 2)) (addAt (ports 3))))))

end SubexponentialSAT.SqrtLog.CodeSearchWalshProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_CodeSearchWalshProgramChecks
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.CodeSearchWalshProgram
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls

def prepare : Code := liftCommand arithmetic 0 3 lowRegisters id

end SubexponentialSAT.SqrtLog.CodeSearchWalshProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_CodeSearchWalshProgram
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.CodeSearchWalshProgram
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls

/-- Source-preserving Walsh check. The three inputs are q,D and a unary h word;
all other stacks start and finish empty. The answer is register8. -/
def command : Code := .seq prepare (.seq (.base (.atom (.set 8 true)))
  (.seq (check 0) (.seq (check 1) clearCount)))

end SubexponentialSAT.SqrtLog.CodeSearchWalshProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_CodeSearchProgramGraphWord
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! One complete Walsh query, executed by a fixed program. The inputs contain
an actual binary matrix, a binary character, and binary words for q and D.
No integer inequality is an instruction: the final comparison invokes the
count/arithmetic/guard routine with its measured bit trace. -/
namespace SubexponentialSAT.SqrtLog.CodeSearchProgram
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls
open StructuredProgram (Atom)

abbrev graphWordCommand : Cmd 16 29 :=
  .seq (liftCommand graphCountsCommand 11 9 graphCountRegisters graphCountStacks) <|
  .seq (.base (.atom (.copy 15 7))) <|
  .seq (liftCommand CodeSearchWalshProgram.command 0 0 graphCheckRegisters graphCheckStacks) <|
  .seq (.base (.atom (.bnot 8 8))) (.base (.atom (.band 15 15 8)))

def graphWordProgram := compiled graphWordCommand 11 9

end SubexponentialSAT.SqrtLog.CodeSearchProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_HashCircuitProgramConstant
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Construct a cached sparse constant from a shape word and a forward flat
coefficient. Zero support bits, key delimiters, reversal, record framing and
cleanup all execute on the native bit machine. -/
namespace SubexponentialSAT.SqrtLog.HashCircuitProgram.Constant
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls

def program := compiled command 0 5

end SubexponentialSAT.SqrtLog.HashCircuitProgram.Constant

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_HashScopeProgramMarkedFrame
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.HashScopeProgram.MarkedFrame
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.Subexp.TupleProgram

abbrev emit : Cmd 11 80 := .seq (pushConst 48 8 false)
  (.seq (escape ports) (pushConst 48 8 true))

abbrev command : Cmd 11 80 := .seq emit fix

end SubexponentialSAT.SqrtLog.HashScopeProgram.MarkedFrame

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_HashScopeProgramRawFrame
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.HashScopeProgram.RawFrame
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.Subexp.TupleProgram

abbrev emit : Cmd 11 49 := .seq (pushConst 48 8 false)
  (.seq (escape ports) (pushConst 48 8 true))

abbrev command : Cmd 11 49 := .seq emit fix

end SubexponentialSAT.SqrtLog.HashScopeProgram.RawFrame

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_HashSelectProgramCore
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Fixed-port binary argmin calls and a parser for unevaluated candidate
payloads. The scores are absent from the input encoding. All supplied commands
are actual finite programs; semantic scores are never atomic instructions. -/

namespace SubexponentialSAT.SqrtLog.HashSelectProgram

open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls

noncomputable def state {r s : ℕ} (p : Ports r s) (frame : State r s)
    (regs : Fin 8 → Bool) (next best : Entry) (queue : List Bool) : State r s :=
  embedState p.register p.stack frame (BinaryArgmin.data regs next best queue)

@[simp] theorem state_register {r s : ℕ} (p : Ports r s) (frame : State r s)
    (regs : Fin 8 → Bool) (next best : Entry) (queue : List Bool) (i : Fin 8) :
    (state p frame regs next best queue).regs (p.register i) = regs i :=
  embedState_register _ _ _ _ p.register_injective i

@[simp] theorem state_stack {r s : ℕ} (p : Ports r s) (frame : State r s)
    (regs : Fin 8 → Bool) (next best : Entry) (queue : List Bool) (i : Fin 9) :
    (state p frame regs next best queue).stacks (p.stack i) =
      BinaryArgmin.store next best queue i :=
  embedState_stack _ _ _ _ p.stack_injective i

def updateProgram := compiled BinaryArgmin.update 8 2

abbrev update {r s : ℕ} (p : Ports r s) : Cmd r s :=
  .call (ProgramLinking.liftProgram updateProgram p.register p.stack)

abbrev parse {r s : ℕ} (p : Ports r s) : Cmd r s :=
  .call (ProgramLinking.liftProgram parserProgram p.register p.stack)

end SubexponentialSAT.SqrtLog.HashSelectProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_HeadScatterProgram
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Runtime scatter of head bits into the original ambient coordinate order.
Coordinate identifiers are framed unary words; array replacement is a genuine
runtime scan. No coordinate permutation is compiled into the instruction table. -/
namespace SubexponentialSAT.SqrtLog.HeadScatterProgram

open SubexponentialSAT BitProgram StructuredCalls Subexp.MatrixProgramSupport

def scatterStep : Code :=
  .seq popIndexTag (.seq (readFrame 2 3 (by decide))
    (.seq popBit (.seq pushBit (.seq replaceBit clearBit))))

end SubexponentialSAT.SqrtLog.HeadScatterProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_HeadScatterProgramInit
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.HeadScatterProgram
open SubexponentialSAT BitProgram StructuredCalls

def initCommand : Code :=
  .seq (.call (StackRoutines.copyProgram 10 2 3 (0 : Fin 8) 1))
    (.seq (.call (StackRoutines.copyProgram 11 1 3 (0 : Fin 8) 1))
      (.seq (.call (StackRoutines.copyProgram 12 3 4 (0 : Fin 8) 1))
        (.seq (.call zeroProgram) (Subexp.TupleProgram.pushConst 5 0 true))))

end SubexponentialSAT.SqrtLog.HeadScatterProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_HeadScatterProgramScan
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.HeadScatterProgram
open SubexponentialSAT BitProgram StructuredCalls

def scanBody : Code := .seq scatterStep peekBits
def scanLoop : Code := .while 1 scanBody
def scanCommand : Code := .seq peekBits scanLoop

end SubexponentialSAT.SqrtLog.HeadScatterProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_HeadScatterProgramRun
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.HeadScatterProgram
open SubexponentialSAT BitProgram StructuredCalls

def finishWidth : Code := WorkspaceCleanupProgram.command 0 1 [2,5]

end SubexponentialSAT.SqrtLog.HeadScatterProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_SetupPrimitives
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Actual fixed bit programs for the two logarithmic setup quantities.
Input and output numbers are arbitrary padded little-endian words. -/
namespace SubexponentialSAT.SqrtLog.Setup

open BitProgram StructuredCalls
open CounterPrograms (value ripple)

/-- The floor binary logarithm plus one, with zero mapped to one. -/
abbrev logSucc : Cmd 3 3 := .seq logarithm increment

end SubexponentialSAT.SqrtLog.Setup

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_RingScanServiceBasic
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Shared native coefficient-ring ABI. All service programs have fixed size. -/
namespace SubexponentialSAT.SqrtLog.RingScan
open BitProgram StructuredCalls StackRoutines
open SubexponentialSAT.SubexpLiftRing SubexponentialSAT.SubexpQuarticRing

theorem servicePrepare_eval (regs : Fin 8 → Bool) (s : ServiceStore) :
    Eval servicePrepare (7*s.table.length+5)
      (serviceWorkState regs {s with tableWork := []})
      (serviceWorkState (readRegs regs 1 3 none) {s with tableWork := s.table}) := by
  have h := serviceCopy_eval (serviceWorkState regs {s with tableWork := []}) 22 20
    (by decide) (by decide) (by decide) (by rfl)
  convert h using 1
  · rfl
  apply congrArg₂ StructuredProgram.State.mk
  · rfl
  · funext i; fin_cases i <;> simp [serviceWorkState, serviceTapes, copyStacks]

end SubexponentialSAT.SqrtLog.RingScan

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_IdempotentPreparationProgram
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! One fixed native preparation command accepts only the runtime binary
precision. It constructs its modulus, scalar cache, table, arrays and counters
with charged bit instructions, ready for the fixed Newton program. -/
namespace SubexponentialSAT.SqrtLog.IdempotentPreparationProgram

open BitProgram StructuredCalls SubexpQuarticRing

theorem preparationBudget_polynomial (t inputWidth : ℕ) :
    preparationBudget t inputWidth ≤ 100000000*(t+inputWidth+2)^4 := by
  simp only [preparationBudget,finishBudget,Scan.tableBudget,Scan.scanBudget,
    RingProgram.ternary_baseWidth]
  nlinarith [Nat.zero_le (t^4),Nat.zero_le (t^3*inputWidth),
    Nat.zero_le (t^2*inputWidth^2),Nat.zero_le (t*inputWidth^3),Nat.zero_le (inputWidth^4),
    Nat.zero_le (t^3),Nat.zero_le (t^2*inputWidth),Nat.zero_le (t*inputWidth^2),
    Nat.zero_le (inputWidth^3),Nat.zero_le (t^2),Nat.zero_le (t*inputWidth),
    Nat.zero_le (inputWidth^2)]

end SubexponentialSAT.SqrtLog.IdempotentPreparationProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_IdempotentProgramCompleteCost
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! An explicit polynomial primitive-time envelope for native preparation
and all Newton iterations, as a function of precision and input length. -/
namespace SubexponentialSAT.SqrtLog.IdempotentProgram

open BitProgram

theorem completeBudget_polynomial (t inputWidth : ℕ) :
    completeBudget t inputWidth ≤ polynomialBudget t inputWidth := by
  have hp:=IdempotentPreparationProgram.preparationBudget_polynomial t inputWidth
  have ha:=arithmeticBudget_polynomial (SubexpLiftRing.baseWidth 3 t) (3*t)
  rw [RingProgram.ternary_baseWidth] at ha
  have hl:=binaryClog_le t
  unfold completeBudget nativeLiftBudget polynomialBudget
  rw [RingProgram.ternary_baseWidth]
  calc
    _ ≤ 100000000*(t+inputWidth+2)^4 +
        (7*t*(41000*(3*t+1)^3*(2*t+1)^2)+
          (t+1)*(16*(inputWidth+1)+16)+1)+1 := by gcongr
    _ = _ := by omega

end SubexponentialSAT.SqrtLog.IdempotentProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SubexpNodeCost
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! # A polynomial instruction bound for the fixed four-coordinate node program -/

namespace SubexponentialSAT.SubexpNodeCost

open Subexp.TupleProgram

theorem tupleCost_eq (alphabet : List (List Bool)) (word : List Bool) :
    tupleCost alphabet word = (12 * alphabet.length + 2) * word.length +
      (25 * payloadSize alphabet + 36 * alphabet.length + 18) := by
  have hb : RecordPrograms.budget (fun x => 5 * x.length + 12 * word.length + 15) alphabet =
      (5 + 6) * payloadSize alphabet + (12 * word.length + 15 + 7) * alphabet.length := by
    simpa only [Nat.add_assoc] using budget_affine alphabet 5 (12 * word.length + 15)
  rw [tupleCost, ProgramEncoding.encodeRecords_length, hb]
  change 7 * (2 * payloadSize alphabet + 2 * alphabet.length + 1) +
    ((5 + 6) * payloadSize alphabet + (12 * word.length + 15 + 7) * alphabet.length) +
      2 * word.length + 11 = _
  ring

theorem expansionCost_eq (rows alphabet : List (List Bool)) :
    expansionCost rows alphabet = 3 + (12 * alphabet.length + 8) * payloadSize rows +
      (25 * payloadSize alphabet + 36 * alphabet.length + 25) * rows.length := by
  have h : tupleCost alphabet = fun word => (12 * alphabet.length + 2) * word.length +
      (25 * payloadSize alphabet + 36 * alphabet.length + 18) := funext (tupleCost_eq alphabet)
  rw [expansionCost, h, budget_affine]
  ring

end SubexponentialSAT.SubexpNodeCost

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SubexpOrderedTupleProgram
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# Fixed-depth ordered tuple generation

The programs at depths two and four have fixed finite instruction tables.
Each Cartesian expansion is followed by the actual record reversal routine,
so the output order agrees exactly with QuarticSearch.vectors.
-/

namespace SubexponentialSAT.SubexpOrderedTupleProgram

open BitProgram StructuredCalls Subexp.TupleProgram SubexpOrderedTupleData

theorem stepCost_eq (rows alphabet : List (List Bool)) :
    SubexpOrderedTupleStep.stepCost rows alphabet =
      17 + (32 * alphabet.length + 8) * SubexpNodeCost.payloadSize rows +
        (45 * SubexpNodeCost.payloadSize alphabet + 56 * alphabet.length + 25) * rows.length := by
  rw [SubexpOrderedTupleStep.stepCost, SubexpNodeCost.expansionCost_eq,
    ProgramEncoding.encodeRecords_length]
  change _ + 10 * (2 * SubexpNodeCost.payloadSize (cartesianOutput rows alphabet) +
    2 * (cartesianOutput rows alphabet).length + 1) + 4 = _
  rw [SubexpNodeCost.payloadSize_cartesian, cartesianOutput_length]
  ring

end SubexponentialSAT.SubexpOrderedTupleProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_IrreducibleSearchEnumerationCost
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.IrreducibleSearchEnumeration

open SubexpOrderedTupleData Subexp.PairScoreBounds SubexpEnumerationPayload

theorem ordered_step_le (rows alphabet : List (List Bool)) (L W : ℕ)
    (hr : ∀ row ∈ rows, row.length ≤ L)
    (ha : ∀ row ∈ alphabet, row.length ≤ W) :
    SubexpOrderedTupleStep.stepCost rows alphabet + 2 ≤
      200 * (rows.length + 1) * (alphabet.length + 1) * (L + W + 1) := by
  have hv := volume_le rows L hr
  have hu := volume_le alphabet W ha
  rw [SubexpOrderedTupleProgram.stepCost_eq]
  change 17 + (32 * alphabet.length + 8) * volume rows +
    (45 * volume alphabet + 56 * alphabet.length + 25) * rows.length + 2 ≤ _
  calc
    _ = 19 + (32 * alphabet.length + 8) * volume rows +
        (45 * volume alphabet + 56 * alphabet.length + 25) * rows.length := by ring
    _ ≤ 19 + (32 * alphabet.length + 8) * (rows.length * L) +
        (45 * (alphabet.length * W) + 56 * alphabet.length + 25) * rows.length := by
      gcongr
    _ ≤ _ + (168 * rows.length * alphabet.length * L + 155 * rows.length * alphabet.length * W +
        144 * rows.length * alphabet.length + 192 * rows.length * L + 200 * rows.length * W +
        175 * rows.length + 200 * alphabet.length * L + 200 * alphabet.length * W +
        200 * alphabet.length + 200 * L + 200 * W + 181) := Nat.le_add_right _ _
    _ = _ := by ring

theorem powerCost_le (alphabet rows : List (List Bool)) (n L W : ℕ)
    (hA : 1 ≤ alphabet.length)
    (hr : ∀ row ∈ rows, row.length ≤ L)
    (ha : ∀ row ∈ alphabet, row.length ≤ W) :
    powerCost alphabet n rows ≤
      400 * (n + 1) * (rows.length + 1) * alphabet.length ^ n * (L + n * W + W + 1) := by
  induction n generalizing rows L with
  | zero =>
    simp only [powerCost, Nat.zero_add, pow_zero, Nat.mul_one, Nat.zero_mul]
    nlinarith
  | succ n ih =>
    have hi := ih (orderedCartesian rows alphabet) (L + W)
      (cartesian_width rows alphabet L W hr ha)
    rw [orderedCartesian_length] at hi
    have hs := ordered_step_le rows alphabet L W hr ha
    have hA' : alphabet.length + 1 ≤ 2 * alphabet.length := by omega
    have hs' : SubexpOrderedTupleStep.stepCost rows alphabet + 2 ≤
        400 * (rows.length + 1) * alphabet.length * (L + W + 1) := by
      calc
        _ ≤ 200 * (rows.length + 1) * (alphabet.length + 1) * (L + W + 1) := hs
        _ ≤ 200 * (rows.length + 1) * (2 * alphabet.length) * (L + W + 1) := by gcongr
        _ = _ := by ring
    have hpow : alphabet.length ≤ alphabet.length ^ (n + 1) := by
      simpa only [pow_one] using pow_le_pow_right₀ hA (show 1 ≤ n + 1 by omega)
    have hwidth : L + W + 1 ≤ L + (n + 1) * W + W + 1 := by nlinarith
    have hstep : SubexpOrderedTupleStep.stepCost rows alphabet + 2 ≤
        400 * (rows.length + 1) * alphabet.length ^ (n + 1) *
          (L + (n + 1) * W + W + 1) := by
      exact hs'.trans (by gcongr)
    have hrA : rows.length * alphabet.length + 1 ≤ (rows.length + 1) * alphabet.length := by
      nlinarith
    have hrec : powerCost alphabet n (orderedCartesian rows alphabet) ≤
        400 * (n + 1) * (rows.length + 1) * alphabet.length ^ (n + 1) *
          (L + (n + 1) * W + W + 1) := by
      calc
        _ ≤ 400 * (n + 1) * (rows.length * alphabet.length + 1) * alphabet.length ^ n *
            (L + W + n * W + W + 1) := hi
        _ ≤ 400 * (n + 1) * ((rows.length + 1) * alphabet.length) * alphabet.length ^ n *
            (L + W + n * W + W + 1) := by gcongr
        _ = _ := by rw [pow_succ]; ring
    rw [powerCost]
    have hsum := Nat.add_le_add hstep hrec
    nlinarith

theorem generated_powerCost_le (alphabet : List (List Bool)) (n W : ℕ)
    (hA : 1 ≤ alphabet.length) (ha : ∀ row ∈ alphabet, row.length ≤ W) :
    powerCost alphabet n [[]] ≤
      800 * (n + 1) * alphabet.length ^ n * ((n + 1) * W + 1) := by
  have h := powerCost_le alphabet [[]] n 0 W hA (by simp) ha
  calc
    _ ≤ 400 * (n + 1) * ([[]] : List (List Bool)).length.succ * alphabet.length ^ n *
        (0 + n * W + W + 1) := h
    _ = _ := by simp only [List.length_cons, List.length_nil, Nat.succ_eq_add_one]; ring

theorem cost_le (d : ℕ) : cost d ≤
    800 * (d + 1) * 3 ^ d * ((d + 1) * scalarWidth 3 + 1) + 9 := by
  have h := generated_powerCost_le alphabet d (scalarWidth 3)
    (by simp) (by
      intro row hrow
      obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hrow
      exact le_of_eq ((scalarCode 3).length_block x))
  simpa only [cost, alphabet_length] using Nat.add_le_add_right h 9

end SubexponentialSAT.SqrtLog.IrreducibleSearchEnumeration

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_IrreducibleSearchProgramScalar
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# Fixed truth-table arithmetic for the irreducible search over F₃

The six input bits select one of 64 *static* leaves. No parameter of the
polynomial search occurs in this instruction table. The two output bits
encode the multiply-add `s + a*b` in the same two-bit scalar format as the
audited tuple generator.
-/
namespace SubexponentialSAT.SqrtLog.IrreducibleSearchProgram

open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredProgram

theorem scalarBits_encoding (a : IrreducibleSearch.F) :
    [(scalarBits a).1, (scalarBits a).2] =
      SubexpEnumerationPayload.scalarBits a :=
  by
    have hw : SubexpEnumerationPayload.scalarWidth 3 = 2 := by
      have hl : Nat.log 2 3 = 1 := Nat.log_eq_of_pow_le_of_lt_pow (by norm_num) (by norm_num)
      simp only [SubexpEnumerationPayload.scalarWidth, hl]
    unfold SubexpEnumerationPayload.scalarBits
    rw [hw]
    fin_cases a <;> decide

end SubexponentialSAT.SqrtLog.IrreducibleSearchProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_IrreducibleSearchProgramStorage
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Paid preserving access to the search's coefficient arrays. The address
is a unary input stack, never a program parameter; every access uses the
same 38-label program. The source and scalar width are restored. -/
namespace SubexponentialSAT.SqrtLog.IrreducibleSearchProgram

open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredProgram

theorem coefficientArray_ofFn {d : ℕ} (a : Fin d → IrreducibleSearch.F) :
    coefficientArray (List.ofFn a) =
      SubexpTupleRefinement.encodeTuple (SubexpEnumerationPayload.scalarCode 3) a := rfl

end SubexponentialSAT.SqrtLog.IrreducibleSearchProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_IrreducibleSearchProgramDot
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! A fixed bit program for the dynamically long F₃ dot product. Every
coefficient is physically read and every multiply-add uses the static
64-entry bit table. The source arrays are consumed. -/
namespace SubexponentialSAT.SqrtLog.IrreducibleSearchProgram

open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredProgram

@[simp] theorem coefficientWord_eq (a : IrreducibleSearch.F) :
    coefficientWord a = [(scalarBits a).1, (scalarBits a).2] :=
  (scalarBits_encoding a).symm

end SubexponentialSAT.SqrtLog.IrreducibleSearchProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_IrreducibleSearchProgramPrefix
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Runtime-length padded prefixes, with reversal by coefficient rather
than by bit. This is the physical stream preparation needed before a
convolution dot product. A unary count controls one fixed eight-label
program; exhaustion of the coefficient source supplies the zero cell. -/
namespace SubexponentialSAT.SqrtLog.IrreducibleSearchProgram

open SubexponentialSAT.BitProgram

def paddedPrefix : ℕ → List IrreducibleSearch.F → List IrreducibleSearch.F
  | 0, _ => []
  | n + 1, as => as.headD 0 :: paddedPrefix n as.tail

@[simp] theorem paddedPrefix_length (n : ℕ) (as : List IrreducibleSearch.F) :
    (paddedPrefix n as).length = n := by
  induction n generalizing as with
  | zero => rfl
  | succ n ih => simp [paddedPrefix, ih]

end SubexponentialSAT.SqrtLog.IrreducibleSearchProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SubexpSetupStorage
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# Physical storage operations for the closed parameter setup

All copies, clears, and register resets are fixed instruction sequences or
calls to proved bit programs. Their state transformations below are assertion
notation only. The setup program uses them to isolate dirty arithmetic
subroutines from the persistent parameter words.
-/

namespace SubexponentialSAT.SubexpSetupStorage

open BitProgram StructuredCalls

def prepare {S : ℕ} (tmp : Fin S) (ports : List (Fin S))
    (inputs : List (Fin S × Fin S)) : Command S :=
  .seq (clearMany [tmp]) (.seq (clearMany ports) (.seq resetWork (copyMany tmp inputs)))

def finish {S : ℕ} (tmp : Fin S) (ports : List (Fin S))
    (outputs : List (Fin S × Fin S)) : Command S :=
  .seq (clearMany (outputs.map Prod.snd))
    (.seq (copyMany tmp outputs) (.seq (clearMany ports) resetWork))

abbrev isolated {r s l S : ℕ} (p : Program r s l)
    (register : Fin r → Fin 16) (stack : Fin s → Fin S)
    (tmp : Fin S) (ports : List (Fin S))
    (inputs outputs : List (Fin S × Fin S)) : Command S :=
  .seq (prepare tmp ports inputs)
    (.seq (invoke p register stack) (finish tmp ports outputs))

end SubexponentialSAT.SubexpSetupStorage

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_IrreducibleSearchNativeScan
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Fixed native irreducible-polynomial search: concrete factor callbacks,
saved universal scans, exact ordered candidate selection, and measured cost. -/

/-! A fixed factor-pair callback and universal scan. All checker arithmetic,
record extraction, array splitting, and cleanup use explicit bit programs. -/
namespace SubexponentialSAT.SqrtLog.IrreducibleSearchFactorControl

open BitProgram StructuredCalls IrreducibleSearchProgram
open Subexp.BlockSearchPreparation (restrictState )
attribute [local simp] Fin.addCases Fin.coe_ofNat_eq_mod

def pairEncode {d : ℕ}
    (ab : (Fin (d + 1) → IrreducibleSearch.F) × (Fin (d + 1) → IrreducibleSearch.F)) : List Bool :=
  coefficientArray (List.ofFn ab.1 ++ List.ofFn ab.2)

def factorRecords (d : ℕ) : List (List Bool) :=
  (IrreducibleSearch.factorPairs d).map pairEncode

def scanCost (d : ℕ) : ℕ :=
  9 * (ProgramEncoding.encodeRecords (factorRecords d)).length +
    RecordPrograms.budget (fun _ => 15000 * (d + 1)^2 + 2) (factorRecords d) + 14

end SubexponentialSAT.SqrtLog.IrreducibleSearchFactorControl

namespace SubexponentialSAT.SqrtLog.IrreducibleSearchFactorControl

open IrreducibleSearchProgram

@[simp] theorem factorRecords_length (d : ℕ) :
    (factorRecords d).length = 3 ^ (2 * (d + 1)) := by
  simp [factorRecords]

theorem factorRecords_volume (d : ℕ) :
    ((factorRecords d).map List.length).sum =
      4 * (d + 1) * 3 ^ (2 * (d + 1)) := by
  have he : (fun ab : (Fin (d + 1) → IrreducibleSearch.F) ×
      (Fin (d + 1) → IrreducibleSearch.F) => (pairEncode ab).length) =
      (fun _ => 4 * (d + 1)) := by
    funext ab
    simp only [pairEncode, coefficientArray_length, List.length_append, List.length_ofFn]
    omega
  rw [factorRecords, List.map_map]
  change ((IrreducibleSearch.factorPairs d).map (fun ab => (pairEncode ab).length)).sum = _
  rw [he]
  simp only [List.map_const', List.sum_replicate, smul_eq_mul, IrreducibleSearch.length_factorPairs]
  ring

theorem scanCost_eq (d : ℕ) : scanCost d =
    (15000 * (d + 1)^2 + 96 * (d + 1) + 27) * 3 ^ (2 * (d + 1)) + 23 := by
  rw [scanCost, ProgramEncoding.encodeRecords_length, RecordPrograms.budget_eq,
    factorRecords_volume, factorRecords_length]
  simp only [List.map_const', List.sum_replicate, smul_eq_mul, factorRecords_length]
  ring

theorem scanCost_le (d : ℕ) : scanCost d ≤
    16000 * (d + 1)^2 * 3 ^ (2 * (d + 1)) + 23 := by
  rw [scanCost_eq]
  have hc : 15000 * (d + 1)^2 + 96 * (d + 1) + 27 ≤ 16000 * (d + 1)^2 := by
    nlinarith
  exact Nat.add_le_add_right (Nat.mul_le_mul_right _ hc) 23

end SubexponentialSAT.SqrtLog.IrreducibleSearchFactorControl

/-! Fixed first-success scan using the concrete saved factor checker. -/
namespace SubexponentialSAT.SqrtLog.IrreducibleSearchCandidateControl

open BitProgram StructuredCalls IrreducibleSearchProgram
open Subexp.BlockSearchPreparation (restrictState )
open SubexpEnumerationPayload SubexpTupleRefinement
attribute [local simp] Fin.addCases Fin.coe_ofNat_eq_mod

def candidateCost (d : ℕ) := IrreducibleSearchFactorControl.scanCost d + 20 * (d + 1) + 10

def searchCost (d : ℕ) := 4 + RecordPrograms.budget (fun _ => candidateCost d) (candidateRecords d)

end SubexponentialSAT.SqrtLog.IrreducibleSearchCandidateControl

namespace SubexponentialSAT.SqrtLog.IrreducibleSearchCandidateControl

theorem candidateRecords_volume (d : ℕ) :
    ((candidateRecords d).map List.length).sum = 2 * d * 3 ^ d := by
  have he : (fun c : Fin d → IrreducibleSearch.F =>
      (SubexpTupleRefinement.encodeTuple (SubexpEnumerationPayload.scalarCode 3) c).length) =
      (fun _ => 2 * d) := by
    funext c
    rw [← IrreducibleSearchProgram.coefficientArray_ofFn]
    simp only [IrreducibleSearchProgram.coefficientArray_length, List.length_ofFn]
  rw [candidateRecords, List.map_map]
  change ((IrreducibleSearch.candidates d).map (fun c =>
    (SubexpTupleRefinement.encodeTuple (SubexpEnumerationPayload.scalarCode 3) c).length)).sum = _
  rw [he]
  simp only [List.map_const', List.sum_replicate, smul_eq_mul, IrreducibleSearch.length_candidates]
  ring

theorem searchCost_eq (d : ℕ) : searchCost d = (candidateCost d + 12 * d + 7) * 3 ^ d + 4 := by
  rw [searchCost, RecordPrograms.budget_eq, candidateRecords_volume, candidateRecords_length]
  simp only [List.map_const', List.sum_replicate, smul_eq_mul, candidateRecords_length]
  ring

theorem searchCost_le (d : ℕ) : searchCost d ≤
    17000 * (d + 1)^2 * 3 ^ (3 * d + 2) + 4 := by
  have hscan := IrreducibleSearchFactorControl.scanCost_le d
  have hp : 1 ≤ 3 ^ (2 * (d + 1)) := Nat.one_le_pow _ _ (by decide)
  have hl : 32 * d + 60 ≤ 1000 * (d + 1)^2 := by nlinarith
  have hl' : 32 * d + 60 ≤ 1000 * (d + 1)^2 * 3 ^ (2 * (d + 1)) :=
    hl.trans (Nat.le_mul_of_pos_right _ (by omega))
  have hc : candidateCost d + 12 * d + 7 ≤
      17000 * (d + 1)^2 * 3 ^ (2 * (d + 1)) := by
    dsimp [candidateCost]
    nlinarith
  rw [searchCost_eq]
  calc
    _ ≤ (17000 * (d + 1)^2 * 3 ^ (2 * (d + 1))) * 3 ^ d + 4 :=
      Nat.add_le_add_right (Nat.mul_le_mul_right _ hc) 4
    _ = _ := by
      rw [mul_assoc (17000 * (d + 1)^2), ← pow_add,
        show 2 * (d + 1) + d = 3 * d + 2 by omega]

theorem searchCost_exponential (d : ℕ) : searchCost d ≤ 3 ^ (5 * d + 12) := by
  have hs := Nat.pow_le_pow_left (IrreducibleSearch.succ_le_three_pow d) 2
  have hp : 1 ≤ 3 ^ (5 * d + 2) := Nat.one_le_pow _ _ (by decide)
  calc
    searchCost d ≤ 17000 * (d + 1)^2 * 3 ^ (3 * d + 2) + 4 := searchCost_le d
    _ ≤ 17000 * (3 ^ d)^2 * 3 ^ (3 * d + 2) + 4 :=
      Nat.add_le_add_right (Nat.mul_le_mul_right _ (Nat.mul_le_mul_left 17000 hs)) 4
    _ = 17000 * 3 ^ (5 * d + 2) + 4 := by
      rw [← pow_mul, mul_assoc, ← pow_add,
        show d * 2 + (3 * d + 2) = 5 * d + 2 by omega]
    _ ≤ 59049 * 3 ^ (5 * d + 2) := by omega
    _ = 3 ^ (5 * d + 12) := by
      have h : (59049 : ℕ) = 3 ^ 10 := by norm_num
      rw [h, ← pow_add, show 10 + (5 * d + 2) = 5 * d + 12 by omega]

theorem searchCost_cardinality (d : ℕ) :
    searchCost d ≤ 531441 * (3 ^ d)^5 := by
  calc
    searchCost d ≤ 3 ^ (5 * d + 12) := searchCost_exponential d
    _ = 531441 * (3 ^ d)^5 := by
      rw [pow_add, Nat.mul_comm 5 d, pow_mul]
      norm_num [Nat.mul_comm]

/-- The implemented degree is `Nat.size Q + 1`; its proved field-size bound
is quadratic in `Q + 1`, giving degree ten for the search. -/
theorem searchCost_sizeDegreeBound {d Q : ℕ} (h : 3 ^ d ≤ 16 * (Q + 1)^2) :
    searchCost d ≤ (531441 * 16^5) * (Q + 1)^10 := by
  calc
    searchCost d ≤ 531441 * (3 ^ d)^5 := searchCost_cardinality d
    _ ≤ 531441 * (16 * (Q + 1)^2)^5 :=
      Nat.mul_le_mul_left _ (Nat.pow_le_pow_left h 5)
    _ = (531441 * 16^5) * (Q + 1)^10 := by ring

end SubexponentialSAT.SqrtLog.IrreducibleSearchCandidateControl

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_IrreducibleSearchBootstrap
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms


namespace SubexponentialSAT.SqrtLog.IrreducibleSearchBootstrap

open BitProgram StructuredCalls
open SubexpEnumerationPayload SubexpTupleRefinement IrreducibleSearchProgram
attribute [local simp] Fin.addCases Fin.coe_ofNat_eq_mod

def totalCost (d : ℕ) : ℕ := cost d + IrreducibleSearchCandidateControl.searchCost d + 1


end SubexponentialSAT.SqrtLog.IrreducibleSearchBootstrap

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_IrreducibleSearchBootstrapCost
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.IrreducibleSearchBootstrap

open SubexpEnumerationPayload

/-- An expanded bound uses only the audited generator estimate and fixed constants. -/
theorem cost_le (d : ℕ) : cost d ≤
    800 * (d + 1) * 3 ^ d * ((d + 1) * scalarWidth 3 + 1) +
    800 * ((d + 1) + (d + 1) + 1) * 3 ^ ((d + 1) + (d + 1)) *
      (((d + 1) + (d + 1) + 1) * scalarWidth 3 + 1) +
    28 * d + 4 * alphabetWord.length + 89 := by
  have h1 := IrreducibleSearchEnumeration.cost_le d
  have h2 := IrreducibleSearchEnumeration.cost_le ((d + 1) + (d + 1))
  dsimp only [cost]
  omega

theorem alphabetWord_length_le : alphabetWord.length ≤ 19 := by
  have h := ProgramEncoding.encodeRecords_length_le IrreducibleSearchEnumeration.alphabet 2 (by
    intro row hrow
    obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hrow
    have hx' : ((scalarCode 3).block x).length = scalarWidth 3 :=
      (scalarCode 3).length_block x
    exact le_of_eq (hx'.trans scalarWidth_three))
  simpa only [alphabetWord, IrreducibleSearchEnumeration.alphabet_length] using h

theorem coefficient_bound :
    800 * (scalarWidth 3 + 1) + 21600 * (3 * scalarWidth 3 + 1) +
      28 + 4 * alphabetWord.length + 89 ≤ preparationConstant := by
  have h := alphabetWord_length_le
  norm_num [scalarWidth_three, preparationConstant]
  omega

theorem cost_cardinality (d : ℕ) : cost d ≤ preparationConstant * (3 ^ d)^4 := by
  have h := cost_le d
  rw [factor_power] at h
  have hb := h.trans (terms_bound d (3 ^ d) (scalarWidth 3) alphabetWord.length
    (Nat.one_le_pow _ _ (by decide)) (IrreducibleSearch.succ_le_three_pow d))
  exact hb.trans (Nat.mul_le_mul_right _ coefficient_bound)

/-- The implemented degree uses a quadratic field-size bound in `Q + 1`. -/
theorem cost_sizeDegreeBound {d Q : ℕ} (h : 3 ^ d ≤ 16 * (Q + 1)^2) :
    cost d ≤ (preparationConstant * 16^4) * (Q + 1)^8 := by
  calc
    cost d ≤ preparationConstant * (3 ^ d)^4 := cost_cardinality d
    _ ≤ preparationConstant * (16 * (Q + 1)^2)^4 :=
      Nat.mul_le_mul_left _ (Nat.pow_le_pow_left h 4)
    _ = _ := by
      rw [mul_pow, ← pow_mul]
      simp only [Nat.mul_assoc]

end SubexponentialSAT.SqrtLog.IrreducibleSearchBootstrap

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafParameterArithmeticQuotient
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! A source-preserving floor quotient call using the audited finite binary
long-division program. Operands are runtime padded Boolean words. -/
namespace SubexponentialSAT.SqrtLog.LeafParameterArithmetic

open BitProgram StructuredCalls
open BinaryArithmetic (toNat)

abbrev quotientAt {S : ℕ} (p : QuotientPorts S) : Cmd 8 S :=
  .seq (ArithmeticCalls.copyAt p.left (p.work 5) (p.work 1))
    (.seq (.call (ProgramLinking.liftProgram ModularQuotientPrograms.quotientProgram
      id (quotientStackMap p))) (ArithmeticExpressionSupport.clearCmd (p.work 0)))

end SubexponentialSAT.SqrtLog.LeafParameterArithmetic

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_MomentsProgramProduct
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms


/-! A fixed sparse-product instruction table. Its three subservices perform
coefficient scaling, key join/clipping, and additive normalization, respectively.
All outer source lengths and ring dimensions live on tape. -/
namespace SubexponentialSAT.SqrtLog.MomentsProgram.Product
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.StackRoutines

abbrev keyPhase : Cmd 8 56 := .seq (copy 38 0) (.seq (clear 38)
  (.seq (transfer 43 1) (.seq (copy 45 2) (.seq (copy 46 3)
    (.seq keyMap (.seq (clear 1) (.seq (clear 2) (clear 3))))))))

end SubexponentialSAT.SqrtLog.MomentsProgram.Product


end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SubexpConvolutionPair
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# One actual product-and-accumulate step for packed jet convolution

The global state has sixteen Boolean registers and 256 Boolean-word stacks.
The multiplier occupies the fixed high bank beginning at 128. Its result is
moved, with order preserved, to the low-bank jet-cell accumulator service.
-/

namespace SubexponentialSAT.SubexpConvolutionPair

open BitProgram StructuredCalls SubexpScanPrimitives
open SubexpLiftRing SubexpQuarticRing

attribute [local simp] Fin.coe_ofNat_eq_mod

@[simp] theorem moveOut_regs_high (d : Data) (i : Fin 8) :
    (moveOut d).regs (Fin.natAdd 8 i) = d.regs (Fin.natAdd 8 i) := by
  have h0 : Fin.natAdd 8 i ≠ (0 : Fin 16) := by
    intro h
    have := congrArg (fun j : Fin 16 => j.val) h
    simp only [Fin.val_natAdd, Fin.coe_ofNat_eq_mod] at this
    omega
  have h1 : Fin.natAdd 8 i ≠ (1 : Fin 16) := by
    intro h
    have := congrArg (fun j : Fin 16 => j.val) h
    simp only [Fin.val_natAdd, Fin.coe_ofNat_eq_mod] at this
    omega
  simp only [moveOut, readRegs, Function.update_of_ne h0, Function.update_of_ne h1]

end SubexponentialSAT.SubexpConvolutionPair

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SubexpEnumerationProgram
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# Encoded interval enumeration by fixed finite control

A current label and a remaining count live on little-endian Boolean stacks.
The program invokes an actual body command once per label and advances using
verified finite-table increment/decrement routines.  Mathematical state
embeddings below occur only in execution proofs; no instruction evaluates an
arbitrary semantic function.
-/

namespace SubexponentialSAT.SubexpEnumerationProgram

open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredProgram
open SubexponentialSAT.CounterPrograms

variable {R S : ℕ}

@[simp] theorem install_register (p : Ports R S) (q : Bool) (d : Data R S)
    (b present flag : Bool) (xs ys : List Bool) (i : Fin 3) :
    (install p q d b present flag xs ys).regs (p.register i) =
      counterRegs b present flag i :=
  StructuredCalls.embedState_register _ _ _ _ p.register.injective i

@[simp] theorem install_target (p : Ports R S) (q : Bool) (d : Data R S)
    (b present flag : Bool) (xs ys : List Bool) :
    (install p q d b present flag xs ys).stacks (target p q) = xs :=
  StructuredCalls.embedState_stack _ _ _ _ (stackPorts p q).injective 0

@[simp] theorem install_scratch (p : Ports R S) (q : Bool) (d : Data R S)
    (b present flag : Bool) (xs ys : List Bool) :
    (install p q d b present flag xs ys).stacks p.scratch = ys :=
  StructuredCalls.embedState_stack _ _ _ _ (stackPorts p q).injective 1

noncomputable def rippleResult (p : Ports R S) (q c : Bool) (d : Data R S) : Data R S :=
  install p q d false false (d.regs (p.register 2))
    (ripple c (d.stacks (target p q))) []

noncomputable def zeroResult (p : Ports R S) (d : Data R S) : Data R S :=
  install p false d false false (isZero (d.stacks p.remaining)) (d.stacks p.remaining) []

noncomputable def testResult (p : Ports R S) (d : Data R S) : Data R S :=
  (StructuredProgram.Atom.bnot (p.register 2) (p.register 2)).eval (zeroResult p d)

@[simp] theorem testResult_flag (p : Ports R S) (d : Data R S) :
    (testResult p d).regs (p.register 2) = !(isZero (d.stacks p.remaining)) := by
  simp only [testResult, Atom.eval, State.ofCfg, Atom.instr, execInstr, Function.update_self]
  simp [zeroResult]

@[simp] theorem rippleResult_target (p : Ports R S) (q c : Bool) (d : Data R S) :
    (rippleResult p q c d).stacks (target p q) = ripple c (d.stacks (target p q)) := by
  exact install_target p q d _ _ _ _ _

@[simp] theorem rippleResult_scratch (p : Ports R S) (q c : Bool) (d : Data R S) :
    (rippleResult p q c d).stacks p.scratch = [] := by
  exact install_scratch p q d _ _ _ _ _

end SubexponentialSAT.SubexpEnumerationProgram

end OAI.Algorithms
end


