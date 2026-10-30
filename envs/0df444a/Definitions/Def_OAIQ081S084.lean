-- Prove2me | Definitions.Def_OAIQ081S084
-- name    : OAIQ081S084
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-29T22:06:56.525823+00:00
-- url     : https://prove2.me/theorems/63f3e53f-27a9-4bc4-b148-5b021a845373
-- title:
--   Definitions bundle OAIQ081S084 of the split of OpenAI, The Exponential Time Hypothesis is False
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.exact_count_and_sat`, carved from OpenAI's openai/math development (OpenAI, *The Exponential Time Hypothesis is False*, OpenAI Math Release, October 25, 2026, result family 378, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 149 declarations of OpenAI's Lean: 141 definitions, 2 inductive types or structures and 6 theorems. The definitions and types are `OAI.Algorithms.SubexponentialSAT.SqrtLog.CodeRowsProgram.Cell.Data`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.CodeRowsProgram.Cell.state`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.CodeRowsProgram.Data`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.CodeRowsProgram.Shift.Data`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.CodeRowsProgram.Shift.state`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.CodeRowsProgram.counterPorts`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.CodeSearchProgram.GraphSearchState`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.CodeSearchProgram.GraphWordState`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.CodeSearchProgram.callbackProgram`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.CodeSearchProgram.extendMatrixState`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.CodeSearchProgram.extendPairState`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.CodeSearchProgram.graphCallbackProgram`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.CodeSearchProgram.graphInputCopies`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.CodeSearchProgram.graphLiteralCommand`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.CodeSearchProgram.graphLiteralState`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.CodeSearchProgram.graphWordCallback`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.CodeSearchProgram.inputCopies`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.CodeSearchProgram.literalCommand`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.CodeSearchProgram.prepareGraphWordCommand`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.CodeSearchProgram.prepareWordCommand`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.CodeSearchProgram.preparedGraphWord`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.CodeSearchProgram.wordCallback`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.CodeSearchWalshProgram.ArithData`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.CodeSearchWalshProgram.Data`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.CodeSearchWalshProgram.cleared`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.CodeSearchWalshProgram.init`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.CodeSearchWalshProgram.inputLength`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.CodeSearchWalshProgram.pass`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.CodeSearchWalshProgram.ready`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.CodeSearchWalshProgram.size`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.DensePolynomialProgram.mulProgram`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.Execution.HashInputs.Ready`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.HashCircuitProgram.Constant.Data`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.HashCircuitProgram.Constant.data`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.HashCircuitProgram.Data`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.HashCircuitProgram.Decode.Data`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.HashCircuitProgram.Decode.data`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.HashCircuitProgram.Decode.input`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.HashCircuitProgram.Decode.output`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.HashCircuitProgram.Decode.ready` and 103 more.
--
--   **Sources.** They come from these modules of lean/OAI/Algorithms, in whole or in part: `SubexponentialSAT_SqrtLog_CodeRowsProgramCell`, `SubexponentialSAT_SqrtLog_CodeRowsProgramCode`, `SubexponentialSAT_SqrtLog_CodeRowsProgramCounter`, `SubexponentialSAT_SqrtLog_CodeRowsProgramShiftBasic`, `SubexponentialSAT_SqrtLog_CodeSearchProgramCallback`, `SubexponentialSAT_SqrtLog_CodeSearchProgramGraphCallback`, `SubexponentialSAT_SqrtLog_CodeSearchProgramGraphCounts`, `SubexponentialSAT_SqrtLog_CodeSearchProgramGraphPrepare`, `SubexponentialSAT_SqrtLog_CodeSearchProgramGraphWord`, `SubexponentialSAT_SqrtLog_CodeSearchProgramPrepare`, `SubexponentialSAT_SqrtLog_CodeSearchProgramWord`, `SubexponentialSAT_SqrtLog_CodeSearchWalshProgram`, `SubexponentialSAT_SqrtLog_CodeSearchWalshProgramArithmetic`, `SubexponentialSAT_SqrtLog_CodeSearchWalshProgramChecks`, `SubexponentialSAT_SqrtLog_CodeSearchWalshProgramCount`, `SubexponentialSAT_SqrtLog_DensePolynomialProgramMul`, `SubexponentialSAT_SqrtLog_ExecutionHashInputs`, `SubexponentialSAT_SqrtLog_HashCircuitProgramArithmeticNative`, `SubexponentialSAT_SqrtLog_HashCircuitProgramConstant`, `SubexponentialSAT_SqrtLog_HashCircuitProgramControl`, `SubexponentialSAT_SqrtLog_HashCircuitProgramDecode`, `SubexponentialSAT_SqrtLog_HashCircuitProgramFrame`, `SubexponentialSAT_SqrtLog_HashCircuitProgramInterpreter`, `SubexponentialSAT_SqrtLog_HashCircuitProgramLiteralState`, `SubexponentialSAT_SqrtLog_HashCircuitProgramLookup`, `SubexponentialSAT_SqrtLog_HashCircuitProgramMemory`, `SubexponentialSAT_SqrtLog_HashCircuitProgramPayload`, `SubexponentialSAT_SqrtLog_HashCircuitProgramRowMemory`, `SubexponentialSAT_SqrtLog_HashCircuitProgramWeightedCore`, `SubexponentialSAT_SqrtLog_HashInputProgramFrame`, `SubexponentialSAT_SqrtLog_HashInputProgramLoop`, `SubexponentialSAT_SqrtLog_HashInputProgramLoopDecode`, `SubexponentialSAT_SqrtLog_HashInputProgramLoopFinal`, `SubexponentialSAT_SqrtLog_HashInputProgramLoopReverse`, `SubexponentialSAT_SqrtLog_HashInputProgramLoopTerm`, `SubexponentialSAT_SqrtLog_HashInputProgramSource`, `SubexponentialSAT_SqrtLog_HashParametersProgramFinal`, `SubexponentialSAT_SqrtLog_HashParametersProgramLog`, `SubexponentialSAT_SqrtLog_HashScopeProgramMarkedSource`, `SubexponentialSAT_SqrtLog_HashScopeProgramMarkedTableCalls`, `SubexponentialSAT_SqrtLog_HashScopeProgramRawTable`, `SubexponentialSAT_SqrtLog_IrreducibleSearchBootstrapBounds`, `SubexponentialSAT_SqrtLog_LeafParameterArithmetic`, `SubexponentialSAT_SqrtLog_LeafParameterArithmeticSqrt`, `SubexponentialSAT_SqrtLog_LeafParametersProgramNative`, `SubexponentialSAT_SqrtLog_MomentsProgramDictionaryBase`, `SubexponentialSAT_SqrtLog_MomentsProgramNormalize`, `SubexponentialSAT_SqrtLog_MomentsProgramProduct`, `SubexponentialSAT_SqrtLog_RingScanServiceBasic`, `SubexponentialSAT_SqrtLog_SetupCleanup`, `SubexponentialSAT_SqrtLog_SetupSearch`, `SubexponentialSAT_SqrtLog_SquarefreeScaleProgram`, `SubexponentialSAT_SubexpLiteralChunkProgram`, `SubexponentialSAT_Subexp_PairScoreProgram`.
--
--   **Imports.** It imports the published bundle `Def_SubexponentialSAT`; the bundles `OAIQ081S066`, `OAIQ081S067`, `OAIQ081S068` and `OAIQ081S069` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ081S102`, `OAIQ081S104`, `OAIQ081S105`, `OAIQ081S106`, `OAIQ081S107`, `OAIQ081S108`, `OAIQ081S109`, `OAIQ081S110`, `OAIQ081S111`, `OAIQ081S112`, `OAIQ081S113`, `OAIQ081S114` and `OAIQ081S115`; the statements `OAI.Algorithms.SubexponentialSAT.SqrtLog.CodeRowsProgram.Shift.command_eval`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.CodeSearchProgram.graphCounts_eval`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.CodeSearchProgram.graphWord_eval`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.CodeSearchProgram.wordInput_length_le`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.CodeSearchWalshProgram.prepare_eval`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.HashCircuitProgram.Native.fetchLiteral_from_state`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.HashCircuitProgram.Native.rowFrame_memory`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.HashCircuitProgram.literalDictionary_hit`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.HashInputProgram.Loop.frameRecord_eval`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.HashInputProgram.Loop.frameWeight_eval` and `OAI.Algorithms.SubexponentialSAT.SqrtLog.HashInputProgram.Loop.lookup_eval`; the proofs of `OAI.Algorithms.SubexponentialSAT.SqrtLog.CodeRowsProgram.Shift.command_eval`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.CodeSearchProgram.graphCountTail_eval`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.CodeSearchProgram.graphCounts_eval`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.CodeSearchProgram.graphWord_eval`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.CodeSearchProgram.wordInput_length_le`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.CodeSearchProgram.wordTail_eval`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.CodeSearchWalshProgram.prepare_eval`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.HashCircuitProgram.Native.fetchLiteral_from_state`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.HashCircuitProgram.Native.rowFrame_memory`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.HashCircuitProgram.literalDictionary_hit`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.HashInputProgram.Loop.frameRecord_eval`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.HashInputProgram.Loop.frameWeight_eval`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.HashInputProgram.Loop.lookup_eval` and `OAI.Algorithms.SubexponentialSAT.SqrtLog.IdempotentApplyProgram.ReadScalar.emit_eval`.
-- source:
--   OpenAI, The Exponential Time Hypothesis is False, OpenAI Math Release, October 25, 2026, https://github.com/openai/math (result family 378; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/The-Exponential-Time-Hypothesis-is-False-October-25-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Algorithms at commit 7ef5c0c

import Mathlib
import Definitions.Def_SubexponentialSAT
import Definitions.Def_OAIQ081S066
import Definitions.Def_OAIQ081S067
import Definitions.Def_OAIQ081S068
import Definitions.Def_OAIQ081S069

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

@[simp] theorem readPair_pairBytes (pair : PlanPair) : readPair (pairBytes pair) = pair := by
  rcases pair with ⟨left, right⟩
  have hr : Encoding.readFrame (Encoding.frame (CollisionStreamProgram.planBytes right)) =
      some (CollisionStreamProgram.planBytes right, []) := by
    simpa only [List.append_nil] using
      Encoding.readFrame_frame_append (CollisionStreamProgram.planBytes right) []
  simp [readPair, pairBytes, hr]

def pairStream (ctx : Context) (pair : PlanPair) (stream : List Bool) : List Bool :=
  CollisionTupleProgram.streamed ctx.current.flatten ctx.width.length pair.1 pair.2
    (TupleProgram.powerRows ctx.alphabet ctx.depth.length [[]]) stream

def streamedPairs (ctx : Context) (pairs : List PlanPair) (stream : List Bool) : List Bool :=
  pairs.foldl (fun acc pair => pairStream ctx pair acc) stream

def score (ctx : Context) (pairs : List PlanPair) : ℕ :=
  PaddedCompletion.trueCount (streamedPairs ctx pairs [])

def outputState (ctx : Context) (pairs : List PlanPair) : Data :=
  afterTally (baseState ctx (streamedPairs ctx pairs []))

@[simp] theorem outputState_output (ctx : Context) (pairs : List PlanPair) :
    (outputState ctx pairs).stacks 18 = UnaryCompare.encode (score ctx pairs) := by
  simp [outputState, afterTally, baseState, score, UnaryCompare.encode]

end SubexponentialSAT.Subexp.PairScoreProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_CodeRowsProgramCell
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! A native five-pop decoder for the scalar frames emitted by code search.
It consumes one frame and exposes its two little-endian scalar bits. -/
namespace SubexponentialSAT.SqrtLog.CodeRowsProgram.Cell
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls

abbrev Data := State 4 1

def state (regs : Fin 4 → Bool) (bits : List Bool) : Data := ⟨regs,![bits]⟩

end SubexponentialSAT.SqrtLog.CodeRowsProgram.Cell

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_CodeRowsProgramShiftBasic
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Fixed native operations for adding a Cayley shift to a vertex word.
The Boolean mode chooses left or right incidence; shift frames are consumed
on both sides so each iteration advances exactly one local port. -/
namespace SubexponentialSAT.SqrtLog.CodeRowsProgram.Shift
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls

abbrev Data := State 8 4

def state (regs : Fin 8 → Bool) (source vertex accum out : List Bool) : Data :=
  ⟨regs,![source,vertex,accum,out]⟩

end SubexponentialSAT.SqrtLog.CodeRowsProgram.Shift

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_CodeRowsProgramCode
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! The finite table for sparse code rows. Runtime loops visit vertices,
local checks, and local ports only. The original clause count is used for a
binary comparison, never as the bound of a per-row scan. -/
namespace SubexponentialSAT.SqrtLog.CodeRowsProgram
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls

abbrev Data := State 16 64

end SubexponentialSAT.SqrtLog.CodeRowsProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_CodeRowsProgramCounter
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.CodeRowsProgram
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls

def counterPorts (src : Fin 64) (hs : src≠41) : CounterForPrograms.Ports 16 64 :=
  ⟨⟨low3,low3_injective_p0⟩,src,41,hs⟩

end SubexponentialSAT.SqrtLog.CodeRowsProgram

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

def extendMatrixState (base : State 8 16) (d : ℕ) (saved : List Bool) : ScanState :=
  ⟨base.regs, fun j => if h : j.val < 16 then base.stacks ⟨j.val,h⟩
    else if j = 16 then List.replicate d true else saved⟩

end SubexponentialSAT.SqrtLog.CodeSearchProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_CodeSearchProgramPrepare
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Fixed physical input preparation for the local-code word checker. The
matrix, row count, and threshold are copied from persistent tapes. A parsed
reversed payload is transferred once, restoring the word's forward order. -/
namespace SubexponentialSAT.SqrtLog.CodeSearchProgram
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.SubexpSetupStorage
open StructuredProgram (Atom)

abbrev inputCopies : Cmd 16 24 := copyMany 23 inputMoves

abbrev literalCommand : Cmd 16 24 :=
  .seq (.base (.atom (.set 0 false))) <|
  .seq (.base (.atom (.push 5 0))) <|
  .seq (.base (.atom (.push 14 0))) <|
  .seq (.base (.atom (.push 14 0))) <|
  .seq (.base (.atom (.set 0 true))) <|
  .seq (.base (.atom (.push 5 0))) (.base (.atom (.push 5 0)))

abbrev prepareWordCommand : Cmd 16 24 :=
  .seq inputCopies (.seq (.call (StackRoutines.transferProgram 22 12 0 1)) literalCommand)


end SubexponentialSAT.SqrtLog.CodeSearchProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_CodeSearchProgramCallback
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! An actual reusable local-code callback: preparation, the complete word
predicate, then physical cleanup. All surrounding record-parser tapes and
flags are outside the invoked routine's ports. -/
namespace SubexponentialSAT.SqrtLog.CodeSearchProgram
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.SubexpSetupStorage
open StructuredProgram (Atom)

abbrev wordCallback : Cmd 16 24 :=
  .seq prepareWordCommand <|
  .seq (invoke wordProgram wordRegisters wordStacks) <|
  .seq (.base (.atom (.copy 15 7))) (clearMany workPorts)

def callbackProgram := compiled wordCallback 22 22

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

def extendPairState (base : State 8 16) (first second : List Bool) : ScanState :=
  ⟨base.regs,fun j => if h : j.val < 16 then base.stacks ⟨j.val,h⟩
    else if j = 16 then first else second⟩

end SubexponentialSAT.SqrtLog.CodeSearchProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_CodeSearchWalshProgramCount
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.CodeSearchWalshProgram
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls

abbrev ArithData := State 8 14

end SubexponentialSAT.SqrtLog.CodeSearchWalshProgram

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

def inputLength (d : ArithData) : ℕ := (d.stacks 0).length + (d.stacks 1).length + (d.stacks 2).length
def ready (d : ArithData) : Prop := ∀ j : Fin 14, 3 ≤ j.val → d.stacks j = []

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

abbrev Data := State 9 14
def size (d : Data) : ℕ := inputLength (projectState lowRegisters id d)

def cleared (d : Data) : Data := ⟨readRegs d.regs 0 1 none, Function.update d.stacks 3 []⟩

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

def pass (d : Data) : Bool := decide (good (BinaryArithmetic.toNat (d.stacks 0))
  (BinaryArithmetic.toNat (d.stacks 1)) (d.stacks 2).length)

def init (d : Data) : Data := ⟨Function.update d.regs 8 true, d.stacks⟩

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

abbrev GraphWordState := State 16 29

end SubexponentialSAT.SqrtLog.CodeSearchProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_CodeSearchProgramGraphPrepare
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Fixed physical input preparation for the Walsh character checker. The
matrix, row count, and two binary scalar words are copied from persistent tapes. A parsed
reversed payload is transferred once, restoring the word's forward order. -/
namespace SubexponentialSAT.SqrtLog.CodeSearchProgram
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.SubexpSetupStorage
open StructuredProgram (Atom)

abbrev GraphSearchState := State 16 36

abbrev graphInputCopies : Cmd 16 36 := copyMany 35 graphInputMoves

abbrev graphLiteralCommand : Cmd 16 36 :=
  .seq (.base (.atom (.set 0 false))) <|
  .seq (.base (.atom (.push 5 0))) <|
  .seq (.base (.atom (.push 14 0))) <|
  .seq (.base (.atom (.push 14 0))) <|
  .seq (.base (.atom (.set 0 true))) <|
  .seq (.base (.atom (.push 5 0))) <|
  .seq (.base (.atom (.set 0 false))) (.base (.atom (.push 5 0)))

def graphLiteralState (a : GraphSearchState) : GraphSearchState :=
  (Atom.push 5 0).eval ((Atom.set 0 false).eval ((Atom.push 5 0).eval ((Atom.set 0 true).eval
    ((Atom.push 14 0).eval ((Atom.push 14 0).eval ((Atom.push 5 0).eval
      ((Atom.set 0 false).eval a)))))))

abbrev prepareGraphWordCommand : Cmd 16 36 :=
  .seq graphInputCopies (.seq (.call (StackRoutines.transferProgram 34 12 0 1)) graphLiteralCommand)

def preparedGraphWord (a : GraphSearchState) : GraphSearchState :=
  graphLiteralState (SubexpScanPrimitives.afterTransfer (copyManyState graphInputMoves a) 34 12 0 1)

end SubexponentialSAT.SqrtLog.CodeSearchProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_CodeSearchProgramGraphCallback
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! An actual reusable local-code callback: preparation, the complete word
predicate, then physical cleanup. All surrounding record-parser tapes and
flags are outside the invoked routine's ports. -/
namespace SubexponentialSAT.SqrtLog.CodeSearchProgram
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.SubexpSetupStorage
open StructuredProgram (Atom)

abbrev graphWordCallback : Cmd 16 36 :=
  .seq prepareGraphWordCommand <|
  .seq (invoke graphWordProgram graphWorkRegisters graphWordStacks) (clearMany graphWorkPorts)

def graphCallbackProgram := compiled graphWordCallback 34 34

end SubexponentialSAT.SqrtLog.CodeSearchProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_DensePolynomialProgramMul
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Runtime-sized dense convolution and old-compatible cached-array services.
The local pair premise is an actual fixed-command trace; all scans, writes,
copies, counter steps, and final halts are included by the audited controller.
A concrete native ring-pair instantiation is supplied separately. -/
namespace SubexponentialSAT.SqrtLog.DensePolynomialProgram
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.SubexpConvolutionControl
open SubexponentialSAT.SubexpSymbolicCost

variable {C R : Type*}

def mulProgram (pair : Code) := compiled (mulCommand pair) 240 244

end SubexponentialSAT.SqrtLog.DensePolynomialProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_ExecutionHashInputs
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Actual preparation of the selector's alphabet and its two unary loop
counters. Input ports0,5,6 hold binary alphabet size, tuple depth and round
count. Port9 is an arbitrary saved row stream; other ports start empty.
The arithmetic that computes these three binary values remains a separate
caller obligation. Their expansion is performed here, with its full cost. -/

namespace SubexponentialSAT.SqrtLog.Execution.HashInputs

open BitProgram StructuredCalls

def Ready (a : State 10 14) : Prop :=
  ∀ i : Fin 14, i ≠ 0 → i ≠ 5 → i ≠ 6 → i ≠ 9 → a.stacks i = []

end SubexponentialSAT.SqrtLog.Execution.HashInputs

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_HashCircuitProgramLookup
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# Native literal parsing and hash-specific incidence lookup

A literal payload is `key ++ [positive]`; the existing record parser supplies
its reversal. The key selects a variable in a physically selected hash slice.
The fixed command pops the polarity, copies and scans the saved incidence
slice, returns its framed dictionary payload, and reclaims both scan and query.
There is no circuit-evaluation instruction and no scope truth table.
-/
namespace SubexponentialSAT.SqrtLog.HashCircuitProgram

open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.SubexpRecordScan

abbrev Data := State 6 7

abbrev extend (d : State 5 6) (positive : Bool) (table : List Bool) : Data :=
  ⟨![d.regs 0,d.regs 1,d.regs 2,d.regs 3,d.regs 4,positive],
   ![d.stacks 0,d.stacks 1,d.stacks 2,d.stacks 3,d.stacks 4,d.stacks 5,table]⟩

abbrev data (regs : Fin 5 → Bool) (positive : Bool)
    (scan query output table : List Bool) : Data :=
  extend (recordState regs scan [] query [] [] output) positive table

def copied (d : Data) (src dst : Fin 7) : Data :=
  ⟨readRegs d.regs 0 1 none, StackRoutines.copyStacks src dst d.stacks⟩

def cleared (d : Data) (src : Fin 7) : Data :=
  ⟨readRegs d.regs 0 1 none, StackRoutines.clearStacks src d.stacks⟩

end SubexponentialSAT.SqrtLog.HashCircuitProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_HashCircuitProgramDecode
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Native conversion from the audited unary literal code `2*v+polarity` to
variable-key/polarity syntax. The source is a reversed parsed `encodeNat` record.
The loop consumes two unary marks per variable mark and records an odd tail as
positive polarity. Its instruction table is independent of the variable index. -/
namespace SubexponentialSAT.SqrtLog.HashCircuitProgram
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls

namespace Decode
abbrev Data := State 4 2

def data (value present positive : Bool) (src dst : List Bool) : Data :=
  ⟨![value,present,true,positive], ![src,dst]⟩

def ready (m : ℕ) (acc : List Bool) : Data :=
  match m with
  | 0 => data false false false [] acc
  | m+1 => data true true false (List.replicate m true) acc

def input (regs : Fin 4 → Bool) (m : ℕ) : Data :=
  ⟨regs, ![(Encoding.encodeNat m).reverse, []]⟩

def output (positive : Bool) (v : ℕ) : Data :=
  data false false positive ((Encoding.encodeNat v ++ [positive]).reverse) []

end Decode
end SubexponentialSAT.SqrtLog.HashCircuitProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_HashCircuitProgramPayload
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Native unframing of the selected incidence dictionary. A successful literal
lookup returns the actual forward dictionary bits on stack5. The success guard
handles a missing key without invoking a parser on an absent frame. -/
namespace SubexponentialSAT.SqrtLog.HashCircuitProgram
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.SubexpRecordScan

def transferred (d : Data) (src dst : Fin 7) : Data :=
  ⟨readRegs d.regs 0 1 none, StackRoutines.transferStacks src dst d.stacks⟩

end SubexponentialSAT.SqrtLog.HashCircuitProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_HashCircuitProgramFrame
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Fixed caller framing for the native sparse-hash interpreter. Low ports
0--55 are reserved for arithmetic. Literal lookup uses 56--62, leaving the
clause, row and constant accumulators physically untouched. -/
namespace SubexponentialSAT.SqrtLog.HashCircuitProgram.Native
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls

abbrev Machine := State 8 96

noncomputable def literalFrame (base : Machine) (regs : Fin 5 → Bool) (positive : Bool)
    (scan query result table : List Bool) : Machine :=
  embedState literalRegisters literalStacks base (data regs positive scan query result table)

noncomputable abbrev rowFrame (base : Machine) (regs : Fin 5 → Bool) (payload clause weight : List Bool) : Machine :=
  embedState rowRegisters rowStacks base
    (SubexponentialSAT.SubexpRecordScan.recordState regs payload [] clause [] [] weight)

end SubexponentialSAT.SqrtLog.HashCircuitProgram.Native

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_HashCircuitProgramControl
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Fixed record-control code for sparse-hash evaluation. This module fixes
all parsing and traversal code. Arithmetic components below are finite native
commands, to be instantiated by the separate dictionary modules; no semantic
function is called by the machine. -/
namespace SubexponentialSAT.SqrtLog.HashCircuitProgram.Native
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls

def copied (d : Machine) (src dst : Fin 96) : Machine :=
  ⟨readRegs d.regs 0 1 none,StackRoutines.copyStacks src dst d.stacks⟩
def cleared (d : Machine) (src : Fin 96) : Machine :=
  ⟨readRegs d.regs 0 1 none,StackRoutines.clearStacks src d.stacks⟩
def transferred (d : Machine) (src dst : Fin 96) : Machine :=
  ⟨readRegs d.regs 0 1 none,StackRoutines.transferStacks src dst d.stacks⟩

def returned (d : Machine) : Machine :=
  { d with regs := Function.update (Function.update (Function.update d.regs 0 false) 1 true) 2 false }

@[simp] theorem returned_stack (d : Machine) (i : Fin 96) :
    (returned d).stacks i = d.stacks i := rfl

end SubexponentialSAT.SqrtLog.HashCircuitProgram.Native

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_HashCircuitProgramMemory
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Split-memory rules for composing the actual low arithmetic workspace with
persistent high interpreter data. All movement lemmas retain primitive costs. -/
namespace SubexponentialSAT.SqrtLog.HashCircuitProgram.Native.Memory
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls

def state (regs : Fin 8 → Bool) (low : Fin 56 → List Bool) (high : Fin 40 → List Bool) : Machine :=
  ⟨regs,tapes low high⟩

end SubexponentialSAT.SqrtLog.HashCircuitProgram.Native.Memory

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_MomentsProgramDictionaryBase
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Fixed physical dictionary-insertion program. All dictionary/key/vector
lengths are input data. The complete semantic composition is proved separately;
this file defines the finite table and its paid stack primitives. -/
namespace SubexponentialSAT.SqrtLog.MomentsProgram.Dictionary
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.StackRoutines

abbrev add : Cmd 8 27 := .call
  (ProgramLinking.liftProgram RingScan.addVectorProgram id nativeStacks)

abbrev onHit : Cmd 8 27 :=
  .seq parseOld (.seq (transfer 8 9)
    (.seq (copy 17 8 23) (.seq (copy 24 11 23) add)))

/-- Dictionary15, query.reverse16, new coefficient17, modulus5, coefficient
width12, extension dimension24 are inputs. Result dictionary15 replaces the
old value by new+old, once the local semantic composition is discharged. -/
abbrev insert : Cmd 8 27 :=
  .seq (copy 15 18 23)
    (.seq lookup
      (.seq (.ite 4 onHit onMiss)
        (.seq (clear 18)
          (.seq (transfer 0 26)
            (.seq replace (.seq (copy 25 15 23) (clear 25)))))))

def insertProgram := compiled insert 15 15

end SubexponentialSAT.SqrtLog.MomentsProgram.Dictionary

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_MomentsProgramNormalize
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms



namespace SubexponentialSAT.SqrtLog.MomentsProgram.Normalize
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls
open SubexponentialSAT.SubexpLiftRing SubexponentialSAT.SubexpQuarticRing

abbrev insert : Cmd 8 28 := .call (ProgramLinking.liftProgram Dictionary.insertProgram id lower)

end SubexponentialSAT.SqrtLog.MomentsProgram.Normalize


namespace SubexponentialSAT.SqrtLog.MomentsProgram.Normalize
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.StackRoutines
open SubexponentialSAT.SubexpLiftRing SubexponentialSAT.SubexpQuarticRing

abbrev step : Cmd 8 28 := .seq Squarefree.Program.takeDictionaryRecord (.seq insert clearCoefficient)

end SubexponentialSAT.SqrtLog.MomentsProgram.Normalize


namespace SubexponentialSAT.SqrtLog.MomentsProgram.Normalize
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls
open SubexponentialSAT.SubexpLiftRing SubexponentialSAT.SubexpQuarticRing

variable {K : Type*} [DecidableEq K]

abbrev loop : Cmd 8 28 := .while 7 (.seq step peek)
abbrev scan : Cmd 8 28 := .seq peek loop
def program := compiled scan 27 15

end SubexponentialSAT.SqrtLog.MomentsProgram.Normalize


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

theorem serviceRoute_eval (regs : Fin 8 → Bool) (s : ServiceStore) :
    Eval serviceRoute (2*s.x.length + 2*s.y.length + 6*s.stream.length + 12)
      (serviceWorkState regs {s with reverseStream := []})
      (serviceWorkState (readRegs regs 1 3 none) {s with x := [], y := s.stream, reverseStream := [], stream := []}) := by
  let a := serviceWorkState regs {s with reverseStream := []}
  let b := serviceAfterClear a 8
  let c := serviceAfterClear b 9
  let d := serviceAfterTransfer c 23 21
  have h1 := serviceClear_eval a 8
  have h2 := serviceClear_eval b 9
  have h3 := serviceTransfer_eval c 23 21 (by decide)
  have h4 := serviceTransfer_eval d 21 9 (by decide)
  have he := h1.seq (h2.seq (h3.seq h4))
  have hf : serviceAfterTransfer d 21 9 =
      serviceWorkState (readRegs regs 1 3 none) {s with x := [], y := s.stream, reverseStream := [], stream := []} := by
    apply congrArg₂ StructuredProgram.State.mk
    · simp [d, c, b, a, serviceAfterTransfer, serviceAfterClear, serviceWorkState, readRegs_reset]
    · funext i; fin_cases i <;>
        simp [d, c, b, a, serviceAfterTransfer, serviceAfterClear, serviceWorkState,
          serviceTapes, clearStacks, transferStacks]
  rw [hf] at he
  convert he using 1
  all_goals try with_reducible_and_instances rfl
  simp [d, c, b, a, serviceAfterTransfer, serviceAfterClear, serviceWorkState,
    serviceTapes, clearStacks, transferStacks]
  omega

end SubexponentialSAT.SqrtLog.RingScan

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_SquarefreeScaleProgram
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Base stage. -/
/-! Fixed physical ABI for scaling all coefficients in a sparse dictionary.
The low 32 stacks are the common coefficient-ring service. The eight high
stacks hold source, reversed output, scalar, key, coefficient staging, frame
staging, final output, and a preserved copy of the unary degree. -/

/-! Moves stage. -/

/-! Emit stage. -/

/-! Native stage. -/
namespace SubexponentialSAT.SqrtLog.Squarefree.ScaleProgram
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls
open SubexponentialSAT.SubexpLiftRing SubexponentialSAT.SubexpQuarticRing

abbrev multiply : Cmd 8 40 :=
  .call (ProgramLinking.liftProgram RingScan.serviceMulProgram id nativePorts)

abbrev step : Cmd 8 40 := .seq prepare (.seq multiply emit)

end SubexponentialSAT.SqrtLog.Squarefree.ScaleProgram

/-! Loop stage. -/
namespace SubexponentialSAT.SqrtLog.Squarefree.ScaleProgram
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls
open SubexponentialSAT.SubexpLiftRing SubexponentialSAT.SubexpQuarticRing

variable {K : Type*}

abbrev loop : Cmd 8 40 := .while 7 (.seq step peek)

abbrev command : Cmd 8 40 := .seq peek (.seq loop finish)
def program := compiled command 32 38

end SubexponentialSAT.SqrtLog.Squarefree.ScaleProgram

/-! Cost stage. -/

/-! Semantics stage. -/

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

abbrev scale : Cmd 8 56 := .call (ProgramLinking.liftProgram Squarefree.ScaleProgram.program id scalePorts)
abbrev normalize : Cmd 8 56 := .call (ProgramLinking.liftProgram Normalize.program id normalizePorts)

abbrev scalePhase : Cmd 8 56 := .seq (copy 41 32) (.seq (copy 44 34)
  (.seq scale (.seq (clear 34) (clear 44))))

abbrev normalizePhase : Cmd 8 56 := .seq (copy 4 27) (.seq (clear 4)
  (.seq (copy 39 51) (.seq normalize (clear 51))))

abbrev step : Cmd 8 56 := .seq read (.seq scalePhase (.seq keyPhase normalizePhase))
abbrev loop : Cmd 8 56 := .while 7 (.seq step peek)
abbrev command : Cmd 8 56 := .seq peek loop
def program := compiled command 40 42

end SubexponentialSAT.SqrtLog.MomentsProgram.Product


end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_HashCircuitProgramWeightedCore
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Shared native weighted sparse accumulation. This local56-stack core is
used by hash rows and head moments. It retains the source dictionary41,
consumes the flat coefficient44, and replaces accumulator42 by the normalized
weighted sum. Its output restores all temporary work used by these phases. -/
namespace SubexponentialSAT.SqrtLog.HashCircuitProgram.WeightedCore
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls
open SubexponentialSAT.SubexpLiftRing SubexponentialSAT.SubexpQuarticRing
open MomentsProgram

/-- Both subphases are concrete fixed bit programs. -/
abbrev command : Cmd 8 56 :=
  .seq Product.scalePhase
    (.seq (Product.copy 38 4) (.seq (Product.clear 38) Product.normalizePhase))

end SubexponentialSAT.SqrtLog.HashCircuitProgram.WeightedCore

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_HashCircuitProgramArithmeticNative
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms


/-! Component: HashCircuitProgramArithmetic. All public namespaces and APIs are retained. -/


/-! Native arithmetic wiring for the hash interpreter. Scale and normalized
addition are fixed imported instruction tables. Product is wired separately
when the native product table is supplied by its implementation module. -/
namespace SubexponentialSAT.SqrtLog.HashCircuitProgram.Native
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls

/-- Shared fixed weighted-sum core, retaining the low56 arithmetic ABI. -/
abbrev weightedCore : Cmd 8 96 :=
  liftCommand WeightedCore.command 41 42 id arithmeticPorts

/-- Input61 is replaced by one minus its value. -/
abbrev complement : Cmd 8 96 :=
  .seq (copy 61 41 70)
    (.seq (copy 76 44 70)
      (.seq (copy 69 42 70)
        (.seq weightedCore
          (.seq (clear 61)
            (.seq (copy 42 61 70) (.seq (clear 42) (clear 41)))))))

/-- Parsed reversed weight65 becomes forward coefficient44 through an actual
transfer. The scaled clause is accumulated with the prior row dictionary. -/
abbrev accumulate : Cmd 8 96 :=
  .seq (copy 67 41 70)
    (.seq (transfer 65 44)
      (.seq (copy 68 42 70)
        (.seq weightedCore
          (.seq (clear 67)
            (.seq (clear 68)
              (.seq (copy 42 68 70) (.seq (clear 42) (clear 41))))))))

abbrev wiredArithmetic (product : Cmd 8 96) : Arithmetic :=
  ⟨complement,productAdapter product,accumulate⟩

end SubexponentialSAT.SqrtLog.HashCircuitProgram.Native

/-! Component: HashCircuitProgram. All public namespaces and APIs are retained. -/


/-! The fixed native sparse-hash row instruction table. All arithmetic
components are now concrete native programs: there are no operation-valued
parameters in `command` or `program`. The complete serialized semantic and
primitive-time theorem must additionally discharge the local callback
contracts for this table; no such theorem is asserted merely by compilation. -/
namespace SubexponentialSAT.SqrtLog.HashCircuitProgram.Native
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls

abbrev product : Cmd 8 96 :=
  .call (ProgramLinking.liftProgram MomentsProgram.Product.program id productPorts)

def arithmetic : Arithmetic := wiredArithmetic product

abbrev command : Cmd 8 96 := rowCommand arithmetic

def program := compiled command 64 68

end SubexponentialSAT.SqrtLog.HashCircuitProgram.Native

/-! Component: HashCircuitProgramMemoryExtra. All public namespaces and APIs are retained. -/


/-! Component: HashCircuitProgramWeightedCallbacks. All public namespaces and APIs are retained. -/


/-! The two concrete weighted arithmetic adapters used by the hash evaluator.
The statements expose exact dictionary bytes and restoration of the common
arithmetic workspace. In particular they do not assume callback correctness. -/

/-! Component: HashCircuitProgramProduct. All public namespaces and APIs are retained. -/


/-! Concrete product callback refinement. Both sparse operands are copied from
persistent interpreter stacks into the real product program. The result is
copied back, and all temporary operands are physically reclaimed. -/

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

abbrev Data := State 8 6

def data (regs : Fin 8 → Bool) (shape input key coeff rev output : List Bool) : Data :=
  ⟨regs,![shape,input,key,coeff,rev,output]⟩

end SubexponentialSAT.SqrtLog.HashCircuitProgram.Constant

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_HashCircuitProgramLiteralState
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Direct-call interface from the actual caller state. This avoids preparing
an extra machine-state embedding between the record parser and literal lookup. -/
namespace SubexponentialSAT.SqrtLog.HashCircuitProgram.Native
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls

def callerRegs (d : Machine) : Fin 5 → Bool := fun i => d.regs (Fin.castAdd 3 i)

structure LookupReady (d : Machine) (table : List Bool) : Prop where
  scan : d.stacks 56 = []
  temporary : d.stacks 57 = []
  compare : d.stacks 59 = []
  scratch : d.stacks 60 = []
  output : d.stacks 61 = []
  saved : d.stacks 62 = table

end SubexponentialSAT.SqrtLog.HashCircuitProgram.Native

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_HashCircuitProgramRowMemory
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Exact frame for unpacking an inline weighted clause into the two physical
operands used by the clause loop and weighted accumulator. -/
namespace SubexponentialSAT.SqrtLog.HashCircuitProgram.Native
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls

structure WeightedReady (d : Machine) : Prop where
  temporary : d.stacks 57 = []
  clause : d.stacks 63 = []
  compare : d.stacks 59 = []
  scratch : d.stacks 60 = []
  weight : d.stacks 65 = []

def rowCallerRegs (d : Machine) : Fin 5 → Bool := fun i => d.regs (rowRegisters i)

end SubexponentialSAT.SqrtLog.HashCircuitProgram.Native

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_HashCircuitProgramInterpreter
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

attribute [local simp] Fin.addCases Fin.coe_ofNat_eq_mod Fin.ext_iff


/-! Component: HashCircuitProgramLiteralCallback. All public namespaces and APIs are retained. -/


/-! Literal callback with actual lookup, polarity, sparse product, and return.
The represented minus-one and one values are explicit cached inputs. All work
is performed by the fixed native commands wired into the row interpreter. -/

/-! Component: HashCircuitProgramClause. All public namespaces and APIs are retained. -/


/-! Typed clause traversal using the fixed native literal callback. Input is
still the original unary literal encoding; the type is used only to specify
which dictionary entry the native decoder and lookup retrieve. -/
namespace SubexponentialSAT.SqrtLog.HashCircuitProgram.Native.Clause
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls
open SubexponentialSAT.SubexpLiftRing SubexponentialSAT.SubexpQuarticRing
open MomentsProgram

def base (regs : Fin 8 → Bool) (e : Product.Store) (high : Fin 40 → List Bool) (acc : List Bool) : Machine :=
  Memory.state regs (Product.tapes e) (baseHigh high acc)

end SubexponentialSAT.SqrtLog.HashCircuitProgram.Native.Clause

/-! Component: HashCircuitProgramRow. All public namespaces and APIs are retained. -/


/-! The actual nested hash-row interpreter. The only inputs below are serialized
literal clauses, flat represented scalars, the selected incidence dictionary,
and the ring/cache words used by the native services. -/
namespace SubexponentialSAT.SqrtLog.HashCircuitProgram.Native.Row
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls
open SubexponentialSAT.SubexpLiftRing SubexponentialSAT.SubexpQuarticRing
open MomentsProgram

def base (regs : Fin 8 → Bool) (e : Product.Store) (high : Fin 40 → List Bool) (acc : List Bool) : Machine :=
  Memory.state regs (Product.tapes e) (baseHigh high acc)

end SubexponentialSAT.SqrtLog.HashCircuitProgram.Native.Row

/-! Component: HashCircuitProgramRun. All public namespaces and APIs are retained. -/


/-! Compiled fixed-program trace for one serialized sparse hash row. The
initial accumulator is physically cleared, and the final halt is charged. -/

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_HashInputProgramFrame
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Paid construction of the agreed inline record payload: a framed flat ring
coefficient followed by the ORIGINAL canonical literal-list payload. -/
namespace SubexponentialSAT.SqrtLog.HashInputProgram.Frame
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.SubexpScanPrimitives

def data (regs : Fin 3 → Bool) (weight clause tmp : List Bool) : State 3 3 :=
  ⟨regs,![weight,clause,tmp]⟩

end SubexponentialSAT.SqrtLog.HashInputProgram.Frame

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_HashInputProgramSource
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Physical positional lookup in the ORIGINAL encoded clause list. The index
is a canonical natural field; all preceding records are scanned and discarded.
The master source is copied, preserved, and charged. No pre-expanded hash input
table is assumed. -/
namespace SubexponentialSAT.SqrtLog.HashInputProgram.Source
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.SubexpScanPrimitives

abbrev Data := State 3 6
def data (v p f : Bool) (master scan index payload tmp out : List Bool) : Data :=
  ⟨ExecCNFRecords.regs v p f, ![master,scan,index,payload,tmp,out]⟩

end SubexponentialSAT.SqrtLog.HashInputProgram.Source

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_HashInputProgramLoopDecode
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Fixed native decoding of one raw hash digit.  The width and modulus are
runtime data.  A digit is split into its coefficient quotient and original
clause-index remainder; the latter is emitted in the source list's canonical
natural-field syntax.  No expanded clause payload is an input. -/
namespace SubexponentialSAT.SqrtLog.HashInputProgram.LoopDecode
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.SubexpScanPrimitives

abbrev Data := State 8 14

abbrev data (regs : Fin 8 → Bool) (raw width modulus chunk remainder quotient index : List Bool) : Data :=
  ⟨regs,tapes raw width modulus chunk remainder quotient index⟩

abbrev take : Cmd 8 14 := takeWord 1 2 3 0 4 0 1

abbrev divide : Cmd 8 14 := .call (SubexponentialSAT.ModularQuotientLift.programAt divisionPorts)

abbrev encode : Cmd 8 14 := .call (ProgramLinking.liftProgram
  SubexponentialSAT.CounterConversions.encodeNatProgram conversionRegisters conversionStacks)

end SubexponentialSAT.SqrtLog.HashInputProgram.LoopDecode

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_HashInputProgramLoopReverse
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! The raw selector parser exposes a reversed payload. Decode its last
fixed-width digit first, reversing only that digit, so prepending emitted
records later restores the original tuple order. -/
namespace SubexponentialSAT.SqrtLog.HashInputProgram.LoopDecode
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.SubexpScanPrimitives

abbrev reverseChunk : Cmd 8 14 := .call (StackRoutines.reverseProgram 4 2 3 0 1)

abbrev reversedCommand : Cmd 8 14 := .seq take (.seq reverseChunk (.seq divide encode))

def reversedProgram := compiled reversedCommand 0 12

end SubexponentialSAT.SqrtLog.HashInputProgram.LoopDecode

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_HashInputProgramLoopTerm
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Assembly of one raw tuple term. All source lookup, coefficient lifting,
and record framing are executed by fixed native programs. The only persistent
data are the unexpanded original source, word width, modulus, ring shape,
unread raw bytes, and the already emitted output. -/
namespace SubexponentialSAT.SqrtLog.HashInputProgram.Loop
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.SubexpScanPrimitives

abbrev Data := State 8 24

def data (regs : Fin 8 → Bool)
    (raw width modulus master shape acc quotient index payload shapeTmp : List Bool) : Data :=
  ⟨regs,tapes raw width modulus master shape acc quotient index payload shapeTmp⟩

abbrev decode : Cmd 8 24 := .call (ProgramLinking.liftProgram
  LoopDecode.reversedProgram id decoderStacks)

abbrev lookup : Cmd 8 24 := .call (ProgramLinking.liftProgram
  Source.fetchProgram lowRegisters lookupStacks)

abbrev copyShape : Cmd 8 24 := .call (StackRoutines.copyProgram 15 19 20 0 1)

abbrev normalize : Cmd 8 24 := .call (ProgramLinking.liftProgram
  SubexponentialSAT.ModularRingPrograms.normalizeProgram id normalizationStacks)

abbrev frameWeight : Cmd 8 24 := .call (ProgramLinking.liftProgram
  Frame.program lowRegisters frameStacks)

abbrev frameRecord : Cmd 8 24 := .call (ProgramLinking.liftProgram
  Frame.program lowRegisters recordStacks)

abbrev tagRecord : Cmd 8 24 := .seq (.base (.atom (.set 0 true))) (.base (.atom (.push 16 0)))

end SubexponentialSAT.SqrtLog.HashInputProgram.Loop

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_HashInputProgramLoop
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! A fixed raw-tuple assembler. The machine traverses raw digit bytes, not a
pre-expanded clause table. Each step looks up one ORIGINAL source clause and
emits its lifted coefficient plus unchanged canonical literal bytes. -/
namespace SubexponentialSAT.SqrtLog.HashInputProgram.Loop
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls

abbrev term : Cmd 8 24 := .seq decode (.seq lookup (.seq copyShape
  (.seq normalize (.seq frameWeight (.seq frameRecord tagRecord)))))

abbrev peek : Cmd 8 24 := .seq (.base (.atom (.pop 0 0 1)))
  (.ite 1 (.base (.atom (.push 0 0))) (.base .skip))

abbrev loop : Cmd 8 24 := .seq peek (.while 1 (.seq term peek))

end SubexponentialSAT.SqrtLog.HashInputProgram.Loop

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_HashInputProgramLoopFinal
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Public raw-input ABI and the uniform paid execution theorem. All control
tables are fixed independently of source size, raw tuple length and ring width.
Repeated source references and zero coefficients remain separate records. -/
namespace SubexponentialSAT.SqrtLog.HashInputProgram.Loop
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls

abbrev initializeRow : Cmd 8 24 := .seq (.base (.atom (.set 0 false))) (.base (.atom (.push 16 0)))

abbrev assemble : Cmd 8 24 := .seq initializeRow loop
def assembleProgram := compiled assemble 0 16

end SubexponentialSAT.SqrtLog.HashInputProgram.Loop

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_HashParametersProgramLog
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Native logarithmic component of the hash-parameter setup. -/
namespace SubexponentialSAT.SqrtLog.HashParametersProgram

open BitProgram StructuredCalls BinaryArithmetic SubexpBlockParameterProgram

abbrev resetLog : Cmd 3 3 := .base (SubexpParameterProgram.atoms
  [.set 0 false, .set 1 false, .set 2 false])

abbrev logCommand : Cmd 3 3 := .seq resetLog Setup.logSucc

abbrev logCall : Cmd 8 22 := liftCommand logCommand 0 0 logRegisters logStacks

abbrev copyClause : Cmd 8 22 := ArithmeticExpressionSupport.copyCmd 1 3 21

end SubexponentialSAT.SqrtLog.HashParametersProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_HashParametersProgramFinal
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Production hash-parameter program. The arithmetic, ABI, and cost proofs
are checked together; the former split module paths remain compatibility
imports of this file. -/

/-! Fixed native arithmetic for alphabet size, sparse-code distance parameter,
and selector round cap. Every operation is a proved finite Boolean program. -/


/-! Exact metadata loading and selector-port installation. Metadata is outside
all fourteen selector ports. The fixed scratch bank is physically cleared. -/
namespace SubexponentialSAT.SqrtLog.HashParametersProgram.ABI

open BitProgram StructuredCalls SubexpSetupStorage

def prepared (a : Data) : Data := prepareState 39 work inputs a

/-- Assertion notation for the returned frame; the executable object is command. -/
noncomputable def returned (a : Data) (out : State 8 22) : Data :=
  finishState work outputs (embedState registers stackMap (prepared a) out)

end SubexponentialSAT.SqrtLog.HashParametersProgram.ABI


/-! Polynomial step budget for the complete physical parameter setup. -/


/-! Exported fixed program and the selector's actual fourteen-port interface. -/
namespace SubexponentialSAT.SqrtLog.HashParametersProgram.ABI

open BitProgram StructuredCalls SubexpSetupStorage

def selectorState (a : Data) : State 10 14 := projectState selectorRegisters selectorStacks a

def ReadyInput (a : Data) : Prop := Execution.HashInputs.Ready (selectorState a)

end SubexponentialSAT.SqrtLog.HashParametersProgram.ABI

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SubexpLiteralChunkProgram
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# Actual literal-index to chunk-index conversion

The input is one reversed canonical unary literal field and a binary chunk
width. The fixed program decodes the variable index, counts it into binary,
divides by the chunk width, and constructs the reversed canonical chunk field.
-/

namespace SubexponentialSAT.SubexpLiteralChunkProgram

open BitProgram StructuredCalls StackRoutines


abbrev clearRemainder : Cmd 8 19 := .call (clearProgram 0 0 1)

end SubexponentialSAT.SubexpLiteralChunkProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_HashScopeProgramMarkedSource
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Native lookup of the optional original marked clause. Local ports49/50
stage original masters705/706; source14 stages original formula700. -/
namespace SubexponentialSAT.SqrtLog.HashScopeProgram.Marked
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls
open SubexponentialSAT.Subexp.BlockSearchPreparation (restrictState )

abbrev Data := State 11 80

end SubexponentialSAT.SqrtLog.HashScopeProgram.Marked

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_HashScopeProgramRawTable
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Direct table adapter: raw clause-reference rows to deduplicated scope rows.
The original source table and all decoding parameters remain on their tapes. -/
namespace SubexponentialSAT.SqrtLog.HashScopeProgram.RawTable
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls
open SubexponentialSAT.Subexp.BlockSearchPreparation (restrictState )

abbrev reverse : Cmd 11 49 := .call (ProgramLinking.liftProgram
  SubexpNormalizeProgram.reverseRecordsProgram reverseRegisters reverseStacks)

end SubexponentialSAT.SqrtLog.HashScopeProgram.RawTable

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_HashScopeProgramMarkedTableCalls
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.HashScopeProgram.Complete
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls
open SubexponentialSAT.Subexp.BlockSearchPreparation (restrictState )

abbrev Data := Marked.Data

def reverseProgram := compiled RawTable.reverse 46 46

abbrev initializeCmd : Cmd 11 80 := SubexponentialSAT.Subexp.TupleProgram.pushConst 48 8 false

end SubexponentialSAT.SqrtLog.HashScopeProgram.Complete

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_IrreducibleSearchBootstrapBounds
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.IrreducibleSearchBootstrap


theorem totalCost_sizeDegreeBound {d Q : ℕ} (h : 3 ^ d ≤ 16 * (Q + 1)^2) :
    totalCost d ≤
      (preparationConstant * 16^4 + 531441 * 16^5 + 1) * (Q + 1)^10 := by
  have hprep := cost_sizeDegreeBound h
  have hscan := IrreducibleSearchCandidateControl.searchCost_sizeDegreeBound h
  have hp : (Q + 1)^8 ≤ (Q + 1)^10 := pow_le_pow_right₀ (by omega) (by decide)
  have h1 : 1 ≤ (Q + 1)^10 := Nat.one_le_pow _ _ (by omega)
  have hprep' := hprep.trans (Nat.mul_le_mul_left (preparationConstant * 16^4) hp)
  unfold totalCost
  calc
    _ ≤ (preparationConstant * 16^4) * (Q + 1)^10 +
        (531441 * 16^5) * (Q + 1)^10 + (Q + 1)^10 :=
      Nat.add_le_add (Nat.add_le_add hprep' hscan) h1
    _ = _ := by simp only [add_mul, one_mul]


end SubexponentialSAT.SqrtLog.IrreducibleSearchBootstrap

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_SetupSearch
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.Setup.Search

open BitProgram StructuredCalls
open CounterPrograms (value ripple)

abbrev guard : Cmd 8 15 :=
  .call (ProgramLinking.liftProgram (compiled Guard.command 0 0) id guardPorts)

abbrev incrementPorts : CounterForPrograms.Ports 8 15 :=
  ⟨CeilingDivisionPrograms.registers, 0, 11, by decide⟩

abbrev loopPorts : CounterForPrograms.Ports 8 15 :=
  ⟨CeilingDivisionPrograms.registers, 13, 14, by decide⟩

abbrev save : Cmd 8 15 :=
  .seq (ArithmeticExpressionSupport.clearCmd 12) (ArithmeticCalls.copyAt 0 12 11)

abbrev body : Cmd 8 15 :=
  .seq (CeilingDivisionPrograms.incrementCmd incrementPorts)
    (.seq guard (.ite 0 save (.base .skip)))

abbrev command : Cmd 8 15 := CounterForPrograms.forCmd loopPorts body

end SubexponentialSAT.SqrtLog.Setup.Search

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_SetupCleanup
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.Setup.Cleanup

open BitProgram StructuredCalls

def clearMany {S : ℕ} : List (Fin S) → Cmd 8 S
  | [] => .base .skip
  | i::is => .seq (ArithmeticExpressionSupport.clearCmd i) (clearMany is)

end SubexponentialSAT.SqrtLog.Setup.Cleanup

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafParameterArithmeticSqrt
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Actual finite square-root calls. Search is bounded by the runtime input
value, which is charged explicitly; arbitrary padding is charged separately. -/
namespace SubexponentialSAT.SqrtLog.LeafParameterArithmetic

open BitProgram StructuredCalls
open CounterPrograms (value)

abbrev sqrtLocal : Cmd 8 15 :=
  .seq (ArithmeticExpressionSupport.pushWord 1 [true])
    (.seq (ArithmeticCalls.copyAt 2 13 11)
      (.seq Setup.Search.command (Setup.Cleanup.clearMany [0,1,13])))

end SubexponentialSAT.SqrtLog.LeafParameterArithmetic

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafParameterArithmetic
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Framed runtime square-root and quotient interfaces for parameter pipelines.
All program syntax is fixed by the port maps, never by the operand values. -/
namespace SubexponentialSAT.SqrtLog.LeafParameterArithmetic


open BitProgram StructuredCalls
open BinaryArithmetic (toNat)

abbrev sqrtAt {S : ℕ} (p : SqrtPorts S) : Cmd 8 S :=
  .call (ProgramLinking.liftProgram (compiled sqrtLocal 2 12) id (sqrtBlock p))

end SubexponentialSAT.SqrtLog.LeafParameterArithmetic

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafParametersProgramNative
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Native runtime leaf parameter production, integer guards, and paid setup.
The former composition modules are import-only compatibility shims. -/


/- Component: SubexponentialSAT.SqrtLog.LeafParametersProgramBankRoots -/

/-! A fixed ten-comparison bit guard. All operands are runtime binary words.
This module states their data relation separately from parameter production. -/

namespace SubexponentialSAT.SqrtLog.LeafParametersProgram.Circuit

open BitProgram StructuredCalls BinaryArithmetic Bank

@[simp] theorem budget_append (xs ys : List Instr) (m : Model) :
    budget (xs++ys) m=budget xs m+budget ys (result xs m) := by
  induction xs generalizing m with
  | nil => simp [budget,result]
  | cons x xs ih => simp [budget,result,ih,Nat.add_assoc]

end SubexponentialSAT.SqrtLog.LeafParametersProgram.Circuit


/- Component: SubexponentialSAT.SqrtLog.LeafParametersProgramLayout -/


end OAI.Algorithms
end


