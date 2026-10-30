-- Prove2me | Definitions.Def_OAIQ081S050
-- name    : OAIQ081S050
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-29T21:37:23.902842+00:00
-- url     : https://prove2.me/theorems/5e1f39b9-d16f-4d8d-865f-17e30c768da2
-- title:
--   Definitions bundle OAIQ081S050 of the split of OpenAI, The Exponential Time Hypothesis is False
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.exact_count_and_sat`, carved from OpenAI's openai/math development (OpenAI, *The Exponential Time Hypothesis is False*, OpenAI Math Release, October 25, 2026, result family 378, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 134 declarations of OpenAI's Lean: 87 definitions and 47 theorems. The definitions and types are `OAI.Algorithms.SubexponentialSAT.SqrtLog.CodeRowsProgram.Cell.program`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.CodeRowsProgram.Shift.cell`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.CodeRowsProgram.Shift.command`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.CodeRowsProgram.Shift.loop`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.CodeRowsProgram.Shift.program`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.CodeRowsProgram.Shift.step`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.CodeRowsProgram.checkRows`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.CodeRowsProgram.collectedRows`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.CodeRowsProgram.matrixSuffix`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.CodeRowsProgram.prefixSlots`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.CodeRowsProgram.rowStream`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.CodeRowsProgram.shiftRows`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.CodeRowsProgram.vertexPairs`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.CodeRowsProgram.vertexPrefix`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.CodeRowsProgram.vertexRows`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.CodeSearchProgram.ScanState`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.CodeSearchProgram.SearchState`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.CodeSearchProgram.alphabetBits`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.CodeSearchProgram.framedAlphabet`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.CodeSearchProgram.framedMatrix`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.CodeSearchProgram.framedScalarCode`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.CodeSearchProgram.framedVector`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.CodeSearchProgram.literalState`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.CodeSearchProgram.matrixFrames`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.CodeSearchProgram.matrixInput`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.CodeSearchProgram.matrixOutput`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.CodeSearchProgram.preparedWord`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.CodeSearchProgram.scalarFrames`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.CodeSearchWalshProgram.check`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.CodeSearchWalshProgram.clearCount`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.CodeSearchWalshProgram.count`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.CodeSetupCost.fixedConstant`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.CodeSetupOuterCost.searchExponent`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.CodeSetupOuterCost.setupMajorant`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.IdempotentPreparationProgram.preparationBudget`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.IdempotentProgram.completeBudget`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.IdempotentProgram.nativeLiftBudget`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.evaluate`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.factorPairs`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.pairPass` and 47 more.
--
--   **Sources.** They come from these modules of lean/OAI/Algorithms, in whole or in part: `SubexponentialSAT_SqrtLog_CodeRowsProgramCell`, `SubexponentialSAT_SqrtLog_CodeRowsProgramCheckLoop`, `SubexponentialSAT_SqrtLog_CodeRowsProgramPortSemantic`, `SubexponentialSAT_SqrtLog_CodeRowsProgramPrefix`, `SubexponentialSAT_SqrtLog_CodeRowsProgramRows`, `SubexponentialSAT_SqrtLog_CodeRowsProgramShiftBasic`, `SubexponentialSAT_SqrtLog_CodeRowsProgramStream`, `SubexponentialSAT_SqrtLog_CodeRowsProgramVertexLoop`, `SubexponentialSAT_SqrtLog_CodeRowsProgramVertexStep`, `SubexponentialSAT_SqrtLog_CodeSearchProgramFramed`, `SubexponentialSAT_SqrtLog_CodeSearchProgramGenerate`, `SubexponentialSAT_SqrtLog_CodeSearchProgramMatrix`, `SubexponentialSAT_SqrtLog_CodeSearchProgramPrepare`, `SubexponentialSAT_SqrtLog_CodeSearchProgramScan`, `SubexponentialSAT_SqrtLog_CodeSearchWalshProgramChecks`, `SubexponentialSAT_SqrtLog_CodeSearchWalshProgramCount`, `SubexponentialSAT_SqrtLog_CodeSetupCostNative`, `SubexponentialSAT_SqrtLog_CodeSetupOuterCostMajorant`, `SubexponentialSAT_SqrtLog_IdempotentPreparationProgram`, `SubexponentialSAT_SqrtLog_IdempotentProgramComplete`, `SubexponentialSAT_SqrtLog_IdempotentProgramFinal`, `SubexponentialSAT_SqrtLog_IrreducibleSearch`, `SubexponentialSAT_SqrtLog_IrreducibleSearchBasic`, `SubexponentialSAT_SqrtLog_IrreducibleSearchBootstrapPreparation`, `SubexponentialSAT_SqrtLog_IrreducibleSearchEnumeration`, `SubexponentialSAT_SqrtLog_IrreducibleSearchEnumerationCost`, `SubexponentialSAT_SqrtLog_IrreducibleSearchNativeScan`, `SubexponentialSAT_SqrtLog_IrreducibleSearchProgramScalar`, `SubexponentialSAT_SqrtLog_IrreducibleSearchProgramStorage`, `SubexponentialSAT_SqrtLog_LeafNodeSamplesProgram`, `SubexponentialSAT_SqrtLog_LeafRingSetupProgramNative`, `SubexponentialSAT_SqrtLog_LeafStatisticsProgramBinary`, `SubexponentialSAT_SqrtLog_RingScanServiceLifts`, `SubexponentialSAT_SqrtLog_SetupGuard`, `SubexponentialSAT_SqrtLog_SetupPrimitives`, `SubexponentialSAT_SubexpConvolutionPair`, `SubexponentialSAT_SubexpEnumerationPayload`, `SubexponentialSAT_SubexpEnumerationProgram`, `SubexponentialSAT_SubexpEvaluationProgram`, `SubexponentialSAT_SubexpGuardProgram`, `SubexponentialSAT_SubexpOrderedTupleStep`, `SubexponentialSAT_SubexpParameterProgram`, `SubexponentialSAT_SubexpPostfixControl`, `SubexponentialSAT_SubexpPostfixGlobal`, `SubexponentialSAT_SubexpPostfixInterpreter`, `SubexponentialSAT_SubexpSetupStorage`, `SubexponentialSAT_Subexp_BasisTransposeProgram`, `SubexponentialSAT_Subexp_CollisionStreamProgram`, `SubexponentialSAT_Subexp_GatherProgram`, `SubexponentialSAT_Subexp_MatrixScalarProgram`, `SubexponentialSAT_Subexp_MatrixVectorProgram`, `SubexponentialSAT_Subexp_PairScoreProgram`, `SubexponentialSAT_Subexp_TupleProgram`.
--
--   **Imports.** It imports the published bundle `Def_SubexponentialSAT`; the bundles `OAIQ081S023`, `OAIQ081S024`, `OAIQ081S025`, `OAIQ081S027`, `OAIQ081S028`, `OAIQ081S029` and `OAIQ081S030` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ081S069`, `OAIQ081S070`, `OAIQ081S071`, `OAIQ081S072`, `OAIQ081S073`, `OAIQ081S075`, `OAIQ081S076`, `OAIQ081S077`, `OAIQ081S078`, `OAIQ081S079` and `OAIQ081S081`; the statements `OAI.Algorithms.SubexponentialSAT.SqrtLog.CodeSearchProgram.graphCountTail_eval`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.CodeSearchProgram.matrixFrames_ternary_length` and `OAI.Algorithms.SubexponentialSAT.SqrtLog.CodeSearchProgram.wordTail_eval`; the proof of `OAI.Algorithms.SubexponentialSAT.SqrtLog.CodeSearchProgram.matrixFrames_ternary_length`.
-- source:
--   OpenAI, The Exponential Time Hypothesis is False, OpenAI Math Release, October 25, 2026, https://github.com/openai/math (result family 378; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/The-Exponential-Time-Hypothesis-is-False-October-25-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Algorithms at commit 7ef5c0c

import Mathlib
import Definitions.Def_SubexponentialSAT
import Definitions.Def_OAIQ081S023
import Definitions.Def_OAIQ081S024
import Definitions.Def_OAIQ081S025
import Definitions.Def_OAIQ081S027
import Definitions.Def_OAIQ081S028
import Definitions.Def_OAIQ081S029
import Definitions.Def_OAIQ081S030

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SubexpEnumerationPayload
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# A fixed machine emitting the encoded increment schedule

The input contains the actual one-pass increment payload and the unary number
of outer basepoints.  `BlockCopyProgram.program` preserves that payload and
emits one copy for each outer basepoint.  The payloads below are computed from
the supplied vector arrays, and their lengths follow from the proved coset
cardinalities rather than from numerical premises about execution.

This is the increment schedule used by the separate color sums.  It does not
construct the basis arrays, add outer basepoints, or evaluate the summands.
The cost of preparing the input stacks remains a separate obligation.
-/

namespace SubexponentialSAT.SubexpEnumerationPayload

open scoped BigOperators

theorem scalarBits_value {p : ℕ} [Fact p.Prime] (x : ZMod p) :
    BinaryArithmetic.toNat (scalarBits x) = x.val := by
  apply SubexpLiftRing.toNat_fixedBits_of_lt
  exact x.val_lt.trans (Nat.lt_pow_succ_log_self Nat.one_lt_two p)

theorem scalarBits_injective {p : ℕ} [Fact p.Prime] :
    Function.Injective (scalarBits (p := p)) := by
  intro a b h
  have hv := congrArg BinaryArithmetic.toNat h
  simp only [scalarBits_value] at hv
  simpa using congrArg (fun n : ℕ => (n : ZMod p)) hv

def scalarCode (p : ℕ) [Fact p.Prime] : StackEncoding.BlockCode (ZMod p) where
  width := scalarWidth p
  width_pos := Nat.zero_lt_succ _
  block := scalarBits
  length_block := scalarBits_length
  injective_block := scalarBits_injective

end SubexponentialSAT.SubexpEnumerationPayload

end OAI.Algorithms
end

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

def tupleCost (alphabet : Records) (tuple : List Bool) : ℕ :=
  7 * (ProgramEncoding.encodeRecords alphabet).length +
    RecordPrograms.budget (fun word => 5 * word.length + 12 * tuple.length + 15) alphabet +
    2 * tuple.length + 11

def expansionCost (tuples alphabet : Records) : ℕ :=
  3 + RecordPrograms.budget (tupleCost alphabet) tuples

end SubexponentialSAT.Subexp.TupleProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_Subexp_GatherProgram
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# A fixed program gathering runtime-selected rows

The packed assignment is on stack 0 and its unary row width on stack 3.
Stack 8 contains `ProgramEncoding.encodeRecords` of unary index words.
The program preserves the assignment and width and writes the selected rows,
in plan order, to stack 1. All widths and indices are stack data.
-/

namespace SubexponentialSAT.Subexp.GatherProgram

open BitProgram StackRoutines StructuredCalls

def ports : RecordPrograms.Ports 3 10 where
  tag := 0
  present := 1
  found := 2
  source := 8
  payload := 2
  tag_ne_present := by decide
  found_ne_tag := by decide
  found_ne_present := by decide
  source_ne_payload := by decide

def baseState (array width acc : List Bool) : State 3 10 :=
  ⟨fun _ => false,
   fun j => if j = 0 then array else if j = 3 then width else if j = 9 then acc else []⟩

def inputState (rows : List (List Bool)) (width : List Bool) (plan : List ℕ) : State 3 10 :=
  RecordPrograms.state ports (baseState rows.flatten width []) false false false
    (ProgramEncoding.encodeRecords (indexRecords plan)) []

def outputState (rows : List (List Bool)) (width : List Bool) (plan : List ℕ) : State 3 10 :=
  ⟨fun _ => false,
   fun j => if j = 0 then rows.flatten else if j = 3 then width
     else if j = 1 then gathered rows plan else []⟩

@[simp] theorem inputState_array (rows : List (List Bool)) (width : List Bool) (plan : List ℕ) :
    (inputState rows width plan).stacks 0 = rows.flatten := by
  simp [inputState, ports, RecordPrograms.state, baseState]

@[simp] theorem inputState_width (rows : List (List Bool)) (width : List Bool) (plan : List ℕ) :
    (inputState rows width plan).stacks 3 = width := by
  simp [inputState, ports, RecordPrograms.state, baseState]

@[simp] theorem inputState_plan (rows : List (List Bool)) (width : List Bool) (plan : List ℕ) :
    (inputState rows width plan).stacks 8 = ProgramEncoding.encodeRecords (indexRecords plan) := by
  simp [inputState, ports, RecordPrograms.state, baseState]

@[simp] theorem outputState_array (rows : List (List Bool)) (width : List Bool) (plan : List ℕ) :
    (outputState rows width plan).stacks 0 = rows.flatten := by simp [outputState]

@[simp] theorem outputState_width (rows : List (List Bool)) (width : List Bool) (plan : List ℕ) :
    (outputState rows width plan).stacks 3 = width := by simp [outputState]

@[simp] theorem outputState_output (rows : List (List Bool)) (width : List Bool) (plan : List ℕ) :
    (outputState rows width plan).stacks 1 = gathered rows plan := by simp [outputState]

end SubexponentialSAT.Subexp.GatherProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_Subexp_CollisionStreamProgram
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# A fixed collision callback with a persistent output stream

The runtime ABI reserves stack 0 for a packed row table, stack 3 for its unary
word width, stacks 8 and 10 for the two read plans, and stack 11 for the output
stream. Stacks 1 and 12 hold the two gathered type encodings. The remaining
stacks are gathering scratch. All sizes, plans, and encoded words are data.

The equality stage below uses the existing fixed equality program, clears its
possibly unconsumed input suffixes, and pushes one collision bit. In particular,
an early mismatch cannot leave stale type bytes in the next callback's scratch.
-/

namespace SubexponentialSAT.Subexp.CollisionStreamProgram

open BitProgram StackRoutines StructuredCalls

def planBytes (plan : List ℕ) : List Bool :=
  ProgramEncoding.encodeRecords (GatherProgram.indexRecords plan)

end SubexponentialSAT.Subexp.CollisionStreamProgram

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

abbrev Data := StructuredProgram.State 13 26

/-- Public pair-record payload: exactly two consecutive escape frames, each
containing the selected plan's ordinary unary-index record encoding. -/
def pairBytes (pair : PlanPair) : List Bool :=
  Encoding.frame (CollisionStreamProgram.planBytes pair.1) ++
    Encoding.frame (CollisionStreamProgram.planBytes pair.2)

/-- Persistent ports are current 13, width 3, alphabet 19, depth template 23.
Stream 11 accumulates leaves; stack 18 is reserved for the final unary score. -/
def baseState (ctx : Context) (stream : List Bool) : Data :=
  ⟨fun j => decide (j = 11), fun j =>
    if j = 3 then ctx.width else if j = 13 then ctx.current.flatten
    else if j = 19 then ProgramEncoding.encodeRecords ctx.alphabet
    else if j = 23 then ctx.depth else if j = 11 then stream else []⟩

def afterTally (d : Data) : Data :=
  ⟨readRegs d.regs 0 1 none,
    Function.update (Function.update d.stacks 11 []) 18
      (List.replicate (PaddedCompletion.trueCount (d.stacks 11)) false ++ d.stacks 18)⟩

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

abbrev Data := StructuredProgram.State 8 16

abbrev state (regs : Fin 8 → Bool)
    (x y modulus acc left right saved output zero input : List Bool) : Data :=
  ⟨regs, scalarStacks x y modulus acc left right saved output zero input⟩

abbrev add : Cmd 8 16 :=
  .call (ProgramLinking.liftProgram wordAddProgram id servicePort)

end SubexponentialSAT.Subexp.MatrixScalarProgram

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

def matrixWords : List (List (List Bool)) → List Bool
  | [] => []
  | ys :: rows => words ys ++ matrixWords rows

end SubexponentialSAT.Subexp.MatrixVectorProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_CodeSearchProgramMatrix
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Concrete prime-field matrix application used by both search predicates.
All row/column counts and operands are runtime data for the same 359-label
program. The format is the actual scalar-frame stream, not a free matrix
oracle. Input recoding is kept separate from this application theorem. -/

namespace SubexponentialSAT.SqrtLog.CodeSearchProgram

open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls
open SubexponentialSAT.Subexp
open scoped BigOperators

def scalarFrames {p : ℕ} [Fact p.Prime] (xs : List (ZMod p)) : List Bool :=
  MatrixProgramSupport.words (xs.map (MatrixWordEncoding.word p))

def matrixFrames {p t D : ℕ} [Fact p.Prime]
    (Q : Fin t → Fin D → ZMod p) : List Bool :=
  MatrixVectorProgram.matrixWords
    (List.ofFn fun i => List.ofFn fun j => MatrixWordEncoding.word p (Q i j))

def matrixInput {p t D : ℕ} [Fact p.Prime]
    (Q : Fin t → Fin D → ZMod p) (x : Fin D → ZMod p)
    (regs : Fin 8 → Bool) : State 8 16 :=
  MatrixScalarProgram.state regs [] [] (MatrixWordEncoding.modulus p) [] []
    (matrixFrames Q) (scalarFrames (List.ofFn x)) []
    (MatrixWordEncoding.zero p) (List.replicate t true)

def matrixOutput {p t D : ℕ} [Fact p.Prime]
    (Q : Fin t → Fin D → ZMod p) (x : Fin D → ZMod p)
    (regs : Fin 8 → Bool) : State 8 16 :=
  MatrixScalarProgram.state regs [] [] (MatrixWordEncoding.modulus p)
    (scalarFrames (List.ofFn fun i => ∑ j, Q i j * x j)) [] []
    (scalarFrames (List.ofFn x)) [] (MatrixWordEncoding.zero p) []

end SubexponentialSAT.SqrtLog.CodeSearchProgram

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

def program := compiled command 0 0

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

abbrev cell : Cmd 8 4 := .call (ProgramLinking.liftProgram Cell.program cellRegisters cellStacks)

abbrev step : Cmd 8 4 := .seq cell (.seq combine (.base (.atom (.push 2 4))))
abbrev loop : Cmd 8 4 := .seq pop (.while 5 (.seq step pop))
abbrev command : Cmd 8 4 := .seq loop (.call (StackRoutines.transferProgram 2 3 0 1))
def program := compiled command 0 3

end SubexponentialSAT.SqrtLog.CodeRowsProgram.Shift

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SubexpPostfixControl
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# Concrete postfix instruction dispatch and literal push

The fixed prefix tags are push `0`, add `10`, and multiply `11`.
A push tag is followed by an `Encoding.frame` coefficient payload. End of
the code stack ends the instruction stream. The base dispatcher exposes
explicit service exits. The linked program implements literal push through
the actual frame parser and a Boolean-stack encoding loop; scalar arithmetic
remains at explicit service boundaries.

Registers: 0 last bit, 1 successful-pop flag, 2 binary-operation flag.
Stacks: 0 serialized code, 1 unary operand depth, 2 framed operand data.
The operand data stack is preserved throughout dispatch. On a successful
dispatch the depth stack has already been adjusted for the pending service.
The linked literal service uses stack 3 as initially empty scratch and returns
to dispatch with that scratch empty and the framed operand list updated.
-/

namespace SubexponentialSAT.SubexpPostfixControl

open BitProgram

/-! ## Serialization of the existing postfix instruction type -/

/-! ## Literal-push service with the framed-list operand ABI -/

@[simp] theorem update_quadruple_zero {α : Type*} (a b c d e : α) :
    Function.update (quadruple a b c d) 0 e = quadruple e b c d := by
  funext i; fin_cases i <;> simp [quadruple]
@[simp] theorem update_quadruple_one {α : Type*} (a b c d e : α) :
    Function.update (quadruple a b c d) 1 e = quadruple a e c d := by
  funext i; fin_cases i <;> simp [quadruple]
@[simp] theorem update_quadruple_two {α : Type*} (a b c d e : α) :
    Function.update (quadruple a b c d) 2 e = quadruple a b e d := by
  funext i; fin_cases i <;> simp [quadruple]
@[simp] theorem update_quadruple_three {α : Type*} (a b c d e : α) :
    Function.update (quadruple a b c d) 3 e = quadruple a b c e := by
  funext i; fin_cases i <;> simp [quadruple]

end SubexponentialSAT.SubexpPostfixControl

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SubexpPostfixInterpreter
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# A finite postfix interpreter with linked arithmetic services

The interpreter contains the concrete tag dispatcher and literal loader, two
initialization instructions, and the supplied finite arithmetic instruction
tables. Arithmetic correctness is required as a local Boolean-machine trace
contract; an arithmetic operation is never added to the instruction language.
-/

namespace SubexponentialSAT.SubexpPostfixInterpreter

open BitProgram
open SubexpPostfixControl

variable {r s a b : ℕ}

/-- Scratch stack 3 is empty. Additional stacks carry the fixed arithmetic
context, including empty scratch slots and persistent ring parameters. -/
def cfg {l : ℕ} (pc : Option (Fin l)) (v p op : Bool)
    (code depth operands : List Bool) (context : Fin s → List Bool := fun _ => []) :
    Cfg (3 + r) (4 + s) l where
  pc := pc
  regs := Fin.addCases (triple v p op) (fun _ => false)
  «stacks» := Fin.addCases (quadruple code depth operands []) context

end SubexponentialSAT.SubexpPostfixInterpreter

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SubexpPostfixGlobal
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# Shared-machine port adapter for the concrete postfix interpreter

The shared machine uses code/depth/operand/scratch stacks 26/28/27/29.
A fixed permutation installs the proved interpreter there while accepting
arithmetic service tables already written for the shared 16-register,
128-stack machine. Port renaming adds no machine transitions.
-/

namespace SubexponentialSAT.SubexpPostfixGlobal

open BitProgram
open SubexpPostfixInterpreter

def physicalCfg {l : ℕ} (pc : Option (Fin l)) (v p op : Bool)
    (code depth operands : List Bool) (context : Fin 124 → List Bool) : Cfg 16 128 l :=
  reindexCfg ports (cfg (r := 13) (s := 124) pc v p op code depth operands context)

@[simp] theorem physicalCfg_code {l : ℕ} (pc : Option (Fin l)) (v p op : Bool)
    (code depth operands : List Bool) (context : Fin 124 → List Bool) :
    (physicalCfg pc v p op code depth operands context).stacks 26 = code := by
  simp [physicalCfg, reindexCfg, cfg]
  rfl

@[simp] theorem physicalCfg_depth {l : ℕ} (pc : Option (Fin l)) (v p op : Bool)
    (code depth operands : List Bool) (context : Fin 124 → List Bool) :
    (physicalCfg pc v p op code depth operands context).stacks 28 = depth := by
  simp [physicalCfg, reindexCfg, cfg]
  rfl

@[simp] theorem physicalCfg_operands {l : ℕ} (pc : Option (Fin l)) (v p op : Bool)
    (code depth operands : List Bool) (context : Fin 124 → List Bool) :
    (physicalCfg pc v p op code depth operands context).stacks 27 = operands := by
  simp [physicalCfg, reindexCfg, cfg]
  rfl

@[simp] theorem physicalCfg_scratch {l : ℕ} (pc : Option (Fin l)) (v p op : Bool)
    (code depth operands : List Bool) (context : Fin 124 → List Bool) :
    (physicalCfg pc v p op code depth operands context).stacks 29 = [] := by
  simp [physicalCfg, reindexCfg, cfg]
  rfl

@[simp] theorem physicalCfg_context {l : ℕ} (pc : Option (Fin l)) (v p op : Bool)
    (code depth operands : List Bool) (context : Fin 124 → List Bool) (i : Fin 124) :
    (physicalCfg pc v p op code depth operands context).stacks
      (ports (Fin.natAdd 4 i)) = context i := by
  simp [physicalCfg, reindexCfg, cfg]

end SubexponentialSAT.SubexpPostfixGlobal

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SubexpEvaluationProgram
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# Concrete evaluation-result extraction

The extractor removes the singleton operand-list framing, parses the result
payload into a reversed scratch stack, and transfers it to physical stack 15.
It clears the operand/depth/scratch stacks and preserves every other stack.
-/

namespace SubexponentialSAT.SubexpEvaluationProgram

open BitProgram
open SubexpPostfixControl

def extractProgram : Program 16 128 17 where
  inputStack := 27
  outputStack := 15
  entry := 0
  code := Fin.addCases (motive := fun _ : Fin (3 + (7 + 7)) => Instr 16 128 17)
    (fun i : Fin 3 => match i.val with
      | 0 => .pop 15 0 1 1
      | 1 => .branch 1 0 2
      | _ => .pop 27 0 1 3)
    (Fin.addCases (motive := fun _ : Fin (7 + 7) => Instr 16 128 17)
      (fun i : Fin 7 => ProgramLinking.relocateInstr parserRegister parserStack parserLabel
        (some 10) (ParserProgram.frameProgram.code i))
      (fun i : Fin 7 => match i.val with
        | 0 => .pop 27 0 1 11
        | 1 => .pop 28 0 1 12
        | 2 => .set 2 false 13
        | 3 => .pop 29 0 1 14
        | 4 => .branch 1 15 16
        | 5 => .push 15 0 13
        | _ => .halt))

@[simp] theorem code0 : extractProgram.code 0 = .pop 15 0 1 1 := rfl
@[simp] theorem code1 : extractProgram.code 1 = .branch 1 0 2 := rfl
@[simp] theorem code2 : extractProgram.code 2 = .pop 27 0 1 3 := rfl
@[simp] theorem code10 : extractProgram.code 10 = .pop 27 0 1 11 := rfl
@[simp] theorem code11 : extractProgram.code 11 = .pop 28 0 1 12 := rfl
@[simp] theorem code12 : extractProgram.code 12 = .set 2 false 13 := rfl
@[simp] theorem code13 : extractProgram.code 13 = .pop 29 0 1 14 := rfl
@[simp] theorem code14 : extractProgram.code 14 = .branch 1 15 16 := rfl
@[simp] theorem code15 : extractProgram.code 15 = .push 15 0 13 := rfl
@[simp] theorem code16 : extractProgram.code 16 = .halt := rfl

open SubexpPostfixGlobal

/-- The interpreter's final stack contents before the framing is removed. -/
def snapshot (bits : List Bool) (context : Fin 124 → List Bool) : Fin 128 → List Bool :=
  (physicalCfg (l := 1) none false false false [] [true]
    (true :: (Encoding.frame bits ++ [false])) context).stacks

@[simp] theorem snapshot_operand (bits : List Bool) (context : Fin 124 → List Bool) :
    snapshot bits context 27 = true :: (Encoding.frame bits ++ [false]) :=
  physicalCfg_operands _ _ _ _ _ _ _ _

/-! ## Entry from arbitrary caller registers -/

end SubexponentialSAT.SubexpEvaluationProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_Subexp_BasisTransposeProgram
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# Gathering a searched basis table into vector-major order

The local search stores ambient coordinates as rows and basis vectors as
columns. Its scalar frames have fixed width, so the checked gather program
can transpose those frames without decoding or changing a field element.
The result is exactly the kernel/complement table consumed by block copying.

This adapter's runtime inputs are the searched table, its unary frame width,
and the explicit transpose read plan. It proves the physical reordering and
the plan's polynomial size; producing the read-plan bytes is a separate stage.
-/

namespace SubexponentialSAT.Subexp.BasisTransposeProgram

open StackEncoding

def framedCode {A : Type*} (code : BlockCode A) : BlockCode A where
  width := 2 * code.width + 1
  width_pos := by omega
  block a := Encoding.frame (code.block a)
  length_block a := by simp [code.length_block]
  injective_block := by
    intro a b h
    apply code.injective_block
    exact (Encoding.frame_append_injective (bits := code.block a) (bits' := code.block b)
      (rest := []) (rest' := []) (by simpa using h)).1

end SubexponentialSAT.Subexp.BasisTransposeProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_CodeSearchProgramFramed
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Generating framed scalar entries directly avoids an uncharged recoding
step. The same fixed tuple machine concatenates scalar frames; the outer
list frame delimits candidates, while the inner frames delimit entries. -/

namespace SubexponentialSAT.SqrtLog.CodeSearchProgram

open SubexponentialSAT.BitProgram SubexponentialSAT.Subexp.TupleProgram SubexponentialSAT.SubexpTupleRefinement
open SubexponentialSAT.SubexpEnumerationPayload

def framedScalarCode (p : ℕ) [Fact p.Prime] : StackEncoding.BlockCode (ZMod p) :=
  Subexp.BasisTransposeProgram.framedCode (scalarCode p)

def framedAlphabet (p : ℕ) [Fact p.Prime] : List (List Bool) :=
  (QuarticSearch.elements p).map (framedScalarCode p).block

def framedVector {p d : ℕ} [Fact p.Prime] (v : Fin d → ZMod p) : List Bool :=
  encodeTuple (framedScalarCode p) v

def framedMatrix {p rows cols : ℕ} [Fact p.Prime]
    (M : Fin rows → Fin cols → ZMod p) : List Bool :=
  framedVector (flattenMatrix M)

@[simp] theorem framedAlphabet_length (p : ℕ) [Fact p.Prime] :
    (framedAlphabet p).length = p := by
  simp [framedAlphabet, QuarticSearch.elements]

end SubexponentialSAT.SqrtLog.CodeSearchProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_CodeRowsProgramPrefix
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.CodeSearchProgram.instDecidableGraphWordRejects _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.CodeSearchProgram.instDecidableWordRejects _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.CodeRowsProgram

def shiftRows {r : ℕ} (xs : List (Cayley.Cube r)) : List Bool :=
  xs.flatMap fun v => Shift.frames (vertexBits v)

def prefixSlots {r D t : ℕ} (m : ℕ) (shifts : Fin D → Cayley.Cube r)
    (Q : Fin t → Fin D → SparseCode.F3) (side : Bool) (v : Cayley.Cube r)
    (a : Fin t) (i : ℕ) : List (Fin m × SparseCode.F3) :=
  ((List.finRange D).take i).filterMap (slot m shifts Q side v a)

@[simp] theorem prefixSlots_zero {r D t : ℕ} (m : ℕ) (shifts : Fin D → Cayley.Cube r)
    (Q : Fin t → Fin D → SparseCode.F3) (side : Bool) (v : Cayley.Cube r) (a : Fin t) :
    prefixSlots m shifts Q side v a 0=[] := rfl

@[simp] theorem prefixSlots_full {r D t : ℕ} (m : ℕ) (shifts : Fin D → Cayley.Cube r)
    (Q : Fin t → Fin D → SparseCode.F3) (side : Bool) (v : Cayley.Cube r) (a : Fin t) :
    prefixSlots m shifts Q side v a D=slots m shifts Q side v a := by
  have ht : (List.finRange D).take D=List.finRange D :=
    List.take_of_length_le (by simp)
  simp only [prefixSlots,slots,ht]

end SubexponentialSAT.SqrtLog.CodeRowsProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_CodeRowsProgramPortSemantic
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.CodeSearchProgram.instDecidableGraphWordRejects _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.CodeRowsProgram
open SubexponentialSAT.BinaryArithmetic

def vertexPairs {r : ℕ} (v s : Cayley.Cube r) : List (Bool × Bool) :=
  List.ofFn fun i => (decide (v i=1),decide (s i=1))

@[simp] theorem vertexPairs_first {r : ℕ} (v s : Cayley.Cube r) :
    (vertexPairs v s).map Prod.fst=vertexBits v := by
  simp [vertexPairs,vertexBits,List.map_ofFn,Function.comp_def]

@[simp] theorem vertexPairs_second {r : ℕ} (v s : Cayley.Cube r) :
    (vertexPairs v s).map Prod.snd=vertexBits s := by
  simp [vertexPairs,vertexBits,List.map_ofFn,Function.comp_def]

@[simp] theorem vertexPairs_length {r : ℕ} (v s : Cayley.Cube r) :
    (vertexPairs v s).length=r := List.length_ofFn

end SubexponentialSAT.SqrtLog.CodeRowsProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_CodeRowsProgramStream
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.CodeSearchProgram.instDecidableWordRejects _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.CodeRowsProgram

def collectedRows {m : ℕ} (b : ℕ) (rs : List (List (Fin m × SparseCode.F3)))
    (tail : List Bool) : List Bool := rowRecords b rs.reverse++tail

@[simp] theorem collectedRows_nil {m : ℕ} (b : ℕ) (tail : List Bool) :
    collectedRows (m:=m) b [] tail=tail := rfl

end SubexponentialSAT.SqrtLog.CodeRowsProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_CodeRowsProgramCheckLoop
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.CodeSearchProgram.instDecidableGraphWordRejects _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.CodeSearchProgram.instDecidableWordRejects _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.CodeRowsProgram
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.BinaryArithmetic

def matrixSuffix {D t : ℕ} (Q : Fin t → Fin D → SparseCode.F3) (i : ℕ) : List Bool :=
  ((List.ofFn fun a => CodeSearchProgram.scalarFrames (List.ofFn (Q a))).drop i).flatten

def checkRows {r D t : ℕ} (m : ℕ) (shifts : Fin D → Cayley.Cube r)
    (Q : Fin t → Fin D → SparseCode.F3) (side : Bool) (v : Cayley.Cube r) :
    List (List (Fin m × SparseCode.F3)) := List.ofFn (slots m shifts Q side v)

end SubexponentialSAT.SqrtLog.CodeRowsProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_CodeRowsProgramRows
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.CodeSearchProgram.instDecidableGraphWordRejects _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.CodeSearchProgram.instDecidableWordRejects _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! The precise order emitted by the native vertex/check loops. Each row is
present even when shortening removes every one of its local ports. -/
namespace SubexponentialSAT.SqrtLog.CodeRowsProgram
open scoped BigOperators

variable {r D t m : ℕ}

def rowStream (b m : ℕ) (shifts : Fin D → Cayley.Cube r)
    (Q : Fin t → Fin D → SparseCode.F3) : List Bool :=
  Encoding.encodeList (rowPayload b m) (serializedRows m shifts Q)

end SubexponentialSAT.SqrtLog.CodeRowsProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_CodeRowsProgramVertexStep
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.CodeSearchProgram.instDecidableGraphWordRejects _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.CodeSearchProgram.instDecidableWordRejects _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.CodeRowsProgram
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls

def vertexRows {r D t : ℕ} (m : ℕ) (shifts : Fin D → Cayley.Cube r)
    (Q : Fin t → Fin D → SparseCode.F3) (v : Cayley.Cube r) :
    List (List (Fin m × SparseCode.F3)) :=
  checkRows m shifts Q false v++checkRows m shifts Q true v

end SubexponentialSAT.SqrtLog.CodeRowsProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_CodeRowsProgramVertexLoop
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.CodeSearchProgram.instDecidableGraphWordRejects _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.CodeSearchProgram.instDecidableWordRejects _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms


namespace SubexponentialSAT.SqrtLog.CodeRowsProgram
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.BinaryArithmetic

def vertexPrefix {r D t : ℕ} (m : ℕ) (shifts : Fin D → Cayley.Cube r)
    (Q : Fin t → Fin D → SparseCode.F3) (i : ℕ) : List (List (Fin m × SparseCode.F3)) :=
  ((List.finRange (2^r)).take i).flatMap fun j =>
    vertexRows m shifts Q (WalshExistence.cubeEquiv r j)

end SubexponentialSAT.SqrtLog.CodeRowsProgram

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

def clearCmd {S : ℕ} (port : Fin S) : Command S :=
  .call (StackRoutines.clearProgram port 0 1)

def clearMany {S : ℕ} : List (Fin S) → Command S
  | [] => .base .skip
  | p :: ps => .seq (clearCmd p) (clearMany ps)

end SubexponentialSAT.SubexpSetupStorage

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_CodeSearchProgramGenerate
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! A closed storage wrapper for tuple generation. Only p is fixed in the
instruction table (we use p=2 and p=3); the tuple depth is read at runtime.
The literal alphabet, preserved depth copy, output copy, and scratch cleanup
are all paid bit operations. -/
namespace SubexponentialSAT.SqrtLog.CodeSearchProgram
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.SubexpSetupStorage
open SubexponentialSAT.Subexp.TupleProgram SubexponentialSAT.SubexpEnumerationPayload

def alphabetBits (p : ℕ) [Fact p.Prime] := ProgramEncoding.encodeRecords (framedAlphabet p)

end SubexponentialSAT.SqrtLog.CodeSearchProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_CodeSearchProgramScan
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Framed support and unary comparison as framed subroutine calls. The port
maps are fixed finite maps; the lengths being scanned occur only on tapes. -/
namespace SubexponentialSAT.SqrtLog.CodeSearchProgram
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls

abbrev ScanState := State 8 18

end SubexponentialSAT.SqrtLog.CodeSearchProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SubexpParameterProgram
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# Actual finite programs for the growing packing parameters

Numbers are little-endian Boolean stacks, with leading zeroes allowed. The
programs below manipulate only bits and stacks; natural-number quantities in
their specifications and cost bounds are not machine registers.
-/

namespace SubexponentialSAT.SubexpParameterProgram

open SubexponentialSAT.BitProgram
open SubexponentialSAT.CounterPrograms

/-! ## Consume a most-significant zero prefix and the leading one -/

/-! ## Concrete input reversal -/

/-! ## Reindex and call the checked binary word-length counter -/

abbrev swappedLengthProgram : Program 3 3 14 :=
  ProgramLinking.liftProgram lengthProgram id swapStacks

abbrev logProgram : Program 3 3 24 := ProgramLinking.link prepareLogProgram swappedLengthProgram

end SubexponentialSAT.SubexpParameterProgram

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

open StructuredProgram

/-- Compare one pair, invert strict-less, and conjoin the result into register 8. -/
abbrev checkPair (j : Fin 3) : StructuredCalls.Cmd 9 6 :=
  .seq (.call (ProgramLinking.liftProgram Compare.program workRegister (pairStack j)))
    (.base (.seq (.atom (.bnot 0 0)) (.atom (.band 8 8 0))))


end SubexponentialSAT.SubexpGuardProgram

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

@[ext] theorem data_ext {a b : Data R S} (hr : a.regs = b.regs)
    (hs : a.stacks = b.stacks) : a = b := by
  cases a
  cases b
  cases hr
  cases hs
  rfl

def localData (b present flag : Bool) (xs ys : List Bool) : Data 3 2 :=
  ⟨counterRegs b present flag, counterStacks xs ys⟩

/-- A proof-level frame embedding; executable code uses only its fixed port maps. -/
noncomputable def install (p : Ports R S) (q : Bool) (d : Data R S)
    (b present flag : Bool) (xs ys : List Bool) : Data R S :=
  StructuredCalls.embedState p.register (stackPorts p q) d (localData b present flag xs ys)

end SubexponentialSAT.SubexpEnumerationProgram

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

abbrev SearchState := State 16 24

def literalState (a : SearchState) : SearchState :=
  (Atom.push 5 0).eval ((Atom.push 5 0).eval ((Atom.set 0 true).eval
    ((Atom.push 14 0).eval ((Atom.push 14 0).eval ((Atom.push 5 0).eval
      ((Atom.set 0 false).eval a))))))

def preparedWord (a : SearchState) : SearchState :=
  literalState (SubexpScanPrimitives.afterTransfer (copyManyState inputMoves a) 22 12 0 1)


end SubexponentialSAT.SqrtLog.CodeSearchProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafStatisticsProgramBinary
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Native unary-to-binary conversion for each statistics output. -/
namespace SubexponentialSAT.SqrtLog.LeafStatisticsProgram.Binary
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls
abbrev command : Cmd 3 3 := .seq (.base (.atom (.set 2 false))) (.call CounterPrograms.lengthProgram)

end SubexponentialSAT.SqrtLog.LeafStatisticsProgram.Binary

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

/-- Preserve the unary count word on2 and compute its binary length on3. -/
abbrev count : Cmd 8 14 := .seq (ArithmeticCalls.copyAt 2 13 12)
  (liftCommand LeafStatisticsProgram.Binary.command 0 1 countRegisters countStacks)

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

def check (j : Fin 2) : Code :=
  liftCommand (SubexpGuardProgram.checkPair (Fin.castAdd 1 j)) 0 0 id checkStacks

def clearCount : Code := .call (StackRoutines.clearProgram 3 0 1)

end SubexponentialSAT.SqrtLog.CodeSearchWalshProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_CodeSetupCostNative
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.CodeSetupCost
open CostAssembly Asymptotic Filter
open scoped Topology

def fixedConstant (f g : ℕ) : ℕ :=
  1000000000000*(f+g+1)+(CodeSearchProgram.alphabetBits 2).length+
    (CodeSearchProgram.alphabetBits 3).length+
    SubexponentialSAT.SubexpEnumerationPayload.scalarWidth 2+SubexponentialSAT.SubexpEnumerationPayload.scalarWidth 3

end SubexponentialSAT.SqrtLog.CodeSetupCost

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

abbrev logarithm : Cmd 3 3 := .call SubexpParameterProgram.logProgram

end SubexponentialSAT.SqrtLog.Setup

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_SetupGuard
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.Setup.Guard

open BitProgram StructuredCalls
open ArithmeticExpressionSupport (clearCmd )

abbrev command : Cmd 8 12 :=
  .seq (ArithmeticCalls.multiplyAt squarePorts)
    (.seq (ArithmeticCalls.multiplyAt productPorts)
      (.seq (clearCmd 3)
        (.seq (ArithmeticCalls.copyAt 2 5 11)
          (.seq (.call (ProgramLinking.liftProgram SubexpGuardProgram.Compare.program
            id comparePorts)) (.base (.atom (.bnot 0 0)))))))

end SubexponentialSAT.SqrtLog.Setup.Guard

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_CodeSetupOuterCostMajorant
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.CodeSetupOuterCost
open SubexponentialSAT Filter CostAssembly Asymptotic
open scoped Topology

/-- Padding-independent exponent for the two actual exhaustive searches. -/
def searchExponent (q n : ℕ) : ℕ :=
  CodeSetupCost.exponent (CodeSetupCost.fixedConstant 1 1)
    (CodeSetupCost.heightCoefficient q * L n^(2*q+3))

/-- An explicit integer resource count; physical padding is charged separately. -/
def setupMajorant (C d q n : ℕ) : ℕ := (n+1)^(C+d+searchExponent q n)

end SubexponentialSAT.SqrtLog.CodeSetupOuterCost

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_RingScanServiceLifts
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.RingScan
open BitProgram StructuredCalls StackRoutines
open SubexponentialSAT.SubexpLiftRing SubexponentialSAT.SubexpQuarticRing

theorem embed_expand_service (regs : Fin 8 → Bool) (r : Fin 2 → Bool)
    (s : ServiceStore) (table stream : List Bool) :
    embedState loadRegisters serviceExpandPorts (serviceWorkState regs s)
      (RingTriple.state r {(RingTriple.layout s.x s.y s.degree s.width) with table := table, xs := stream}) =
    serviceWorkState (Function.update (Function.update regs 1 (r 0)) 3 (r 1))
      {s with tableWork := table, stream := stream, reverseStream := []} := by
  apply embedState_eq_of_ports _ _ _ _ _ loadRegisters_injective serviceExpandPorts_injective
  · intro i; fin_cases i <;> simp [loadRegisters, RingTriple.state, serviceWorkState]
  · intro i hi
    have h1 : i ≠ 1 := fun h => hi ⟨0, h.symm⟩
    have h3 : i ≠ 3 := fun h => hi ⟨1, h.symm⟩
    simp [serviceWorkState, h1, h3]
  · intro i; fin_cases i <;> rfl
  · intro i hi
    have h20 : i ≠ 20 := fun h => hi ⟨2, h.symm⟩
    have h21 : i ≠ 21 := fun h => hi ⟨3, h.symm⟩
    have h23 : i ≠ 23 := fun h => hi ⟨4, h.symm⟩
    simp [serviceWorkState, serviceTapes, h20, h21, h23]


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

def preparationBudget (t inputWidth : ℕ) : ℕ :=
  2001*(t+inputWidth+2)^2 + 500000*(t+(2*t+inputWidth)+1)^3 +
    finishBudget t (SubexpLiftRing.baseWidth 3 t) (2*t+inputWidth)

end SubexponentialSAT.SqrtLog.IdempotentPreparationProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_IdempotentProgramFinal
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Concrete native Newton lift and the exact degree-three coefficient output.
The input-state contract includes prepared scalar constants and the cached
H-adic table; native preparation is a separate remaining construction. -/
namespace SubexponentialSAT.SqrtLog.IdempotentProgram

open scoped BigOperators
open BitProgram StructuredCalls SubexpSymbolicCost
open SubexponentialSAT.SubexpLiftRing SubexponentialSAT.SubexpQuarticRing

def nativeLiftBudget (t counterWidth : ℕ) : ℕ :=
  7*Nat.clog 2 t*arithmeticBudget (baseWidth 3 t) (3*t) +
    (Nat.clog 2 t+1)*(16*counterWidth+16)+1

end SubexponentialSAT.SqrtLog.IdempotentProgram


end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_IdempotentProgramComplete
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! A fixed finite bit program constructs the ternary H-adic lift from its
binary precision alone. Preparation, array arithmetic, iteration and output
serialization are all covered by actual bit-instruction traces. -/
namespace SubexponentialSAT.SqrtLog.IdempotentProgram

open scoped BigOperators
open BitProgram StructuredCalls SubexpQuarticRing

def completeBudget (t inputWidth : ℕ) : ℕ :=
  IdempotentPreparationProgram.preparationBudget t inputWidth +
    nativeLiftBudget t (inputWidth+1)+1

end SubexponentialSAT.SqrtLog.IdempotentProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_IrreducibleSearchBasic
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.labelFintype _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.variableFintype _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# Finite coefficient tests for arbitrary-degree irreducible search

Only vectors, finite lists, and scalar arithmetic are executed. `ofFn` and
the polynomial interpretation occur solely in the correctness proofs.
-/
namespace SubexponentialSAT.SqrtLog.IrreducibleSearch

open Polynomial
open scoped BigOperators

/-- Compare all potentially nonzero product coefficients. -/
def productEq {d : ℕ} (c : Fin d → F) (a b : Fin (d + 1) → F) : Bool :=
  (List.range (2 * d + 1)).all fun j =>
    decide (convolution a b j = candidateEntry c j)

end SubexponentialSAT.SqrtLog.IrreducibleSearch

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_IrreducibleSearch
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.labelFintype _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.variableFintype _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# Executable arbitrary-degree irreducible search over F₃

Search all monic degree-`d` coefficient vectors and reject each candidate
which is the product of two nonconstant arrays of degree at most `d`.
The test uses explicit convolution. Mathematical finite-field existence
proves that the executable search succeeds for every positive `d`.
-/
namespace SubexponentialSAT.SqrtLog.IrreducibleSearch

open Polynomial

def factorPairs (d : ℕ) : List ((Fin (d + 1) → F) × (Fin (d + 1) → F)) :=
  (candidates (d + 1)).flatMap fun a => (candidates (d + 1)).map fun b => (a, b)

@[simp] theorem length_factorPairs (d : ℕ) :
    (factorPairs d).length = 3 ^ (2 * (d + 1)) := by
  simp [factorPairs, List.length_flatMap, ← pow_two, ← pow_mul, Nat.mul_comm]

def pairPass {d : ℕ} (c : Fin d → F)
    (ab : (Fin (d + 1) → F) × (Fin (d + 1) → F)) : Bool :=
  !(nonconstant ab.1 && nonconstant ab.2 && productEq c ab.1 ab.2)

def passes {d : ℕ} (c : Fin d → F) : Bool := (factorPairs d).all (pairPass c)

def evaluate {d : ℕ} (c : Fin d → F) : Bool × ℕ :=
  QuarticSearch.checkAll (pairPass c) (factorPairs d)

@[simp] theorem evaluate_value {d : ℕ} (c : Fin d → F) :
    (evaluate c).1 = passes c := QuarticSearch.checkAll_value _ _

end SubexponentialSAT.SqrtLog.IrreducibleSearch

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SubexpOrderedTupleStep
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! # A fixed Cartesian expansion in exact enumeration order -/

namespace SubexponentialSAT.SubexpOrderedTupleStep

open BitProgram StructuredCalls Subexp.TupleProgram SubexpOrderedTupleData

def stepCost (rows alphabet : Records) : ℕ :=
  expansionCost rows alphabet +
    10 * (ProgramEncoding.encodeRecords (cartesianOutput rows alphabet)).length + 4

end SubexponentialSAT.SubexpOrderedTupleStep

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_IrreducibleSearchEnumeration
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Fixed finite-control generation in the exact irreducible-search order. -/
namespace SubexponentialSAT.SqrtLog.IrreducibleSearchEnumeration

open BitProgram StructuredCalls Subexp.TupleProgram SubexpOrderedTupleData

def powerCost (alphabet : Records) : ℕ → Records → ℕ
  | 0, _ => 2
  | n + 1, rows => SubexpOrderedTupleStep.stepCost rows alphabet +
      powerCost alphabet n (orderedCartesian rows alphabet) + 2

open SubexpEnumerationPayload SubexpTupleRefinement

def alphabet : Records := (QuarticSearch.elements 3).map (scalarCode 3).block

def cost (d : ℕ) : ℕ := powerCost alphabet d [[]] + 9

end SubexponentialSAT.SqrtLog.IrreducibleSearchEnumeration

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

@[simp] theorem alphabet_length : alphabet.length = 3 := by
  simp [alphabet, QuarticSearch.length_elements]

end SubexponentialSAT.SqrtLog.IrreducibleSearchEnumeration

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_IrreducibleSearchBootstrapPreparation
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms


/-! A fixed framed call generates an ordered table from a runtime unary depth.
Only its output and depth ports change; the generator's sentinel is paid for
and cleared before returning. -/
namespace SubexponentialSAT.SqrtLog.IrreducibleSearchBootstrap

open BitProgram StructuredCalls
open Subexp.TupleProgram SubexpOrderedTupleData
open SubexpEnumerationPayload SubexpTupleRefinement

def alphabetWord : List Bool :=
  ProgramEncoding.encodeRecords IrreducibleSearchEnumeration.alphabet

end SubexponentialSAT.SqrtLog.IrreducibleSearchBootstrap


/-! Paid construction of both search tables from a single unary depth word. -/
namespace SubexponentialSAT.SqrtLog.IrreducibleSearchBootstrap

open BitProgram StructuredCalls


def cost (d : ℕ) : ℕ := IrreducibleSearchEnumeration.cost d +
  IrreducibleSearchEnumeration.cost ((d + 1) + (d + 1)) +
  28 * d + 4 * alphabetWord.length + 71

end SubexponentialSAT.SqrtLog.IrreducibleSearchBootstrap

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

def scalarBits (a : IrreducibleSearch.F) : Bool × Bool :=
  (a.val == 1, a.val == 2)

def scalarValue (a b : Bool) : IrreducibleSearch.F :=
  (if a then 1 else 0) + (if b then 2 else 0)

@[simp] theorem scalarValue_bits (a : IrreducibleSearch.F) :
    scalarValue (scalarBits a).1 (scalarBits a).2 = a := by
  apply ZMod.val_injective
  have ha : a.val < 3 := a.val_lt
  interval_cases h : a.val <;>
    simp [scalarValue, scalarBits, h, ZMod.val_ofNat, ZMod.val_one 3]

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

def coefficientWord (a : IrreducibleSearch.F) : List Bool :=
  (SubexpEnumerationPayload.scalarCode 3).block a

def coefficientArray (as : List IrreducibleSearch.F) : List Bool :=
  StackEncoding.encodeDataStack (SubexpEnumerationPayload.scalarCode 3) as

@[simp] theorem coefficientWord_length (a : IrreducibleSearch.F) :
    (coefficientWord a).length = 2 := by
  have h := SubexpEnumerationPayload.scalarBits_length a
  have hw : SubexpEnumerationPayload.scalarWidth 3 = 2 := by
    have hl : Nat.log 2 3 = 1 := Nat.log_eq_of_pow_le_of_lt_pow (by norm_num) (by norm_num)
    simp only [SubexpEnumerationPayload.scalarWidth, hl]
  simpa only [coefficientWord, SubexpEnumerationPayload.scalarCode, hw] using h

@[simp] theorem coefficientArray_nil : coefficientArray [] = [] := rfl

@[simp] theorem coefficientArray_cons (a : IrreducibleSearch.F)
    (as : List IrreducibleSearch.F) :
    coefficientArray (a :: as) = coefficientWord a ++ coefficientArray as := rfl

@[simp] theorem coefficientArray_append (as bs : List IrreducibleSearch.F) :
    coefficientArray (as ++ bs) = coefficientArray as ++ coefficientArray bs :=
  StackEncoding.encodeDataStack_append _ _ _

@[simp] theorem coefficientArray_length (as : List IrreducibleSearch.F) :
    (coefficientArray as).length = 2 * as.length := by
  induction as with
  | nil => rfl
  | cons a as ih => simp [ih]; omega

end SubexponentialSAT.SqrtLog.IrreducibleSearchProgram

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

/-! Fixed first-success scan using the concrete saved factor checker. -/
namespace SubexponentialSAT.SqrtLog.IrreducibleSearchCandidateControl

open BitProgram StructuredCalls IrreducibleSearchProgram
open SubexpEnumerationPayload SubexpTupleRefinement
attribute [local simp] Fin.addCases Fin.coe_ofNat_eq_mod

def candidateRecords (d : ℕ) :=
  (IrreducibleSearch.candidates d).map (encodeTuple (scalarCode 3))

end SubexponentialSAT.SqrtLog.IrreducibleSearchCandidateControl

namespace SubexponentialSAT.SqrtLog.IrreducibleSearchCandidateControl

@[simp] theorem candidateRecords_length (d : ℕ) :
    (candidateRecords d).length = 3 ^ d := by simp [candidateRecords]

end SubexponentialSAT.SqrtLog.IrreducibleSearchCandidateControl

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

abbrev Data := State 40 768

end SubexponentialSAT.SqrtLog.LeafNodeSamplesProgram


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

def moveOut (d : Data) : Data :=
  ⟨readRegs d.regs 0 1 none,
    Function.update (Function.update d.stacks 200 []) 8 (d.stacks 200)⟩

end SubexponentialSAT.SubexpConvolutionPair

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
open BitProgram StructuredCalls SubexpQuarticRing SubexpLiftRing StackRoutines

def idempotentBudget (t W : ℕ) : ℕ :=
  idempotentStartPorts.length*(2*W+3)+(7*W+8)+32+
    IdempotentProgram.completeBudget t W+(7*(6*t^2)+8)

end SubexponentialSAT.SqrtLog.LeafRingSetupProgram

end OAI.Algorithms
end


