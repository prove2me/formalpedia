-- Prove2me | Definitions.Def_OAIQ081S036
-- name    : OAIQ081S036
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-29T21:31:24.048572+00:00
-- url     : https://prove2.me/theorems/7eb93482-ff21-438e-98fd-321250278592
-- title:
--   Definitions bundle OAIQ081S036 of the split of OpenAI, The Exponential Time Hypothesis is False
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.exact_count_and_sat`, carved from OpenAI's openai/math development (OpenAI, *The Exponential Time Hypothesis is False*, OpenAI Math Release, October 25, 2026, result family 378, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 155 declarations of OpenAI's Lean: 115 definitions, 1 inductive type or structure, 1 instance and 38 theorems. The definitions and types are `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgram.PowerData`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgram.SourceBank.cleanupOps`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgram.SourceBank.stageEmitterOps`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgram.SourceBank.stageTypesOps`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgram.SourceTyped.factor`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgram.SourceTyped.row`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgram.SourceTyped.tables`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgram.SourceTyped.term`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgram.Staging.Action.destination`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgram.normalizeReady`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgram.powerAfterRead`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgram.powerState`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgramScalar.Triple`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgramScalar.cacheIter`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgramScalar.cacheLast`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgramScalar.cacheScan`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgramScalar.cacheWord`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgramScalar.scalarCost`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgramScalar.tripleWords`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutRank.rowLinear`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutSignatureBound.boolSignature`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutSourcePlanLookup.Code`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutSourcePlanLookup.copy`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutSourcePlanLookup.push`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutSourceRowsProgram.TypedSourceRel`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutSourceRowsProgram.fiberState`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutSourceRowsProgram.foldSources`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutSourceRowsProgram.indexBytes`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutSourceRowsProgram.ownerSum`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutSourceRowsProgram.sourceRowFamily`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutSourceValuesProgram.Native.integerBits`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutTriplePreparationProgram.factoredTerm`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafAssignmentMergeProgram.Data`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafAssignmentMergeProgram.Native.command`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafAssignmentMergeProgram.Native.copy`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafAssignmentMergeProgram.Native.data`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafAssignmentMergeProgram.Native.program`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafAssignmentMergeProgram.Native.scan`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafAssignmentMergeProgram.body`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafAssignmentMergeProgram.command` and 76 more.
--
--   **Sources.** They come from these modules of lean/OAI/Algorithms, in whole or in part: `SubexponentialSAT_SqrtLog_LayoutProgramNormalize`, `SubexponentialSAT_SqrtLog_LayoutProgramPower`, `SubexponentialSAT_SqrtLog_LayoutProgramScalarCacheCell`, `SubexponentialSAT_SqrtLog_LayoutProgramScalarStep`, `SubexponentialSAT_SqrtLog_LayoutProgramSourceBank`, `SubexponentialSAT_SqrtLog_LayoutProgramSourceTables`, `SubexponentialSAT_SqrtLog_LayoutProgramSourceTyped`, `SubexponentialSAT_SqrtLog_LayoutProgramStaging`, `SubexponentialSAT_SqrtLog_LayoutPullback`, `SubexponentialSAT_SqrtLog_LayoutRank`, `SubexponentialSAT_SqrtLog_LayoutSignatureBound`, `SubexponentialSAT_SqrtLog_LayoutSourcePlanLookupBasic`, `SubexponentialSAT_SqrtLog_LayoutSourceRowsProgram`, `SubexponentialSAT_SqrtLog_LayoutSourceRowsProgramFamily`, `SubexponentialSAT_SqrtLog_LayoutSourceRowsProgramSemantics`, `SubexponentialSAT_SqrtLog_LayoutSourceRowsProgramTyped`, `SubexponentialSAT_SqrtLog_LayoutSourceValuesProgram`, `SubexponentialSAT_SqrtLog_LayoutTriplePreparationProgramInterface`, `SubexponentialSAT_SqrtLog_LeafAssignmentMergeProgram`, `SubexponentialSAT_SqrtLog_LeafAssignmentMergeProgramNative`, `SubexponentialSAT_SqrtLog_LeafAssignmentSetupProgramBase`, `SubexponentialSAT_SqrtLog_LeafFactorDispatchProgram`, `SubexponentialSAT_SqrtLog_LeafFactorDispatchProgramBranches`, `SubexponentialSAT_SqrtLog_LeafFactorDispatchProgramChoose`, `SubexponentialSAT_SqrtLog_LeafFactorDispatchProgramRun`, `SubexponentialSAT_SqrtLog_LeafHeadFactorsProgramSemantics`, `SubexponentialSAT_SqrtLog_LeafProgramMass`, `SubexponentialSAT_SqrtLog_LeafStatisticsProgramBoot`, `SubexponentialSAT_SqrtLog_LeafWeightProgramNative`, `SubexponentialSAT_SubexpEvaluationProgram`, `SubexponentialSAT_SubexpKernelControl`, `SubexponentialSAT_SubexpNodeIndexProgram`, `SubexponentialSAT_SubexpPostfixControl`, `SubexponentialSAT_SubexpPredecessorProgram`, `SubexponentialSAT_SubexpRecordScan`, `SubexponentialSAT_SubexpRepresentedRows`, `SubexponentialSAT_SubexpRowInterpolation`, `SubexponentialSAT_SubexpUnaryRangeProgram`, `SubexponentialSAT_SubexpVertexIndexProgram`, `SubexponentialSAT_Subexp_AssignmentSeedRange`, `SubexponentialSAT_Subexp_BlockZeroProgram`, `SubexponentialSAT_Subexp_BucketProgram`, `SubexponentialSAT_Subexp_DimensionProgram`, `SubexponentialSAT_Subexp_MismatchPlanProgram`, `SubexponentialSAT_Subexp_PackingAddressSemantics`, `SubexponentialSAT_Subexp_PackingBucketTable`, `SubexponentialSAT_Subexp_PackingExtractionOuter`, `SubexponentialSAT_Subexp_PackingExtractionSemantics`, `SubexponentialSAT_Subexp_PackingFrameCount`, `SubexponentialSAT_Subexp_PackingFrameSkip`, `SubexponentialSAT_Subexp_PackingLeftovers`, `SubexponentialSAT_Subexp_PackingMetadata`, `SubexponentialSAT_Subexp_PackingUnaryMin`, `SubexponentialSAT_Subexp_SelectorMapProgram`, `SubexponentialSAT_Subexp_SelectorProgram`, `SubexponentialSAT_Subexp_SequentialProgram`, `SubexponentialSAT_Subexp_UniversalRowDataProgram`, `SubexponentialSAT_Subexp_UniversalRowEmitCall`, `SubexponentialSAT_Subexp_UniversalRowExecution`, `SubexponentialSAT_Subexp_UniversalRowLoop`, `SubexponentialSAT_Subexp_UniversalRowMismatchProgram`, `SubexponentialSAT_Subexp_UniversalRowProgram`, `SubexponentialSAT_Subexp_UniversalRowSourceBound`, `SubexponentialSAT_Subexp_UniversalRowTermProgram`.
--
--   **Imports.** It imports the published bundle `Def_SubexponentialSAT`; the bundles `OAIQ081S000`, `OAIQ081S001`, `OAIQ081S002`, `OAIQ081S003`, `OAIQ081S005`, `OAIQ081S006`, `OAIQ081S007`, `OAIQ081S008`, `OAIQ081S011`, `OAIQ081S012`, `OAIQ081S013` and `OAIQ081S014` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ081S056`, `OAIQ081S057`, `OAIQ081S058`, `OAIQ081S062`, `OAIQ081S063`, `OAIQ081S064` and `OAIQ081S065`; the proofs of `OAI.Algorithms.SubexponentialSAT.SqrtLog.HashCircuitProgram.Native.rowFrame_memory` and `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutRank.blocks_data_total_rank_le`.
-- source:
--   OpenAI, The Exponential Time Hypothesis is False, OpenAI Math Release, October 25, 2026, https://github.com/openai/math (result family 378; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/The-Exponential-Time-Hypothesis-is-False-October-25-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Algorithms at commit 7ef5c0c

import Mathlib
import Definitions.Def_SubexponentialSAT
import Definitions.Def_OAIQ081S000
import Definitions.Def_OAIQ081S001
import Definitions.Def_OAIQ081S002
import Definitions.Def_OAIQ081S003
import Definitions.Def_OAIQ081S005
import Definitions.Def_OAIQ081S006
import Definitions.Def_OAIQ081S007
import Definitions.Def_OAIQ081S008
import Definitions.Def_OAIQ081S011
import Definitions.Def_OAIQ081S012
import Definitions.Def_OAIQ081S013
import Definitions.Def_OAIQ081S014

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LayoutProgramNormalize
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Runtime-width normalization for signed-component matrix words. This uses
only the existing padding, clear and transfer bit programs. In particular,
normalizing a component never invokes modular integer arithmetic. -/

namespace SubexponentialSAT.SqrtLog.LayoutProgram

open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.ModularArithmetic SubexponentialSAT.StackRoutines
open SubexponentialSAT.ModularRingPrograms

variable {s : ℕ}

def normalizeReady (ports : Fin 8 ↪ Fin s) (d : State 8 s) : Prop :=
  ∀ i : Fin 8, i ≠ 0 → i ≠ 5 → i ≠ 7 → d.stacks (ports i) = []

end SubexponentialSAT.SqrtLog.LayoutProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LayoutProgramPower
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! A fixed bit program generates the power-of-two clearing denominator from
its unary exponent. The exponent is runtime data, never control-table size. -/

namespace SubexponentialSAT.SqrtLog.LayoutProgram

open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls
open SubexponentialSAT.BinaryArithmetic

abbrev PowerData := State 2 2

def powerState (regs : Fin 2 → Bool) (counter output : List Bool) : PowerData :=
  ⟨regs, ![counter,output]⟩

def powerAfterRead (regs : Fin 2 → Bool) (counter output : List Bool) : PowerData :=
  powerState (readRegs regs 0 1 counter.head?) counter.tail output

theorem powerWord_value (q : ℕ) :
    BinaryArithmetic.toNat (List.replicate q false ++ [true]) = 2 ^ q := by
  induction q with
  | zero => simp [BinaryArithmetic.toNat, bitVal]
  | succ q ih => simp [List.replicate_succ, bitVal, ih, pow_succ, Nat.mul_comm]

end SubexponentialSAT.SqrtLog.LayoutProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SubexpPostfixControl
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
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

def serializeInstr {R : Type*} (encode : R → List Bool) : Algorithm.Instr R → List Bool
  | .push x => false :: Encoding.frame (encode x)
  | .add => [true, false]
  | .mul => [true, true]

def serializeCode {R : Type*} (encode : R → List Bool) : List (Algorithm.Instr R) → List Bool
  | [] => []
  | i :: is => serializeInstr encode i ++ serializeCode encode is

/-! ## Literal-push service with the framed-list operand ABI -/

end SubexponentialSAT.SubexpPostfixControl

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LayoutProgramScalarCacheCell
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! The unsigned cache recurrence is executed by a one-bit shift followed by
the original finite little-endian adder. Its representation growth is linear
in the number of cells; no canonical-word assumption is used. -/
namespace SubexponentialSAT.SqrtLog.LayoutProgramScalar

open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls
open SubexponentialSAT.BinaryArithmetic
open SubexponentialSAT.SqrtLog.RowSelectionProgram

def cacheWord (prior old : List Bool) : List Bool := add (false::prior) old

def cacheScan : List Bool → List (List Bool) → List (List Bool)
  | _, [] => []
  | prior, old::rest => let next := cacheWord prior old; next::cacheScan next rest

@[simp] theorem cacheScan_length (prior : List Bool) (xs : List (List Bool)) :
    (cacheScan prior xs).length = xs.length := by
  induction xs generalizing prior with
  | nil => rfl
  | cons x xs ih => simp [cacheScan,ih]

end SubexponentialSAT.SqrtLog.LayoutProgramScalar

/-! One complete cache-row transform, including record parsing and preserving
emission of every newly computed value. -/
namespace SubexponentialSAT.SqrtLog.LayoutProgramScalar

open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls
open SubexponentialSAT.SqrtLog.RowSelectionProgram

def cacheLast : List Bool → List (List Bool) → List Bool
  | prior, [] => prior
  | prior, old::rest => cacheLast (cacheWord prior old) rest

end SubexponentialSAT.SqrtLog.LayoutProgramScalar

/-! Complete reusable cache pass: read one encoded row, compute and emit its
new row, append the end marker, reverse the output, and clear the carry. -/

/-! The number of coefficient-cache rows is runtime unary data. This fixed
loop invokes the complete paid row pass and preserves the current encoded row.
-/
namespace SubexponentialSAT.SqrtLog.LayoutProgramScalar

open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls
open SubexponentialSAT.SqrtLog.RowSelectionProgram

def cacheIter : ℕ → List (List Bool) → List (List Bool)
  | 0, xs => xs
  | n+1, xs => cacheIter n (cacheScan [] xs)

end SubexponentialSAT.SqrtLog.LayoutProgramScalar

/-! The physical unsigned cache computes the original coefficient recurrence's
natural magnitudes, in ascending degree order. -/

/-! A fixed loop builds the initial all-one cache row from a runtime unary
length. The constant program contains one record, independent of that length. -/

/-! One fixed program builds the complete unsigned H cache from the unary
runtime parameters A and R. No coefficient or initial cache is free input. -/

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LayoutProgramScalarStep
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! A single cached scalar term: three parsed operands, three real signed
multiplications, and one real signed addition. -/
namespace SubexponentialSAT.SqrtLog.LayoutProgramScalar

open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls
open SubexponentialSAT.SqrtLog.RowSelectionProgram

abbrev Triple := WordPair × WordPair × WordPair

def tripleWords (xs : List Triple) : List WordPair :=
  xs.flatMap fun x => [x.1,x.2.1,x.2.2]

def scalarCost : ℕ → ℕ → ℕ → ℕ
  | 0, _, _ => 4
  | n+1, A, B => 6*B+11+termCost A B+scalarCost n (A+termGrowth B) B+1

end SubexponentialSAT.SqrtLog.LayoutProgramScalar

/-! Polynomial source-step bounds for the concrete cached scalar arithmetic.
The stream has three actual binary signed operands per summand, not a stream
of precomputed products or an assumed arithmetic callback. -/

/-! Exact unsigned component totals for the same concrete scalar program.
The extra invariant controls cancellation without changing any instruction. -/

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SubexpKernelControl
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# A fixed controller constructing the separated postfix source

The input contains literal payloads and the three nested lists of blocks,
color groups, and terms.  The controller only parses frames, copies bits,
and emits postfix tags.  It has no arithmetic callback and never builds a
Cartesian product of the inner lists.  Three unary stacks hold the pending
right-fold operators, so the emitted source has exactly the association of
`SubexpAlgorithm.momentExpression`.
-/

namespace SubexponentialSAT.SubexpKernelControl

open BitProgram StructuredCalls

def pushWord (payload : Word) : Word := false :: Encoding.frame payload

/-! ## Fixed source-constructor control -/

abbrev atom (a : StructuredProgram.Atom 3 8) : Cmd 3 8 := .base (.atom a)
local infixr:60 " ;; " => Cmd.seq

/-- Every list length is data on stack 0. -/
abbrev popTag : Cmd 3 8 := atom (.pop 0 0 1)

abbrev emitOperator (mul : Bool) : Cmd 3 8 :=
  if mul then atom (.push 3 2) ;; atom (.push 3 2)
  else atom (.push 3 2) ;; atom (.set 0 false) ;; atom (.push 3 0)

abbrev countOne (counter : Fin 8) : Cmd 3 8 := atom (.push counter 2)

abbrev drain (counter : Fin 8) (mul : Bool) : Cmd 3 8 :=
  atom (.pop counter 0 1) ;;
    .while 1 (emitOperator mul ;; atom (.pop counter 0 1))

/-! ## Concrete machine states and elementary traces -/

/-! The following induction rule accounts for actual executions of the fixed
payload body. Its premises will be proved for `termBody`, `groupBody`, and
`blockBody`; the exported whole-controller statement has no callback argument. -/

/-! ## Forward-output service boundary -/

abbrev transferOutput : Cmd 3 8 := .call (StackRoutines.transferProgram 3 0 0 1)

end SubexponentialSAT.SubexpKernelControl

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SubexpRecordScan
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# Fixed-control selection of serialized coefficient records

The inner record body is `frame key ++ frame coefficient`. All execution
claims below are traces of fixed Boolean-register/stack instruction tables.
-/

namespace SubexponentialSAT.SubexpRecordScan

open BitProgram StructuredProgram StructuredCalls

theorem state_ext {r s : ℕ} {a b : StructuredProgram.State r s}
    (hr : a.regs = b.regs) (hs : a.stacks = b.stacks) : a = b := by
  cases a
  cases b
  cases hr
  cases hs
  rfl

theorem lowRegs_injective : Function.Injective lowRegs := by
  intro a b h
  apply Fin.ext
  exact congrArg (fun x : Fin 5 => x.val) h

theorem onlyInput_injective : Function.Injective onlyInput := by
  intro a b _
  exact Subsingleton.elim _ _

@[simp] theorem storage_zero (a b c d e f : List Bool) : storage a b c d e f 0 = a := rfl
@[simp] theorem storage_one (a b c d e f : List Bool) : storage a b c d e f 1 = b := rfl
@[simp] theorem storage_two (a b c d e f : List Bool) : storage a b c d e f 2 = c := rfl
@[simp] theorem storage_three (a b c d e f : List Bool) : storage a b c d e f 3 = d := rfl
@[simp] theorem storage_four (a b c d e f : List Bool) : storage a b c d e f 4 = e := rfl
@[simp] theorem storage_five (a b c d e f : List Bool) : storage a b c d e f 5 = f := rfl

@[simp] theorem storage_update_zero (a b c d e f x : List Bool) :
    Function.update (storage a b c d e f) 0 x = storage x b c d e f := by
  funext j; fin_cases j <;> simp [storage]

@[simp] theorem storage_update_one (a b c d e f x : List Bool) :
    Function.update (storage a b c d e f) 1 x = storage a x c d e f := by
  funext j; fin_cases j <;> simp [storage]

@[simp] theorem storage_update_three (a b c d e f x : List Bool) :
    Function.update (storage a b c d e f) 3 x = storage a b c x e f := by
  funext j; fin_cases j <;> simp [storage]

@[simp] theorem storage_update_five (a b c d e f x : List Bool) :
    Function.update (storage a b c d e f) 5 x = storage a b c d e x := by
  funext j; fin_cases j <;> simp [storage]

end SubexponentialSAT.SubexpRecordScan

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_Subexp_SelectorProgram
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# Fixed-code lookup with fallback for local read plans

The table is a raw sequence of framed key/payload pairs. The query and table
are runtime bit strings. The program reuses the verified key comparison and
record parsing routines, retaining the first matching payload.
-/

namespace SubexponentialSAT.Subexp.SelectorProgram

open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.SubexpRecordScan

def framedResult (result : Option (List Bool)) : List Bool :=
  (result.map Encoding.frame).getD []

end SubexponentialSAT.Subexp.SelectorProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_Subexp_PackingMetadata
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Exact lookup semantics for the storage-ordered packing metadata table.
The physical extraction proof identifies its emitted records with this table. -/

namespace SubexponentialSAT.Subexp.PackingMetadata

open ConstructivePacking
open GlobalBasisMetadata (Metadata)

theorem unary_injective : Function.Injective unary := by
  intro a b h
  simpa [unary] using congrArg List.length h

end SubexponentialSAT.Subexp.PackingMetadata

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_Subexp_SelectorMapProgram
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# A fixed loop applying the selected-index map to query records

The selector uses ports 0--5.  Port 6 is the framed query cursor, port 7
preserves the raw key/payload table, and port 8 accumulates framed answers.
Answers are prepended, so the returned record list reverses query order.
-/

namespace SubexponentialSAT.Subexp.SelectorMapProgram

open BitProgram StructuredCalls

theorem instruction_stack_bound {r s l : ℕ} (op : Instr r s l)
    (c : Cfg r s l) (j : Fin s) :
    ((execInstr op c).stacks j).length ≤ (c.stacks j).length + 1 := by
  cases op <;> simp only [execInstr]
  all_goals try omega
  · rename_i stack src next
    by_cases h : j = stack <;> simp [ h]
  · rename_i stack value present next
    by_cases h : j = stack <;> simp [ h] ; omega

theorem trace_stack_bound {r s l n : ℕ} (p : Program r s l)
    {a b : Cfg r s l} (h : Trace p n a b) (j : Fin s) :
    (b.stacks j).length ≤ (a.stacks j).length + n := by
  induction h with
  | refl => omega
  | @cons n a b c hs ht ih =>
      have hone : (b.stacks j).length ≤ (a.stacks j).length + 1 := by
        cases hp : a.pc with
        | none => simp [step, hp] at hs
        | some label =>
            have hb : execInstr (p.code label) a = b := by simpa [step, hp] using hs
            rw [← hb]
            exact instruction_stack_bound _ _ _
      omega

def recordPrefix (records : List (List Bool)) : List Bool :=
  records.flatMap (fun bits => true :: Encoding.frame bits)

end SubexponentialSAT.Subexp.SelectorMapProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_Subexp_PackingAddressSemantics
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! The emitted storage-address table is the graph of the actual packed
coordinate order. Its lookups produce the existing reordering read plan. -/

namespace SubexponentialSAT.Subexp.PackingAddressSemantics

open ConstructivePacking

variable {V U : Type*} [DecidableEq V] [DecidableEq U]

theorem addressRows_map_graph {A : Type*} [DecidableEq A] (vertices : List A)
    (encode : A → List Bool) (hn : vertices.Nodup) :
    addressRows (vertices.map encode) 0 =
      vertices.map (fun v => (encode v, List.replicate (vertices.idxOf v) true)) := by
  unfold addressRows
  rw [List.length_map, ← List.range_eq_range',
    ← SubexponentialSAT.LocalExpectation.map_idxOf_eq_range vertices hn,
    List.zipWith_map, List.zipWith_self]
  simp only [SubexponentialSAT.LocalExpectation.indexCode]

theorem lookup_reverse_addressRows {A : Type*} [DecidableEq A] (vertices : List A)
    (encode : A → List Bool) (hn : vertices.Nodup) (he : Function.Injective encode)
    (v : A) (hv : v ∈ vertices) :
    ((addressRows (vertices.map encode) 0).reverse).lookup (encode v) =
      some (List.replicate (vertices.idxOf v) true) := by
  rw [addressRows_map_graph vertices encode hn, ← List.map_reverse]
  exact PackingMetadata.lookup_graph_encoded vertices.reverse encode
    (fun v => List.replicate (vertices.idxOf v) true) he v (by simpa using hv)

end SubexponentialSAT.Subexp.PackingAddressSemantics

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SubexpUnaryRangeProgram
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! A fixed unary range enumerator which physically emits every framed index. -/
namespace SubexponentialSAT.SubexpUnaryRangeProgram

open BitProgram StructuredCalls

abbrev setSelected : Cmd 10 10 := .base (.atom (.set 4 true))

abbrev peek : Cmd 10 10 := .base (.atom (.peek 6 7 9))
abbrev pop : Cmd 10 10 := .base (.atom (.pop 6 7 9))

end SubexponentialSAT.SubexpUnaryRangeProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_Subexp_DimensionProgram
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# A fixed generator for all unary dimensions from zero through a runtime bound

The input bound is a unary stack, and the output is a framed list of unary
payloads. The program has no bound-dependent control labels.
-/

namespace SubexponentialSAT.Subexp.DimensionProgram

open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls
open SubexponentialSAT.Subexp.TupleProgram

/-- Descending unary records, including both endpoints. -/
def dimensionRows (k : ℕ) : ℕ → Records
  | 0 => [List.replicate k true]
  | n + 1 => dimensionRows (k + 1) n ++ [List.replicate k true]

/-- Exact cost of the bound-consuming loop, excluding its final endpoint. -/
def loopCost (k : ℕ) : ℕ → ℕ
  | 0 => 2
  | n + 1 => (12 * k + 12) + 2 + loopCost (k + 1) n + 2

def earlierRows (k : ℕ) : ℕ → Records
  | 0 => []
  | n + 1 => earlierRows (k + 1) n ++ [List.replicate k true]

theorem loopCost_eq (k n : ℕ) :
    loopCost k n = 6 * n ^ 2 + (12 * k + 10) * n + 2 := by
  induction n generalizing k with
  | zero => simp [loopCost]
  | succ n ih => rw [loopCost, ih]; ring

end SubexponentialSAT.Subexp.DimensionProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SubexpVertexIndexProgram
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! A fixed generator for exactly the vertex indices below unary D. -/
namespace SubexponentialSAT.SubexpVertexIndexProgram

open BitProgram StructuredCalls

theorem earlierRows_eq (k n : ℕ) :
    Subexp.DimensionProgram.earlierRows k n = (List.range' k n).reverse.map unary := by
  induction n generalizing k with
  | zero => rfl
  | succ n ih =>
      simp [Subexp.DimensionProgram.earlierRows,List.range'_succ,ih,List.reverse_cons]

end SubexponentialSAT.SubexpVertexIndexProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_Subexp_BucketProgram
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# A fixed bit program for one packing bucket

The input is a framed query followed by framed `(type key, vertex payload)`
records. The routine compares actual bit strings. It consumes all records,
keeps the query on port 2, and prepends matching framed payloads on port 5.
Supplying records in reverse vertex order produces the original bucket order.
-/

namespace SubexponentialSAT.Subexp.BucketProgram

open BitProgram StructuredProgram StructuredCalls SubexpRecordScan

def frames : List (List Bool) → List Bool
  | [] => []
  | x :: xs => Encoding.frame x ++ frames xs

theorem frames_append (xs ys : List (List Bool)) :
    frames (xs ++ ys) = frames xs ++ frames ys := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp [frames, ih, List.append_assoc]

end SubexponentialSAT.Subexp.BucketProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_Subexp_PackingFrameCount
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! A fixed frame counter for the complete-block packing controller. -/

namespace SubexponentialSAT.Subexp.PackingFrameCount

open BitProgram StructuredCalls

abbrev peek : Cmd 8 3 := .base (.atom (.peek 0 0 1))

end SubexponentialSAT.Subexp.PackingFrameCount

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_Subexp_PackingUnaryMin
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! A fixed destructive minimum routine for unary packing counts. -/

namespace SubexponentialSAT.Subexp.PackingUnaryMin

open BitProgram StructuredCalls

abbrev core : Program 8 3 8 where
  inputStack := 0
  outputStack := 2
  entry := 0
  code q := match q.val with
    | 0 => .pop 0 0 1 1
    | 1 => .pop 1 0 2 2
    | 2 => .branch 1 3 7
    | 3 => .branch 2 4 7
    | 4 => .set 0 true 5
    | 5 => .push 2 0 6
    | 6 => .goto 0
    | _ => .halt

def popped (regs : Fin 8 → Bool) (left right : Option Bool) : Fin 8 → Bool :=
  readRegs (readRegs regs 0 1 left) 0 2 right

end SubexponentialSAT.Subexp.PackingUnaryMin

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_Subexp_PackingBucketTable
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! The fixed all-key bucket/minimum controller. -/

namespace SubexponentialSAT.Subexp.PackingBucketTable

open BitProgram StructuredCalls PackingBucketCalls

abbrev sequence (cs : List (Cmd 8 15)) : Cmd 8 15 :=
  cs.foldr Cmd.seq (.base .skip)

end SubexponentialSAT.Subexp.PackingBucketTable

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_Subexp_BlockZeroProgram
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! A fixed bit program testing whether all payload bits in a sequence of
frames are zero. Frame delimiters are ignored; no scalar arithmetic is hidden
inside this program. -/

namespace SubexponentialSAT.Subexp.BlockZeroProgram

open BitProgram

def frames (words : List (List Bool)) : List Bool := words.flatMap Encoding.frame

/-- Consume a runtime number of complete scalar frames. Stack 0 is the
unary count and stack 1 the framed scalar stream. -/
abbrev skipProgram : Program 3 2 6 where
  inputStack := 1
  outputStack := 1
  entry := 0
  code := ![.pop 0 0 1 1, .branch 1 2 5, .pop 1 0 2 3,
    .branch 0 4 0, .pop 1 0 2 2, .halt]

def skipCfg (pc : Option (Fin 6)) (v countPresent scalarPresent : Bool)
    (count input : List Bool) : Cfg 3 2 6 :=
  ⟨pc, ![v, countPresent, scalarPresent], ![count, input]⟩

theorem skipFrame_trace (bits rest count : List Bool) (v pr sp : Bool) :
    Trace skipProgram (3 * bits.length + 2)
      (skipCfg (some 2) v pr sp count (Encoding.frame bits ++ rest))
      (skipCfg (some 0) false pr true count rest) := by
  induction bits generalizing v sp with
  | nil =>
      refine .cons (b := skipCfg (some 3) false pr true count rest) ?_ ?_
      · simp [step, skipCfg, execInstr, readRegs, Encoding.frame]
      refine .cons ?_ (.refl _)
      simp [step, skipCfg, execInstr]
  | cons bit bits ih =>
      have first : Trace skipProgram 3
          (skipCfg (some 2) v pr sp count (Encoding.frame (bit :: bits) ++ rest))
          (skipCfg (some 2) bit pr true count (Encoding.frame bits ++ rest)) := by
        refine .cons (b := skipCfg (some 3) true pr true count
          (bit :: (Encoding.frame bits ++ rest))) ?_ ?_
        · simp [step, skipCfg, execInstr, readRegs, Encoding.frame]
        refine .cons (b := skipCfg (some 4) true pr true count
          (bit :: (Encoding.frame bits ++ rest))) ?_ ?_
        · simp [step, skipCfg, execInstr]
        refine .cons ?_ (.refl _)
        simp [step, skipCfg, execInstr, readRegs]
      convert first.trans (ih bit true) using 1 ; simp [List.length_cons] ; omega

theorem skipProgram_trace (words : List (List Bool)) (rest count : List Bool)
    (hc : count.length = words.length) (v pr sp : Bool) :
    Trace skipProgram (skipCost words)
      (skipCfg (some skipProgram.entry) v pr sp count (frames words ++ rest))
      (skipCfg none false false (sp || !words.isEmpty) [] rest) := by
  induction words generalizing count v pr sp with
  | nil =>
      have hn : count = [] := List.length_eq_zero_iff.mp (by simpa using hc)
      subst count
      refine .cons (b := skipCfg (some 1) false false sp [] rest) ?_ ?_
      · simp [step, skipCfg, execInstr, readRegs, frames]
      refine .cons (b := skipCfg (some 5) false false sp [] rest) ?_ ?_
      · simp [step, skipCfg, execInstr]
      refine .cons ?_ (.refl _)
      simp [step, skipCfg, execInstr]
  | cons bits words ih =>
      cases count with
      | nil => simp at hc
      | cons bit count =>
          have ht : count.length = words.length := by simpa using hc
          have first : Trace skipProgram 2
              (skipCfg (some skipProgram.entry) v pr sp (bit :: count)
                (frames (bits :: words) ++ rest))
              (skipCfg (some 2) bit true sp count
                (Encoding.frame bits ++ (frames words ++ rest))) := by
            refine .cons (b := skipCfg (some 1) bit true sp count
              (Encoding.frame bits ++ (frames words ++ rest))) ?_ ?_
            · simp [step, skipCfg, execInstr, readRegs, frames, List.append_assoc]
            refine .cons ?_ (.refl _)
            simp [step, skipCfg, execInstr]
          have h := first.trans ((skipFrame_trace bits (frames words ++ rest) count
            bit true sp).trans (ih count ht false true true))
          convert h using 1 <;> simp [skipCost, Bool.or_true, Nat.add_assoc] ; omega

theorem skipCost_le (words : List (List Bool)) :
    skipCost words ≤ 4 * (frames words).length + 3 := by
  induction words with
  | nil => simp [skipCost, frames]
  | cons bits words ih =>
      simp only [skipCost, List.map_cons, List.sum_cons] at *
      simp only [frames, List.flatMap_cons, List.length_append, Encoding.length_frame] at *
      omega

end SubexponentialSAT.Subexp.BlockZeroProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_Subexp_PackingFrameSkip
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! An actual framed-pre skip call with arbitrary surrounding packing data. -/

namespace SubexponentialSAT.Subexp.PackingFrameSkip

open BitProgram StructuredCalls

variable {s : ℕ}

abbrev command (count source : Fin s) : Cmd 8 s :=
  .call (ProgramLinking.liftProgram BlockZeroProgram.skipProgram registers (stackPorts count source))

end SubexponentialSAT.Subexp.PackingFrameSkip

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_Subexp_PackingExtractionOuter
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! The fixed outer loop extracts all complete blocks in block-major order. -/

namespace SubexponentialSAT.Subexp.PackingExtraction

open BitProgram StructuredCalls

abbrev refresh : Cmd 8 19 := .base (.atom (.peek 16 3 4))
abbrev popRemaining : Cmd 8 19 := .base (.atom (.pop 16 3 4))

end SubexponentialSAT.Subexp.PackingExtraction

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_Subexp_PackingExtractionSemantics
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! The records emitted by block extraction have the exact computed packing order. -/

namespace SubexponentialSAT.Subexp.PackingExtraction

open ConstructivePacking

def vertexPrefix (vertices : List (List Bool)) : List Bool :=
  vertices.flatMap fun v => true :: Encoding.frame v

end SubexponentialSAT.Subexp.PackingExtraction

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_Subexp_AssignmentSeedRange
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Ascending framed unary seed indices from a runtime unary seed count. -/

namespace SubexponentialSAT.Subexp.AssignmentSeedRange

open BitProgram StructuredCalls TupleProgram

theorem earlierRows_eq (k n : ℕ) :
    DimensionProgram.earlierRows k n = (List.range' k n).reverse.map unary := by
  induction n generalizing k with
  | zero => simp [DimensionProgram.earlierRows]
  | succ n ih =>
      simp only [DimensionProgram.earlierRows, List.range'_succ, List.reverse_cons,
        List.map_append, List.map_singleton, ih]

end SubexponentialSAT.Subexp.AssignmentSeedRange

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_Subexp_SequentialProgram
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# Fixed sequential assignment control

The loop counter, processed index, word width, alphabet, and assignment are
runtime stack data. A fixed score-building command is composed with the
verified minimum selector and preserving packed-array operations.
-/

namespace SubexponentialSAT.Subexp.SequentialProgram

open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.StackRoutines

theorem instruction_stack_length_le {r s l : ℕ} (instr : Instr r s l)
    (c : Cfg r s l) (j : Fin s) :
    ((execInstr instr c).stacks j).length ≤ (c.stacks j).length + 1 := by
  cases instr <;> simp [execInstr, Function.update_apply]
  all_goals split_ifs <;> simp_all [List.length_tail] <;> omega

theorem trace_stack_length_le {r s l : ℕ} {p : Program r s l} {t : ℕ}
    {c e : Cfg r s l} (ht : Trace p t c e) (j : Fin s) :
    (e.stacks j).length ≤ (c.stacks j).length + t := by
  induction ht with
  | refl => simp
  | @cons n a b c hs ht ih =>
      have hb : (b.stacks j).length ≤ (a.stacks j).length + 1 := by
        cases hp : a.pc with
        | none => simp [BitProgram.step, hp] at hs
        | some q =>
            have h := Option.some.inj (by simpa [BitProgram.step, hp] using hs)
            rw [← h]
            exact instruction_stack_length_le _ _ j
      omega

end SubexponentialSAT.Subexp.SequentialProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_Subexp_PackingLeftovers
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# Actual leftover packing pass

The immutable covered table is searched for every original vertex. A found
vertex is skipped. A missing vertex is appended to reversed storage and both
lookup tables, with actual unary rank/address increments.
-/
namespace SubexponentialSAT.Subexp.PackingLeftovers

open BitProgram StructuredCalls

theorem queryRegs_injective : Function.Injective queryRegs := Fin.castAdd_injective 5 3

def storageRecords (vertices : List ℕ) : List Bool :=
  vertices.flatMap (fun v => true :: Encoding.frame (unary v))

end SubexponentialSAT.Subexp.PackingLeftovers

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LayoutPullback
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.labelFintype _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.variableFintype _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
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

omit [Fintype V] in
theorem row_apply_injective (owner : I → V) (hinj : Function.Injective owner)
    (a : I → R) (i : I) : row owner a (owner i) = a i := by
  classical
  simp only [row, hinj.eq_iff]
  simp

omit [Fintype V] in
theorem row_eq_zero (owner : I → V) (a : I → R) (v : V)
    (hv : v ∉ Set.range owner) : row owner a v = 0 := by
  apply Finset.sum_eq_zero
  intro i _
  have hi : owner i ≠ v := fun h => hv ⟨i, h⟩
  simp [hi]

end Ring

end SubexponentialSAT.SqrtLog.LayoutPullback

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SubexpRowInterpolation
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.labelFintype _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.variableFintype _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# Explicit mismatch interpolation for the multi-color layout

Section 3.3 of `subexponential-sat.txt`. All inverse data are supplied as
units. The polynomials are finite sums and products, not chosen witnesses.
Their scalar evaluation functions are executable from the supplied ring
operations and units; the semantic polynomial definitions use mathlib's
noncomputable polynomial representation.
-/

namespace SubexponentialSAT.SubexpRowInterpolation

open scoped BigOperators

variable {E I V C : Type*} [CommRing E] [DecidableEq I]

variable {node : I → E}

theorem basisDivisor_natDegree_le (u : NodeUnits node) (i j : I) :
    (basisDivisor u i j).natDegree ≤ 1 := by
  exact (Polynomial.natDegree_C_mul_le _ _).trans
    (by simpa using (Polynomial.natDegree_X_le (R := E)))

variable [DecidableEq V]

theorem rowPath_eval_zero (v : V) (c : V → Polynomial E)
    (hc : ∀ y, (c y).eval 0 = 0) :
    (fun y => (rowPath v c y).eval 0) = Pi.single v (1 : E) := by
  funext y
  simp [rowPath, hc]

theorem rowPath_natDegree_le (v : V) (c : V → Polynomial E) {R : ℕ}
    (hc : ∀ y, (c y).natDegree ≤ R) (y : V) :
    (rowPath v c y).natDegree ≤ R := by
  exact Polynomial.natDegree_add_le_of_degree_le (by simp) (hc y)

/-! ## Executable finite expression codes

The following constructors produce polynomial expression data using only
finite `List.ofFn` traversals. Their denotations are the proved polynomials
above. This supplies a concrete path representation in addition to the
executable scalar evaluator.
-/

end SubexponentialSAT.SubexpRowInterpolation

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SubexpRepresentedRows
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# Polynomial rows generated from represented field operations

The producer uses code words, finite expression constructors, and the supplied
arithmetic callbacks. It never extracts coefficients from an abstract field
value. Inverse constants are computed by finite-field powering. The canonical
coefficient lift is applied only after compiling the source polynomial.
-/

namespace SubexponentialSAT.SubexpRepresentedRows

open SubexpSymbolicCost SubexpRowInterpolation

variable {C E : Type*} {Q : ℕ}

def basis (ops : RingProgram C) (cache : NodeCache C Q)
    (s : Finset (Fin Q)) (i : Fin Q) : PolynomialCode C :=
  .mul (.mul (.constant (cache.inverse i)) .indeterminate)
    (productCode ops.oneRun.1 (List.ofFn fun j : Fin Q =>
      if j ∈ s.erase i then
        .mul (.constant (cache.difference i j))
          (.add .indeterminate (.constant (ops.negRun (cache.node j)).1))
      else .constant ops.oneRun.1))

def correction (ops : RingProgram C) (cache : NodeCache C Q)
    (s : Finset (Fin Q)) (d : Fin Q → C) : PolynomialCode C :=
  sumCode ops.zeroRun.1 (List.ofFn fun i : Fin Q =>
    if i ∈ s then .mul (.constant (d i)) (basis ops cache s i)
    else .constant ops.zeroRun.1)

def row {V G : Type*} [Fintype V] [DecidableEq V] [DecidableEq G]
    (ops : RingProgram C) (cache : NodeCache C Q)
    (v : V) (head : V → Fin Q → G) (σ : Fin Q → G) (R : ℕ)
    (d : V → Fin Q → C) (y : V) : PolynomialCode C :=
  .add (.constant (if v = y then ops.oneRun.1 else ops.zeroRun.1))
    (if y ∈ correctionColumns head σ R then
      correction ops cache (mismatchPositions head σ y) (d y)
    else .constant ops.zeroRun.1)

end SubexponentialSAT.SubexpRepresentedRows

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_Subexp_UniversalRowProgram
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# Physical source construction for universal interpolation rows

The input holds raw coefficient payloads, node inverses, and negative nodes.
It does not contain polynomial instructions. Fixed nested scans emit the
Lagrange products and correction sum as postfix source in canonical list order.
The surrounding row-data producer supplies the selected mismatch positions;
its matrix, cache, and type-mask construction is tracked separately.
-/

namespace SubexponentialSAT.Subexp.UniversalRowProgram

open BitProgram StructuredCalls
open SubexpKernelControl (Word pushWord popTag emitOperator countOne drain )

structure Row (C : Type*) where
  delta : C
  terms : List (Term C)

end SubexponentialSAT.Subexp.UniversalRowProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_Subexp_UniversalRowTermProgram
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! One actual correction-term iteration, from packed tables to a row record. -/

namespace SubexponentialSAT.Subexp.UniversalRowTermProgram

open BitProgram StructuredCalls StackRoutines
open UniversalRowGather (Word)
open UniversalRowFactorLoop (indexWord)

def indices (positions : List ℕ) : Word :=
  Encoding.encodeList id (positions.reverse.map indexWord)

def term (values inverses negatives differences : List Word) (positions : List ℕ) (i : ℕ) :
    UniversalRowProgram.Term Word :=
  ⟨values.getD i [], inverses.getD i [],
    UniversalRowFactorLoop.factors differences negatives i positions⟩

end SubexponentialSAT.Subexp.UniversalRowTermProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_Subexp_UniversalRowLoop
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! The actual outer loop assembling correction terms in selected-index order. -/

namespace SubexponentialSAT.Subexp.UniversalRowLoop

open BitProgram StructuredCalls
open UniversalRowGather (Word)
open UniversalRowFactorLoop (indexWord)

def term (t : Tables) (positions : List ℕ) (i : ℕ) : UniversalRowProgram.Term Word :=
  UniversalRowTermProgram.term t.values t.inverses t.negatives (t.differences.getD i []) positions i

end SubexponentialSAT.Subexp.UniversalRowLoop

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_Subexp_UniversalRowDataProgram
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Assemble a complete raw row from runtime scalar/cache tables. -/

namespace SubexponentialSAT.Subexp.UniversalRowDataProgram

open BitProgram StructuredCalls StackRoutines
open UniversalRowGather (Word)
open UniversalRowLoop (Tables )
open UniversalRowFactorLoop (indexWord)

def row (t : Tables) (positions : List ℕ) (delta limit : Word) : UniversalRowProgram.Row Word :=
  ⟨delta, if positions.length ≤ limit.length then positions.map (UniversalRowLoop.term t positions) else []⟩

end SubexponentialSAT.Subexp.UniversalRowDataProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_Subexp_UniversalRowExecution
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Fixed nested source emitter and its actual byte-level execution bound. -/
namespace SubexponentialSAT.Subexp.UniversalRowProgram

open BitProgram StructuredCalls
open SubexpKernelControl (Word pushWord popTag emitOperator countOne drain )

local infixr:60 " ;; " => Cmd.seq

abbrev prepareX : Cmd 3 8 :=
  .call (StackRoutines.copyProgram (2 : Fin 8) 5 4 (0 : Fin 3) 1) ;;
    .call (StackRoutines.copyProgram (1 : Fin 8) 5 4 (0 : Fin 3) 1)

end SubexponentialSAT.Subexp.UniversalRowProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_Subexp_UniversalRowEmitCall
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! A framed call to the actual row source emitter inside the row workspace. -/

namespace SubexponentialSAT.Subexp.UniversalRowEmitCall

open BitProgram StructuredCalls
open UniversalRowProgram (Row)
open SubexpKernelControl (Word)

abbrev reset : Cmd 8 32 :=
  .seq (.base (.atom (.set 0 false)))
    (.seq (.base (.atom (.set 1 false))) (.base (.atom (.set 2 false))))

end SubexponentialSAT.Subexp.UniversalRowEmitCall

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LayoutProgramStaging
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! A finite sequence of genuine copy, clear and constant-bit instructions.
The functional result is only a trace specification; execution uses the
fixed primitive instruction tables. -/
namespace SubexponentialSAT.SqrtLog.LayoutProgram.Staging

open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.Subexp

variable {r s : ℕ}

instance instDecidableValid (tmp : Fin s) (a : Action s) : Decidable (a.Valid tmp) := by
  cases a <;> unfold Action.Valid <;> infer_instance

def Action.destination : Action s → Fin s
  | .copy _ dst => dst
  | .clear dst => dst
  | .push dst _ => dst

end SubexponentialSAT.SqrtLog.LayoutProgram.Staging

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SubexpPredecessorProgram
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! A nine-label bit program for fixed-width binary decrement. -/

namespace SubexponentialSAT.SubexpPredecessorProgram

open SubexponentialSAT.BitProgram SubexponentialSAT.ModularPrograms SubexponentialSAT.ModularArithmetic SubexponentialSAT.BinaryArithmetic

@[simp] theorem toNat_replicate_false (n : ℕ) :
    BinaryArithmetic.toNat (List.replicate n false) = 0 := by
  induction n with
  | zero => rfl
  | succ n ih => simp [List.replicate_succ, toNat_cons, bitVal, ih]

end SubexponentialSAT.SubexpPredecessorProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LayoutTriplePreparationProgramInterface
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

-- LayoutTriplePreparationProgramAlgebra.lean

/-! The factored triple stream uses the positive H cache directly. The outer
parity and both powers in a scalar summand are combined before serialization. -/
namespace SubexponentialSAT.SqrtLog.LayoutTriplePreparationProgram

open scoped BigOperators
open SubexponentialSAT.SqrtLog.RowSelectionProgram
open SubexponentialSAT.SqrtLog.LayoutProgramScalar
open SubexponentialSAT.SqrtLog.LayoutCoefficientAlgorithm
open SubexponentialSAT.SqrtLog.LayoutCoefficientRecurrence

def factoredTerm (A R d h k : ℕ) : ℤ :=
  ((-1 : ℤ)^(A+k) * (H A (R-1-d-k) : ℤ)) * 2^(R-1) * (h.choose k : ℤ)

end SubexponentialSAT.SqrtLog.LayoutTriplePreparationProgram

-- LayoutTriplePreparationProgramSemantics.lean

/-! The actual generated stream has the exact coefficient sum and nonnegative
mass required by the scalar machine, despite the factored cache representation. -/

/-! One consumer-facing contract for native triple preparation. -/

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_Subexp_MismatchPlanProgram
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# Physical mismatch-position selection

The input consists of two packed arrays, a runtime row width, and a framed
list of numeric positions. Each callback reads the two rows with the actual
persistent array reader, compares their bytes, and emits exactly the unequal
positions. The arrays and their order are preserved.
-/

namespace SubexponentialSAT.Subexp.MismatchPlanProgram

open BitProgram StructuredCalls StackRoutines

abbrev copyIndex : Cmd 8 16 := .call (copyProgram 9 2 15 (0 : Fin 8) 1)

def callbackCost (width : ℕ) (bits : Word) : ℕ :=
  (28 * width + 39) * bits.length + 43 * width + 80

def sourceBound (width : ℕ) (records : List Word) : ℕ :=
  8 + RecordPrograms.budget (callbackCost width) records + 10 * (Encoding.encodeList id records).length

def indexRecords (positions : List ℕ) : List Word :=
  positions.map (fun i => List.replicate i true)

end SubexponentialSAT.Subexp.MismatchPlanProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_Subexp_UniversalRowMismatchProgram
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Generate all positions on tape, then retain the mismatches.  The output
is in descending position order, as required by the prepend-based row loops. -/

namespace SubexponentialSAT.Subexp.UniversalRowMismatchProgram

open BitProgram StructuredCalls StackRoutines
open MismatchPlanProgram (indexRecords )

abbrev initializeSource : Cmd 10 17 :=
  .seq (.base (.atom (.set 0 false))) (.base (.atom (.push 8 0)))

def budget (q width : ℕ) : ℕ :=
  9 * q + 13 + SubexpUnaryRangeProgram.steps 0 q +
    MismatchPlanProgram.sourceBound width (indexRecords (List.range q).reverse)

end SubexponentialSAT.Subexp.UniversalRowMismatchProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LayoutProgramSourceBank
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Actual packed source dispatch. This program constructs each polynomial
source from computed metadata and raw scalar caches, not a supplied polynomial
table. The owner-fiber source sum is a separate outer traversal. -/
namespace SubexponentialSAT.SqrtLog.LayoutProgram.SourceBank

open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.Subexp

def stageTypesOps : List (Staging.Action 320) := [.copy 289 23,.copy 292 24]

def stageEmitterOps : List (Staging.Action 320) :=
  [.copy 67 280,.copy 308 281,.copy 309 282,.copy 310 283,.copy 71 284,
   .copy 311 285,.copy 312 286,.copy 313 259,.copy 314 266,.copy 47 269]
def cleanupOps : List (Staging.Action 320) := cleanupPorts.map Staging.Action.clear

end SubexponentialSAT.SqrtLog.LayoutProgram.SourceBank

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LayoutProgramSourceTyped
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Typed witnesses for the actual interpolation table reads. Cached negative
nodes and inverse differences need only have the right decoded value; no
canonical representation or equality with an arithmetic implementation is
assumed. -/
namespace SubexponentialSAT.SqrtLog.LayoutProgram.SourceTyped

open SubexponentialSAT.Subexp SubexponentialSAT.Subexp.UniversalRowProgram SubexponentialSAT.Subexp.UniversalRowSource
open SubexponentialSAT.SubexpSymbolicCost
open SubexponentialSAT.MulticolorTypes SubexponentialSAT.SubexpRepresentedRows SubexponentialSAT.SubexpRowInterpolation

variable {C O : Type*} {Q : ℕ}

def factor (negative : Fin Q → C) (difference : Fin Q → Fin Q → C)
    (i j : Fin Q) : Factor C := ⟨difference i j,negative j⟩

def term (values inverse negative : Fin Q → C) (difference : Fin Q → Fin Q → C)
    (s : Finset (Fin Q)) (i : Fin Q) : Term C :=
  ⟨values i,inverse i,(selected (s.erase i)).map (factor negative difference i)⟩

def row (values inverse negative : Fin Q → C) (difference : Fin Q → Fin Q → C)
    (s : Finset (Fin Q)) (delta : C) (R : ℕ) : Row C :=
  ⟨delta,if s.card ≤ R then (selected s).map (term values inverse negative difference s) else []⟩

end SubexponentialSAT.SqrtLog.LayoutProgram.SourceTyped

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LayoutProgramSourceTables
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Exact table shapes and read validity for finite typed interpolation
caches. Flattening is a specification of the arrays produced natively. -/
namespace SubexponentialSAT.SqrtLog.LayoutProgram.SourceTyped

open SubexponentialSAT.Subexp

variable {C : Type*} {Q : ℕ}

def tables (encode : C → List Bool) (values inverse negative : Fin Q → C)
    (difference : Fin Q → Fin Q → C) : UniversalRowLoop.Tables :=
  ⟨List.ofFn (fun i => encode (values i)),List.ofFn (fun i => encode (inverse i)),
    List.ofFn (fun i => encode (negative i)),List.ofFn (fun i => List.ofFn (fun j => encode (difference i j)))⟩

end SubexponentialSAT.SqrtLog.LayoutProgram.SourceTyped

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LayoutRank
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.labelFintype _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.variableFintype _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Rational row-space bounds for literal integer constraint families. -/

namespace SubexponentialSAT.SqrtLog.LayoutRank

open scoped BigOperators
open Module LayoutPullback LayoutExactBuckets LayoutRowSelection

variable {J I V : Type*} [Fintype J] [Fintype I] [Fintype V]

variable [DecidableEq V]

def rowLinear (owner : I → V) : (I → ℚ) →ₗ[ℚ] (V → ℚ) where
  toFun := row owner
  map_add' a b := by
    funext v
    simp only [row, Pi.add_apply, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    split_ifs <;> simp
  map_smul' c a := by
    funext v
    simp only [row, Pi.smul_apply, smul_eq_mul, RingHom.id_apply, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    split_ifs <;> simp

end SubexponentialSAT.SqrtLog.LayoutRank

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LayoutSignatureBound
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.labelFintype _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.variableFintype _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Exact integer signature ranges for Boolean assignments. -/
namespace SubexponentialSAT.SqrtLog.LayoutSignatureBound

open scoped BigOperators
open LayoutExactBuckets

variable {J V : Type*} [Fintype J] [Fintype V]

/-- Boolean assignments are embedded in the integers before signatures are
computed. No precision-dependent modulus enters this definition. -/
def boolSignature (A : J → V → ℤ) (x : V → Bool) : J → ℤ :=
  signature A (fun v => if x v then 1 else 0)

end SubexponentialSAT.SqrtLog.LayoutSignatureBound

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SubexpNodeIndexProgram
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
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

open BitProgram StructuredCalls

namespace Internal

abbrev copy (src dst : Fin 7) : Cmd 5 7 :=
  .call (StackRoutines.copyProgram src dst 5 (0 : Fin 5) 1)

end Internal

end SubexponentialSAT.SubexpNodeIndexProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LayoutSourcePlanLookupBasic
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! A fixed twelve-stack workspace for a full pair-key lookup. -/
namespace SubexponentialSAT.SqrtLog.LayoutSourcePlanLookup
open SubexponentialSAT BitProgram StructuredCalls

abbrev Code := Cmd 16 12

def copy (src dst : Fin 12) : Code :=
  .call (StackRoutines.copyProgram src dst 11 (0 : Fin 16) 1)

def push (dst : Fin 12) (bit : Bool) : Code :=
  .seq (.base (.atom (.set 0 bit))) (.base (.atom (.push dst 0)))

end SubexponentialSAT.SqrtLog.LayoutSourcePlanLookup

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SubexpEvaluationProgram
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
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

open SubexpPostfixGlobal

/-! ## Entry from arbitrary caller registers -/

def resetList : List (Fin 16) → StructuredProgram.Cmd 16 128
  | [] => .skip
  | i :: is => .seq (.atom (.set i false)) (resetList is)

end SubexponentialSAT.SubexpEvaluationProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LayoutSourceRowsProgram
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Complete finite controllers for source fiber sums and ambient source-row
serialization. Parameters are actual finite programs with paid contracts. -/

/-! A runtime owner-fiber fold of actual serialized polynomial sources. -/
namespace SubexponentialSAT.SqrtLog.LayoutSourceRowsProgram
open SubexponentialSAT BitProgram StructuredCalls

attribute [local simp] Fin.coe_ofNat_eq_mod

def indexBytes (ids : List ℕ) : List Bool := ids.flatMap Encoding.encodeNat

def fiberState (base : Store) (ids : List ℕ) (acc : List Bool) : Store :=
  Function.update (Function.update (Function.update base 328
    (List.replicate ids.length true)) 329 (indexBytes ids)) 333 acc

end SubexponentialSAT.SqrtLog.LayoutSourceRowsProgram

/-! Paid bank relocation and register reset for the native polynomial source
executor. The parameter is a finite BitProgram; the integration selects the
checked polynomial executor, never a polynomial-value instruction. -/

/-! The bytes produced by the runtime fold are the compiler output of the
same finite sum expression, including the empty-owner zero polynomial. -/

namespace SubexponentialSAT.SqrtLog.LayoutSourceRowsProgram
open SubexponentialSAT
variable {R : Type*}

def foldSources (seed : Algorithm.Expr R) (sources : List (Algorithm.Expr R)) : Algorithm.Expr R :=
  sources.foldl Algorithm.Expr.add seed

end SubexponentialSAT.SqrtLog.LayoutSourceRowsProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LayoutSourceRowsProgramSemantics
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! The exact polynomial computed by the native owner-fiber traversal. -/
namespace SubexponentialSAT.SqrtLog.LayoutSourceRowsProgram
open SubexponentialSAT
open scoped BigOperators

variable {A : Type*}

def ownerSum [AddMonoid A] (ps : List (ℕ × ℕ)) (owner : ℕ) (value : ℕ → A) : A :=
  ((LayoutOwnerFiberProgram.fiberIndices owner 0 ps).map value).sum

theorem fiber_empty_of_no_owner (ps : List (ℕ × ℕ)) (owner index : ℕ)
    (h : ∀ p∈ps, p.1≠owner) :
    LayoutOwnerFiberProgram.fiberIndices owner index ps=[] := by
  induction ps generalizing index with
  | nil => rfl
  | cons p ps ih =>
      have hp := h p (by simp)
      have ht : ∀ q∈ps, q.1≠owner := by intro q hq; exact h q (by simp [hq])
      simp [LayoutOwnerFiberProgram.fiberIndices,hp,ih (index+1) ht]

theorem ownerSum_zero [AddMonoid A] (ps : List (ℕ × ℕ)) (owner : ℕ) (value : ℕ → A)
    (h : ∀ p∈ps, p.1≠owner) : ownerSum ps owner value=0 := by
  simp [ownerSum,fiber_empty_of_no_owner ps owner 0 h]

end SubexponentialSAT.SqrtLog.LayoutSourceRowsProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LayoutSourceRowsProgramFamily
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Total original-coordinate source family computed by the native controller.
The missing-incidence branch is zero; required factor-scope incidences use
the exact packed row selected by the actual plan lookup. -/
namespace SubexponentialSAT.SqrtLog.LayoutSourceRowsProgram
open SubexponentialSAT

def sourceRowFamily {A : Type*} [AddMonoid A] (ps : List (ℕ × ℕ))
    (ambient factor literal : ℕ) (source : ℕ → ℕ → A) (owner : ℕ) : A :=
  if (literal,ambient+factor) ∈ ps then
    ownerSum ps owner (source (ps.idxOf (literal,ambient+factor)))
  else 0

end SubexponentialSAT.SqrtLog.LayoutSourceRowsProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LayoutSourceRowsProgramTyped
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! The paid owner-fiber scan emits the actual compiler bytes of one typed
sum expression. No precomputed polynomial values enter the executable. -/
namespace SubexponentialSAT.SqrtLog.LayoutSourceRowsProgram
open SubexponentialSAT BitProgram StructuredCalls

def TypedSourceRel {C A : Type*} [Add A] [Mul A]
    (encode : C → List Bool) (decode : C → A) (value : ℕ → A) (L : ℕ)
    (i : ℕ) (e : Algorithm.Expr C) : Prop :=
  (e.map decode).eval=value i ∧
    (SubexpPostfixControl.serializeCode encode e.compile).length ≤ L

end SubexponentialSAT.SqrtLog.LayoutSourceRowsProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LayoutSourceValuesProgram
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms


/-! The scalar callback calls the actual integer numerator program, then the
actual binary-to-ring scaler. Its integer result is never supplied as input. -/
namespace SubexponentialSAT.SqrtLog.LayoutSourceValuesProgram

open SubexponentialSAT BitProgram StructuredCalls SubexpConvolutionControl
open MulticolorTypes
open _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RowSelectionProgram (WordPair )
open scoped BigOperators
attribute [local simp] Fin.coe_ofNat_eq_mod

namespace Native



def integerBits (R W P : ℕ) : ℕ := R * LayoutProgramScalar.termGrowth (2*W+P)

end Native
end SubexponentialSAT.SqrtLog.LayoutSourceValuesProgram


/-! Closed correction-table construction from type metadata and integer/ring
caches. No correction-scalar table is supplied to the program or theorem. -/


/-! Uniform polynomial accounting and per-index observation of generated
correction tables. All parameters describe actual bytes and runtime counts. -/

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafAssignmentMergeProgram
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! A fixed physical scan merges a current-head assignment with the bucket
representative, keeping the original ambient coordinate order. -/
namespace SubexponentialSAT.SqrtLog.LeafAssignmentMergeProgram

open SubexponentialSAT BitProgram StructuredCalls StackRoutines

abbrev Data := StructuredProgram.State 8 5

abbrev data (r : Fin 8 → Bool) (a h b out tmp : List Bool) : Data :=
  ⟨r,tapes a h b out tmp⟩
def ready (r : Fin 8 → Bool) (a h b out tmp : List Bool) : Data :=
  data (readRegs r 0 3 a.head?) a.tail h b out tmp

abbrev popAssignment : StructuredProgram.Cmd 8 5 := .atom (.pop 0 0 3)
abbrev put : StructuredProgram.Cmd 8 5 :=
  .ite 1 (.atom (.push 4 0)) (.atom (.push 4 2))
abbrev body : StructuredProgram.Cmd 8 5 := .seq (.atom (.pop 1 1 4)) <|
  .seq (.atom (.pop 2 2 5)) (.seq put popAssignment)
abbrev loop : StructuredProgram.Cmd 8 5 := .while 3 body

abbrev scan : StructuredProgram.Cmd 8 5 := .seq popAssignment loop
abbrev command : Cmd 8 5 := .seq (.base scan) (.call (transferProgram 4 3 0 3))

abbrev program := compiled command 0 3

end SubexponentialSAT.SqrtLog.LeafAssignmentMergeProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafWeightProgramNative
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Preserving physical wrapper for the Boolean head-weight scan. The actual
ring zero and one are arbitrary runtime words, so the ring degree is dynamic. -/
namespace SubexponentialSAT.SqrtLog.LeafWeightProgram.Native

open SubexponentialSAT BitProgram StructuredCalls StackRoutines

abbrev Data := StructuredProgram.State 8 10

abbrev data (r : Fin 8 → Bool) (a s h zero one x y z out : List Bool) : Data :=
  ⟨r,tapes a s h zero one x y z out⟩

abbrev copy (src dst : Fin 10) : Cmd 8 10 := .call (copyProgram src dst 8 0 3)

end SubexponentialSAT.SqrtLog.LeafWeightProgram.Native

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafAssignmentMergeProgramNative
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Preserving shell for the assignment merge. Only output9 and registers
change; the masters and both reserved words are preserved. -/
namespace SubexponentialSAT.SqrtLog.LeafAssignmentMergeProgram.Native

open SubexponentialSAT BitProgram StructuredCalls StackRoutines

abbrev data := LeafWeightProgram.Native.data
abbrev copy := LeafWeightProgram.Native.copy

abbrev scan : Cmd 8 10 :=
  .call (ProgramLinking.liftProgram LeafAssignmentMergeProgram.program id stackMap)

abbrev command : Cmd 8 10 := .seq (copy 0 5)
  (.seq (copy 1 6) (.seq (copy 2 7) scan))

def program := compiled command 0 9

end SubexponentialSAT.SqrtLog.LeafAssignmentMergeProgram.Native

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafAssignmentSetupProgramBase
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Concrete storage and framed service calls for each head assignment. -/
noncomputable section
namespace SubexponentialSAT.SqrtLog.LeafAssignmentSetupProgram
open SubexponentialSAT BitProgram StructuredCalls StackRoutines

abbrev Code := Cmd 40 768

end SubexponentialSAT.SqrtLog.LeafAssignmentSetupProgram
end

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
open SubexponentialSAT BitProgram StructuredCalls

abbrev Code := Cmd 8 16

def copy (src dst : Fin 16) : Code := .call (StackRoutines.copyProgram src dst 14 0 1)

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
open SubexponentialSAT BitProgram StructuredCalls

def mark (isHash isMarked : Bool) : Code :=
  .seq (.base (.atom (.set 5 isHash))) (.base (.atom (.set 6 isMarked)))

end SubexponentialSAT.SqrtLog.LeafFactorDispatchProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafFactorDispatchProgramChoose
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.LeafFactorDispatchProgram
open SubexponentialSAT BitProgram StructuredCalls

def branchBound (rows clauses : List (List Bool)) (m f : ℕ) :=
  2*f+7*m+23*((Encoding.encodeList id rows).length+(Encoding.encodeList id clauses).length)+38

def dispatchBound (rows clauses : List (List Bool)) (m f : ℕ) :=
  2*(13*f+9*rows.length+45)+branchBound rows clauses m f+3

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
open SubexponentialSAT BitProgram StructuredCalls

def baseStacks (rows clauses : List (List Bool)) (m f : ℕ) : Fin 16 → List Bool :=
  ![Encoding.encodeList id rows,Encoding.encodeList id clauses,(Encoding.encodeNat f).reverse,
    unary rows.length,Encoding.encodeNat m,[],[],[],[],[],[],[],[],[],[],[]]

def prepare : Code := .call (StackRoutines.transferProgram 2 6 0 1)

def budget (rows clauses : List (List Bool)) (m f : ℕ) :=
  3*f+7+dispatchBound rows clauses m f

end SubexponentialSAT.SqrtLog.LeafFactorDispatchProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafHeadFactorsProgramSemantics
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! The physical row predicate selects exactly the computed factor colors. -/
namespace SubexponentialSAT.SqrtLog.LeafHeadFactorsProgram
open SubexponentialSAT BitProgram StructuredCalls MulticolorTypes

def indices (A N : ℕ) : List (Fin A ⊕ Fin N) :=
  Packing.headsFirstIndices (List.finRange A) (List.finRange N)

end SubexponentialSAT.SqrtLog.LeafHeadFactorsProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafProgramMass
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! The primitive integer accumulator used after each marked-clause count.
Both operands have runtime lengths. The fixed instruction table adds them
exactly and restores little-endian orientation; no arithmetic instruction or
precomputed mass is admitted into the machine model. -/

namespace SubexponentialSAT.SqrtLog.LeafProgram.Mass

open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls

abbrev command : Cmd 8 3 :=
  .seq (.base (.atom (.set 0 false))) (.call BinaryPrograms.Add.littleEndianProgram)

def program := compiled command 1 0

variable {r s : ℕ}

abbrev invoke (p : Ports r s) : Cmd r s :=
  .call (ProgramLinking.liftProgram program p.register p.stack)

end SubexponentialSAT.SqrtLog.LeafProgram.Mass

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafStatisticsProgramBoot
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! The variable scan is started from actual serialized scopes and a mask.
The factor count is obtained by a physical record scan, never supplied as data. -/
namespace SubexponentialSAT.SqrtLog.LeafStatisticsProgram
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls

def zeroTotals : Totals := ⟨0,0,0,0⟩

end SubexponentialSAT.SqrtLog.LeafStatisticsProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_Subexp_UniversalRowSourceBound
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Polynomial bounds for the actual nested row-data and source emitters. -/

namespace SubexponentialSAT.Subexp.UniversalRowSourceBound

open UniversalRowProgram
open UniversalRowFactorLoop (indexWord)

def termBound (S : ℕ) :=
  S * (28 * S + 14 * S + 51) + 30 * S + 15 * S + 63 +
    7 * indicesBound S + factorLoopBound S +
    (24 * (S + S) + 8 * factorsBytes S + 42) + 2 * S + 2 * S + 20
def outerLoopBound (S : ℕ) := S * (6 * S + termBound S + 7)
def dataBound (S : ℕ) :=
  10 * indicesBound S + 13 * S + 6 * S + 40 +
    (7 * indicesBound S + 8 + outerLoopBound S) + 8 * S + 11
def sourceBound (S : ℕ) := dataBound S + 2048 * inputBound S ^ 2 + 4

end SubexponentialSAT.Subexp.UniversalRowSourceBound

end OAI.Algorithms
end


