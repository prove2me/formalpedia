-- Prove2me | Definitions.Def_OAIQ081S055
-- name    : OAIQ081S055
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-29T21:42:04.835438+00:00
-- url     : https://prove2.me/theorems/5b12ce92-e4e8-4ce1-bcf0-8295249a3474
-- title:
--   Definitions bundle OAIQ081S055 of the split of OpenAI, The Exponential Time Hypothesis is False
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.exact_count_and_sat`, carved from OpenAI's openai/math development (OpenAI, *The Exponential Time Hypothesis is False*, OpenAI Math Release, October 25, 2026, result family 378, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 99 declarations of OpenAI's Lean: 69 definitions and 30 theorems. The definitions and types are `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutFiberSumProgram.addEntry`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutFiberSumProgram.addProgram`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutFiberSumProgram.clearCount`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutFiberSumProgram.finish`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutFiberSumProgram.move`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutFiberSumProgram.parkColumn`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutFiberSumProgram.peek`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutMatrixProgram.MatrixRel`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutMatrixProgram.commandCost`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutMatrixProgram.ids`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutMatrixProgram.parse`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutMatrixProgram.readerPorts`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutMatrixProgram.rowsWords`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutNumerator.entry`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutNumerator.family`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutNumerator.integerDelta`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutNumerator.integerDifference`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutNumerator.joint`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutNumerator.rationalDefect`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutOffsetProgram.budget`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutOffsetProgram.coreBudget`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutOffsetProgram.outputLength`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutOffsetProgram.width`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutOwnerFiberProgram.clear`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutOwnerFiberProgram.compare`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutOwnerFiberProgram.compareOwner`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutOwnerFiberProgram.copyQuery`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutOwnerFiberProgram.forward`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutOwnerFiberProgram.normalize`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutOwnerFiberProgram.outerPorts`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutOwnerFiberProgram.outerRead`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutOwnerFiberProgram.parseOwner`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutOwnerFiberProgram.popScan`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutOwnerFiberProgram.readFrame`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutOwnerFiberProgram.readPorts`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutOwnerFiberProgram.restore`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgram.EntryBank.integerBudget`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgram.addressLabel`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgram.labelPlans`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutScaledMatrices.Numerators` and 29 more.
--
--   **Sources.** They come from these modules of lean/OAI/Algorithms, in whole or in part: `SubexponentialSAT_SqrtLog_LayoutFiberSumProgram`, `SubexponentialSAT_SqrtLog_LayoutFiberSumProgramBasic`, `SubexponentialSAT_SqrtLog_LayoutFiberSumProgramLoop`, `SubexponentialSAT_SqrtLog_LayoutFiberSumProgramMove`, `SubexponentialSAT_SqrtLog_LayoutMatrixProgram`, `SubexponentialSAT_SqrtLog_LayoutMatrixProgramLoop`, `SubexponentialSAT_SqrtLog_LayoutMatrixProgramPrimitives`, `SubexponentialSAT_SqrtLog_LayoutMatrixProgramRowScan`, `SubexponentialSAT_SqrtLog_LayoutNumerator`, `SubexponentialSAT_SqrtLog_LayoutNumeratorBridge`, `SubexponentialSAT_SqrtLog_LayoutOffsetProgram`, `SubexponentialSAT_SqrtLog_LayoutOwnerFiberProgram`, `SubexponentialSAT_SqrtLog_LayoutOwnerFiberProgramCompare`, `SubexponentialSAT_SqrtLog_LayoutOwnerFiberProgramCore`, `SubexponentialSAT_SqrtLog_LayoutOwnerFiberProgramEmit`, `SubexponentialSAT_SqrtLog_LayoutOwnerFiberProgramParse`, `SubexponentialSAT_SqrtLog_LayoutOwnerFiberProgramVisit`, `SubexponentialSAT_SqrtLog_LayoutProgramEntryBankCost`, `SubexponentialSAT_SqrtLog_LayoutProgramLabels`, `SubexponentialSAT_SqrtLog_LayoutProgramScalar`, `SubexponentialSAT_SqrtLog_LayoutScaledMatrices`, `SubexponentialSAT_SqrtLog_LayoutSourceValuesProgram`, `SubexponentialSAT_SqrtLog_PackingIncidenceInputSemantics`, `SubexponentialSAT_SqrtLog_PackingProgramArithmetic`, `SubexponentialSAT_SqrtLog_RowSelectionProgramArithmetic`, `SubexponentialSAT_SqrtLog_RowSelectionProgramResources`, `SubexponentialSAT_SqrtLog_RowSelectionProgramReuse`, `SubexponentialSAT_SqrtLog_RowSelectionProgramStream`, `SubexponentialSAT_SubexpAnnihilation`, `SubexponentialSAT_SubexpNodeIndexProgram`, `SubexponentialSAT_Subexp_AssignmentAlphabetSemantics`, `SubexponentialSAT_Subexp_MatrixEntryEvaluation`, `SubexponentialSAT_Subexp_MatrixEntryExtract`, `SubexponentialSAT_Subexp_MatrixExtendedEntryProgram`, `SubexponentialSAT_Subexp_MatrixScanSemantics`, `SubexponentialSAT_Subexp_MatrixSupport`, `SubexponentialSAT_Subexp_ReadPlan`, `SubexponentialSAT_Subexp_TensorSpectrum`.
--
--   **Imports.** It imports the published bundle `Def_SubexponentialSAT`; the bundles `OAIQ081S023`, `OAIQ081S024`, `OAIQ081S025`, `OAIQ081S026`, `OAIQ081S027`, `OAIQ081S028`, `OAIQ081S032`, `OAIQ081S033`, `OAIQ081S034` and `OAIQ081S035` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ081S072`, `OAIQ081S073`, `OAIQ081S075`, `OAIQ081S078` and `OAIQ081S081`; the statements `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutCoefficientAlgorithm.scalarEntry_cast`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutNumerator.centered_rationalDefect_rank_relative`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutTriplePreparationProgram.scanCounts_bounds_of_anchor`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutTriplePreparationProgram.scanFormula_eq_scalarEntry` and `OAI.Algorithms.SubexponentialSAT.SqrtLog.RowSelectionProgram.multiplyReuseCommand_eval_total`; the proofs of `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutCoefficientAlgorithm.scalarEntry_cast`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutTriplePreparationProgram.scanCounts_bounds_of_anchor`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutTriplePreparationProgram.scanFormula_eq_scalarEntry` and `OAI.Algorithms.SubexponentialSAT.SqrtLog.RowSelectionProgram.multiplyReuseCommand_eval_total`.
-- source:
--   OpenAI, The Exponential Time Hypothesis is False, OpenAI Math Release, October 25, 2026, https://github.com/openai/math (result family 378; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/The-Exponential-Time-Hypothesis-is-False-October-25-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Algorithms at commit 7ef5c0c

import Mathlib
import Definitions.Def_SubexponentialSAT
import Definitions.Def_OAIQ081S023
import Definitions.Def_OAIQ081S024
import Definitions.Def_OAIQ081S025
import Definitions.Def_OAIQ081S026
import Definitions.Def_OAIQ081S027
import Definitions.Def_OAIQ081S028
import Definitions.Def_OAIQ081S032
import Definitions.Def_OAIQ081S033
import Definitions.Def_OAIQ081S034
import Definitions.Def_OAIQ081S035

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_PackingProgramArithmetic
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! One fixed binary machine combines the two collision counts. Its instruction
count and every output length are charged in terms of actual input bit lengths. -/
namespace SubexponentialSAT.SqrtLog.PackingProgram
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.ArithmeticCalls

abbrev weightedScoreCommand : Cmd 8 12 :=
  .seq (multiplyAt firstProductPorts)
    (.seq (multiplyAt secondProductPorts) (addAt productSumPorts))

abbrev weightedScoreProgram := compiled weightedScoreCommand 0 6

end SubexponentialSAT.SqrtLog.PackingProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_RowSelectionProgramArithmetic
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Exact signed arithmetic for minor enumeration. Integers are represented as
pairs of natural binary words. No modular arithmetic, integer oracle, or
parameter-dependent instruction table is used. -/
namespace SubexponentialSAT.SqrtLog.RowSelectionProgram

open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls
open SubexponentialSAT.BinaryArithmetic

abbrev scoreCall (ports : Fin 12 → Fin 15) : Cmd 8 15 :=
  .call (ProgramLinking.liftProgram PackingProgram.weightedScoreProgram id ports)

/-- Inputs 0,1 represent the first integer and 2,3 the second. Outputs 6,9
represent their product. Ports 4,5,7,8 contain intermediate products; 10--14
are restored empty. All input words are preserved. -/
abbrev multiplyCommand : Cmd 8 15 :=
  .seq (scoreCall positivePorts) (scoreCall negativePorts)

end SubexponentialSAT.SqrtLog.RowSelectionProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_RowSelectionProgramResources
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Stack-size accounting and fixed cleanup loops for signed minor arithmetic. -/
namespace SubexponentialSAT.SqrtLog.RowSelectionProgram

open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls

abbrev clearAt (j : Fin 15) : Cmd 8 15 :=
  .call (StackRoutines.clearProgram j 0 1)

def clearList : List (Fin 15) → Cmd 8 15
  | [] => .base .skip
  | j :: js => .seq (clearAt j) (clearList js)

end SubexponentialSAT.SqrtLog.RowSelectionProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_RowSelectionProgramReuse
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! A fixed cleanup adapter makes signed arithmetic reusable inside loops. -/
namespace SubexponentialSAT.SqrtLog.RowSelectionProgram

open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls

abbrev finishCommand : Cmd 8 15 :=
  .seq (clearList [0,1,2,3,4,5,7,8])
    (.seq (ArithmeticCalls.copyAt 6 0 10)
      (.seq (ArithmeticCalls.copyAt 9 1 10) (clearList [6,9])))

/-- Reusable signed multiplication: result returns on 0/1 and all other
stacks are empty. The source operands on 0/1 and 2/3 are consumed. -/
abbrev multiplyReuseCommand : Cmd 8 15 := .seq multiplyCommand finishCommand

/-- Reusable signed addition with a linear bound on the total result-word size. -/
abbrev addReuseCommand : Cmd 8 15 := .seq addCommand finishCommand

end SubexponentialSAT.SqrtLog.RowSelectionProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_RowSelectionProgramStream
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Arithmetic callbacks on a fixed stream ABI. The remaining record stream is
preserved byte-for-byte across each real signed-arithmetic call. -/
namespace SubexponentialSAT.SqrtLog.RowSelectionProgram

open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls

abbrev localOperation (multiply : Bool) : Cmd 8 15 :=
  if multiply then multiplyReuseCommand else addReuseCommand

def localOperationProgram (multiply : Bool) := compiled (localOperation multiply) 0 1

abbrev streamOperation (multiply : Bool) : Cmd 8 16 :=
  .call (ProgramLinking.liftProgram (localOperationProgram multiply) id streamPorts)

end SubexponentialSAT.SqrtLog.RowSelectionProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LayoutFiberSumProgramBasic
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Native owner-fiber summation helpers. The remaining fiber is a stream of
actual unary index fields, never an array of precomputed matrix entries. -/
namespace SubexponentialSAT.SqrtLog.LayoutFiberSumProgram
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls
open RowSelectionProgram

def addProgram := compiled (RowSelectionProgram.streamOperation false) 0 1
def addEntry : Code := .call (ProgramLinking.liftProgram addProgram addRegisters addStacks)

end SubexponentialSAT.SqrtLog.LayoutFiberSumProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LayoutFiberSumProgramLoop
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.LayoutFiberSumProgram
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls RowSelectionProgram

def peek : Code := .seq (.base (.atom (.pop 214 14 15)))
  (.ite 15 (.base (.atom (.push 214 14))) (.base .skip))

end SubexponentialSAT.SqrtLog.LayoutFiberSumProgram

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

abbrev compare : Cmd 5 7 :=
  .call (ProgramLinking.liftProgram ExecClauseCost.bitEqualityProgram id comparePorts)

end Internal

end SubexponentialSAT.SubexpNodeIndexProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_Subexp_ReadPlan
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree _root_.OAI.Algorithms.SubexponentialSAT.Subexp.MatrixEntryKernel.compatibleDecidable _root_.OAI.Algorithms.SubexponentialSAT.Subexp.MatrixEntryKernel.spectatorsAgreeDecidable _root_.OAI.Algorithms.SubexponentialSAT.Subexp.MatrixExtendedEntryProgram.instDecidableAnchorValid
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# Explicit local read plans

Read plans are lists of numeric positions in the explicit seed array. The
machine-facing data are fixed-width one-hot word records and unary indices.
Gathering them in head/slot order reproduces the actual type encoding.
-/

namespace SubexponentialSAT.Subexp.ReadPlan

open SubexponentialSAT.MulticolorTypes SubexponentialSAT.SlotAssignment

section Encoding

variable {r Q Δ : ℕ}

/-- Concatenating encoded head and slot words is the existing type encoding. -/
theorem encodeType_eq_words (u : UniversalType r Q Δ) :
    CollisionProgram.encodeType u =
      (List.ofFn fun a : Fin (Δ + 1) =>
        encodeWord (CollisionProgram.registerWord u a)).flatten := by
  calc
    CollisionProgram.encodeType u =
        ((List.ofFn fun a : Fin (Δ + 1) => List.ofFn fun q : Fin Q =>
          List.ofFn fun c : Fin r =>
            decide (CollisionProgram.registerWord u a q = c)).flatten).flatten := by
      unfold CollisionProgram.encodeType
      unfold CollisionProgram.typeWidth
      change List.ofFn (fun j : Fin (((Δ + 1) * Q) * r) =>
        CollisionProgram.codeBit u j) = _
      rw [ofFn_prod (m := (Δ + 1) * Q) (n := r)]
      rw [ofFn_prod (m := Δ + 1) (n := Q)]
      simp only [CollisionProgram.codeBit, Equiv.symm_apply_apply]
    _ = _ := by
      rw [List.flatten_flatten, List.map_ofFn]
      rfl

end Encoding

end SubexponentialSAT.Subexp.ReadPlan

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LayoutOwnerFiberProgramCore
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Native owner-fiber scan primitives. Original ambient IDs are compared as
unary strings; the emitted indices count positions in the actual plan stream. -/
namespace SubexponentialSAT.SqrtLog.LayoutOwnerFiberProgram
open SubexponentialSAT BitProgram StructuredCalls SubexpScanPrimitives

def forward : Code := .call (StackRoutines.transferProgram 3 4 0 1)

def readPorts : RecordPrograms.Ports 5 11 where
  tag:=0; present:=1; found:=4; source:=4; payload:=3
  tag_ne_present:=by decide
  found_ne_tag:=by decide
  found_ne_present:=by decide
  source_ne_payload:=by decide

def readFrame : Code := RecordPrograms.reader readPorts

def clear (src : Fin 11) : Code := .call (StackRoutines.clearProgram src 0 1)

end SubexponentialSAT.SqrtLog.LayoutOwnerFiberProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LayoutOwnerFiberProgramCompare
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.LayoutOwnerFiberProgram
open SubexponentialSAT BitProgram StructuredCalls SubexpScanPrimitives

def compare : Code := liftCommand SubexponentialSAT.SubexpNodeIndexProgram.Internal.compare 3 4 id compareSlots

def copyQuery : Code := .call (StackRoutines.copyProgram 0 5 6 0 1)

def compareOwner : Code := .seq copyQuery (.seq compare (.seq (clear 3) (clear 5)))

end SubexponentialSAT.SqrtLog.LayoutOwnerFiberProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LayoutOwnerFiberProgramEmit
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.LayoutOwnerFiberProgram
open SubexponentialSAT BitProgram StructuredCalls SubexpScanPrimitives

def normalize : Code := .seq (.base (.atom (.set 0 false)))
  (.seq (.base (.atom (.set 1 true))) (.base (.atom (.set 4 false))))

end SubexponentialSAT.SqrtLog.LayoutOwnerFiberProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LayoutOwnerFiberProgramParse
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.LayoutOwnerFiberProgram
open SubexponentialSAT BitProgram StructuredCalls SubexpScanPrimitives

def parseOwner : Code := .seq forward (.seq readFrame (.seq forward
  (.seq popDecoded (.seq readFrame (clear 4)))))

end SubexponentialSAT.SqrtLog.LayoutOwnerFiberProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LayoutOwnerFiberProgramVisit
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.LayoutOwnerFiberProgram
open SubexponentialSAT BitProgram StructuredCalls SubexpScanPrimitives

def outerPorts : RecordPrograms.Ports 5 11 where
  tag:=0; present:=1; found:=4; source:=2; payload:=3
  tag_ne_present:=by decide
  found_ne_tag:=by decide
  found_ne_present:=by decide
  source_ne_payload:=by decide

def outerRead : Code := RecordPrograms.reader outerPorts

def popScan : Code := .base (.atom (.pop 2 0 1))

end SubexponentialSAT.SqrtLog.LayoutOwnerFiberProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LayoutOwnerFiberProgram
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.LayoutOwnerFiberProgram
open SubexponentialSAT BitProgram StructuredCalls SubexpScanPrimitives

def restore : Code := .call (StackRoutines.transferProgram 8 10 0 1)

end SubexponentialSAT.SqrtLog.LayoutOwnerFiberProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LayoutFiberSumProgramMove
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.LayoutFiberSumProgram
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls

def move (src dst tmp : Fin 256) : Code :=
  .seq (.call (StackRoutines.copyProgram src dst tmp 0 1))
    (.call (StackRoutines.clearProgram src 0 1))

end SubexponentialSAT.SqrtLog.LayoutFiberSumProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LayoutFiberSumProgram
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.LayoutFiberSumProgram
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls RowSelectionProgram

def parkColumn : Code := move 253 216 224
def clearCount : Code := .call (StackRoutines.clearProgram 215 0 1)
def finish : Code := .seq (move 212 254 224)
  (.seq (move 213 255 224) (move 216 253 224))

end SubexponentialSAT.SqrtLog.LayoutFiberSumProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LayoutMatrixProgramPrimitives
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Fixed stack and framing adapters for direct construction of all incidence
rows. The adapters expose native instruction counts and exact stack effects. -/
namespace SubexponentialSAT.SqrtLog.LayoutMatrixProgram
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls

abbrev readerPorts {s : ℕ} (src dst : Fin s) (h : src ≠ dst) : RecordPrograms.Ports 16 s :=
  ⟨0,1,2,src,dst,by decide,by decide,by decide,h⟩

abbrev parse {s : ℕ} (src dst : Fin s) (h : src ≠ dst) : Code s :=
  .seq (.base (.atom (.pop src 2 3)))
    (.ite 2 (RecordPrograms.reader (readerPorts src dst h)) (.base .skip))

end SubexponentialSAT.SqrtLog.LayoutMatrixProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LayoutMatrixProgramRowScan
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Paid traversal of the explicit original-column identifier records. -/
namespace SubexponentialSAT.SqrtLog.LayoutMatrixProgram
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls

def ids (js : List ℕ) : List Bool :=
  ProgramEncoding.encodeRecords (js.map fun j => List.replicate j true)

end SubexponentialSAT.SqrtLog.LayoutMatrixProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LayoutMatrixProgramLoop
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Fixed nested traversal: descending unary rows and reversed original head
IDs, with prepending restoring the requested row and column order. -/
namespace SubexponentialSAT.SqrtLog.LayoutMatrixProgram
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls

def rowsWords (rows : List (List Pair)) : List Bool :=
  Subexp.MatrixProgramSupport.words (rows.map pairWords)

end SubexponentialSAT.SqrtLog.LayoutMatrixProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LayoutMatrixProgram
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Direct all-incidence-row signed matrix construction by one fixed program.
The entry dependency is an explicit native finite-bank command contract. -/
namespace SubexponentialSAT.SqrtLog.LayoutMatrixProgram
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls

@[simp] theorem ids_reverse_length (js : List ℕ) : (ids js.reverse).length=(ids js).length := by
  simp [ids,List.map_reverse,ProgramEncoding.encodeRecords_length]

def commandCost (T B D n : ℕ) (js : List ℕ) : ℕ :=
  19*(ids js).length+12+D*(rowBodyCost T B n D (ids js).length js.length+2)

def MatrixRel (Rel : ℕ → ℕ → Pair → Prop) (B D : ℕ) (js : List ℕ)
    (rows : List (List Pair)) : Prop :=
  List.Forall₂ (fun j row => List.Forall₂ (fun v p => Rel j v p ∧ pairLength p ≤ B) js row)
    (List.range D) rows

end SubexponentialSAT.SqrtLog.LayoutMatrixProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_Subexp_MatrixSupport
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.labelFintype _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.variableFintype _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree _root_.OAI.Algorithms.SubexponentialSAT.Subexp.MatrixEntryKernel.compatibleDecidable _root_.OAI.Algorithms.SubexponentialSAT.Subexp.MatrixEntryKernel.spectatorsAgreeDecidable _root_.OAI.Algorithms.SubexponentialSAT.Subexp.MatrixExtendedEntryProgram.instDecidableAnchorValid
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# Restricted support of the multicolor interpolation matrices

The multicolor register permutations and the products of (1 - J_l) / 2 are constructed
explicitly.  The support conclusion is derived from their sublist expansion.
-/

namespace SubexponentialSAT.Subexp.MatrixSupport

open SubexponentialSAT.MulticolorTypes
open scoped BigOperators

variable {r Q Δ : ℕ}

/-- Ordered application of the position involutions. -/
def applySwaps (i : Fin Δ) : List (Fin Q) → UniversalType r Q Δ → UniversalType r Q Δ
  | [], u => u
  | a :: as, u => applySwaps i as (swapPositions i {a} u)

theorem applySwaps_head_of_not_mem (i : Fin Δ) (as : List (Fin Q))
    (u : UniversalType r Q Δ) {l : Fin Q} (hl : l ∉ as) :
    (applySwaps i as u).head l = u.head l := by
  induction as generalizing u with
  | nil => rfl
  | cons a as ih =>
    simp only [List.mem_cons, not_or] at hl
    rw [applySwaps, ih _ hl.2]
    simp [hl.1]

/-- Any possible mismatches are in the omitted set, together with position t. -/
theorem mismatches_card_le (i : Fin Δ) (t : Fin Q) (A : Finset (Fin Q))
    (u y : UniversalType r Q Δ)
    (h : ∀ l, l ≠ t → l ∉ A → y.head l = u.slot i l) :
    (mismatches i u y).card ≤ A.card + 1 := by
  have hs : mismatches i u y ⊆ insert t A := by
    intro l hl
    by_cases hlt : l = t
    · simp [hlt]
    · have hlA : l ∈ A := by
        by_contra hn
        exact ((mem_mismatches i u y l).mp hl) (h l hlt hn)
      exact Finset.mem_insert_of_mem hlA
  exact (Finset.card_le_card hs).trans (Finset.card_insert_le t A)

section Operators

variable {K : Type*} [Field K]

/-- Full expansion: one term for each choice of the permutation part of a factor. -/
theorem differenceProduct_expansion (i : Fin Δ) (as : List (Fin Q))
    (f : UniversalType r Q Δ → K) (u : UniversalType r Q Δ) :
    differenceProduct i as f u =
      (as.sublists'.map (fun bs =>
        (-1 : K) ^ bs.length * f (applySwaps i bs u))).sum := by
  induction as generalizing u with
  | nil => simp [differenceProduct, applySwaps]
  | cons a as ih =>
    simp only [differenceProduct, ih, List.sublists'_cons, List.map_append,
      List.sum_append, List.map_map, Function.comp_def, List.length_cons,
      applySwaps, pow_succ]
    simp only [mul_assoc, mul_comm (-1 : K) ]
    simp only [← mul_assoc]
    rw [List.sum_map_mul_right]
    ring

/-- The normalized expansion is valid even when some coefficients cancel. -/
theorem projectorProduct_expansion (i : Fin Δ) (as : List (Fin Q))
    (f : UniversalType r Q Δ → K) (u : UniversalType r Q Δ) :
    projectorProduct i as f u =
      (2 : K)⁻¹ ^ as.length *
        (as.sublists'.map (fun bs =>
          (-1 : K) ^ bs.length * f (applySwaps i bs u))).sum := by
  rw [projectorProduct, differenceProduct_expansion]

/-- Equation (3.5), evaluated on the column basis vector indexed by y.
The outer full permutation is pullback by swapPositions.
-/
noncomputable def matrixEntry (i : Fin Δ) (t : Fin Q) (R : ℕ) (c : ℕ → K)
    (u y : UniversalType r Q Δ) : K :=
  ∑ j ∈ Finset.range R,
    c j * elementaryProjector i t j (delta y) (swapPositions i (activePositions t) u)

/-- Every subword of omitted flips leaves all other positions equal to the original slot. -/
theorem applySwaps_mismatches_card_le (i : Fin Δ) (t : Fin Q)
    (as : List (Fin Q)) (u : UniversalType r Q Δ) :
    (mismatches i u (applySwaps i as (swapPositions i (activePositions t) u))).card ≤
      as.toFinset.card + 1 := by
  apply mismatches_card_le i t as.toFinset
  intro l hlt hl
  rw [applySwaps_head_of_not_mem i as _ (by simpa using hl)]
  simp [activePositions, hlt]

theorem delta_applySwaps_eq_zero (i : Fin Δ) (t : Fin Q) (A : Finset (Fin Q))
    (as : List (Fin Q)) (has : as.Sublist A.toList) (u y : UniversalType r Q Δ)
    (hbad : A.card + 1 < (mismatches i u y).card) :
    (delta y (applySwaps i as (swapPositions i (activePositions t) u)) : K) = 0 := by
  unfold delta
  split_ifs with heq
  · have hbound := applySwaps_mismatches_card_le i t as u
    rw [heq] at hbound
    have hsub : as.toFinset ⊆ A := by
      intro l hl
      have hm : l ∈ as := by simpa using hl
      have hm' : l ∈ A.toList := has.subset hm
      simpa using hm'
    have hc := Finset.card_le_card hsub
    omega
  · rfl

/-- Each elementary projector term has restricted support after the full permutation. -/
theorem projectorProduct_delta_eq_zero (i : Fin Δ) (t : Fin Q)
    (A : Finset (Fin Q)) (u y : UniversalType r Q Δ)
    (hbad : A.card + 1 < (mismatches i u y).card) :
    projectorProduct i A.toList (delta y)
      (swapPositions i (activePositions t) u) = (0 : K) := by
  rw [projectorProduct_expansion]
  suffices hsum :
      (A.toList.sublists'.map (fun bs =>
        (-1 : K) ^ bs.length *
          delta y (applySwaps i bs (swapPositions i (activePositions t) u)))).sum = 0 by
    rw [hsum, mul_zero]
  apply List.sum_eq_zero
  intro a ha
  obtain ⟨bs, hbs, rfl⟩ := List.mem_map.mp ha
  have hsub := List.mem_sublists'.mp hbs
  rw [delta_applySwaps_eq_zero i t A bs hsub u y hbad, mul_zero]

/-- The restricted-support conclusion for the actual matrix formula, with no
assumption on the coefficients or on whether expansion terms cancel. -/
theorem matrixEntry_support (i : Fin Δ) (t : Fin Q) (R : ℕ) (c : ℕ → K)
    (u y : UniversalType r Q Δ) (hne : matrixEntry i t R c u y ≠ 0) :
    (mismatches i u y).card ≤ R := by
  by_contra h
  have hbad : R < (mismatches i u y).card := by omega
  apply hne
  unfold matrixEntry
  apply Finset.sum_eq_zero
  intro j hj
  have hjR : j < R := Finset.mem_range.mp hj
  have he : elementaryProjector i t j (delta y)
      (swapPositions i (activePositions t) u) = (0 : K) := by
    unfold elementaryProjector
    apply Finset.sum_eq_zero
    intro A hA
    have hcard : A.card = j := (Finset.mem_powersetCard.mp hA).2
    apply projectorProduct_delta_eq_zero i t A u y
    omega
  rw [he, mul_zero]

/-- The matrix on the joint fiber used by the universal-block construction. -/
noncomputable def jointMatrix (i : Fin Δ) (t : Fin Q) (g : Fin r)
    (R : ℕ) (c : ℕ → K) :
    Matrix (Joint t g i) (Joint t g i) K :=
  fun u y => matrixEntry i t R c u.val y.val

theorem jointMatrix_support (i : Fin Δ) (t : Fin Q) (g : Fin r)
    (R : ℕ) (c : ℕ → K) (u y : Joint t g i)
    (hne : jointMatrix i t g R c u y ≠ 0) :
    (mismatches i u.val y.val).card ≤ R :=
  matrixEntry_support i t R c u.val y.val hne

end Operators

end SubexponentialSAT.Subexp.MatrixSupport

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LayoutNumerator
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.labelFintype _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.variableFintype _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree _root_.OAI.Algorithms.SubexponentialSAT.Subexp.MatrixEntryKernel.compatibleDecidable _root_.OAI.Algorithms.SubexponentialSAT.Subexp.MatrixEntryKernel.spectatorsAgreeDecidable _root_.OAI.Algorithms.SubexponentialSAT.Subexp.MatrixExtendedEntryProgram.instDecidableAnchorValid
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# Integer numerators for the actual universal swap matrices

The parity coefficients are the immutable library's coefficients, instantiated
over the integers. Their images are the same coefficients over every
commutative ring. Clearing the projector denominators uses only powers of two.
-/

namespace SubexponentialSAT.SqrtLog.LayoutNumerator

open scoped BigOperators
open SubexponentialSAT.MulticolorTypes
open SubexponentialSAT.BinomialInterpolation
open SubexponentialSAT.Subexp.MatrixSupport

variable {r Q Δ : ℕ}

/-- The same ordered difference product, without requiring a field. -/
def integerDifference (i : Fin Δ) : List (Fin Q) →
    (UniversalType r Q Δ → ℤ) → UniversalType r Q Δ → ℤ
  | [], f, u => f u
  | a :: as, f, u => integerDifference i as f u -
      integerDifference i as f (swapPositions i {a} u)

theorem integerDifference_cast (K : Type*) [Field K] (i : Fin Δ)
    (as : List (Fin Q)) (f : UniversalType r Q Δ → ℤ)
    (u : UniversalType r Q Δ) :
    (integerDifference i as f u : K) =
      differenceProduct i as (fun v => (f v : K)) u := by
  induction as generalizing u with
  | nil => rfl
  | cons a as ih => simp only [integerDifference, Int.cast_sub, differenceProduct, ih]

def integerDelta (y x : UniversalType r Q Δ) : ℤ :=
  if x = y then 1 else 0

theorem integerDelta_cast (K : Type*) [Field K]
    (y x : UniversalType r Q Δ) : (integerDelta y x : K) = delta y x := by
  simp [integerDelta, delta]

/-- Each summand is a literal integer; no rational rounding is used. -/
noncomputable def entry (i : Fin Δ) (t : Fin Q) (A R : ℕ)
    (u y : UniversalType r Q Δ) : ℤ :=
  ∑ j ∈ Finset.range R,
    extendCoefficients (parityCoefficients (K := ℤ) A R) j *
      2 ^ (R - 1 - j) *
      ∑ S ∈ (activePositions t).powersetCard j,
        integerDifference i S.toList (integerDelta y)
          (swapPositions i (activePositions t) u)

noncomputable def joint (i : Fin Δ) (t : Fin Q) (g : Fin r) (A R : ℕ) :
    Matrix (Joint t g i) (Joint t g i) ℤ :=
  fun u y => entry i t A R u.val y.val

theorem entry_cast (K : Type*) [Field K] (h2 : (2 : K) ≠ 0)
    (i : Fin Δ) (t : Fin Q) (A R : ℕ)
    (u y : UniversalType r Q Δ) :
    (entry i t A R u y : K) =
      (denominator R : K) * matrixEntry i t R
        (extendCoefficients (parityCoefficients (K := K) A R)) u y := by
  classical
  simp only [entry, Int.cast_sum, Int.cast_mul, Int.cast_pow, Int.cast_ofNat,
    extend_parityCoefficients_intCast, matrixEntry, denominator]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  rw [pow_two_clear K h2 R j (Finset.mem_range.mp hj)]
  simp only [elementaryProjector, projectorProduct, Finset.length_toList,
    integerDifference_cast]
  simp_rw [integerDelta_cast]
  have hsum :
      (∑ S ∈ (activePositions t).powersetCard j,
        (2 : K)⁻¹ ^ S.card *
          differenceProduct i S.toList (delta y)
            (swapPositions i (activePositions t) u)) =
      (2 : K)⁻¹ ^ j *
        ∑ S ∈ (activePositions t).powersetCard j,
          differenceProduct i S.toList (delta y)
            (swapPositions i (activePositions t) u) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro S hS
    rw [(Finset.mem_powersetCard.mp hS).2]
  rw [hsum]
  ring

theorem joint_cast (K : Type*) [Field K] (h2 : (2 : K) ≠ 0)
    (i : Fin Δ) (t : Fin Q) (g : Fin r) (A R : ℕ)
    (u y : Joint t g i) :
    (joint i t g A R u y : K) =
      (denominator R : K) * jointMatrix i t g R
        (extendCoefficients (parityCoefficients (K := K) A R)) u y :=
  entry_cast K h2 i t A R u.val y.val

theorem joint_support (i : Fin Δ) (t : Fin Q) (g : Fin r) (A R : ℕ)
    (u y : Joint t g i) (hne : joint i t g A R u y ≠ 0) :
    (mismatches i u.val y.val).card ≤ R := by
  apply jointMatrix_support i t g R
    (extendCoefficients (parityCoefficients (K := ℚ) A R)) u y
  intro hz
  have hc := joint_cast ℚ (by norm_num) i t g A R u y
  rw [hz, mul_zero] at hc
  exact hne (by exact_mod_cast hc)

end SubexponentialSAT.SqrtLog.LayoutNumerator

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SubexpAnnihilation
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.FiniteField.fieldFintype _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.labelFintype _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.variableFintype _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree _root_.OAI.Algorithms.SubexponentialSAT.Subexp.MatrixEntryKernel.compatibleDecidable _root_.OAI.Algorithms.SubexponentialSAT.Subexp.MatrixEntryKernel.spectatorsAgreeDecidable _root_.OAI.Algorithms.SubexponentialSAT.Subexp.MatrixExtendedEntryProgram.instDecidableAnchorValid
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# Simultaneous row annihilation for the multicolor layout

Section 3.3 of `source/subexponential-sat.txt`.  At a fixed interpolation
position, the same row annihilates every color different from its slot color.
The old two-color modules are preserved and used only for generic finite-sum
lemmas.
-/

namespace SubexponentialSAT.SubexpAnnihilation

open scoped BigOperators
open Matrix

section TypeBlock

open MulticolorTypes

variable {K : Type*} [Ring K] {r Q Δ : ℕ}

/-- Finite-sum cancellation at any color other than the slot color. The
selected matrix row is required to be supported on `Y`; no assertion is
needed about unrelated rows. Diagonal corrections are included. -/
theorem typeBlock_annihilation
    (t : Fin Q) (i : Fin Δ) (u : UniversalType r Q Δ) (g : Fin r)
    (hg : g ≠ u.slot i t) (Y : Finset (UniversalType r Q Δ))
    (M : Matrix (Joint t g i) (Joint t g i) K)
    (c z : UniversalType r Q Δ → K)
    (hz : ∀ y, y.head t ≠ g → z y = 0)
    (hc : ∀ y, y ∉ Y → c y = 0)
    (hm : ∀ (hu : u.head t = g) (y : Joint t g i),
      M ⟨u, hu, hg.symm⟩ y ≠ 0 → (y : UniversalType r Q Δ) ∈ Y)
    (hcEval : ∀ y, y ∈ Y → y.head t = g →
      c y = -zeroExtendMatrix (joint t g i) M u y)
    (hfix : M *ᵥ (fun y : Joint t g i => z y) =
      fun y : Joint t g i => z y) :
    (Pi.single u 1 + c) ⬝ᵥ z = 0 := by
  classical
  by_cases hu : u.head t = g
  · apply Annihilation.annihilates_of_head_inside (side t g) (joint t g i)
      Y M ⟨u, hu, hg.symm⟩ c z hz hc ?_ ?_ hfix
    · intro y hy
      by_contra hne
      exact hy (hm hu y hne)
    · intro y hyS hyY
      rw [hcEval y hyY hyS,
        zeroExtendMatrix_of_row_mem (joint t g i) M u y ⟨hu, hg.symm⟩]
  · apply Annihilation.annihilates_of_head_outside (side t g) Y u c z hu hz hc
    intro y hyS hyY
    rw [hcEval y hyY hyS,
      zeroExtendMatrix_of_row_not_mem (joint t g i) M u y
        (fun h => hu h.1), neg_zero]

end TypeBlock

section Prescriptions

open MulticolorTypes

variable {F E : Type*} [Ring F] [Ring E] {r Q Δ : ℕ}

/-- Explicit values for the single row path. The column's own head color
chooses which matrix supplies the value, as required by equation (3.8). -/
def matrixPrescription (φ : F →+* E)
    (M : (t : Fin Q) → (g : Fin r) → (i : Fin Δ) →
      Matrix (Joint t g i) (Joint t g i) F)
    (u : UniversalType r Q Δ) (i : Fin Δ)
    (y : UniversalType r Q Δ) (t : Fin Q) : E :=
  -φ (zeroExtendMatrix (joint t (y.head t) i) (M t (y.head t) i) u y)

/-- At every active-side coordinate, the same prescription is the negative
row of that side's matrix; the zero extension handles both missing indices. -/
theorem matrixPrescription_on_side (φ : F →+* E)
    (M : (t : Fin Q) → (g : Fin r) → (i : Fin Δ) →
      Matrix (Joint t g i) (Joint t g i) F)
    (u : UniversalType r Q Δ) (i : Fin Δ)
    (y : UniversalType r Q Δ) (t : Fin Q) (g : Fin r)
    (hy : y.head t = g) :
    matrixPrescription φ M u i y t =
      -zeroExtendMatrix (joint t g i) ((M t g i).map φ) u y := by
  unfold matrixPrescription
  rw [hy, zeroExtendMatrix_map]

end Prescriptions

end SubexponentialSAT.SubexpAnnihilation

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LayoutScaledMatrices
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.labelFintype _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.variableFintype _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# Cleared integer matrices and exact ring-valued source rows

The rational spectral argument will supply integer numerators `N` and a
power-of-two denominator `d`. Over the target coefficient ring only the
unit representing `d` is inverted. Exact integer equations `d I - N`
therefore imply the fixed-vector equations needed by the original
multicolor row construction, without a map from `ℚ` to the target ring.
-/

namespace SubexponentialSAT.SqrtLog.LayoutScaledMatrices

open scoped BigOperators
open Matrix

section SourceRows

open SubexponentialSAT.MulticolorTypes SubexponentialSAT.SubexpRowInterpolation

variable {O : Type*} [CommRing O] {r Q Δ : ℕ}
variable {node : Fin Q → O}

abbrev Numerators (r Q Δ : ℕ) :=
  (t : Fin Q) → (g : Fin r) → (i : Fin Δ) →
    Matrix (Joint t g i) (Joint t g i) ℤ

end SourceRows

end SubexponentialSAT.SqrtLog.LayoutScaledMatrices

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_Subexp_TensorSpectrum
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.FiniteField.fieldFintype _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.labelFintype _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.variableFintype _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# Tensor eigenbases for the multicolor register swap

The finite change of basis is constructed from invertible local kernels. This
module then specializes it to the actual register swap and transports it to the
joint fiber of universal types; multiplicities count those actual basis labels.
-/

namespace SubexponentialSAT.Subexp.TensorSpectrum

open scoped BigOperators

section ProductKernel

variable (K : Type*) [Field K]
variable {β ι : Type*} [Fintype β] [DecidableEq β] [Fintype ι] [DecidableEq ι]

/-- Explicit mutually inverse finite tensor transforms. -/
noncomputable def productCoordinateEquiv (A B : β → β → K)
    (hAB : ∀ x y, (∑ z, A x z * B z y) = if x = y then 1 else 0)
    (hBA : ∀ x y, (∑ z, B x z * A z y) = if x = y then 1 else 0) :
    ((ι → β) → K) ≃ₗ[K] ((ι → β) → K) where
  toFun := SubexponentialSAT.LocalSpectrum.kernelMap K (productKernel K B)
  invFun := SubexponentialSAT.LocalSpectrum.kernelMap K (productKernel K A)
  left_inv := SubexponentialSAT.LocalSpectrum.kernelMap_inverse K _ _
    (productKernel_inverse K _ _ hAB)
  right_inv := SubexponentialSAT.LocalSpectrum.kernelMap_inverse K _ _
    (productKernel_inverse K _ _ hBA)
  map_add' := (SubexponentialSAT.LocalSpectrum.kernelMap K _).map_add
  map_smul' := (SubexponentialSAT.LocalSpectrum.kernelMap K _).map_smul

end ProductKernel

section Spectators

variable (K : Type*) [Field K]
variable {β ι U : Type*} [Fintype β] [DecidableEq β] [Fintype ι] [DecidableEq ι]

/-- Apply the tensor change of basis independently on each spectator fiber. -/
noncomputable def spectatorCoordinateEquiv (A B : β → β → K)
    (hAB : ∀ x y, (∑ z, A x z * B z y) = if x = y then 1 else 0)
    (hBA : ∀ x y, (∑ z, B x z * A z y) = if x = y then 1 else 0) :
    (((ι → β) × U) → K) ≃ₗ[K] ((U × (ι → β)) → K) where
  toFun f p := productCoordinateEquiv K A B hAB hBA (fun x => f (x, p.1)) p.2
  invFun c p := (productCoordinateEquiv K A B hAB hBA).symm (fun a => c (p.2, a)) p.1
  left_inv f := by
    funext ⟨x, u⟩
    exact congrFun ((productCoordinateEquiv K A B hAB hBA).symm_apply_apply
      (fun y => f (y, u))) x
  right_inv c := by
    funext ⟨u, a⟩
    exact congrFun ((productCoordinateEquiv K A B hAB hBA).apply_symm_apply
      (fun b => c (u, b))) a
  map_add' f g := by
    funext ⟨u, a⟩
    exact congrFun ((productCoordinateEquiv K A B hAB hBA).map_add
      (fun x => f (x, u)) (fun x => g (x, u))) a
  map_smul' c f := by
    funext ⟨u, a⟩
    exact congrFun ((productCoordinateEquiv K A B hAB hBA).map_smul c
      (fun x => f (x, u))) a

variable [Fintype U] [DecidableEq U]

/-- Include a separate coordinate vector for every assignment of the untouched registers. -/
noncomputable def spectatorBasis (A B : β → β → K)
    (hAB : ∀ x y, (∑ z, A x z * B z y) = if x = y then 1 else 0)
    (hBA : ∀ x y, (∑ z, B x z * A z y) = if x = y then 1 else 0) :
    Module.Basis (U × (ι → β)) K ((((ι → β) × U) → K)) :=
  Module.Basis.ofEquivFun (spectatorCoordinateEquiv K A B hAB hBA)

end Spectators

section JointBasis

open SubexponentialSAT.MulticolorTypes

variable {r Q Δ : ℕ}

/-- Labels of the genuine joint eigenbasis. The spectator includes the
non-head color of the pinned slot and all unused slot words. -/
abbrev JointBasisIndex (t : Fin Q) (g : Fin r) (i : Fin Δ) :=
  Spectator (Q := Q) g i × (OtherPosition t → Fin r × Fin r)

noncomputable def jointEigenbasis (K : Type*) [Field K]
    (h2 : (2 : K) ≠ 0) (t : Fin Q) (g : Fin r) (i : Fin Δ) :
    Module.Basis (JointBasisIndex t g i) K (Joint t g i → K) :=
  (@spectatorBasis K inferInstance (Fin r × Fin r) (OtherPosition t)
    (Spectator (Q := Q) g i) inferInstance inferInstance inferInstance inferInstance
    inferInstance
    (LocalSpectrum.localKernel K (α := Fin r)) (LocalSpectrum.localDualKernel K (α := Fin r))
    (pairKernel_inverse K h2 inferInstance) (pairDualKernel_inverse K h2 inferInstance)).map
      (LinearEquiv.funCongrLeft K K (jointEquivPairs t g i))

@[simp] theorem jointEigenbasis_apply (K : Type*) [Field K]
    (h2 : (2 : K) ≠ 0) (t : Fin Q) (g : Fin r) (i : Fin Δ)
    (a : JointBasisIndex t g i) (u : Joint t g i) :
    jointEigenbasis K h2 t g i a u =
      @spectatorBasis K inferInstance (Fin r × Fin r) (OtherPosition t)
        (Spectator (Q := Q) g i) inferInstance inferInstance inferInstance inferInstance
        inferInstance
        (LocalSpectrum.localKernel K (α := Fin r)) (LocalSpectrum.localDualKernel K (α := Fin r))
        (pairKernel_inverse K h2 inferInstance) (pairDualKernel_inverse K h2 inferInstance)
        a (jointEquivPairs t g i u) := rfl

end JointBasis

end SubexponentialSAT.Subexp.TensorSpectrum

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LayoutNumeratorBridge
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.FiniteField.fieldFintype _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.labelFintype _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.variableFintype _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree _root_.OAI.Algorithms.SubexponentialSAT.Subexp.MatrixEntryKernel.compatibleDecidable _root_.OAI.Algorithms.SubexponentialSAT.Subexp.MatrixEntryKernel.spectatorsAgreeDecidable _root_.OAI.Algorithms.SubexponentialSAT.Subexp.MatrixExtendedEntryProgram.instDecidableAnchorValid
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# From the rational spectral matrix to the integer constraint family

The integer constraints are literally `d I - N`. Their rational range has
exactly the dimension of `I - M`, and the same numerators supply the ring
row construction from `LayoutScaledMatrices`.
-/

namespace SubexponentialSAT.SqrtLog.LayoutNumerator

open scoped BigOperators
open Matrix Module
open SubexponentialSAT.MulticolorTypes SubexponentialSAT.BinomialInterpolation SubexponentialSAT.Subexp.MatrixSupport
open LayoutScaledMatrices

variable {r Q Δ : ℕ}

noncomputable def family (r Q Δ A R : ℕ) : Numerators r Q Δ :=
  fun t g i => joint i t g A R

theorem family_support (A R : ℕ) (t : Fin Q) (g : Fin r) (i : Fin Δ)
    (a b : Joint t g i) (hne : family r Q Δ A R t g i a b ≠ 0) :
    (SubexponentialSAT.SubexpRowInterpolation.mismatchPositions
      (fun y : UniversalType r Q Δ => y.head) (a.val.slot i) b.val).card ≤ R :=
  joint_support i t g A R a b hne

/-- The rational matrix obtained by casting the literal integer constraints. -/
noncomputable def rationalDefect (i : Fin Δ) (t : Fin Q) (g : Fin r) (A R : ℕ) :
    Matrix (Joint t g i) (Joint t g i) ℚ :=
  fun a b => (clearedDefect (denominator R) (joint i t g A R) a b : ℚ)

end SubexponentialSAT.SqrtLog.LayoutNumerator

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LayoutOffsetProgram
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! A fixed native producer of the signed-bucket offset 2*B*(8*Q)^(2*R).
All arithmetic acts on runtime binary words. This offset is unrelated to
the unary scalar-row width 1+2*A*R+Q. -/
namespace SubexponentialSAT.SqrtLog.LayoutOffsetProgram
open SubexponentialSAT BitProgram StructuredCalls BinaryArithmetic
open SubexpBlockParameterProgram

@[simp] theorem two_value : BinaryArithmetic.toNat two=2 := by decide
@[simp] theorem eight_value : BinaryArithmetic.toNat eight=8 := by decide
@[simp] theorem two_length : two.length=2 := rfl
@[simp] theorem eight_length : eight.length=4 := rfl

def width (B Q R : List Bool) : ℕ := (2*BinaryArithmetic.toNat R+1)*(sourceWidth B Q R+1)

def outputLength (B Q R : List Bool) : ℕ := B.length+2*BinaryArithmetic.toNat R*(Q.length+5)+5

def coreBudget (B Q R : List Bool) : ℕ := 4000*(width B Q R)^2

def budget (B Q R : List Bool) : ℕ := 5000*(width B Q R)^2

end SubexponentialSAT.SqrtLog.LayoutOffsetProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_Subexp_AssignmentAlphabetSemantics
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! The actual tuple-generator order is retained in the initializer alphabet. -/

namespace SubexponentialSAT.Subexp.AssignmentAlphabetSemantics

open OneHotAlphabetProgram MulticolorTypes

theorem encodeTuple_eq {r Q : ℕ} (hr : 0 < r) (w : Word r Q) :
    SubexpTupleRefinement.encodeTuple (colorCode hr) w = ReadPlan.encodeWord w := by
  rw [SubexpTupleRefinement.encodeTuple, StackEncoding.encodeDataStack_eq_flatMap]
  rw [List.flatMap_def, List.map_ofFn]
  rfl

end SubexponentialSAT.Subexp.AssignmentAlphabetSemantics

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_Subexp_MatrixScanSemantics
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree _root_.OAI.Algorithms.SubexponentialSAT.Subexp.MatrixEntryKernel.compatibleDecidable _root_.OAI.Algorithms.SubexponentialSAT.Subexp.MatrixEntryKernel.spectatorsAgreeDecidable _root_.OAI.Algorithms.SubexponentialSAT.Subexp.MatrixExtendedEntryProgram.instDecidableAnchorValid
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Arithmetic meaning of the two physical unary counters and the
compatibility register, including the one-hot color encoding boundary. -/

namespace SubexponentialSAT.Subexp.MatrixScanProgram

open BitProgram StructuredCalls StackRoutines

def typedRow {r Q Δ : ℕ} (i : Fin Δ)
    (u y : MulticolorTypes.UniversalType r Q Δ) (l : Fin Q) : ColorRow :=
  ![encodeColor (u.head l), encodeColor (u.slot i l),
    encodeColor (y.head l), encodeColor (y.slot i l)]

@[simp] theorem typedRow_length {r Q Δ : ℕ} (i : Fin Δ)
    (u y : MulticolorTypes.UniversalType r Q Δ) (l : Fin Q) (j : Fin 4) :
    (typedRow i u y l j).length = r := by
  fin_cases j <;> simp [typedRow]

end SubexponentialSAT.Subexp.MatrixScanProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_Subexp_MatrixEntryEvaluation
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree _root_.OAI.Algorithms.SubexponentialSAT.Subexp.MatrixExtendedEntryProgram.instDecidableAnchorValid
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Connect the concrete scan counters and adjacent-add value to the actual
joint matrix. These are refinement lemmas for the physical component programs,
not alternative definitions of their runtime instructions. -/

namespace SubexponentialSAT.Subexp.MatrixEntryEvaluation

open MulticolorTypes MatrixScanProgram
open scoped BigOperators

variable {r Q Δ : ℕ}

def rows (i : Fin Δ) (u y : UniversalType r Q Δ) : List ColorRow :=
  List.ofFn (typedRow i u y)

@[simp] theorem rows_length (i : Fin Δ) (u y : UniversalType r Q Δ) :
    (rows i u y).length = Q := by simp [rows]

end SubexponentialSAT.Subexp.MatrixEntryEvaluation

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_Subexp_MatrixEntryExtract
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! The actual extractor and color scanner on canonical universal-type bytes. -/

namespace SubexponentialSAT.Subexp.MatrixEntryProgram

open BitProgram StructuredCalls StackRoutines MulticolorTypes

variable {r Q Δ : ℕ}

def scanStageCost (r Q Δ i : ℕ) : ℕ :=
  (7 * Q + 5) +
    (36 * CollisionProgram.typeWidth r Q Δ +
      4 * (i + 1) * (14 * (Q * r) + 17) + 203 * (Q * r) + 265) +
    (Q * (208 * r + 149) + 3)

end SubexponentialSAT.Subexp.MatrixEntryProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_Subexp_MatrixExtendedEntryProgram
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Fixed control for the zero-extended joint entry on arbitrary universal
types. The unary position cursor is preserved on37. -/

namespace SubexponentialSAT.Subexp.MatrixExtendedEntryProgram

open BitProgram StructuredCalls StackRoutines MulticolorTypes

variable {r Q Δ : ℕ}

open BitProgram StructuredCalls StackRoutines

open BitProgram StructuredCalls StackRoutines MulticolorTypes


def guardStageCost (r Q Δ i t : ℕ) : ℕ :=
  (36 * CollisionProgram.typeWidth r Q Δ +
    4 * (i + 1) * (14 * (Q * r) + 17) + 203 * (Q * r) + 265) +
  (4 * (9 * (Q * r) + t * (14 * r + 17) + 30 * r + 43) + 1) +
  (81 * r + 107) + (8 * (Q * r) + 8 * r + 24)

end SubexponentialSAT.Subexp.MatrixExtendedEntryProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LayoutProgramScalar
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Concrete arithmetic adapters for the cached layout scalar loop.
The working signed pair occupies 0/1, the next operand 2/3, the record queue
15, and the saved sum 16/17. All arithmetic is an actual compiled bit program.
-/
namespace SubexponentialSAT.SqrtLog.LayoutProgramScalar

open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls
open SubexponentialSAT.SqrtLog.RowSelectionProgram

@[simp] theorem one_length : pairLength one = 1 := rfl

end SubexponentialSAT.SqrtLog.LayoutProgramScalar

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


/-! Closed correction-table construction from type metadata and integer/ring
caches. No correction-scalar table is supplied to the program or theorem. -/


/-! Uniform polynomial accounting and per-index observation of generated
correction tables. All parameters describe actual bytes and runtime counts. -/
namespace SubexponentialSAT.SqrtLog.LayoutSourceValuesProgram.Native

open SubexponentialSAT BitProgram StructuredCalls SubexpConvolutionControl
open MulticolorTypes IntegerRingLiftProgram
open _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RowSelectionProgram (WordPair pairValue pairLength)
open scoped BigOperators

/-- guardStageCost and scanStageCost are explicit fixed polynomials too. -/
def numeratorAllowance (r Q A R W P : ℕ) : ℕ :=
  Subexp.MatrixExtendedEntryProgram.guardStageCost r Q 1 0 Q +
    Subexp.MatrixEntryProgram.scanStageCost r Q 1 0 + 7*Q + scalarAllowance A R Q W P + 20

end SubexponentialSAT.SqrtLog.LayoutSourceValuesProgram.Native


end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LayoutProgramEntryBankCost
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Uniform numerical bounds for the concrete entry program. The universal
type words affect the result, but no type-dependent search is charged here. -/
namespace SubexponentialSAT.SqrtLog.LayoutProgram.EntryBank

open SubexponentialSAT.BitProgram SubexponentialSAT.Subexp SubexponentialSAT.MulticolorTypes RowSelectionProgram

variable {r Q : ℕ}

def integerBudget (r Q A R W P D : ℕ) : ℕ :=
  MatrixExtendedEntryProgram.guardStageCost r Q 1 0 Q+
    LayoutSourceValuesProgram.Native.numeratorAllowance r Q A R W P+
    27*CollisionProgram.typeWidth r Q 1+
    9*(R*LayoutProgramScalar.termGrowth (2*W+P))+
    100*(R*LayoutProgramScalar.termGrowth (2*W+P)+D+1)^2+60

end SubexponentialSAT.SqrtLog.LayoutProgram.EntryBank

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LayoutProgramLabels
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree _root_.OAI.Algorithms.SubexponentialSAT.Subexp.MatrixEntryKernel.compatibleDecidable _root_.OAI.Algorithms.SubexponentialSAT.Subexp.MatrixEntryKernel.spectatorsAgreeDecidable _root_.OAI.Algorithms.SubexponentialSAT.Subexp.MatrixExtendedEntryProgram.instDecidableAnchorValid
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Materialize incidence labels from actual two-address read plans. The
physical gather reads the head and factor words in that order. Incidence
numbers are the read-plan list positions, including repeated plans. -/
namespace SubexponentialSAT.SqrtLog.LayoutProgram

open SubexponentialSAT.MulticolorTypes SubexponentialSAT.Subexp
open SubexponentialSAT.BitProgram

variable {D r Q : ℕ}

def labelPlans (words : List (Word r Q))
    (address : Fin D → Fin words.length × Fin words.length) : List (List ℕ) :=
  (List.finRange D).map (fun i => [(address i).1.val, (address i).2.val])

def addressLabel (words : List (Word r Q))
    (address : Fin D → Fin words.length × Fin words.length) (i : Fin D) :
    UniversalType r Q 1 :=
  ⟨words.get (address i).1, fun _ => words.get (address i).2⟩

end SubexponentialSAT.SqrtLog.LayoutProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_PackingIncidenceInputSemantics
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Typed original-variable/factor semantics of the native address list. -/
namespace SubexponentialSAT.SqrtLog.PackingIncidenceInput.Semantics
open SubexponentialSAT.Subexp

theorem factor_lt_next (scopes : List (List ℕ)) (v z e : ℕ)
    (hz : scopes.length ≤ z) (he : e ∈ Step.factors scopes v z) :
    e < Step.next scopes v z := by
  by_cases h : Scan.indices scopes v = []
  · have heq : e = z := by simpa [Step.factors,h] using he
    subst e
    simp [Step.next,h]
  · have he' : e ∈ Scan.indices scopes v := by simpa [Step.factors,h] using he
    have hh := IncidencePlanSpec.incidentIndex_lt scopes v e he'
    simpa [Step.next,h] using hh.trans_le hz

theorem entry_bounds (scopes : List (List ℕ)) (mask : List Bool) :
    ∀ n v z, v+mask.length ≤ n → scopes.length ≤ z →
      ∀ p ∈ entries scopes v z mask, p.1 < n ∧ p.2 < Loop.finalCounter scopes v z mask := by
  induction mask with
  | nil => simp [entries]
  | cons high mask ih =>
      intro n v z hn hz p hp
      have hnext := next_le scopes v z
      cases high
      · simp only [entries,Bool.false_eq_true,ite_false,List.mem_append] at hp
        rcases hp with hp|hp
        · exact ih n (v+1) (Step.next scopes v z) (by simp only [List.length_cons] at hn; omega)
            (hz.trans hnext) p hp
        · obtain ⟨e,he,rfl⟩ := List.mem_map.mp hp
          exact ⟨by simp only [List.length_cons] at hn; omega,
            (factor_lt_next scopes v z e hz he).trans_le (counter_mono scopes mask (v+1) _)⟩
      · simp only [entries,ite_true, if_true,List.append_nil] at hp
        exact ih n (v+1) z (by simp only [List.length_cons] at hn; omega) hz p hp

def owner (scopes : List (List ℕ)) (n : ℕ) (mask : List Bool) (hm : mask.length ≤ n)
    (i : Incidences scopes mask) : Fin n :=
  ⟨((nativeEntries scopes mask).get i).1,
    (entry_bounds scopes mask n 0 scopes.length (by omega) le_rfl _ (List.get_mem _ i)).1⟩
def factor (scopes : List (List ℕ)) (n : ℕ) (mask : List Bool) (hm : mask.length ≤ n)
    (i : Incidences scopes mask) : Fin (factorCount scopes mask) :=
  ⟨((nativeEntries scopes mask).get i).2,
    (entry_bounds scopes mask n 0 scopes.length (by omega) le_rfl _ (List.get_mem _ i)).2⟩
end SubexponentialSAT.SqrtLog.PackingIncidenceInput.Semantics

end OAI.Algorithms
end


