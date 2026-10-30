-- Prove2me | Definitions.Def_OAIQ081S123
-- name    : OAIQ081S123
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-29T22:36:33.301991+00:00
-- url     : https://prove2.me/theorems/69eeec6e-e183-4960-85ae-efe51d53f407
-- title:
--   Definitions bundle OAIQ081S123 of the split of OpenAI, The Exponential Time Hypothesis is False
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.exact_count_and_sat`, carved from OpenAI's openai/math development (OpenAI, *The Exponential Time Hypothesis is False*, OpenAI Math Release, October 25, 2026, result family 378, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 91 declarations of OpenAI's Lean: 83 definitions and 8 theorems. The definitions and types are `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutMatrixProgram.clearRowIndex`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutMatrixProgram.copyIDs`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutMatrixProgram.copyInputIDs`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutMatrixProgram.copyRowIndex`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutMatrixProgram.counter`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutMatrixProgram.emitPair`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutMatrixProgram.entryCall`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutMatrixProgram.finalState`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutMatrixProgram.initialState`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutMatrixProgram.initializeIDs`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutMatrixProgram.reverseIDs`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutMatrixProgram.state`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgram.Count.body`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgram.Count.command`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgram.Count.ports`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgram.Count.program`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgram.Count.state`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgram.Count.subtractCommand`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgram.EntryBank.Code`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgram.EntryBank.cleanup`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgram.EntryBank.exportPair`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgram.EntryBank.lookup`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgram.EntryBank.prepare`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgram.IntegerCache.copies`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgram.IntegerCache.copy`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgram.IntegerCache.makePower`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgram.IntegerCache.popCounter`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgram.IntegerCache.powerCall`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgram.IntegerFinish.command`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgram.LookupPair.Data`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgram.LookupPair.colCall`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgram.LookupPair.command`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgram.LookupPair.program`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgram.LookupPair.rowCall`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgram.LookupPair.state`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgram.NativeFrontend.Params.input`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgram.NativeFrontend.Params.labelsBound`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgram.NativeFrontend.Params.planStream`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgram.NativeFrontend.Params.typeStream`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgram.NativeFrontend.Params.typesBound` and 43 more.
--
--   **Sources.** They come from these modules of lean/OAI/Algorithms, in whole or in part: `SubexponentialSAT_SqrtLog_LayoutMatrixProgram`, `SubexponentialSAT_SqrtLog_LayoutMatrixProgramInitialize`, `SubexponentialSAT_SqrtLog_LayoutMatrixProgramLoop`, `SubexponentialSAT_SqrtLog_LayoutMatrixProgramRow`, `SubexponentialSAT_SqrtLog_LayoutMatrixProgramRowStep`, `SubexponentialSAT_SqrtLog_LayoutMatrixProgramSource`, `SubexponentialSAT_SqrtLog_LayoutProgramCount`, `SubexponentialSAT_SqrtLog_LayoutProgramEntryBank`, `SubexponentialSAT_SqrtLog_LayoutProgramFrontend`, `SubexponentialSAT_SqrtLog_LayoutProgramIntegerCache`, `SubexponentialSAT_SqrtLog_LayoutProgramIntegerFinish`, `SubexponentialSAT_SqrtLog_LayoutProgramLookupPair`, `SubexponentialSAT_SqrtLog_LayoutProgramNumerator`, `SubexponentialSAT_SqrtLog_LayoutProgramPackLabels`, `SubexponentialSAT_SqrtLog_LayoutProgramScalarCacheCell`, `SubexponentialSAT_SqrtLog_LayoutProgramScalarFromCountsDefinitions`, `SubexponentialSAT_SqrtLog_LayoutProgramScalarFromCountsPrimitives`, `SubexponentialSAT_SqrtLog_LayoutProgramUniversalEntry`, `SubexponentialSAT_SqrtLog_LayoutSourceRowsProgram`, `SubexponentialSAT_SqrtLog_LeafRingSetupProgramNative`, `SubexponentialSAT_Subexp_AssignmentSeedRange`, `SubexponentialSAT_Subexp_PackingBucketStage`, `SubexponentialSAT_Subexp_PackingExtractionStage`, `SubexponentialSAT_Subexp_PackingFrontendData`, `SubexponentialSAT_Subexp_PackingInverseStage`, `SubexponentialSAT_Subexp_PackingProgramInput`, `SubexponentialSAT_Subexp_UniversalTypeProgram`.
--
--   **Imports.** It imports the published bundle `Def_SubexponentialSAT`; the bundles `OAIQ081S093`, `OAIQ081S100`, `OAIQ081S102` and `OAIQ081S106` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ081S143`, `OAIQ081S144`, `OAIQ081S145`, `OAIQ081S146` and `OAIQ081S147`; the statements `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgramScalar.FromCounts.numerator_eval` and `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgram.EntryBankFrame.lookup_lifted`; the proofs of `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgramScalar.FromCounts.numerator_eval` and `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgram.EntryBankFrame.lookup_lifted`.
-- source:
--   OpenAI, The Exponential Time Hypothesis is False, OpenAI Math Release, October 25, 2026, https://github.com/openai/math (result family 378; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/The-Exponential-Time-Hypothesis-is-False-October-25-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Algorithms at commit 7ef5c0c

import Mathlib
import Definitions.Def_SubexponentialSAT
import Definitions.Def_OAIQ081S093
import Definitions.Def_OAIQ081S100
import Definitions.Def_OAIQ081S102
import Definitions.Def_OAIQ081S106

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LayoutMatrixProgramSource
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Relocatable finite-bank contract for integer incidence entries, and the
fixed physical storage layout used by the direct all-row matrix builder. -/
namespace SubexponentialSAT.SqrtLog.LayoutMatrixProgram
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls

def state (base : Fin 288 → List Bool) (regs : Fin 16 → Bool) (q : Store) : Data 288 :=
  ⟨regs,fun i => if i=277 then q.rowIndex else if i=278 then q.columnIndex else
    if i=279 then q.positive else if i=280 then q.negative else if i=281 then q.remaining else
    if i=282 then q.reversedIDs else if i=283 then q.todo else if i=284 then q.row else
    if i=24 then q.matrix else base i⟩

def entryCall (entry : Code 256) : Code 288 :=
  .call (ProgramLinking.liftProgram (compiled entry 252 254) id bankPort)

end SubexponentialSAT.SqrtLog.LayoutMatrixProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LayoutMatrixProgramRowStep
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! One actual matrix coefficient call followed by physical signed framing. -/
namespace SubexponentialSAT.SqrtLog.LayoutMatrixProgram
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls

/-- Prepend the two little-endian component frames, preserving coefficient order. -/
def emitPair : Code 288 := .seq (frame 280 284 286 (by decide)) (frame 279 284 286 (by decide))

end SubexponentialSAT.SqrtLog.LayoutMatrixProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LayoutMatrixProgramInitialize
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Paid preparation of reversed original head-ID records. -/
namespace SubexponentialSAT.SqrtLog.LayoutMatrixProgram
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls

def reverseIDs : Code 288 := .call
  (ProgramLinking.liftProgram SubexpNormalizeProgram.reverseRecordsProgram reverseRegs reversePorts)

def copyInputIDs : Code 288 := .call (StackRoutines.copyProgram 17 283 285 0 1)
def initializeIDs : Code 288 := .seq copyInputIDs
  (.seq (Subexp.TupleProgram.pushConst 282 0 false) reverseIDs)

end SubexponentialSAT.SqrtLog.LayoutMatrixProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LayoutMatrixProgramRow
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Physical row preparation and output framing for all-D construction. -/
namespace SubexponentialSAT.SqrtLog.LayoutMatrixProgram
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls

def copyRowIndex : Code 288 := .call (StackRoutines.copyProgram 281 277 285 0 1)
def copyIDs : Code 288 := .call (StackRoutines.copyProgram 282 283 285 0 1)
def clearRowIndex : Code 288 := .call (StackRoutines.clearProgram 277 0 1)

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

def counter : UnaryForPrograms.Ports 16 288 := ⟨281,0,1⟩

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

def initialState (base : Fin 288 → List Bool) (regs : Fin 16 → Bool) (D : ℕ) : Data 288 :=
  state base regs {remaining:=List.replicate D true}

def finalState (base : Fin 288 → List Bool) (regs : Fin 16 → Bool)
    (rows : List (List Pair)) : Data 288 := state base regs {matrix:=rowsWords rows}

end SubexponentialSAT.SqrtLog.LayoutMatrixProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LayoutProgramCount
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! The scalar loop length R−d is computed by deleting actual unary tokens.
The scan's distinguished unchanged anchor is removed first. Neither natural
subtraction nor a loop-count constructor is a machine primitive. -/
namespace SubexponentialSAT.SqrtLog.LayoutProgram.Count

open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls

abbrev ports : SubexponentialSAT.UnaryForPrograms.Ports 2 2 := ⟨1,0,1⟩
abbrev body : Cmd 2 2 := .base (.atom (.pop 0 0 1))
abbrev subtractCommand : Cmd 2 2 := SubexponentialSAT.UnaryForPrograms.forCmd ports body
abbrev command : Cmd 2 2 := .seq (SubexponentialSAT.UnaryForPrograms.popCmd ports) subtractCommand
abbrev program := compiled command 0 0

abbrev state (regs : Fin 2 → Bool) (left count : List Bool) : Data := ⟨regs,![left,count]⟩

end SubexponentialSAT.SqrtLog.LayoutProgram.Count

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
namespace SubexponentialSAT.SqrtLog.LayoutProgramScalar

open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls
open SubexponentialSAT.BinaryArithmetic
open SubexponentialSAT.SqrtLog.RowSelectionProgram

abbrev cacheCellLocal : Cmd 8 3 :=
  .seq (.base (.atom (.set 0 false)))
    (.seq (.base (.atom (.push 0 0))) (.call BinaryPrograms.Add.littleEndianProgram))

abbrev cacheCell : Cmd 8 18 :=
  .call (ProgramLinking.liftProgram (compiled cacheCellLocal 0 0) id cacheCellPorts)

end SubexponentialSAT.SqrtLog.LayoutProgramScalar

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

def initialPorts : UnaryForPrograms.Ports 8 18 := ⟨17,7,6⟩

abbrev initialBody : Cmd 8 18 := ArithmeticExpressionSupport.pushWord 15 initialRecord

abbrev initialCommand : Cmd 8 18 :=
  .seq (ArithmeticExpressionSupport.pushWord 15 [false])
    (UnaryForPrograms.forCmd initialPorts initialBody)

end SubexponentialSAT.SqrtLog.LayoutProgramScalar

/-! One fixed program builds the complete unsigned H cache from the unary
runtime parameters A and R. No coefficient or initial cache is free input. -/
namespace SubexponentialSAT.SqrtLog.LayoutProgramScalar

open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls
open SubexponentialSAT.SqrtLog.RowSelectionProgram

abbrev initialBuild : Cmd 8 19 :=
  .call (ProgramLinking.liftProgram (compiled initialCommand 17 15) id initialBuildPorts)

end SubexponentialSAT.SqrtLog.LayoutProgramScalar

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LayoutProgramScalarFromCountsPrimitives
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.LayoutProgramScalar.FromCounts

attribute [local simp] Fin.coe_ofNat_eq_mod

open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls RowSelectionProgram

abbrev copy (src dst : Fin 40) : Cmd 9 40 :=
  .call (StackRoutines.copyProgram src dst 14 0 1)
abbrev copies : Cmd 9 40 := .seq (copy 5 9) (.seq (copy 5 10) (copy 6 11))
abbrev count : Cmd 9 40 := .call (ProgramLinking.liftProgram LayoutProgram.Count.program regs2 countPorts)
abbrev clear (src : Fin 40) : Cmd 9 40 := .call (StackRoutines.clearProgram src 0 1)
abbrev cleanup : Cmd 9 40 := .seq (clear 12) (clear 13)

end SubexponentialSAT.SqrtLog.LayoutProgramScalar.FromCounts

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LayoutProgramScalarFromCountsDefinitions
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.LayoutProgramScalar.FromCounts

attribute [local simp] Fin.coe_ofNat_eq_mod

open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls RowSelectionProgram
open LayoutTriplePreparationProgram

abbrev numerator : Cmd 9 40 := .call (ProgramLinking.liftProgram numeratorProgram id numeratorPorts)


end SubexponentialSAT.SqrtLog.LayoutProgramScalar.FromCounts

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LayoutProgramUniversalEntry
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Fixed control for one universal integer constraint entry. The concrete
local stages are lifted into one bank; subsequent lemmas compose their traces.
No ring inversion or field-valued matrix is used in this integer procedure. -/
namespace SubexponentialSAT.SqrtLog.LayoutProgram.UniversalEntry

open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.Subexp
open SubexponentialSAT.MulticolorTypes

abbrev guard : Cmd 10 64 := liftCommand MatrixExtendedEntryProgram.guardStage 23 0 id guardPorts
abbrev defect : Cmd 10 64 := liftCommand Defect.command 0 3 smallRegs defectPorts
abbrev clear (src : Fin 64) : Cmd 10 64 := .call (StackRoutines.clearProgram src 0 1)
abbrev clearNumerator : Cmd 10 64 := .seq (clear 50) (clear 51)
abbrev clearCounts : Cmd 10 64 := .seq (clear 2) (clear 3)

end SubexponentialSAT.SqrtLog.LayoutProgram.UniversalEntry

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LayoutProgramIntegerFinish
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Final physical defect conversion, preserving all caller inputs and
removing the temporary numerator pair. -/
namespace SubexponentialSAT.SqrtLog.LayoutProgram.IntegerFinish

open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.Subexp RowSelectionProgram
open UniversalEntry

attribute [local simp] Fin.coe_ofNat_eq_mod

abbrev command : Cmd 10 64 := .seq defect clearNumerator

end SubexponentialSAT.SqrtLog.LayoutProgram.IntegerFinish

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LayoutProgramNumerator
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Concrete universal numerator evaluation from encoded type words and the
paid unsigned coefficient cache. -/
namespace SubexponentialSAT.SqrtLog.LayoutProgram.Numerator

open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.Subexp SubexponentialSAT.MulticolorTypes
open UniversalEntry RowSelectionProgram
attribute [local simp] Fin.coe_ofNat_eq_mod

variable {r Q : ℕ}

def baseStacks (c : Saved) (t : Fin Q) (u y : UniversalType r Q 1) : Fin 64 → List Bool :=
  fun j => if hj : j.val < 42 then
    (Guard.guardInput (0 : Fin 1) t u y [] [] [] [] (fun _ => false)).stacks ⟨j.val,hj⟩
  else if j=42 then c.hp else if j=43 then c.hn else if j=44 then c.width
  else if j=45 then c.power.1 else if j=46 then c.power.2 else if j=47 then c.r
  else if j=48 then c.a else []

end SubexponentialSAT.SqrtLog.LayoutProgram.Numerator

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_Subexp_UniversalTypeProgram
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Actual universal-type generation from the saved word alphabet and unary
slot count. The extra head coordinate is installed by one real push. -/

namespace SubexponentialSAT.Subexp.UniversalTypeProgram

open BitProgram StructuredCalls TupleProgram

def inputState (alphabet : Records) (depth : List Bool) (regs : Fin 10 → Bool) : State 10 9 :=
  ⟨regs, ![[], ProgramEncoding.encodeRecords alphabet, [], [], [], [], [], [], depth]⟩

def outputState (alphabet rows : Records) (regs : Fin 10 → Bool) : State 10 9 :=
  ⟨regs, ![ProgramEncoding.encodeRecords rows, ProgramEncoding.encodeRecords alphabet,
    [], [], [], [false], [], [], []]⟩

abbrev command : Cmd 10 9 :=
  .seq (pushConst 8 6 true) (.call generateProgram)

def program := compiled command 1 0

theorem ready_eq (alphabet rows : Records) (a : State 10 9)
    (ha : Ready alphabet rows [] false a) : a = outputState alphabet rows a.regs := by
  apply congrArg₂ StructuredProgram.State.mk rfl
  funext i
  rcases ha with ⟨⟨h1,h3,h4,h6,h7,h8,h9⟩,h0,h2,h5⟩
  fin_cases i <;> simp [h0,h1,h2,h3,h4,h5,h6,h7,h8]

theorem program_runsIn (alphabet : Records) (depth : List Bool) (regs : Fin 10 → Bool) :
    ∃ nextRegs, RunsIn program (budget alphabet depth.length)
      ((inputState alphabet depth regs).withPC (some program.entry))
      ((outputState alphabet (powerRows alphabet (depth.length + 1) [[]]) nextRegs).withPC none) := by
  let a := inputState alphabet depth regs
  let b := pushedState 8 6 true a
  have hb : outerInvariant alphabet (true :: depth) (regs 9) b := by
    simp [outerInvariant,b,a,inputState]
  obtain ⟨next,hn, n, hbound, ht⟩ := generateProgram_runsIn alphabet (true :: depth) (regs 9) b hb
    (by simp [b,a,inputState])
    (by simp [b,a,inputState])
    (by simp [b,a,inputState])
  have he : Eval command (2 + n) a next := (pushConst_eval 8 6 true a).seq (.call _ ht)
  have hout := ready_eq alphabet (powerRows alphabet (depth.length + 1) [[]]) next
    (by simpa only [List.length_cons] using hn)
  rw [hout] at he
  refine ⟨next.regs, 2 + n + 1, ?_, compiled_halt_trace he 1 0⟩
  simp only [List.length_cons] at hbound
  dsimp [budget]
  omega

end SubexponentialSAT.Subexp.UniversalTypeProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_Subexp_PackingProgramInput
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Input preparation stages of the fixed physical packing controller. -/
namespace SubexponentialSAT.Subexp.PackingProgram

open BitProgram StructuredCalls PackingProgramSupport

def inputState (input : Input) (regs : Fin 16 → Bool) : Data :=
  ⟨regs, fun i =>
    if i = 40 then input.assignment else
    if i = 41 then input.width else
    if i = 42 then input.dimension else
    if i = 43 then input.degree else
    if i = 44 then input.scopes else
    if i = 45 then input.alphabet else []⟩

def frontendOutputState (input : Input) (labelBytes typeBytes : List Bool)
    (regs : Fin 16 → Bool) : Data :=
  ⟨regs, fun i => if i = 26 then labelBytes else if i = 27 then typeBytes
    else (inputState input regs).stacks i⟩

abbrev labelsCall : Cmd 16 48 := lowCall PackingVertexLabels.program (by decide) (by decide)
abbrev typesCall : Cmd 16 48 := lowCall UniversalTypeProgram.program (by decide) (by decide)

abbrev labels : Cmd 16 48 := .seq (PackingPlumbing.command labelsSetup)
  (.seq labelsCall (PackingPlumbing.command labelsSave))
abbrev types : Cmd 16 48 := .seq (PackingPlumbing.command typesSetup)
  (.seq typesCall (PackingPlumbing.command typesSave))

end SubexponentialSAT.Subexp.PackingProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_Subexp_PackingFrontendData
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Runtime input data and explicit budgets for the physical packing frontend. -/
namespace SubexponentialSAT.Subexp.PackingFrontend

namespace Params

def input (p : Params) : PackingProgram.Input :=
  ⟨p.rows.flatten,p.width,List.replicate p.D true,List.replicate p.Δ true,
    SubexpPlanAlphabetBase.scopeBytes p.scopes,ProgramEncoding.encodeRecords p.alphabet⟩

end Params
end SubexponentialSAT.Subexp.PackingFrontend

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_Subexp_PackingBucketStage
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Actual all-key bucketing in the final 16-register controller. -/

namespace SubexponentialSAT.Subexp.PackingProgram

open BitProgram StructuredCalls PackingProgramSupport

def bucketsBudget (records : List BucketProgram.Record) (keys : List (List Bool)) (D : ℕ) : ℕ :=
  8 * (BucketProgram.encodeRecords records.reverse).length +
  6 * (ProgramEncoding.encodeRecords keys).length + 7 * D +
  6 * (ProgramEncoding.encodeRecords (PackingBucketTable.table records keys)).length +
  6 * PackingBucketTable.minimum records keys D + 32 + PackingBucketTable.budget records keys

end SubexponentialSAT.Subexp.PackingProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_Subexp_AssignmentSeedRange
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Ascending framed unary seed indices from a runtime unary seed count. -/

namespace SubexponentialSAT.Subexp.AssignmentSeedRange

open BitProgram StructuredCalls TupleProgram

abbrev Data := State 5 6

def seedRecords (n : ℕ) : List Bool :=
  ProgramEncoding.encodeRecords ((List.range n).map unary)

end SubexponentialSAT.Subexp.AssignmentSeedRange

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_Subexp_PackingExtractionStage
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Exact relocation of complete-block extraction in the final controller. -/

namespace SubexponentialSAT.Subexp.PackingProgram

open BitProgram StructuredCalls PackingProgramSupport

def initialExtraction (entries : List PackingExtraction.Entry) (n : ℕ) : PackingExtraction.Context :=
  ⟨[], [], [], [], [], [], [], ProgramEncoding.encodeRecords (entries.map PackingExtraction.entryWord),
    List.replicate n true⟩

def extracted (entries : List PackingExtraction.Entry) (n : ℕ) : PackingExtraction.Context :=
  PackingExtraction.advanceMany entries n 0 (initialExtraction entries n)

def extractionBudget (entries : List PackingExtraction.Entry) (n : ℕ) : ℕ :=
  PackingExtraction.loopBudget entries n 0 (initialExtraction entries n) + 6 * n +
    2 * (ProgramEncoding.encodeRecords (entries.map PackingExtraction.entryWord)).length +
    7 * (extracted entries n).metadata.length + 16

end SubexponentialSAT.Subexp.PackingProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_Subexp_PackingInverseStage
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! The inverse read plan is constructed by actual generated vertex queries
and actual scans of the emitted address table. -/

namespace SubexponentialSAT.Subexp.PackingProgram

open BitProgram StructuredCalls PackingProgramSupport

def inverseBudget (records : List (List Bool × List Bool)) (D : ℕ) : ℕ :=
  6 * D ^ 2 + 19 * D + 33 +
  6 * (ProgramEncoding.encodeRecords (inverseQueries D)).length +
  9 * (SelectorProgram.rawRecords records).length +
  6 * (ProgramEncoding.encodeRecords (inverseRows records D)).length +
  SelectorMapProgram.budget records (inverseQueries D)

end SubexponentialSAT.Subexp.PackingProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LayoutProgramPackLabels
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Packing from physically produced label records. This route accepts the
incidence pair-gatherer's type labels directly, avoiding reconstruction of a
factor-to-incidence scope table. The fixed program computes blocks, uncovered
coordinates, metadata, storage order, and inverse addresses. It does not
assume any of those outputs. Label and universal-type byte production remain
explicit upstream obligations. -/
namespace SubexponentialSAT.SqrtLog.LayoutProgram.PackLabels

open SubexponentialSAT.Subexp SubexponentialSAT.Subexp.ConstructivePacking
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls

variable {U : Type*} [DecidableEq U]

def context (s : Spec U) : PackingExtraction.Context :=
  PackingProgram.extracted (entries s) s.packing.blockCount

end SubexponentialSAT.SqrtLog.LayoutProgram.PackLabels

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LayoutProgramLookupPair
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Two actual metadata lookups with disjoint returned records. Both query
indices and the computed metadata master are preserved. -/
namespace SubexponentialSAT.SqrtLog.LayoutProgram.LookupPair

open SubexponentialSAT.Subexp SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls
open GlobalBasisMetadata

abbrev Data := State 6 16

def state (regs : Fin 6 → Bool) (master row col : List Bool)
    (rb rt rr cb ct cr : List Bool) : Data :=
  ⟨regs,![master,row,col,rb,rt,rr,cb,ct,cr,[],[],[],[],[],[],[]]⟩

abbrev rowCall : Cmd 6 16 := .call (ProgramLinking.liftProgram GlobalBasisMetadata.program
  rowRegisters rowPorts)
abbrev colCall : Cmd 6 16 := .call (ProgramLinking.liftProgram GlobalBasisMetadata.program
  colRegisters colPorts)
abbrev command : Cmd 6 16 := .seq rowCall colCall
def program := compiled command 0 3

end SubexponentialSAT.SqrtLog.LayoutProgram.LookupPair

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LayoutProgramEntryBank
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! The concrete incidence-entry program. Its read-only cache bank is200..211,
its input indices252/253, and the returned signed pair254/255. Ports212..251
belong to the caller and are outside every local subroutine map. -/
namespace SubexponentialSAT.SqrtLog.LayoutProgram.EntryBank

open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.Subexp

abbrev Code := Cmd 16 256

def lookup : Code := .call (ProgramLinking.liftProgram LookupPair.program lookupRegs lookupPorts)
def prepare : Code := Staging.sequence 0 1 199 prepareOps

def exportPair : Code := Staging.sequence 0 1 199 exportOps

def cleanup : Code := Staging.sequence 0 1 199 cleanupOps

end SubexponentialSAT.SqrtLog.LayoutProgram.EntryBank

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LayoutProgramFrontend
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! The physical label/type frontend for arbitrary runtime incidence plans.
The plans have already been produced by the native incidence scan. This
frontend gathers their actual words and generates the complete type alphabet;
it does not accept label records or block metadata as input. -/
namespace SubexponentialSAT.SqrtLog.LayoutProgram.NativeFrontend

open SubexponentialSAT.Subexp SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls
open SubexponentialSAT.Subexp.PackingProgramSupport

namespace Params

def input (p : Params) : PackingProgram.Input := p.base.input

def planStream (p : Params) : List Bool :=
  ProgramEncoding.encodeRecords (p.planList.map PackingVertexLabels.planPayload)
def typeStream (p : Params) : List Bool := ProgramEncoding.encodeRecords p.typeRows
theorem planStream_eq (p : Params) :
    p.planStream = ProgramEncoding.encodeRecords (p.planList.map PackingVertexLabels.planPayload) := rfl

def labelsBound (p : Params) : ℕ :=
  PackingVertexLabels.traceCost p.width.length p.planList 0+
    9*p.rows.flatten.length+9*p.width.length+6*p.planStream.length+6*p.labelStream.length+2*p.D+31
def typesBound (p : Params) : ℕ :=
  UniversalTypeProgram.budget p.alphabet p.Δ+
    9*(ProgramEncoding.encodeRecords p.alphabet).length+7*p.Δ+6*p.typeStream.length+24

end Params

def plansState (p : Params) (regs : Fin 16 → Bool) : Data :=
  ⟨regs,fun i => if i=25 then p.planStream else (PackingProgram.inputState p.input regs).stacks i⟩

def labelsState (p : Params) (regs : Fin 16 → Bool) : Data :=
  ⟨regs,fun i => if i=26 then p.labelStream else (PackingProgram.inputState p.input regs).stacks i⟩

theorem labels_call_stacks (p : Params) (regs : Fin 16 → Bool) (rs : Fin 8 → Bool) :
    (install (by decide : 8 ≤ 16) (by decide : 15 ≤ 48)
      (PackingPlumbing.run PackingProgram.labelsSetup (plansState p regs))
      (PackingVertexLabels.state rs p.rows.flatten [] p.width [] [] []
        (List.replicate p.D true) p.labelStream [])).stacks = fun i =>
      if i=0 then p.rows.flatten else if i=3 then p.width
      else if i=12 then List.replicate p.D true else if i=13 then p.labelStream
      else (PackingProgram.inputState p.input regs).stacks i := by
  funext i
  fin_cases i <;> simp [Fin.coe_ofNat_eq_mod,install,PackingPlumbing.run,PackingPlumbing.Op.next,
    PackingProgram.labelsSetup,PackingPlumbing.move,
    StackRoutines.copyStacks,StackRoutines.transferStacks,
    PackingProgram.inputState,PackingVertexLabels.state,plansState,Params.input,Params.base,PackingFrontend.Params.input,Params.base,PackingFrontend.Params.input]

theorem types_call_stacks (p : Params) (regs : Fin 16 → Bool) (rs : Fin 10 → Bool) :
    (install (by decide : 10 ≤ 16) (by decide : 9 ≤ 48)
      (PackingPlumbing.run PackingProgram.typesSetup (labelsState p regs))
      (UniversalTypeProgram.outputState p.alphabet p.typeRows rs)).stacks = fun i =>
      if i=0 then p.typeStream else if i=1 then ProgramEncoding.encodeRecords p.alphabet
      else if i=5 then [false] else if i=26 then p.labelStream
      else (PackingProgram.inputState p.input regs).stacks i := by
  funext i
  fin_cases i <;> simp [Fin.coe_ofNat_eq_mod,install,PackingPlumbing.run,PackingPlumbing.Op.next,
    PackingProgram.typesSetup,StackRoutines.copyStacks,PackingProgram.inputState,
    UniversalTypeProgram.outputState,labelsState,Params.input,Params.base,PackingFrontend.Params.input,Params.typeStream]

theorem labels_eval (p : Params) (regs : Fin 16 → Bool)
    (hrows : ∀ row ∈ p.rows, row.length=p.width.length)
    (hplans : ∀ plan ∈ p.planList, ∀ i ∈ plan, i < p.rows.length) :
    ∃ (n : ℕ) (rf : Fin 16 → Bool), n ≤ p.labelsBound ∧
      Eval PackingProgram.labels n (plansState p regs) (labelsState p rf) := by
  let a := plansState p regs
  let b := PackingPlumbing.run PackingProgram.labelsSetup a
  have hv : PackingPlumbing.Valid PackingProgram.labelsSetup a := by
    simp [PackingProgram.labelsSetup,PackingPlumbing.move,PackingPlumbing.Valid,PackingPlumbing.Op.Valid,
      PackingPlumbing.Op.next,StackRoutines.copyStacks,a,plansState,PackingProgram.inputState]
  have hsetup := PackingPlumbing.eval PackingProgram.labelsSetup a hv
  have hsetupCost : PackingPlumbing.cost PackingProgram.labelsSetup a =
      7*p.rows.flatten.length+7*p.width.length+6*p.planStream.length+16 := by
    simp [PackingPlumbing.cost,PackingPlumbing.Op.cost,PackingPlumbing.Op.next,
      PackingProgram.labelsSetup,PackingPlumbing.move,a,plansState,PackingProgram.inputState,
      Params.input,Params.base,PackingFrontend.Params.input,StackRoutines.copyStacks,StackRoutines.transferStacks]
    ring
  rw [hsetupCost] at hsetup
  have hproject : project (by decide : 8 ≤ 16) (by decide : 15 ≤ 48) b =
      PackingVertexLabels.state (b.regs ∘ registers (by decide)) p.rows.flatten [] p.width []
        p.planStream [] [] [] [] := by
    apply congrArg₂ StructuredProgram.State.mk rfl
    funext i
    fin_cases i <;> simp [b,a,stackPorts,PackingPlumbing.run,PackingPlumbing.Op.next,
      PackingProgram.labelsSetup,PackingPlumbing.move,StackRoutines.copyStacks,StackRoutines.transferStacks,
      PackingProgram.inputState,plansState,Params.input,Params.base,PackingFrontend.Params.input]
  obtain ⟨n,rs,hn,ht⟩ := PackingVertexLabels.program_trace p.rows p.width p.planList
    (b.regs ∘ registers (by decide)) 0 [] [] hrows hplans
  have hinput : PackingVertexLabels.state (b.regs ∘ registers (by decide)) p.rows.flatten [] p.width []
      (ProgramEncoding.encodeRecords (p.planList.map PackingVertexLabels.planPayload) ++ []) []
      (List.replicate 0 true) [] [] = project (by decide : 8 ≤ 16) (by decide : 15 ≤ 48) b := by
    rw [hproject,← p.planStream_eq]
    simp only [List.append_nil,List.replicate_zero]
  rw [hinput] at ht
  let inner := PackingVertexLabels.state rs p.rows.flatten [] p.width [] [] []
    (List.replicate p.D true) p.labelStream []
  let c := install (by decide : 8 ≤ 16) (by decide : 15 ≤ 48) b inner
  have ht' : Trace PackingVertexLabels.program n
      ((project (by decide : 8 ≤ 16) (by decide : 15 ≤ 48) b).withPC (some PackingVertexLabels.program.entry))
      (inner.withPC none) := by
    simpa only [inner,Params.labelStream,Nat.zero_add,Params.planList_length,List.append_nil] using ht
  have hcall : Eval PackingProgram.labelsCall n b c :=
    lowCall_eval PackingVertexLabels.program (by decide) (by decide) b inner ht'
  have hc : c.stacks = fun i =>
      if i=0 then p.rows.flatten else if i=3 then p.width
      else if i=12 then List.replicate p.D true else if i=13 then p.labelStream
      else (PackingProgram.inputState p.input regs).stacks i := labels_call_stacks p regs rs
  have hsaveValid : PackingPlumbing.Valid PackingProgram.labelsSave c := by
    simp [PackingProgram.labelsSave,PackingPlumbing.move,PackingPlumbing.Valid,PackingPlumbing.Op.Valid]
  have hsave := PackingPlumbing.eval PackingProgram.labelsSave c hsaveValid
  let d := PackingPlumbing.run PackingProgram.labelsSave c
  have hdstate : d = labelsState p d.regs := by
    apply congrArg₂ StructuredProgram.State.mk rfl
    funext i
    fin_cases i <;> simp [d,PackingPlumbing.run,PackingPlumbing.Op.next,
      PackingProgram.labelsSave,PackingPlumbing.move,
      StackRoutines.transferStacks,StackRoutines.clearStacks,hc,
      PackingProgram.inputState]
  have hsaveCost : PackingPlumbing.cost PackingProgram.labelsSave c =
      6*p.labelStream.length+2*p.rows.flatten.length+2*p.width.length+2*p.D+15 := by
    simp [PackingPlumbing.cost,PackingPlumbing.Op.cost,PackingPlumbing.Op.next,
      PackingProgram.labelsSave,PackingPlumbing.move,hc,PackingProgram.inputState,
      StackRoutines.transferStacks,StackRoutines.clearStacks]
    ring
  rw [hsaveCost] at hsave
  change Eval _ _ c d at hsave
  rw [hdstate] at hsave
  refine ⟨_,d.regs,?_,hsetup.seq (hcall.seq hsave)⟩
  dsimp [Params.labelsBound]
  omega

theorem types_eval (p : Params) (regs : Fin 16 → Bool) :
    ∃ (n : ℕ) (rf : Fin 16 → Bool), n ≤ p.typesBound ∧
      Eval PackingProgram.types n (labelsState p regs)
        (PackingProgram.frontendOutputState p.input p.labelStream p.typeStream rf) := by
  let a := labelsState p regs
  let b := PackingPlumbing.run PackingProgram.typesSetup a
  have hv : PackingPlumbing.Valid PackingProgram.typesSetup a := by
    simp [PackingProgram.typesSetup,PackingPlumbing.Valid,PackingPlumbing.Op.Valid,
      PackingPlumbing.Op.next,StackRoutines.copyStacks,a,labelsState,PackingProgram.inputState]
  have hsetup := PackingPlumbing.eval PackingProgram.typesSetup a hv
  have hsetupCost : PackingPlumbing.cost PackingProgram.typesSetup a =
      7*(ProgramEncoding.encodeRecords p.alphabet).length+7*p.Δ+10 := by
    simp [PackingPlumbing.cost,PackingPlumbing.Op.cost,PackingPlumbing.Op.next,
      PackingProgram.typesSetup,a,labelsState,PackingProgram.inputState,Params.input,Params.base,PackingFrontend.Params.input,StackRoutines.copyStacks]
    ring
  rw [hsetupCost] at hsetup
  have hproject : project (by decide : 10 ≤ 16) (by decide : 9 ≤ 48) b =
      UniversalTypeProgram.inputState p.alphabet (List.replicate p.Δ true)
        (b.regs ∘ registers (by decide)) := by
    apply congrArg₂ StructuredProgram.State.mk rfl
    funext i
    fin_cases i <;> simp [b,a,stackPorts,PackingPlumbing.run,PackingPlumbing.Op.next,
      PackingProgram.typesSetup,StackRoutines.copyStacks,PackingProgram.inputState,labelsState,
      Params.input,Params.base,PackingFrontend.Params.input]
  obtain ⟨rs,n,hn,ht⟩ := UniversalTypeProgram.program_runsIn p.alphabet (List.replicate p.Δ true)
    (b.regs ∘ registers (by decide))
  rw [← hproject] at ht
  simp only [List.length_replicate] at hn ht
  let inner := UniversalTypeProgram.outputState p.alphabet p.typeRows rs
  let c := install (by decide : 10 ≤ 16) (by decide : 9 ≤ 48) b inner
  have hcall : Eval PackingProgram.typesCall n b c :=
    lowCall_eval UniversalTypeProgram.program (by decide) (by decide) b inner ht
  have hc : c.stacks = fun i =>
      if i=0 then p.typeStream else if i=1 then ProgramEncoding.encodeRecords p.alphabet
      else if i=5 then [false] else if i=26 then p.labelStream
      else (PackingProgram.inputState p.input regs).stacks i := types_call_stacks p regs rs
  have hsaveValid : PackingPlumbing.Valid PackingProgram.typesSave c := by
    simp [PackingProgram.typesSave,PackingPlumbing.move,PackingPlumbing.Valid,PackingPlumbing.Op.Valid]
  have hsave := PackingPlumbing.eval PackingProgram.typesSave c hsaveValid
  let d := PackingPlumbing.run PackingProgram.typesSave c
  have hdstate : d = PackingProgram.frontendOutputState p.input p.labelStream p.typeStream d.regs := by
    apply congrArg₂ StructuredProgram.State.mk rfl
    funext i
    fin_cases i <;> simp [d,PackingPlumbing.run,PackingPlumbing.Op.next,
      PackingProgram.typesSave,PackingPlumbing.move,
      StackRoutines.transferStacks,StackRoutines.clearStacks,hc,
      PackingProgram.inputState]
  have hsaveCost : PackingPlumbing.cost PackingProgram.typesSave c =
      6*p.typeStream.length+2*(ProgramEncoding.encodeRecords p.alphabet).length+14 := by
    simp [PackingPlumbing.cost,PackingPlumbing.Op.cost,PackingPlumbing.Op.next,
      PackingProgram.typesSave,PackingPlumbing.move,hc,PackingProgram.inputState,
      StackRoutines.transferStacks,StackRoutines.clearStacks]
    ring
  rw [hsaveCost] at hsave
  change Eval _ _ c d at hsave
  rw [hdstate] at hsave
  refine ⟨_,d.regs,?_,hsetup.seq (hcall.seq hsave)⟩
  dsimp [Params.typesBound]
  omega


abbrev command : Cmd 16 48 := .seq PackingProgram.labels PackingProgram.types
def program := compiled command 25 26

theorem program_trace (p : Params) (regs : Fin 16 → Bool)
    (hrows : ∀ row ∈ p.rows, row.length = p.width.length)
    (hplans : ∀ plan ∈ p.planList, ∀ i ∈ plan, i < p.rows.length) :
    ∃ steps ≤ p.labelsBound+p.typesBound+1, ∃ rf,
      Trace program steps ((plansState p regs).withPC (some program.entry))
        ((PackingProgram.frontendOutputState p.input p.labelStream p.typeStream rf).withPC none) := by
  obtain ⟨nl,rl,hl,el⟩ := labels_eval p regs hrows hplans
  obtain ⟨nt,rt,ht,et⟩ := types_eval p rl
  exact ⟨nl+nt+1,by omega,rt,compiled_halt_trace (el.seq et) 25 26⟩

end SubexponentialSAT.SqrtLog.LayoutProgram.NativeFrontend

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LayoutProgramIntegerCache
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Paid reusable integer-cache initialization. The runtime parameters A, R
and common width remain on20/21/22. Outputs are H-positive0, H-negative1,
binary clearing denominator2, and retained local width19. -/
namespace SubexponentialSAT.SqrtLog.LayoutProgram.IntegerCache

open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls
open RowSelectionProgram LayoutProgramScalar

abbrev copy (src dst : Fin 24) : Cmd 8 24 := .call (StackRoutines.copyProgram src dst 3 0 1)
abbrev copies : Cmd 8 24 := .seq (copy 20 17) (.seq (copy 21 18) (copy 22 19))
abbrev powerCall : Cmd 8 24 := .call (ProgramLinking.liftProgram powerProgram powerRegs powerPorts)
abbrev popCounter : Cmd 8 24 := .base (.atom (.pop 23 0 1))
abbrev makePower : Cmd 8 24 := .seq (copy 21 23) (.seq popCounter powerCall)

end SubexponentialSAT.SqrtLog.LayoutProgram.IntegerCache

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LayoutSourceRowsProgram
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
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

def fiberPorts : UnaryForPrograms.Ports 16 340 := ⟨328,14,15⟩

end SubexponentialSAT.SqrtLog.LayoutSourceRowsProgram

/-! Paid bank relocation and register reset for the native polynomial source
executor. The parameter is a finite BitProgram; the integration selects the
checked polynomial executor, never a polynomial-value instruction. -/

/-! The bytes produced by the runtime fold are the compiler output of the
same finite sum expression, including the empty-owner zero polynomial. -/

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
open BitProgram StructuredCalls SubexpQuarticRing SubexpLiftRing

abbrev finalCleanup : Cmd 32 640 := .seq (clearPorts finalDiscard) RegisterResetProgram.all

end SubexponentialSAT.SqrtLog.LeafRingSetupProgram

end OAI.Algorithms
end


