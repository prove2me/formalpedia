-- Prove2me | Definitions.Def_OAIQ081S143
-- name    : OAIQ081S143
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-29T22:50:40.755119+00:00
-- url     : https://prove2.me/theorems/1715f775-8cdb-4761-a033-65678b0069eb
-- title:
--   Definitions bundle OAIQ081S143 of the split of OpenAI, The Exponential Time Hypothesis is False
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.exact_count_and_sat`, carved from OpenAI's openai/math development (OpenAI, *The Exponential Time Hypothesis is False*, OpenAI Math Release, October 25, 2026, result family 378, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 56 declarations of OpenAI's Lean: 43 definitions and 13 theorems. The definitions and types are `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutMatrixProgram.coefficientStep`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutMatrixProgram.command`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutMatrixProgram.program`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutMatrixProgram.rowBody`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutMatrixProgram.rowLoop`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutMatrixProgram.rowScan`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutOffsetProgram.command`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutOffsetProgram.core`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutOffsetProgram.program`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgram.IntegerCache.command`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgram.IntegerCache.flat`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgram.IntegerCache.program`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgram.NativePacking.budget`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgram.NativePacking.command`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgram.NativePacking.program`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgram.PackLabels.Spec.outputState`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgram.PackLabels.budget`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgram.SourceBank.stageEmitter`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgramScalar.buildCommand`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgramScalar.buildProgram`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgramScalar.cacheBuildLoop`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgramScalar.cacheCommand`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgramScalar.cacheLoop`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgramScalar.cachePass`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgramScalar.cacheProgram`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgramScalar.cacheRow`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgramScalar.hFlatBuild`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgramScalar.hFlatCommand`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgramScalar.hFlatProgram`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.PackingIncidenceInput.Clear.Data`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.RingProgramTable.modelTable`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighQueryAdapter.Overlay.clear`, `OAI.Algorithms.SubexponentialSAT.Subexp.AssignmentSeedRange.inputState`, `OAI.Algorithms.SubexponentialSAT.Subexp.AssignmentSeedRange.outputState`, `OAI.Algorithms.SubexponentialSAT.Subexp.AssignmentSeedRange.state`, `OAI.Algorithms.SubexponentialSAT.Subexp.GlobalBasisEntryCore.pop`, `OAI.Algorithms.SubexponentialSAT.Subexp.GlobalBasisEntryCore.sealCall`, `OAI.Algorithms.SubexponentialSAT.Subexp.PackingProgram.bucketsOutputState`, `OAI.Algorithms.SubexponentialSAT.Subexp.PackingProgram.extractionOutputState`, `OAI.Algorithms.SubexponentialSAT.Subexp.PackingProgram.outputState` and 3 more.
--
--   **Sources.** They come from these modules of lean/OAI/Algorithms, in whole or in part: `SubexponentialSAT_SqrtLogSpace_HighQueryAdapter`, `SubexponentialSAT_SqrtLog_LayoutMatrixProgram`, `SubexponentialSAT_SqrtLog_LayoutMatrixProgramLoop`, `SubexponentialSAT_SqrtLog_LayoutMatrixProgramRow`, `SubexponentialSAT_SqrtLog_LayoutMatrixProgramRowScan`, `SubexponentialSAT_SqrtLog_LayoutMatrixProgramRowStep`, `SubexponentialSAT_SqrtLog_LayoutOffsetProgram`, `SubexponentialSAT_SqrtLog_LayoutOffsetProgramRun`, `SubexponentialSAT_SqrtLog_LayoutProgramIntegerCache`, `SubexponentialSAT_SqrtLog_LayoutProgramNativePacking`, `SubexponentialSAT_SqrtLog_LayoutProgramPackLabels`, `SubexponentialSAT_SqrtLog_LayoutProgramScalarCacheCell`, `SubexponentialSAT_SqrtLog_LayoutProgramScalarCacheFlat`, `SubexponentialSAT_SqrtLog_LayoutProgramSourceBank`, `SubexponentialSAT_SqrtLog_PackingIncidenceInputNative`, `SubexponentialSAT_SqrtLog_RingProgramTableModel`, `SubexponentialSAT_SubexpKernelControl`, `SubexponentialSAT_Subexp_AssignmentSeedRange`, `SubexponentialSAT_Subexp_GlobalBasisEntryCore`, `SubexponentialSAT_Subexp_PackingBucketStage`, `SubexponentialSAT_Subexp_PackingExtractionEmit`, `SubexponentialSAT_Subexp_PackingExtractionStage`, `SubexponentialSAT_Subexp_PackingInverseStage`, `SubexponentialSAT_Subexp_PackingLeftoverStage`, `SubexponentialSAT_Subexp_PackingProgramInput`, `SubexponentialSAT_Subexp_SelectorMapProgram`.
--
--   **Imports.** It imports the published bundle `Def_SubexponentialSAT`; the bundles `OAIQ081S117`, `OAIQ081S118`, `OAIQ081S120`, `OAIQ081S122`, `OAIQ081S123`, `OAIQ081S124` and `OAIQ081S126` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ081S155`, `OAIQ081S156`, `OAIQ081S157`, `OAIQ081S158`, `OAIQ081S159`, `OAIQ081S160`, `OAIQ081S162` and `OAIQ081S163`; the statements `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutMatrixProgram.rowLoop_eval`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutMatrixProgram.rowScan_eval` and `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgramScalar.cacheBuildLoop_eval`; the proofs of `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutMatrixProgram.rowLoop_eval`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutMatrixProgram.rowScan_eval` and `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgramScalar.cacheBuildLoop_eval`.
-- source:
--   OpenAI, The Exponential Time Hypothesis is False, OpenAI Math Release, October 25, 2026, https://github.com/openai/math (result family 378; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/The-Exponential-Time-Hypothesis-is-False-October-25-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Algorithms at commit 7ef5c0c

import Mathlib
import Definitions.Def_SubexponentialSAT
import Definitions.Def_OAIQ081S117
import Definitions.Def_OAIQ081S118
import Definitions.Def_OAIQ081S120
import Definitions.Def_OAIQ081S122
import Definitions.Def_OAIQ081S123
import Definitions.Def_OAIQ081S124
import Definitions.Def_OAIQ081S126

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_HighQueryAdapter
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! Concrete per-high-assignment setup and compressed head overlays.
The routines read physical counter/mask words and preserve ambient coordinates. -/
namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighQueryAdapter

open OAI BitProgram StructuredCalls
open OAI.Algorithms.SubexponentialSAT.SqrtLog
open OAI.Algorithms.SubexponentialSAT.SqrtLog.HighIncidenceProgram

open OAI.Algorithms.SubexponentialSAT.StackRoutines

namespace Overlay
open OAI.Algorithms.SubexponentialSAT.StackRoutines

def clear : Code := .call (clearProgram 9 0 1)

end Overlay


end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighQueryAdapter
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

def coefficientStep (entry : Code 256) : Code 288 :=
  .seq (entryCall entry) (.seq emitPair clearColumn)

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

def rowScan (entry : Code 256) : Code 288 :=
  .seq (parse 283 278 (by decide))
    (.while 2 (.seq (coefficientStep entry) (parse 283 278 (by decide))))

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

def rowBody (entry : Code 256) : Code 288 :=
  .seq copyRowIndex (.seq copyIDs (.seq (rowScan entry) (.seq emitRow clearRowIndex)))

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

def rowLoop (entry : Code 256) : Code 288 := UnaryForPrograms.forCmd counter (rowBody entry)

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

def command (entry : Code 256) : Code 288 :=
  .seq initializeIDs (.seq (rowLoop entry) clearIDs)

/-- The compiler produces one finite instruction table, independent of all
runtime dimensions and entry magnitudes. -/
def program (entry : Code 256) := compiled (command entry) 281 24

end SubexponentialSAT.SqrtLog.LayoutMatrixProgram

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

abbrev core : Cmd 8 22 :=
  .seq (loadCmd 3 two) (.seq (loadCmd 4 eight)
    (.seq (multiplyCmd 4 1 5 (by decide) (by decide))
      (.seq (multiplyCmd 3 2 6 (by decide) (by decide))
        (.seq (powerCmd 5 6 7 (by decide) (by decide))
          (.seq (multiplyCmd 3 0 8 (by decide) (by decide))
            (multiplyCmd 8 7 9 (by decide) (by decide)))))))

end SubexponentialSAT.SqrtLog.LayoutOffsetProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LayoutOffsetProgramRun
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.LayoutOffsetProgram
open SubexponentialSAT BitProgram StructuredCalls BinaryArithmetic SubexpBlockParameterProgram

abbrev command : Cmd 8 22 := .seq core (.seq (clearMany scratch) RegisterResetProgram.all)
abbrev program := compiled command 0 9

end SubexponentialSAT.SqrtLog.LayoutOffsetProgram

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

abbrev cacheRow : Cmd 8 18 :=
  .seq parse (.while 7 (.seq cacheCell (.seq cacheEmit parse)))

end SubexponentialSAT.SqrtLog.LayoutProgramScalar

/-! Complete reusable cache pass: read one encoded row, compute and emit its
new row, append the end marker, reverse the output, and clear the carry. -/
namespace SubexponentialSAT.SqrtLog.LayoutProgramScalar

open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls
open SubexponentialSAT.SqrtLog.RowSelectionProgram

abbrev cachePass : Cmd 8 18 := .seq cacheRow (.seq cacheFinishList cacheClear)

end SubexponentialSAT.SqrtLog.LayoutProgramScalar

/-! The number of coefficient-cache rows is runtime unary data. This fixed
loop invokes the complete paid row pass and preserves the current encoded row.
-/
namespace SubexponentialSAT.SqrtLog.LayoutProgramScalar

open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls
open SubexponentialSAT.SqrtLog.RowSelectionProgram

abbrev cacheLoop : Cmd 8 18 := .while 6 (.seq cachePass cacheRead)

abbrev cacheCommand : Cmd 8 18 := .seq cacheRead cacheLoop
def cacheProgram := compiled cacheCommand 17 15

end SubexponentialSAT.SqrtLog.LayoutProgramScalar

/-! The physical unsigned cache computes the original coefficient recurrence's
natural magnitudes, in ascending degree order. -/

/-! A fixed loop builds the initial all-one cache row from a runtime unary
length. The constant program contains one record, independent of that length. -/

/-! One fixed program builds the complete unsigned H cache from the unary
runtime parameters A and R. No coefficient or initial cache is free input. -/
namespace SubexponentialSAT.SqrtLog.LayoutProgramScalar

open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls
open SubexponentialSAT.SqrtLog.RowSelectionProgram

abbrev cacheBuildLoop : Cmd 8 19 :=
  .call (ProgramLinking.liftProgram cacheProgram id cacheBuildPorts)

abbrev buildCommand : Cmd 8 19 := .seq initialBuild cacheBuildLoop
def buildProgram := compiled buildCommand 17 15

end SubexponentialSAT.SqrtLog.LayoutProgramScalar

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LayoutProgramScalarCacheFlat
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! The H cache builder followed by the shared physical fixed-width adapter.
Only the common width survives alongside the two flat output arrays. -/
namespace SubexponentialSAT.SqrtLog.LayoutProgramScalar

attribute [local simp] Fin.coe_ofNat_eq_mod

open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls RowSelectionProgram
open LayoutBinomialProgram (buildFinalPorts finalFlatten normalizedWords normalizedWords_length
  )

 def hFlatBuild : Cmd 8 20 :=
  .call (ProgramLinking.liftProgram buildProgram id buildFinalPorts)

abbrev hFlatCommand : Cmd 8 20 := .seq hFlatBuild finalFlatten
def hFlatProgram := compiled hFlatCommand 17 0

end SubexponentialSAT.SqrtLog.LayoutProgramScalar

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

abbrev flat : Cmd 8 24 := .call (ProgramLinking.liftProgram hFlatProgram id flatPorts)
abbrev command : Cmd 8 24 := .seq copies (.seq flat makePower)
def program := compiled command 20 0

end SubexponentialSAT.SqrtLog.LayoutProgram.IntegerCache

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_Subexp_SelectorMapProgram
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
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

/-- The fixed record loop invokes the proved callback for every query. Its
output is the selected payload list in reverse order, and the table survives. -/
theorem program_trace_from (records : List (List Bool × List Bool)) (queries : List (List Bool))
    (initialRegs : Fin 8 → Bool) :
    ∃ n ≤ budget records queries, ∃ regs,
      Trace program n ((inputStateWith initialRegs records queries).withPC (some program.entry))
        ((outputState records queries regs).withPC none) := by
  let a := inputStateWith initialRegs records queries
  let b := TupleProgram.pushedState (8 : Fin 9) (0 : Fin 8) false a
  have hinit := TupleProgram.pushConst_eval (8 : Fin 9) (0 : Fin 8) false a
  have hb : invariant records b := by
    simp [invariant, b, a, inputStateWith, state ]
  obtain ⟨n, next, hn, hnext, history, hiter⟩ :=
    RecordPrograms.iterate_run_with ports callback (fun _ => false) (callbackCost records)
      (invariant records)
      (fun query a b => b.stacks 8 = TupleProgram.prependRecord (selected records query) (a.stacks 8))
      (callback_contract records) queries [] b hb (b.regs 5) (b.regs 6) (b.regs 7)
  have hstart : RecordPrograms.state ports b (b.regs 5) (b.regs 6) (b.regs 7)
      (Encoding.encodeList id queries ++ []) [] = b := by
    apply RecordPrograms.state_eq_self <;>
      simp [ports, b, a, inputStateWith, state,
        ProgramEncoding.encodeRecords]
  have hout : next.stacks 8 = ProgramEncoding.encodeRecords (mappedRecords records queries) := by
    have hh := history.fold_of_false (fun _ _ => rfl) (fun s => s.stacks 8)
      (fun out query => TupleProgram.prependRecord (selected records query) out)
      (fun _ _ _ h => h)
    rw [fold_prepend] at hh
    simpa [b, a, inputStateWith, state, TupleProgram.pushedState,
      mappedRecords, encodeRecords_eq_prefix] using hh
  let c := RecordPrograms.state ports next false true false [] []
  have hiter' : Eval (RecordPrograms.iterate ports callback) n b c := by
    have hany : queries.any (fun _ => false) = false := by
      induction queries <;> simp_all
    simpa only [hstart, hany, TupleProgram.unread_false] using hiter
  have hc : c = outputState records queries c.regs := by
    apply congrArg₂ StructuredProgram.State.mk
    · rfl
    · funext j
      rcases hnext with ⟨h0, h1, h3, h4, h5, h7⟩
      fin_cases j <;>
        simp [ ports, h0, h1, h3, h4, h5, h7, hout]
  have htrace := compiled_halt_trace (hinit.seq hiter') (6 : Fin 9) 8
  refine ⟨2 + n + 1, by dsimp [budget]; omega, c.regs, ?_⟩
  change Trace program (2 + n + 1) (a.withPC (some program.entry)) (c.withPC none) at htrace
  rw [show c.withPC none = (outputState records queries c.regs).withPC none from
    congrArg (fun s : Data => s.withPC none) hc] at htrace
  exact htrace

end SubexponentialSAT.Subexp.SelectorMapProgram

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

def outputState (input : Input) (blocks leftovers metadata addresses storage inverse : List Bool)
    (regs : Fin 16 → Bool) : Data :=
  ⟨regs, fun i => if i = 30 then blocks else if i = 31 then leftovers else
    if i = 32 then metadata else if i = 33 then addresses else
    if i = 34 then storage else if i = 35 then inverse else (inputState input regs).stacks i⟩

end SubexponentialSAT.Subexp.PackingProgram

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

def bucketsOutputState (input : Input) (table count : List Bool) (regs : Fin 16 → Bool) : Data :=
  ⟨regs, fun i => if i = 15 then table else if i = 16 then count
    else (inputState input regs).stacks i⟩

theorem bucket_call_stacks (input : Input) (records : List BucketProgram.Record)
    (keys : List (List Bool)) (D : ℕ) (regs : Fin 16 → Bool) (rb : Fin 8 → Bool) :
    (install (by decide : 8 ≤ 16) (by decide : 15 ≤ 48)
      (PackingPlumbing.run bucketsSetup
        (frontendOutputState input (BucketProgram.encodeRecords records.reverse)
          (ProgramEncoding.encodeRecords keys) regs))
      (PackingBucketTable.outputState records keys D [] rb)).stacks = fun i =>
        if i = 5 then ProgramEncoding.encodeRecords (PackingBucketTable.table records keys)
        else if i = 6 then BucketProgram.encodeRecords records.reverse
        else if i = 10 then List.replicate (PackingBucketTable.minimum records keys D) true
        else (inputState input regs).stacks i := by
  funext i
  fin_cases i <;>
    simp [install, PackingPlumbing.run, bucketsSetup, PackingPlumbing.move, PackingPlumbing.Op.next,
      frontendOutputState, inputState, PackingBucketTable.outputState, PackingBucketCalls.state,
      StackRoutines.copyStacks, StackRoutines.transferStacks, Fin.coe_ofNat_eq_mod]

theorem bucket_save_stacks (input : Input) (records : List BucketProgram.Record)
    (keys : List (List Bool)) (D : ℕ) (regs : Fin 16 → Bool) (c : Data)
    (hc : c.stacks = fun i =>
      if i = 5 then ProgramEncoding.encodeRecords (PackingBucketTable.table records keys)
      else if i = 6 then BucketProgram.encodeRecords records.reverse
      else if i = 10 then List.replicate (PackingBucketTable.minimum records keys D) true
      else (inputState input regs).stacks i) :
    (PackingPlumbing.run bucketsSave c).stacks =
      (bucketsOutputState input (ProgramEncoding.encodeRecords (PackingBucketTable.table records keys))
        (List.replicate (PackingBucketTable.minimum records keys D) true) regs).stacks := by
  funext i
  fin_cases i <;>
    simp [PackingPlumbing.run, bucketsSave, PackingPlumbing.move, PackingPlumbing.Op.next,
      hc, inputState, bucketsOutputState, StackRoutines.transferStacks,
      StackRoutines.clearStacks]

theorem buckets_eval (input : Input) (records : List BucketProgram.Record)
    (keys : List (List Bool)) (D : ℕ) (hD : input.dimension = List.replicate D true)
    (hcount : D ≤ records.length) (regs : Fin 16 → Bool) :
    ∃ n ≤ bucketsBudget records keys D, ∃ rf,
      Eval buckets n
        (frontendOutputState input (BucketProgram.encodeRecords records.reverse)
          (ProgramEncoding.encodeRecords keys) regs)
        (bucketsOutputState input
          (ProgramEncoding.encodeRecords (PackingBucketTable.table records keys))
          (List.replicate (PackingBucketTable.minimum records keys D) true) rf) := by
  let a := frontendOutputState input (BucketProgram.encodeRecords records.reverse)
    (ProgramEncoding.encodeRecords keys) regs
  have hv : PackingPlumbing.Valid bucketsSetup a := by
    simp [PackingPlumbing.Valid, PackingPlumbing.Op.Valid, bucketsSetup,
      PackingPlumbing.move, PackingPlumbing.Op.next, a, frontendOutputState, inputState,
 StackRoutines.transferStacks]
  let b := PackingPlumbing.run bucketsSetup a
  have hp : project (by decide : 8 ≤ 16) (by decide : 15 ≤ 48) b =
      PackingBucketTable.inputState records keys D []
        (project (by decide : 8 ≤ 16) (by decide : 15 ≤ 48) b).regs := by
    apply congrArg₂ StructuredProgram.State.mk rfl
    funext i
    fin_cases i <;>
      simp [ stackPorts, b, PackingPlumbing.run, bucketsSetup,
        PackingPlumbing.move, PackingPlumbing.Op.next, a, frontendOutputState, inputState,
        StackRoutines.copyStacks, StackRoutines.transferStacks,
 hD]
  obtain ⟨nb, hnb, rb, hbt⟩ := PackingBucketTable.program_trace records keys D hcount []
    (project (by decide : 8 ≤ 16) (by decide : 15 ≤ 48) b).regs
  let c := install (by decide : 8 ≤ 16) (by decide : 15 ≤ 48) b
    (PackingBucketTable.outputState records keys D [] rb)
  have hcall : Eval bucketsCall nb b c := by
    apply lowCall_eval
    rw [hp]
    exact hbt
  have hc : c.stacks = fun i =>
      if i = 5 then ProgramEncoding.encodeRecords (PackingBucketTable.table records keys)
      else if i = 6 then BucketProgram.encodeRecords records.reverse
      else if i = 10 then List.replicate (PackingBucketTable.minimum records keys D) true
      else (inputState input regs).stacks i := bucket_call_stacks input records keys D regs rb
  have hw : PackingPlumbing.Valid bucketsSave c := by
    simp [PackingPlumbing.Valid, PackingPlumbing.Op.Valid, bucketsSave,
      PackingPlumbing.move
]
  let d := PackingPlumbing.run bucketsSave c
  have hd : d = bucketsOutputState input
      (ProgramEncoding.encodeRecords (PackingBucketTable.table records keys))
      (List.replicate (PackingBucketTable.minimum records keys D) true) d.regs := by
    apply congrArg₂ StructuredProgram.State.mk rfl
    exact bucket_save_stacks input records keys D regs c hc
  have hc1 : PackingPlumbing.cost bucketsSetup a =
      6 * (BucketProgram.encodeRecords records.reverse).length +
      6 * (ProgramEncoding.encodeRecords keys).length + 7 * D + 17 := by
    simp [PackingPlumbing.cost, PackingPlumbing.Op.cost, bucketsSetup, PackingPlumbing.move,
      PackingPlumbing.Op.next, a, frontendOutputState, inputState,
 StackRoutines.transferStacks, hD]
    omega
  have hc2 : PackingPlumbing.cost bucketsSave c =
      2 * (BucketProgram.encodeRecords records.reverse).length +
      6 * (ProgramEncoding.encodeRecords (PackingBucketTable.table records keys)).length +
      6 * PackingBucketTable.minimum records keys D + 15 := by
    simp [PackingPlumbing.cost, PackingPlumbing.Op.cost, bucketsSave, PackingPlumbing.move,
      PackingPlumbing.Op.next, hc, inputState, StackRoutines.clearStacks, StackRoutines.transferStacks]
    omega
  have he := (PackingPlumbing.eval bucketsSetup a hv).seq
    (hcall.seq (PackingPlumbing.eval bucketsSave c hw))
  refine ⟨PackingPlumbing.cost bucketsSetup a + (nb + PackingPlumbing.cost bucketsSave c),
    ?_, d.regs, ?_⟩
  · rw [hc1, hc2]
    unfold bucketsBudget
    omega
  · change Eval buckets _ a d at he
    rw [hd] at he
    exact he

end SubexponentialSAT.Subexp.PackingProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_Subexp_PackingExtractionEmit
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Lift the actual covered-entry emitter into the extraction controller. -/

namespace SubexponentialSAT.Subexp.PackingExtraction

open BitProgram StructuredCalls MatrixProgramSupport

theorem emitCall_eval (c : Context) (key vertex : List Bool) (regs : Fin 8 → Bool) :
    ∃ rf, Eval emitCall (PackingEntryEmitter.commandCost vertex key c.block c.address + 1)
      (state regs c [] key [] vertex [] [] [] []) (ready rf (emitted c key vertex)) := by
  obtain ⟨rf, ht⟩ := PackingEntryEmitter.program_trace vertex key c.block c.address
    c.storage c.metadata c.addresses regs
  let a := state regs c [] key [] vertex [] [] [] []
  have hin : embedState id emitPorts a
      (PackingEntryEmitter.state regs vertex key c.block c.address c.storage c.metadata c.addresses) =
      a := by
    apply SelectorMapProgram.embed_eq _ _ Function.injective_id emitPorts_injective
    · intro i; rfl
    · intro i
      fin_cases i <;> rfl
    · intros; rfl
    · intros; rfl
  have hout : embedState id emitPorts a
      (PackingEntryEmitter.state rf [] [] c.block (true :: c.address)
        (PackingEntryEmitter.storageOutput vertex c.storage)
        (PackingEntryEmitter.metadataOutput vertex key c.block c.metadata)
        (PackingEntryEmitter.addressOutput vertex c.address c.addresses)) =
      ready rf (emitted c key vertex) := by
    apply SelectorMapProgram.embed_eq _ _ Function.injective_id emitPorts_injective
    · intro i; rfl
    · intro i
      fin_cases i <;> rfl
    · intro j hj
      exact False.elim (hj ⟨j, rfl⟩)
    · intro j hj
      fin_cases j <;> simp_all [a, ready, state, emitted, emitPorts]
      all_goals
        first | exact False.elim (hj 0 rfl) | exact False.elim (hj 1 rfl) |
          exact False.elim (hj 2 rfl) | exact False.elim (hj 3 rfl) |
          exact False.elim (hj 4 rfl) | exact False.elim (hj 5 rfl) |
          exact False.elim (hj 6 rfl)
  have he := eval_call_lifted PackingEntryEmitter.program id emitPorts a
    Function.injective_id emitPorts_injective ht
  rw [hin, hout] at he
  exact ⟨rf, he⟩

end SubexponentialSAT.Subexp.PackingExtraction

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

def state (regs : Fin 5 → Bool) (current : ℕ) (input descending output : List Bool) : Data :=
  ⟨regs, ![input, unary current, [], descending, [], output]⟩

def inputState (regs : Fin 5 → Bool) (n : ℕ) : Data := state regs 0 (unary n) [] []
def outputState (n : ℕ) : Data := state (fun _ => false) 0 [] [] (seedRecords n)

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

def extractionOutputState (input : Input) (n : ℕ) (c : PackingExtraction.Context)
    (regs : Fin 16 → Bool) : Data :=
  ⟨regs, fun i => if i = 6 then c.metadata else if i = 11 then c.address else
    if i = 12 then c.storage else if i = 13 then c.metadata else if i = 14 then c.addresses else
    if i = 30 then List.replicate n true else (inputState input regs).stacks i⟩

theorem extraction_call_stacks (input : Input) (entries : List PackingExtraction.Entry)
    (n : ℕ) (regs : Fin 16 → Bool) (re : Fin 8 → Bool)
    (hb : (extracted entries n).block = List.replicate n true)
    (hr : (extracted entries n).remaining = [])
    (ht : (extracted entries n).buckets =
      ProgramEncoding.encodeRecords (entries.map PackingExtraction.entryWord)) :
    (install (by decide : 8 ≤ 16) (by decide : 19 ≤ 48)
      (bucketsOutputState input (ProgramEncoding.encodeRecords (entries.map PackingExtraction.entryWord))
        (List.replicate n true) regs)
      (PackingExtraction.base re (extracted entries n))).stacks = fun i =>
      if i = 10 then List.replicate n true else if i = 11 then (extracted entries n).address
      else if i = 12 then (extracted entries n).storage else if i = 13 then (extracted entries n).metadata
      else if i = 14 then (extracted entries n).addresses
      else if i = 15 then ProgramEncoding.encodeRecords (entries.map PackingExtraction.entryWord)
      else (inputState input regs).stacks i := by
  funext i
  fin_cases i <;>
    simp [install, PackingExtraction.base, PackingExtraction.ready, PackingExtraction.state,
      bucketsOutputState, inputState, hb, hr, ht, Fin.coe_ofNat_eq_mod]

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

theorem query_call_stacks (input : Input) (blocks leftovers metadata storage : List Bool)
    (records : List (List Bool × List Bool)) (D : ℕ) (regs : Fin 16 → Bool) (rq : Fin 5 → Bool) :
    (install (by decide : 5 ≤ 16) (by decide : 5 ≤ 48)
      (PackingPlumbing.run queriesSetup
        (outputState input blocks leftovers metadata (SelectorProgram.rawRecords records) storage [] regs))
      (⟨rq, ![[], List.replicate D true, [], ProgramEncoding.encodeRecords (inverseQueries D), []]⟩ :
        State 5 5)).stacks = fun i =>
      if i = 1 then List.replicate D true else if i = 3 then ProgramEncoding.encodeRecords (inverseQueries D)
      else (outputState input blocks leftovers metadata (SelectorProgram.rawRecords records) storage [] regs).stacks i := by
  funext i
  fin_cases i <;>
    simp [install, PackingPlumbing.run, queriesSetup, PackingPlumbing.Op.next,
      outputState, inputState, StackRoutines.copyStacks, Fin.coe_ofNat_eq_mod]

theorem query_save_stacks (input : Input) (blocks leftovers metadata storage : List Bool)
    (records : List (List Bool × List Bool)) (D : ℕ) (regs : Fin 16 → Bool) (c : Data)
    (hc : c.stacks = fun i =>
      if i = 1 then List.replicate D true else if i = 3 then ProgramEncoding.encodeRecords (inverseQueries D)
      else (outputState input blocks leftovers metadata (SelectorProgram.rawRecords records) storage [] regs).stacks i) :
    (PackingPlumbing.run queriesSave c).stacks = fun i =>
      if i = 6 then ProgramEncoding.encodeRecords (inverseQueries D)
      else if i = 7 then SelectorProgram.rawRecords records
      else (outputState input blocks leftovers metadata (SelectorProgram.rawRecords records) storage [] regs).stacks i := by
  funext i
  fin_cases i <;>
    simp [PackingPlumbing.run, queriesSave, PackingPlumbing.move, PackingPlumbing.Op.next,
      hc, outputState, inputState, StackRoutines.copyStacks, StackRoutines.transferStacks,
      StackRoutines.clearStacks]

theorem inverse_call_stacks (input : Input) (blocks leftovers metadata storage : List Bool)
    (records : List (List Bool × List Bool)) (D : ℕ) (regs : Fin 16 → Bool) (d : Data)
    (rs : Fin 8 → Bool)
    (hd : d.stacks = fun i =>
      if i = 6 then ProgramEncoding.encodeRecords (inverseQueries D)
      else if i = 7 then SelectorProgram.rawRecords records
      else (outputState input blocks leftovers metadata (SelectorProgram.rawRecords records) storage [] regs).stacks i) :
    (install (by decide : 8 ≤ 16) (by decide : 9 ≤ 48) d
      (SelectorMapProgram.outputState records (inverseQueries D) rs)).stacks = fun i =>
      if i = 7 then SelectorProgram.rawRecords records
      else if i = 8 then ProgramEncoding.encodeRecords (inverseRows records D)
      else (outputState input blocks leftovers metadata (SelectorProgram.rawRecords records) storage [] regs).stacks i := by
  funext i
  fin_cases i <;>
    simp [install, hd, SelectorMapProgram.outputState, SelectorMapProgram.state,
      outputState, inputState, inverseRows, Fin.coe_ofNat_eq_mod]

end SubexponentialSAT.Subexp.PackingProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_Subexp_PackingLeftoverStage
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Actual generation of ascending vertex indices and the leftover scan in
the fixed packing controller. -/

namespace SubexponentialSAT.Subexp.PackingProgram

open BitProgram StructuredCalls PackingProgramSupport

def verticesOutputState (input : Input) (n D : ℕ) (c : PackingExtraction.Context)
    (regs : Fin 16 → Bool) : Data :=
  ⟨regs, fun i => if i = 7 then AssignmentSeedRange.seedRecords D
    else (extractionOutputState input n c regs).stacks i⟩

def verticesBudget (D : ℕ) : ℕ :=
  7 * D + AssignmentSeedRange.budget D +
    6 * (AssignmentSeedRange.seedRecords D).length + 12

theorem leftovers_call_stacks (input : Input) (n D : ℕ)
    (c : PackingExtraction.Context) (records : PackingLeftovers.Records)
    (result : PackingLeftovers.Snapshot) (regs : Fin 16 → Bool) (rl : Fin 8 → Bool) :
    (install (by decide : 8 ≤ 16) (by decide : 18 ≤ 48)
      (verticesOutputState input n D c regs)
      (PackingLeftovers.state rl (SelectorProgram.rawRecords records) []
        (PackingLeftovers.unary result.rank) (PackingLeftovers.unary result.address)
        result.storage result.metadata result.addresses)).stacks = fun i =>
          if i = 6 then SelectorProgram.rawRecords records
          else if i = 10 then PackingLeftovers.unary result.rank
          else if i = 11 then PackingLeftovers.unary result.address
          else if i = 12 then result.storage
          else if i = 13 then result.metadata
          else if i = 14 then result.addresses
          else if i = 30 then List.replicate n true
          else (inputState input regs).stacks i := by
  funext i
  fin_cases i <;>
    simp [install, verticesOutputState, extractionOutputState, inputState,
      PackingLeftovers.state, PackingLeftovers.data, Fin.coe_ofNat_eq_mod]

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

namespace Spec

variable {U : Type*} [DecidableEq U]

def outputState (s : Spec U) (regs : Fin 16 → Bool) : PackingProgramSupport.Data :=
  PackingProgram.outputState s.params.input
    (List.replicate s.packing.blockCount true) (List.replicate s.packing.leftovers.length true)
    s.metadata s.addresses s.storage s.inverse regs

end Spec

variable {U : Type*} [DecidableEq U]

theorem context_metadata (s : Spec U) :
    (context s).metadata = SelectorProgram.rawRecords (covered s) := by
  have h := PackingExtraction.typed_extraction_metadata s.packing s.encodeVertex s.encodeType
    (PackingProgram.initialExtraction (entries s) s.packing.blockCount) rfl
  simpa only [context, PackingProgram.extracted, entries, covered,
    PackingProgram.initialExtraction, List.append_nil] using h

theorem context_address (s : Spec U) :
    (context s).address = List.replicate (context s).address.length true := by
  have h := PackingExtraction.advanceMany_address_unary (entries s) s.packing.blockCount 0
    (PackingProgram.initialExtraction (entries s) s.packing.blockCount) 0 rfl
  change (context s).address = _ at h
  rw [h]
  simp [PackingMetadata.unary]

def budget (s : Spec U) : ℕ :=
  PackingProgram.bucketsBudget (records s) (keys s) s.params.D +
  PackingProgram.extractionBudget (entries s) s.packing.blockCount +
  PackingProgram.verticesBudget s.params.D +
  PackingProgram.leftoversBudget (covered s) s.params.D (context s) +
  PackingProgram.inverseBudget (addressRecords s) s.params.D + 1

theorem leftover_outputs (s : Spec U) :
    let result := PackingProgram.leftoverResult (covered s) s.params.D (context s)
    result.metadata = s.metadata ∧ result.addresses = s.addresses ∧
    result.storage.reverse ++ [false] = s.storage ∧ result.rank = s.packing.leftovers.length := by
  have h := PackingOutputSemantics.finish_extraction_outputs s.packing Fin.val s.encodeType
    Fin.val_injective (PackingProgram.initialExtraction (entries s) s.packing.blockCount)
    rfl rfl rfl rfl rfl
  have he : PackingProgram.leftoverResult (covered s) s.params.D (context s) =
      PackingOutputSemantics.finish s.packing Fin.val s.encodeType
        (PackingOutputSemantics.snapshotOf (context s)) := by
    simp only [PackingProgram.leftoverResult, PackingOutputSemantics.finish, Spec.packing,
      List.map_coe_finRange] ; rfl
  change (PackingOutputSemantics.finish s.packing Fin.val s.encodeType
      (PackingOutputSemantics.snapshotOf (context s))).metadata = _ ∧ _ at h
  dsimp only
  simp only [he]
  refine ⟨h.1, h.2.2.1, ?_, h.2.2.2.1⟩
  have hstorage : (PackingOutputSemantics.finish s.packing Fin.val s.encodeType
      (PackingOutputSemantics.snapshotOf (context s))).storage =
      (PackingExtraction.vertexPrefix
        ((PackingReorder.storageVertices s.packing).map s.encodeVertex)).reverse := h.2.1
  rw [hstorage, List.reverse_reverse]
  exact (SelectorMapProgram.encodeRecords_eq_prefix
    ((PackingReorder.storageVertices s.packing).map s.encodeVertex)).symm

end SubexponentialSAT.SqrtLog.LayoutProgram.PackLabels

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LayoutProgramNativePacking
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! End-to-end physical packing from runtime word rows and native address
plans. Both labels and the full universal type list are generated before the
bucket/block/leftover controller runs. -/
namespace SubexponentialSAT.SqrtLog.LayoutProgram.NativePacking

open SubexponentialSAT.Subexp SubexponentialSAT.Subexp.ConstructivePacking SubexponentialSAT.MulticolorTypes
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls

abbrev command : Cmd 16 48 := .seq (.call NativeFrontend.program) (.call PackLabels.program)
def program := compiled command 25 32

def budget {U : Type*} [DecidableEq U] (s : Spec U) : ℕ :=
  s.params.labelsBound+s.params.typesBound+PackLabels.budget s.suffix+2

end SubexponentialSAT.SqrtLog.LayoutProgram.NativePacking

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SubexpKernelControl
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
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

/-! ## Fixed source-constructor control -/

/-! ## Concrete machine states and elementary traces -/

def counterWord (i : Fin 3) (a : Accumulator) : Word :=
  if i = 0 then a.outer else if i = 1 then a.groups else a.terms

/-! The following induction rule accounts for actual executions of the fixed
payload body. Its premises will be proved for `termBody`, `groupBody`, and
`blockBody`; the exported whole-controller statement has no callback argument. -/

/-! ## Forward-output service boundary -/

end SubexponentialSAT.SubexpKernelControl

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

def pop (src : Fin 32) : Code := .base (.atom (.pop src 7 0))

def sealCall : Code := liftCommand CollisionStreamProgram.sealCommand 1 11 smallRegs sealPorts

end SubexponentialSAT.Subexp.GlobalBasisEntryCore

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

def stageEmitter : Code := Staging.sequence 0 1 319 stageEmitterOps

end SubexponentialSAT.SqrtLog.LayoutProgram.SourceBank

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_PackingIncidenceInputNative
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms


/-! Convert a physically scanned factor-index stream to incidence plans. -/


/-! Native per-variable incident-factor scan from the original scope stream. -/


/-! Fixed cleanup for the native scope-address scanner. -/
namespace SubexponentialSAT.SqrtLog.PackingIncidenceInput
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.Subexp

namespace Clear
abbrev Data := Scan.Data
end Clear
end SubexponentialSAT.SqrtLog.PackingIncidenceInput


/-! Calls to the fixed record mapper inside the native scope scan. -/


/-! One native low-variable step, including its uncovered neutral factor. -/


/-! Runtime high-mask loop for the original-address incidence stream. -/


/-! Count the physical scope stream before constructing native incidence plans. -/

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_RingProgramTableModel
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.RingProgramTable

open SubexponentialSAT.BitProgram SubexponentialSAT.SubexpLiftRing SubexponentialSAT.SubexpQuarticRing

def modelTable (t : ℕ) {d : ℕ} (a : RingModel.Data d)
    (M : SubexpPreparedQuartic.Modulus 3 t) (cache : RingProgram.ScalarCache 3 t) : List Bool :=
  RingTriple.tableEncoding (RingProgram.structureTableRun (RingProgram.scalarProgram 3 t M cache)
    (RingProgram.liftCoefficientsRun t a.coefficients).1).1

end SubexponentialSAT.SqrtLog.RingProgramTable

end OAI.Algorithms
end


