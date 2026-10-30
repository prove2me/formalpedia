-- Prove2me | Definitions.Def_OAIQ081S085
-- name    : OAIQ081S085
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-29T22:06:45.137318+00:00
-- url     : https://prove2.me/theorems/95d97348-a48e-4fe3-98c0-8ecfc9194911
-- title:
--   Definitions bundle OAIQ081S085 of the split of OpenAI, The Exponential Time Hypothesis is False
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.exact_count_and_sat`, carved from OpenAI's openai/math development (OpenAI, *The Exponential Time Hypothesis is False*, OpenAI Math Release, October 25, 2026, result family 378, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 123 declarations of OpenAI's Lean: 115 definitions and 8 theorems. The definitions and types are `OAI.Algorithms.SubexponentialSAT.SqrtLog.HashScopeProgram.Complete.seed`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.HashScopeProgram.FromTuple.Data`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.HashScopeProgram.FromTuple.clearEll`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.HashScopeProgram.FromTuple.extend`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.HashScopeProgram.FromTuple.scopeState`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.HashScopeProgram.Marked.clearEll`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.HashScopeProgram.Marked.clearIndex`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.HashScopeProgram.Marked.fetch`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.HashScopeProgram.Marked.moveScope`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.HashScopeProgram.Marked.popFlag`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.HashScopeProgram.Marked.prepareScope`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.HashScopeProgram.RawTable.Data`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.HashScopeProgram.RawTable.data`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.HashScopeProgram.RawTable.state`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.HashScopeProgram.RawTable.takeInput`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.HashScopeProgram.RawTable.takeOutput`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.HashScopeProgram.Single.flatten`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.HashScopeProgram.Single.initializeCmd`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.HashScopeProgram.Single.restore`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.HeadScatterProgram.Data`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.HeadScatterProgram.command`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.HeadScatterProgram.input`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.HeadScatterProgram.program`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.HeadScatterProgram.ready`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.HeadScatterProgram.result`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.HeadScatterProgram.state`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.HighIncidenceProgram.Branches.Data`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.HighIncidenceProgram.Cutoff.Code`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.HighIncidenceProgram.Cutoff.Data`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.HighIncidenceProgram.Cutoff.command`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.HighIncidenceProgram.Cutoff.state`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.HighIncidenceProgram.Data`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.HighIncidenceProgram.Mass.Code`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.HighIncidenceProgram.Mass.Data`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.HighIncidenceProgram.Mass.callback`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.HighIncidenceProgram.Mass.counter`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.HighIncidenceProgram.Mass.invariant`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.HighIncidenceProgram.Mass.program`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.HighIncidenceProgram.Mass.read`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.HighIncidenceProgram.Mass.state` and 75 more.
--
--   **Sources.** They come from these modules of lean/OAI/Algorithms, in whole or in part: `SubexponentialSAT_SqrtLog_HashScopeProgramFromTuple`, `SubexponentialSAT_SqrtLog_HashScopeProgramMarkedSource`, `SubexponentialSAT_SqrtLog_HashScopeProgramMarkedStep`, `SubexponentialSAT_SqrtLog_HashScopeProgramMarkedTableCalls`, `SubexponentialSAT_SqrtLog_HashScopeProgramRawCall`, `SubexponentialSAT_SqrtLog_HashScopeProgramRawLoop`, `SubexponentialSAT_SqrtLog_HashScopeProgramSingle`, `SubexponentialSAT_SqrtLog_HeadScatterProgram`, `SubexponentialSAT_SqrtLog_HeadScatterProgramInit`, `SubexponentialSAT_SqrtLog_HeadScatterProgramRun`, `SubexponentialSAT_SqrtLog_HeadScatterProgramScan`, `SubexponentialSAT_SqrtLog_HighIncidenceProgram`, `SubexponentialSAT_SqrtLog_HighIncidenceProgramBranches`, `SubexponentialSAT_SqrtLog_HighIncidenceProgramCutoff`, `SubexponentialSAT_SqrtLog_HighIncidenceProgramMass`, `SubexponentialSAT_SqrtLog_HighIncidenceProgramMassPreserve`, `SubexponentialSAT_SqrtLog_HighIncidenceProgramPrepareOps`, `SubexponentialSAT_SqrtLog_HighIncidenceProgramRestriction`, `SubexponentialSAT_SqrtLog_IdempotentApplyProgramMachine`, `SubexponentialSAT_SqrtLog_IdempotentApplyProgramReadScalar`, `SubexponentialSAT_SqrtLog_IdempotentApplyProgramReadScalarBasic`, `SubexponentialSAT_SqrtLog_IdempotentApplyProgramScalar`, `SubexponentialSAT_SqrtLog_IdempotentPreparationProgramArrays`, `SubexponentialSAT_SqrtLog_IdempotentPreparationProgramLog`, `SubexponentialSAT_SqrtLog_IdempotentPreparationProgramScalarCore`, `SubexponentialSAT_SqrtLog_IdempotentProgramRegisters`, `SubexponentialSAT_SqrtLog_IdempotentProgramService`, `SubexponentialSAT_SqrtLog_LayoutProgramScalarCacheCell`, `SubexponentialSAT_SqrtLog_MomentsProgramProduct`, `SubexponentialSAT_SqrtLog_SetupPrimitives`, `SubexponentialSAT_SqrtLog_SquarefreeProgramStorage`, `SubexponentialSAT_SubexpCeilingProgram`, `SubexponentialSAT_SubexpChunkRecordMap`, `SubexponentialSAT_SubexpClauseMastersProgram`, `SubexponentialSAT_SubexpFactorCountSetup`, `SubexponentialSAT_SubexpIncidencePlanPrimitives`, `SubexponentialSAT_SubexpIncidencePlanScan`, `SubexponentialSAT_SubexpIncidenceSlotProgram`, `SubexponentialSAT_SubexpLiteralChunkProgram`, `SubexponentialSAT_SubexpScopeCountSetup`, `SubexponentialSAT_SubexpScopeProducer`.
--
--   **Imports.** It imports the published bundle `Def_SubexponentialSAT`; the bundles `OAIQ081S066`, `OAIQ081S067`, `OAIQ081S069` and `OAIQ081S070` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ081S102`, `OAIQ081S103`, `OAIQ081S104`, `OAIQ081S105`, `OAIQ081S106`, `OAIQ081S107`, `OAIQ081S108`, `OAIQ081S109`, `OAIQ081S110`, `OAIQ081S112`, `OAIQ081S113`, `OAIQ081S114` and `OAIQ081S115`; the statements `OAI.Algorithms.SubexponentialSAT.SqrtLog.HeadScatterProgram.program_runsIn`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.HighIncidenceProgram.MassPreserve.command_eval`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.HighIncidenceProgram.Prepare.cutoff_eval`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.IdempotentApplyProgram.Multiplier.shiftU_eval` and `OAI.Algorithms.SubexponentialSAT.SqrtLog.IdempotentApplyProgram.ReadScalar.emit_eval`; the proofs of `OAI.Algorithms.SubexponentialSAT.SqrtLog.HeadScatterProgram.program_runsIn`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.HighIncidenceProgram.MassPreserve.command_eval`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.HighIncidenceProgram.Prepare.cutoff_eval` and `OAI.Algorithms.SubexponentialSAT.SqrtLog.IdempotentApplyProgram.ReadScalar.emit_eval`.
-- source:
--   OpenAI, The Exponential Time Hypothesis is False, OpenAI Math Release, October 25, 2026, https://github.com/openai/math (result family 378; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/The-Exponential-Time-Hypothesis-is-False-October-25-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Algorithms at commit 7ef5c0c

import Mathlib
import Definitions.Def_SubexponentialSAT
import Definitions.Def_OAIQ081S066
import Definitions.Def_OAIQ081S067
import Definitions.Def_OAIQ081S069
import Definitions.Def_OAIQ081S070

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

abbrev decode : Cmd 8 19 := .call (ProgramLinking.liftProgram
  SubexpClauseRowProgram.LiteralDecoder.program decodeRegisters decodeStacks)

abbrev count : Cmd 8 19 := .seq (.base (.atom (.set 2 false)))
  (.call (ProgramLinking.liftProgram CounterPrograms.lengthProgram lengthRegisters lengthStacks))

abbrev divide : Cmd 8 19 := .call (ModularQuotientLift.programAt divisionPorts)

abbrev encode : Cmd 8 19 := .call (ProgramLinking.liftProgram
  CounterConversions.encodeNatProgram conversionRegisters conversionStacks)

abbrev reverseField : Cmd 8 19 := .call (transferProgram 10 9 0 1)

abbrev reset : Cmd 8 19 := .base (straight resetOps)

end SubexponentialSAT.SubexpLiteralChunkProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SubexpChunkRecordMap
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# Actual map from literal records to chunk records

The input is the canonical encoded list of literal codes and a preserved binary
chunk width. Each parsed record passes through the actual index decoder,
counter, division program, and record writer. The accumulator is reversed, as
required by the separately checked record-reversal and stable-deduplication
passes. No semantic map is installed as a machine instruction.
-/

namespace SubexponentialSAT.SubexpChunkRecordMap

open BitProgram StructuredCalls

abbrev emit : Cmd 11 22 := .call (ProgramLinking.liftProgram
  SubexpNormalizeProgram.emitIfSelectedProgram emitRegisters emitStacks)

abbrev select : Cmd 11 22 := .base (.atom (.set 10 true))

end SubexponentialSAT.SubexpChunkRecordMap

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SubexpScopeProducer
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# Construct a clause's local chunk scope from its encoded literals

This fixed program maps actual literal records to chunk records, restores the
record order, and invokes the checked stable deduplicator. Its output order is
the last-occurrence order used by the materializer and incidence-plan producer.
-/

namespace SubexponentialSAT.SubexpScopeProducer

open BitProgram StructuredCalls SubexpChunkRecordMap

abbrev initializeOutput : Cmd 11 22 := .base (.atom (.push 20 0))
abbrev seedSource : Cmd 11 22 := .base (.atom (.push 19 0))

abbrev reverse : Cmd 11 22 := .call (ProgramLinking.liftProgram
  SubexpNormalizeProgram.reverseRecordsProgram emitRegisters reverseStacks)

abbrev dedup : Cmd 11 22 := .call (ProgramLinking.liftProgram
  ExecLiteralDedupProgram.dedupProgram dedupRegisters dedupStacks)

end SubexponentialSAT.SubexpScopeProducer

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_HashScopeProgramSingle
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! One fixed program turns a physically materialized weighted raw row into
its deduplicated original-variable scope. All constant initialization is paid. -/
namespace SubexponentialSAT.SqrtLog.HashScopeProgram.Single
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls
open SubexponentialSAT.Subexp.BlockSearchPreparation (restrictState )

abbrev flatten : Cmd 11 22 := .call (ProgramLinking.liftProgram Flatten.program registers stackPorts)

abbrev restore : Cmd 11 22 := .seq (.call (StackRoutines.transferProgram 20 21 8 9))
  (.call (StackRoutines.transferProgram 21 19 8 9))

abbrev initializeCmd : Cmd 11 22 := .seq (SubexponentialSAT.Subexp.TupleProgram.pushConst 18 8 true)
  (SubexponentialSAT.Subexp.TupleProgram.pushConst 20 8 false)

end SubexponentialSAT.SqrtLog.HashScopeProgram.Single

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_HashScopeProgramFromTuple
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Direct original-source-to-scope composition. The finite program first reads
raw tuple references and looks up original clauses, then extracts their scope.
No table of precomputed scopes is supplied to this machine. -/
namespace SubexponentialSAT.SqrtLog.HashScopeProgram.FromTuple
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls
open SubexponentialSAT.Subexp.BlockSearchPreparation (restrictState )

abbrev Data := State 11 46

def extend (a : State 8 24) : Data :=
  ⟨fun i => if h : i.val < 8 then a.regs ⟨i.val,h⟩ else false,
    fun i => if h : i.val < 24 then a.stacks ⟨i.val,h⟩ else []⟩

abbrev clearEll : Cmd 11 46 := .call (StackRoutines.clearProgram 42 8 9)


def scopeState (rf : Fin 11 → Bool) (a : Data) (bits : List Bool) : Data :=
  ⟨rf,fun i => if i=16 then bits else if i=42 then [true] else a.stacks i⟩

end SubexponentialSAT.SqrtLog.HashScopeProgram.FromTuple

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

abbrev fetch : Cmd 11 80 := .call (ProgramLinking.liftProgram HashInputProgram.Source.fetchProgram sourceRegisters sourceStacks)

abbrev prepareScope : Cmd 11 80 := .seq (SubexponentialSAT.Subexp.TupleProgram.pushConst 72 8 true) Reset.all

end SubexponentialSAT.SqrtLog.HashScopeProgram.Marked

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_HashScopeProgramMarkedStep
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! The marked branch appends one scope even when that scope is empty. -/
namespace SubexponentialSAT.SqrtLog.HashScopeProgram.Marked
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls


abbrev clearEll : Cmd 11 80 := .call (StackRoutines.clearProgram 72 8 9)
abbrev moveScope : Cmd 11 80 := .call (StackRoutines.transferProgram 73 47 8 9)

abbrev clearIndex : Cmd 11 80 := .call (StackRoutines.clearProgram 49 8 9)

abbrev popFlag : Cmd 11 80 := .base (.atom (.pop 50 8 9))

end SubexponentialSAT.SqrtLog.HashScopeProgram.Marked

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_HashScopeProgramRawCall
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! One callback for the actual raw-row table. The original clause master,
word width, modulus and ring shape are persistent; all workspace is cleaned. -/
namespace SubexponentialSAT.SqrtLog.HashScopeProgram.RawTable
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls
open SubexponentialSAT.Subexp.BlockSearchPreparation (restrictState )

abbrev Data := State 11 49

def data (rf : Fin 11 → Bool)
    (raw width modulus master shape scopeWire source pay out tmp : List Bool) : Data :=
  ⟨rf,fun i => if i=0 then raw else if i=1 then width else if i=7 then modulus
    else if i=14 then master else if i=15 then shape else if i=16 then scopeWire
    else if i=45 then tmp else if i=46 then source else if i=47 then pay
    else if i=48 then out else []⟩

abbrev takeInput : Cmd 11 49 := .seq (.call (StackRoutines.transferProgram 47 45 8 9))
  (.call (StackRoutines.transferProgram 45 0 8 9))

abbrev takeOutput : Cmd 11 49 := .call (StackRoutines.transferProgram 16 47 8 9)

end SubexponentialSAT.SqrtLog.HashScopeProgram.RawTable

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_HashScopeProgramRawLoop
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Fixed outer scanner for a table of raw tuple payloads. -/
namespace SubexponentialSAT.SqrtLog.HashScopeProgram.RawTable
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls



def state (rf : Fin 11 → Bool) (width modulus master shape source pay out : List Bool) : Data :=
  data rf [] width modulus master shape [] source pay out []

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

abbrev seed : Cmd 11 80 := SubexponentialSAT.Subexp.TupleProgram.pushConst 46 8 false

end SubexponentialSAT.SqrtLog.HashScopeProgram.Complete

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

abbrev Data := State 8 13

/-- The three persistent input stacks are 10, 11, 12. Working stacks are the
ambient mask 0, remaining bits 1, remaining identifiers 2, unary identifier 3,
replacement bit 4, constant width 5, and four array-scan workspaces 6--9. -/
def state (regs : Fin 8 → Bool) (saved : Fin 3 → List Bool)
    (js : List ℕ) (bits mask : List Bool) : Data :=
  ⟨regs, ![mask,bits,indices js,[],[],[true],[],[],[],[],saved 0,saved 1,saved 2]⟩

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

def input (regs : Fin 8 → Bool) (js : List ℕ) (bits : List Bool) (n : ℕ) : Data :=
  ⟨regs, ![[],[],[],[],[],[],[],[],[],[],indices js,bits,unary n]⟩

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

def ready (regs : Fin 8 → Bool) (saved : Fin 3 → List Bool)
    (js : List ℕ) (bits mask : List Bool) : Data :=
  state (readRegs regs 0 1 bits.head?) saved js bits mask

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

def command : Code := .seq initCommand (.seq scanCommand finishWidth)
abbrev program : Program 8 13 (size command+1) := compiled command 10 0

def result (regs : Fin 8 → Bool) (js : List ℕ) (bits : List Bool) (n : ℕ) : Data :=
  ⟨regs, ![mask n js bits,[],[],[],[],[],[],[],[],[],indices js,bits,unary n]⟩

end SubexponentialSAT.SqrtLog.HeadScatterProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SubexpIncidencePlanPrimitives
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Fixed unary-counter and record-emission instructions for incidence plans. -/
namespace SubexponentialSAT.SubexpIncidencePlanPrimitives

open BitProgram StructuredCalls

abbrev emit : Cmd 10 10 :=
  .call (ProgramLinking.liftProgram SubexpNormalizeProgram.emitIfSelectedProgram emitReg emitStack)

end SubexponentialSAT.SubexpIncidencePlanPrimitives

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SubexpIncidencePlanScan
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! A fixed finite scan of encoded scopes. No slot map is supplied as input:
the local slot order is the encounter order of incident factors. -/
namespace SubexponentialSAT.SubexpIncidencePlanScan

open BitProgram StructuredCalls
open SubexpIncidencePlanPrimitives

abbrev callback : Cmd 10 10 :=
  .seq SubexpScopeMembershipProgram.command
    (.seq addDegree (.seq (copy 5 1 3) (.seq emit (increment 5))))

abbrev command : Cmd 10 10 := RecordPrograms.iterate ports callback

end SubexponentialSAT.SubexpIncidencePlanScan

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SubexpIncidenceSlotProgram
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# Physical local-slot query

The three preserved inputs are the encoded scope family and unary factor and
vertex indices. A real mask pass selects the preceding factors, and the checked
incidence scan counts them. No slot map or selected prefix is supplied as input.
-/

namespace SubexponentialSAT.SubexpIncidenceSlotProgram

open BitProgram StructuredCalls

def scan : Code := liftCommand SubexpIncidencePlanScan.command 6 9 id scanPort

def command : Code := .seq prepare (.seq selectPrefix (.seq makeQuery (.seq scan finish)))
def program := compiled command 0 3

end SubexponentialSAT.SubexpIncidenceSlotProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_HighIncidenceProgram
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# Physical high-incidence selection from supplied explicit scopes

The input is a framed list of scopes with original natural-number identifiers.
Every query invokes the audited source-preserving record/membership scan. The
cutoff is a supplied unary integer in this module; no arithmetic or translation
from clauses to scopes is silently performed. The fixed program appends the
strict comparison bit and advances the original-coordinate counter.
-/
namespace SubexponentialSAT.SqrtLog.HighIncidenceProgram

open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls

abbrev Data := State 10 16

end SubexponentialSAT.SqrtLog.HighIncidenceProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_HighIncidenceProgramBranches
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Runtime Boolean branch initialization and exhaustive odometer traces.
The only parameter in the enumeration command is its fixed real callback.
The high dimension is data, not finite control. -/
namespace SubexponentialSAT.SqrtLog.HighIncidenceProgram.Branches
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls

abbrev Data := State 2 2

end SubexponentialSAT.SqrtLog.HighIncidenceProgram.Branches

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SubexpCeilingProgram
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# The actual binary program for the packed dimension

Binary long division yields quotient and remainder. A finite zero test and
conditional increment then produce the ceiling. The input-dependent values are
stack words throughout; the control table is fixed.
-/

namespace SubexponentialSAT.SubexpCeilingProgram

open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredProgram SubexponentialSAT.BinaryArithmetic
open SubexponentialSAT.ModularQuotientArithmetic

abbrev command : StructuredCalls.Cmd 8 8 :=
  .seq (.call ModularQuotientPrograms.quotientProgram) CeilingDivisionPrograms.roundCmd

def program := StructuredCalls.compiled command (6 : Fin 8) 7

end SubexponentialSAT.SubexpCeilingProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_HighIncidenceProgramCutoff
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Actual runtime multiplication and ceiling division for the high-incidence
integer threshold. Inputs are binary S,t,n; the output is binary ceil(S*t/n).
Counting S from scope records and converting the result to unary are separate
physical frontend obligations, not operations hidden in this specification. -/
namespace SubexponentialSAT.SqrtLog.HighIncidenceProgram.Cutoff
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.BinaryArithmetic

abbrev Data := State 8 12
abbrev Code := Cmd 8 12

def state (regs : Fin 8 → Bool) (mass scale dimension : List Bool) : Data :=
  ⟨regs, ![mass, scale, dimension, [], [], [], [], [], [], [], [], []]⟩

def command : Code := .seq (ArithmeticCalls.multiplyAt ports)
  (.call (ProgramLinking.liftProgram SubexpCeilingProgram.program id ceilingPorts))

end SubexponentialSAT.SqrtLog.HighIncidenceProgram.Cutoff

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SubexpFactorCountSetup
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# Preserving setup of a factor-local assignment count

The fixed program copies a unary arity, counts the copy into a binary exponent,
and invokes the actual preserving power routine.  The base and unary arity are
retained verbatim.  The number of bits in either input is runtime data.
-/

namespace SubexponentialSAT.SubexpFactorCountSetup

open BitProgram StructuredCalls StackRoutines

abbrev resetAccumulator : Cmd 8 13 := .base (.atom (.set 2 false))

abbrev countCommand : Cmd 8 13 :=
  .seq (ArithmeticCalls.copyAt 1 4 5)
    (.seq resetAccumulator (.call lengthProgram))

end SubexponentialSAT.SubexpFactorCountSetup

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SubexpScopeCountSetup
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Actual preserving scope-record count and assignment-fuel setup.
The scope and base remain on stacks 1 and 0. The program returns unary arity,
binary exponent, and binary base^arity on stacks 2, 3, and 4. -/

namespace SubexponentialSAT.SubexpScopeCountSetup

open BitProgram StructuredCalls

abbrev countCall : Cmd 8 15 := .call (ProgramLinking.liftProgram counterProgram counterReg counterStack)

abbrev countCommand : Cmd 8 15 := .seq (ArithmeticCalls.copyAt 1 14 5) countCall

end SubexponentialSAT.SubexpScopeCountSetup

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_HighIncidenceProgramMass
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Actual two-level record scan counting explicit scope entries. The ghost
payload decoder occurs only in the loop specification; the executable callback
uses the existing physical record counter. -/
namespace SubexponentialSAT.SqrtLog.HighIncidenceProgram.Mass
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls

abbrev Data := State 5 4
abbrev Code := Cmd 5 4

def state (regs : Fin 5 → Bool) (source payload acc work : List Bool) : Data :=
  ⟨regs, ![source, payload, acc, work]⟩

def counter : Code := .call (ProgramLinking.liftProgram
  SubexpScopeCountSetup.counterProgram registers counterPorts)

def transfer : Code := .call (StackRoutines.transferProgram 1 3 0 1)
def callback : Code := .seq transfer counter

def invariant (d : Data) : Prop := ∃ regs acc, d = state regs [] [] acc []
def read (d : Data) := d.stacks 2

def program := LeafProgram.foldProgram ports callback

end SubexponentialSAT.SqrtLog.HighIncidenceProgram.Mass

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SubexpClauseMastersProgram
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# Physical preparation of the shared clause-factor masters

Four preserved binary input words supply the declared variable count, chunk
width, field modulus, and chunk count. Copies of the three counts are converted
by the checked binary-to-unary program. The checked full-shape capture then
builds the padded-array shape. No desired shape is an input assumption.

The modulus-width shape is a physical copy of the modulus word: its consumers
use its length, not its bits. The other two copies supply the binary chunk
width and field modulus at the clause-family's own persistent ports.
-/

namespace SubexponentialSAT.SubexpClauseMastersProgram

open BitProgram StructuredCalls

abbrev copy (src dst : Fin 14) : Cmd 3 14 :=
  .call (StackRoutines.copyProgram src dst 13 0 1)

abbrev makeUnary (dst : Fin 14) : Cmd 3 14 :=
  .call (ProgramLinking.liftProgram CounterConversions.unaryProgram id (unaryPorts dst))

abbrev unaryCopy (src dst : Fin 14) : Cmd 3 14 :=
  .seq (copy src 11) (makeUnary dst)

end SubexponentialSAT.SubexpClauseMastersProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_HighIncidenceProgramMassPreserve
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Preserving wrapper around the actual nested record counter. -/
namespace SubexponentialSAT.SqrtLog.HighIncidenceProgram.MassPreserve
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls

abbrev Data := State 8 5
abbrev Code := Cmd 8 5
def state (regs : Fin 8 → Bool) (source acc : List Bool) : Data :=
  ⟨regs, ![source, [], acc, [], []]⟩

def reset : Code := .seq (.base (.atom (.set 2 false)))
  (.seq (.base (.atom (.set 3 true))) (.base (.atom (.set 4 false))))

def command : Code := .seq (ArithmeticCalls.copyAt 0 4 3)
  (.seq reset (.call (ProgramLinking.liftProgram Mass.program regs stackPorts)))

end SubexponentialSAT.SqrtLog.HighIncidenceProgram.MassPreserve

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_HighIncidenceProgramPrepareOps
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Fixed ports for the physical high-incidence prefix. Each operation below
is a genuine call to an already verified finite program. -/
namespace SubexponentialSAT.SqrtLog.HighIncidenceProgram.Prepare
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.BinaryArithmetic

abbrev Data := State 10 32
abbrev Code := Cmd 10 32

def countCall : Code := liftCommand SubexpScopeCountSetup.countCommand 1 2 reg8 countPorts
def massCall : Code := liftCommand MassPreserve.command 0 2 reg8 massPorts
def binaryCall : Code := liftCommand SubexpFactorCountSetup.countCommand 1 2 reg8 binaryPorts
def cutoffCall : Code := liftCommand Cutoff.command 0 5 reg8 cutoffPorts
def unaryCall : Code := liftCommand (SubexpClauseMastersProgram.unaryCopy 0 1) 0 1 reg3 unaryPorts
def fuelCall : Code := liftCommand (SubexpClauseMastersProgram.unaryCopy 0 1) 0 1 reg3 fuelPorts
def bump : Code := .seq (.base (.atom (.set 0 true))) (.base (.atom (.push 13 0)))

end SubexponentialSAT.SqrtLog.HighIncidenceProgram.Prepare

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_HighIncidenceProgramRestriction
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Physical merge of high and free Boolean assignments in original order.
This routine never renames a variable or drops an unused coordinate. -/
namespace SubexponentialSAT.SqrtLog.HighIncidenceProgram.Restriction
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls

abbrev Data := State 4 4

end SubexponentialSAT.SqrtLog.HighIncidenceProgram.Restriction

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_SquarefreeProgramStorage
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Port relocation and paid bit-copy primitives for the dictionary builder. -/
namespace SubexponentialSAT.SqrtLog.Squarefree.Program
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls
open SubexponentialSAT.SubexpRecordScan

abbrev StorageData := State 5 7

def extendStorage (d : State 5 6) (saved : List Bool) : StorageData :=
  ⟨d.regs, ![d.stacks 0,d.stacks 1,d.stacks 2,d.stacks 3,d.stacks 4,d.stacks 5,saved]⟩

@[simp] theorem extendStorage_saved (d : State 5 6) (saved : List Bool) :
    (extendStorage d saved).stacks 6 = saved := rfl

end SubexponentialSAT.SqrtLog.Squarefree.Program

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

abbrev Data := State 8 56

end SubexponentialSAT.SqrtLog.MomentsProgram.Product


end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_IdempotentPreparationProgramArrays
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Real allocation of the padded Newton arrays. Prefix coefficient words are
computed scalar cache entries; the zero suffix is generated by native copying
from one zero word and a runtime unary dimension. -/
namespace SubexponentialSAT.SqrtLog.IdempotentPreparationProgram

open BitProgram StructuredCalls SubexpScanPrimitives

abbrev popCount : Cmd 8 41 := .base (.atom (.pop 1 0 1))

def popCounts : ℕ → Cmd 8 41
  | 0 => .base .skip
  | n+1 => .seq popCount (popCounts n)

abbrev paddedZeros (target : Fin 41) (drop : ℕ) : Cmd 8 41 :=
  .seq (.call (StackRoutines.copyProgram 37 1 2 (0 : Fin 8) 1))
    (.seq (popCounts drop) (repeatAt 17 target 2 1))

abbrev negativeOneArray : Cmd 8 41 :=
  .seq (paddedZeros 36 1)
    (.call (StackRoutines.copyProgram 28 36 2 (0 : Fin 8) 1))

end SubexponentialSAT.SqrtLog.IdempotentPreparationProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_IdempotentApplyProgramScalar
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Native injection of a base coefficient into the first coordinate of an
extension-ring coefficient. The remaining coordinates are physically copied
from the canonical zero word. -/
namespace SubexponentialSAT.SqrtLog.IdempotentApplyProgram

open scoped BigOperators
open BitProgram StructuredCalls SubexpQuarticRing SubexpScanPrimitives
open IdempotentPreparationProgram

abbrev injectScalar : Cmd 8 41 :=
  .seq (paddedZeros 32 1) (.call (StackRoutines.copyProgram 31 32 2 (0 : Fin 8) 1))

end SubexponentialSAT.SqrtLog.IdempotentApplyProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_IdempotentApplyProgramReadScalarBasic
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Scalar loading uses only checked stack primitives and constant formatting.
This definition boundary keeps its correctness independent of polynomial arithmetic. -/
namespace SubexponentialSAT.SqrtLog.IdempotentApplyProgram
open BitProgram StructuredCalls
open HashCircuitProgram.Native

abbrev sequence (commands : List (Cmd 8 96)) : Cmd 8 96 :=
  commands.foldr Cmd.seq (.base .skip)

abbrev inject : Cmd 8 96 :=
  liftCommand injectScalar 31 32 id injectPorts

abbrev emitConstant (destination : Fin 96) : Cmd 8 96 :=
  .call (ProgramLinking.liftProgram HashCircuitProgram.Constant.program id
    (constantPorts destination))

/-- Taking a word from the reversed coefficient tape reverses just that word,
so stack80 receives the original forward scalar representation. -/
abbrev readScalar : Cmd 8 96 :=
  .seq (copy 12 82 83)
    (.call (ArrayPrograms.countedTransferProgram 82 79 80 (0 : Fin 8) 1))

abbrev scalarConstant (destination : Fin 96) : Cmd 8 96 := sequence
  [readScalar, inject, clear 80, copy 88 89 70, emitConstant destination]

end SubexponentialSAT.SqrtLog.IdempotentApplyProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_IdempotentApplyProgramMachine
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Fixed native control for applying computed idempotent coefficients.
The input and output ABI is documented below. The semantic execution theorem
is a separate obligation; this module supplies concrete instructions only. -/
namespace SubexponentialSAT.SqrtLog.IdempotentApplyProgram

open BitProgram StructuredCalls
open HashCircuitProgram.Native

abbrev makeUKey : Cmd 8 96 := sequence
  [copy 88 89 70,
   liftCommand HashCircuitProgram.Constant.pad 0 2 id uKeyPorts,
   liftCommand HashCircuitProgram.Constant.tag 2 2 id uKeyPorts,
   .base (.atom (.set 0 true)), .base (.atom (.push 91 0)),
   copy 91 94 70, clear 91]

abbrev shiftU : Cmd 8 96 :=
  .call (ProgramLinking.liftProgram Squarefree.KeyMapProgram.scanProgram id shiftPorts)

abbrev peekCoefficients : Cmd 8 96 := .base (.atom (.peek 79 0 7))

end SubexponentialSAT.SqrtLog.IdempotentApplyProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_IdempotentApplyProgramReadScalar
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Exact native refinements for the scalar coefficient reader and injector.
All stacks outside the named outputs are preserved, including the ambient
low-product environment. -/
namespace SubexponentialSAT.SqrtLog.IdempotentApplyProgram.ReadScalar
open BitProgram StructuredCalls
open HashCircuitProgram.Native

abbrev Machine := State 8 96

end SubexponentialSAT.SqrtLog.IdempotentApplyProgram.ReadScalar


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

theorem increment_eval (xs : List Bool) :
    Eval increment (CounterPrograms.rippleCost true xs + 1) (io xs) (io (ripple true xs)) := by
  have he := eval_call_lifted (CounterPrograms.rippleProgram true) id incrementPorts
    (io xs) Function.injective_id incrementPorts_injective
    (a := StructuredProgram.ioState (0 : Fin 2) xs)
    (b := StructuredProgram.ioState (0 : Fin 2) (ripple true xs))
    (CounterPrograms.ripple_terminal_trace true xs)
  have ha : embedState id incrementPorts (io xs)
      (StructuredProgram.ioState (0 : Fin 2) xs) = io xs := by
    apply embedState_eq_of_ports _ _ _ _ _ Function.injective_id incrementPorts_injective
    · intro i; rfl
    · intro i hi; exact False.elim (hi ⟨i, rfl⟩)
    · intro i; fin_cases i <;> rfl
    · intro i hi; rfl
  have hb : embedState id incrementPorts (io xs)
      (StructuredProgram.ioState (0 : Fin 2) (ripple true xs)) = io (ripple true xs) := by
    apply embedState_eq_of_ports _ _ _ _ _ Function.injective_id incrementPorts_injective
    · intro i; rfl
    · intro i hi; exact False.elim (hi ⟨i, rfl⟩)
    · intro i; fin_cases i <;> rfl
    · intro i hi
      fin_cases i <;> simp_all [incrementPorts, io, StructuredProgram.ioState,
        Fin.exists_fin_succ]
  change Eval increment _ (embedState id incrementPorts (io xs)
    (StructuredProgram.ioState (0 : Fin 2) xs))
    (embedState id incrementPorts (io xs)
      (StructuredProgram.ioState (0 : Fin 2) (ripple true xs))) at he
  simpa only [ha, hb] using he

theorem logSucc_eval (xs : List Bool) :
    ∃ output t, value output = Nat.log2 (value xs) + 1 ∧ output.length ≤ xs.length + 1 ∧
      t ≤ 32 * (xs.length + 1)^2 ∧ Eval logSucc t (io xs) (io output) := by
  obtain ⟨ys, t, hv, hl, ht, he⟩ := logarithm_eval xs
  refine ⟨ripple true ys, t + (CounterPrograms.rippleCost true ys + 1), ?_, ?_, ?_,
    he.seq (increment_eval ys)⟩
  · rw [CounterPrograms.value_increment, hv]
  · exact (CounterPrograms.ripple_length_le true ys).trans (by omega)
  · have hc := CounterPrograms.rippleCost_le true ys
    rw [SubexpParameterProgram.logBound_eq] at ht
    nlinarith

end SubexponentialSAT.SqrtLog.Setup

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_IdempotentPreparationProgramLog
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! A fixed native ceiling-logarithm controller. The positive runtime input
t is changed to t-1; a zero guard handles t=1, otherwise floor-log-plus-one
computes the exact Newton iteration count. -/
namespace SubexponentialSAT.SqrtLog.IdempotentPreparationProgram.Log

open BitProgram StructuredCalls
open CounterPrograms (value ripple)

abbrev Data := StructuredProgram.State 3 3

abbrev decrement : Cmd 3 3 :=
  .call (ProgramLinking.liftProgram (CounterPrograms.rippleProgram false)
    id Setup.incrementPorts)

theorem decrement_eval (xs : List Bool) :
    Eval decrement (CounterPrograms.rippleCost false xs + 1)
      (io xs) (io (ripple false xs)) := by
  have he := eval_call_lifted (CounterPrograms.rippleProgram false) id
    Setup.incrementPorts (io xs) Function.injective_id Setup.incrementPorts_injective
    (a := StructuredProgram.ioState (0 : Fin 2) xs)
    (b := StructuredProgram.ioState (0 : Fin 2) (ripple false xs))
    (CounterPrograms.ripple_terminal_trace false xs)
  have ha : embedState id Setup.incrementPorts (io xs)
      (StructuredProgram.ioState (0 : Fin 2) xs) = io xs := by
    apply embedState_eq_of_ports _ _ _ _ _ Function.injective_id Setup.incrementPorts_injective
    · intro i; rfl
    · intro i hi; exact False.elim (hi ⟨i, rfl⟩)
    · intro i; fin_cases i <;> rfl
    · intro i hi; rfl
  have hb : embedState id Setup.incrementPorts (io xs)
      (StructuredProgram.ioState (0 : Fin 2) (ripple false xs)) = io (ripple false xs) := by
    apply embedState_eq_of_ports _ _ _ _ _ Function.injective_id Setup.incrementPorts_injective
    · intro i; rfl
    · intro i hi; exact False.elim (hi ⟨i, rfl⟩)
    · intro i; fin_cases i <;> rfl
    · intro i hi
      fin_cases i <;> simp_all [Setup.incrementPorts, io, Setup.io,
        StructuredProgram.ioState, Fin.exists_fin_succ]
  simpa only [ha, hb] using he

def zeroPorts : CounterForPrograms.Ports 3 3 where
  register := Function.Embedding.refl _
  counter := 0
  scratch := 1
  counter_ne_scratch := by decide

abbrev reset : Cmd 3 3 := .base (SubexpParameterProgram.atoms
  [.set 0 false, .set 1 false, .set 2 false])

theorem reset_eval (d : Data) : Eval reset 3 d ⟨fun _ => false, d.stacks⟩ := by
  have h := SubexpParameterProgram.atoms_eval
    ([.set 0 false, .set 1 false, .set 2 false] : List (StructuredProgram.Atom 3 3)) d
  convert Eval.base h using 1
  all_goals try with_reducible_and_instances rfl
  apply congrArg₂ StructuredProgram.State.mk
  · first | done | (first | done | (funext i; fin_cases i <;> rfl))
  · rfl

abbrev command : Cmd 3 3 := .seq decrement
  (.seq (CounterForPrograms.zeroCmd zeroPorts)
    (.ite 2 reset (.seq reset Setup.logSucc)))

theorem command_eval (xs : List Bool) (hx : 0 < value xs) :
    ∃ output n, value output = Nat.clog 2 (value xs) ∧
      output.length ≤ xs.length + 1 ∧ n ≤ 64*(xs.length+2)^2 ∧
      Eval command n (io xs) (io output) := by
  let ys := ripple false xs
  let z := CounterForPrograms.zeroResult zeroPorts (io ys)
  have hy : value ys = value xs - 1 := by
    have h := CounterPrograms.value_decrement hx
    dsimp [ys]
    omega
  have hlen : ys.length = xs.length := CounterPrograms.decrement_length hx
  have hz := CounterForPrograms.zero_eval zeroPorts (io ys) (by rfl)
  have hzs : z.stacks = (io ys).stacks := by
    exact CounterForPrograms.install_stacks_self zeroPorts (io ys) _ _ _ rfl
  have hzf : z.regs 2 = CounterPrograms.isZero ys := by
    exact CounterForPrograms.install_register zeroPorts (io ys) _ _ _ _ _ 2
  have hr : Eval reset 3 z (io ys) := by
    simpa only [hzs] using reset_eval z
  have hc := CounterPrograms.rippleCost_le false xs
  by_cases hzero : value ys = 0
  · have ht : value xs = 1 := by omega
    have hb : z.regs 2 = true := hzf.trans ((CounterPrograms.isZero_eq_true_iff ys).mpr hzero)
    refine ⟨ys, (CounterPrograms.rippleCost false xs+1)+((8*ys.length+6)+(3+1)), ?_, ?_, ?_, ?_⟩
    · simp [hzero, ht]
    · omega
    · clear hz hzs hzf hr hb
      rw [hlen]
      nlinarith
    · exact (decrement_eval xs).seq (hz.seq (Eval.ite_true hb hr))
  · obtain ⟨out,n,hv,hl,hn,he⟩ := Setup.logSucc_eval ys
    have hb : z.regs 2 = false := hzf.trans
      ((CounterPrograms.isZero_eq_false_iff ys).mpr (by omega))
    refine ⟨out,(CounterPrograms.rippleCost false xs+1)+((8*ys.length+6)+((3+n)+1)), ?_, ?_, ?_, ?_⟩
    · rw [hv, hy, clog_eq_log_pred _ (by omega)]
    · omega
    · clear hz hzs hzf hr hb he
      rw [hlen] at hn ⊢
      nlinarith
    · exact (decrement_eval xs).seq (hz.seq (Eval.ite_false hb (hr.seq he)))

abbrev program := compiled command 0 0

theorem program_runs (xs : List Bool) (hx : 0 < value xs) :
    ∃ output, value output = Nat.clog 2 (value xs) ∧
      output.length ≤ xs.length+1 ∧
      RunsIn program (65*(xs.length+2)^2)
        (initial program xs) (terminal program output) := by
  obtain ⟨out,n,hv,hl,hn,he⟩ := command_eval xs hx
  exact ⟨out,hv,hl,n+1,by nlinarith,compiled_io_trace 0 0 he⟩

end SubexponentialSAT.SqrtLog.IdempotentPreparationProgram.Log

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_IdempotentProgramRegisters
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Source-preserving storage for the fixed Newton register machine. Every
copy, replacement, and clearing operation is an actual finite bit program. -/
namespace SubexponentialSAT.SqrtLog.IdempotentProgram

open BitProgram StructuredCalls StackRoutines

abbrev registerCopy (source target : Fin 41) : Cmd 8 41 :=
  ArithmeticCalls.copyAt source target 38

abbrev registerClear (target : Fin 41) : Cmd 8 41 :=
  .call (clearProgram target 0 1)

/-- Store the computed result, preserving bit order and emptying the result port. -/
abbrev storeResult (target : Fin 41) : Cmd 8 41 :=
  .seq (registerClear target)
    (.seq (registerCopy 0 target) (registerClear 0))

@[simp] theorem preparedOperands_stacks (d : RegisterData) (left right : Fin 41)
    (hr : 32 ≤ right.val) :
    (preparedOperands d left right).stacks =
      Function.update (Function.update (Function.update d.stacks 8 (d.stacks left))
        9 (d.stacks right)) 11 (d.stacks 37) := by
  have hr8 : right ≠ 8 := by intro h; have hv : right.val = 8 := congrArg Fin.val h; omega
  simp [preparedOperands, ArithmeticCalls.afterCopy, hr8]

end SubexponentialSAT.SqrtLog.IdempotentProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_IdempotentPreparationProgramScalarCore
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Native, source-preserving scalar operations on the preparation ABI.
Only the selected output changes; all low arithmetic scratch is restored. -/
namespace SubexponentialSAT.SqrtLog.IdempotentPreparationProgram.Scalar

open BitProgram StructuredCalls ModularRingPrograms ModularDivisionPrograms
open SubexpLiftRing SubexpQuarticRing
open IdempotentProgram (storeResult )

/-- Arbitrary stacks outside the eight scalar-machine ports are framed. -/
abbrev callLow {l : ℕ} (p : Program 8 8 l) : Cmd 8 41 :=
  .call (ProgramLinking.liftProgram p id low)

def Rest (d : Data) (modulus : List Bool) : Prop :=
  (∀ i : Fin 8, d.stacks (low i) = if i = 5 then modulus else []) ∧ d.stacks 38 = []

abbrev prepare (left right : Fin 41) : Cmd 8 41 :=
  .seq (ArithmeticCalls.copyAt left 0 38) (ArithmeticCalls.copyAt right 1 38)

abbrev binary {l : ℕ} (p : Program 8 8 l) (target left right : Fin 41) : Cmd 8 41 :=
  .seq (prepare left right) (.seq (callLow p) (storeResult target))

end SubexponentialSAT.SqrtLog.IdempotentPreparationProgram.Scalar

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_IdempotentProgramService
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Lift the common 32-stack arithmetic ABI into the Newton machine and prove
that the source-preserving register wrapper has the exact specified effect. -/
namespace SubexponentialSAT.SqrtLog.IdempotentProgram

open BitProgram StructuredCalls

/-- The low workspace at rest. No arithmetic input or output is present. -/
def ServiceContext (d : RegisterData) (modulus width zero table : List Bool) : Prop :=
  ∀ i, d.stacks (servicePorts i) =
    (RingScan.serviceState d.regs modulus [] [] [] [] width zero table).stacks i

end SubexponentialSAT.SqrtLog.IdempotentProgram

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

/-! One fixed program builds the complete unsigned H cache from the unary
runtime parameters A and R. No coefficient or initial cache is free input. -/
namespace SubexponentialSAT.SqrtLog.LayoutProgramScalar

open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls
open SubexponentialSAT.SqrtLog.RowSelectionProgram

abbrev BuildData := State 8 19

end SubexponentialSAT.SqrtLog.LayoutProgramScalar

end OAI.Algorithms
end


