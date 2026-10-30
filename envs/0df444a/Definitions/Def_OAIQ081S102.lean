-- Prove2me | Definitions.Def_OAIQ081S102
-- name    : OAIQ081S102
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-29T22:21:28.988386+00:00
-- url     : https://prove2.me/theorems/4faa3bdb-3b2d-4c5a-bbbe-afc952a73d64
-- title:
--   Definitions bundle OAIQ081S102 of the split of OpenAI, The Exponential Time Hypothesis is False
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.exact_count_and_sat`, carved from OpenAI's openai/math development (OpenAI, *The Exponential Time Hypothesis is False*, OpenAI Math Release, October 25, 2026, result family 378, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 121 declarations of OpenAI's Lean: 99 definitions, 2 inductive types or structures and 20 theorems. The definitions and types are `OAI.Algorithms.SubexponentialSAT.SqrtLog.CodeParametersProgram.minCommand`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.CodeParametersProgram.unaryBudget`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.CodeParametersProgram.unaryWords`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.CodeSearchProgram.GraphWorkEmpty`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.CodeSearchProgram.WorkEmpty`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.CodeSearchProgram.prepareGraphWordCost`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.CodeSearchProgram.prepareWordCost`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.EarlyThreshold.inputWords`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.Execution.HashParameters.command`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.HashParametersProgram.ABI.command`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.HashParametersProgram.ABI.coreProgram`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.HashParametersProgram.command`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.HashParametersProgram.inputWords`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.HashScopeProgram.Complete.command`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.HashScopeProgram.Complete.data`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.HashScopeProgram.Complete.program`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.HashScopeProgram.Complete.rowsProgram`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.HashScopeProgram.Complete.runReverse`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.HashScopeProgram.Complete.runRows`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.HashScopeProgram.FromTuple.assembly`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.HashScopeProgram.FromTuple.command`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.HashScopeProgram.FromTuple.extract`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.HashScopeProgram.FromTuple.finished`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.HashScopeProgram.FromTuple.program`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.HashScopeProgram.Marked.data`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.HashScopeProgram.Marked.extract`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.HashScopeProgram.Marked.optional`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.HashScopeProgram.Marked.process`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.HashScopeProgram.RawTable.call`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.HashScopeProgram.RawTable.callback`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.HashScopeProgram.RawTable.iterate`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.HashScopeProgram.Single.command`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.HashScopeProgram.Single.program`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.HeadIdentifierProgram.Data`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.HighIncidenceProgram.Rank.assignment`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.HighIncidenceProgram.Rank.bitRank`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.HighIncidenceProgram.Rank.highEquiv`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.HighIncidenceProgram.Rank.rankEquiv`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.IdempotentApplyProgram.Multiplier.Runs`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.IdempotentApplyProgram.Multiplier.arithmetic` and 61 more.
--
--   **Sources.** They come from these modules of lean/OAI/Algorithms, in whole or in part: `SubexponentialSAT_SqrtLog_CodeParametersProgramUnary`, `SubexponentialSAT_SqrtLog_CodeSearchProgramGraphPrepare`, `SubexponentialSAT_SqrtLog_CodeSearchProgramPrepare`, `SubexponentialSAT_SqrtLog_EarlyThreshold`, `SubexponentialSAT_SqrtLog_ExecutionHashParameters`, `SubexponentialSAT_SqrtLog_HashParametersProgramFinal`, `SubexponentialSAT_SqrtLog_HashScopeProgramFromTuple`, `SubexponentialSAT_SqrtLog_HashScopeProgramMarkedSource`, `SubexponentialSAT_SqrtLog_HashScopeProgramMarkedStep`, `SubexponentialSAT_SqrtLog_HashScopeProgramMarkedTable`, `SubexponentialSAT_SqrtLog_HashScopeProgramMarkedTableCalls`, `SubexponentialSAT_SqrtLog_HashScopeProgramRawCall`, `SubexponentialSAT_SqrtLog_HashScopeProgramRawLoop`, `SubexponentialSAT_SqrtLog_HashScopeProgramSingle`, `SubexponentialSAT_SqrtLog_HeadIdentifierProgram`, `SubexponentialSAT_SqrtLog_HighIncidenceProgramRank`, `SubexponentialSAT_SqrtLog_IdempotentApplyProgramAdd`, `SubexponentialSAT_SqrtLog_IdempotentApplyProgramMachine`, `SubexponentialSAT_SqrtLog_IdempotentApplyProgramMultiplierKernel`, `SubexponentialSAT_SqrtLog_IdempotentApplyProgramReadScalar`, `SubexponentialSAT_SqrtLog_LeafParametersProgramBank`, `SubexponentialSAT_SqrtLog_LeafParametersProgramBankPred`, `SubexponentialSAT_SqrtLog_LeafParametersProgramBankUnary`, `SubexponentialSAT_SqrtLog_LeafParametersProgramNative`, `SubexponentialSAT_SqrtLog_RingProgramTableData`, `SubexponentialSAT_SqrtLog_RingProgramTableInitial`, `SubexponentialSAT_SqrtLog_RingProgramTableLoop`, `SubexponentialSAT_SqrtLog_RingProgramTablePowers`, `SubexponentialSAT_SqrtLog_RingProgramTableStep`, `SubexponentialSAT_SqrtLog_RingTableLayoutProgramBridge`, `SubexponentialSAT_SqrtLog_RingTripleBridge`, `SubexponentialSAT_SubexpBlockParameterProgram`, `SubexponentialSAT_SubexpChunkRecordMap`, `SubexponentialSAT_SubexpLiteralChunkProgram`, `SubexponentialSAT_SubexpScopeProducer`, `SubexponentialSAT_Subexp_CandidateScoreProgram`, `SubexponentialSAT_Subexp_PairPreparationProgram`.
--
--   **Imports.** It imports the published bundle `Def_SubexponentialSAT`; the bundles `OAIQ081S082`, `OAIQ081S083`, `OAIQ081S084` and `OAIQ081S085` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ081S116`, `OAIQ081S117`, `OAIQ081S118`, `OAIQ081S119`, `OAIQ081S120`, `OAIQ081S122`, `OAIQ081S123`, `OAIQ081S124`, `OAIQ081S125`, `OAIQ081S126`, `OAIQ081S127`, `OAIQ081S128`, `OAIQ081S129`, `OAIQ081S130`, `OAIQ081S131`, `OAIQ081S132`, `OAIQ081S133`, `OAIQ081S134`, `OAIQ081S135`, `OAIQ081S136` and `OAIQ081S137`; the statements `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.CodeChecks.graph_stream_runs`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.CodeChecks.local_checker_runs`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.CodeSearchProgram.graphWordCallback_eval`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.CodeSearchProgram.preparedGraphWord_length_le`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.CodeSearchProgram.wordCallback_eval`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.Execution.HashParameters.command_eval`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.HashScopeProgram.Marked.fetch_eval`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.HashScopeProgram.Marked.optional_eval`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.HashScopeProgram.Single.program_runsIn` and `OAI.Algorithms.SubexponentialSAT.SubexpScopeProducer.command_eval`; the proofs of `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.CodeChecks.graph_stream_runs`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.CodeChecks.local_checker_runs`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.CodeSearchProgram.graphWordCallback_eval`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.CodeSearchProgram.preparedGraphWord_length_le`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.CodeSearchProgram.wordCallback_eval`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.HashScopeProgram.Marked.fetch_eval`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.HashScopeProgram.Marked.optional_eval`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.HashScopeProgram.Single.program_runsIn` and `OAI.Algorithms.SubexponentialSAT.SubexpScopeProducer.command_eval`.
-- source:
--   OpenAI, The Exponential Time Hypothesis is False, OpenAI Math Release, October 25, 2026, https://github.com/openai/math (result family 378; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/The-Exponential-Time-Hypothesis-is-False-October-25-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Algorithms at commit 7ef5c0c

import Mathlib
import Definitions.Def_SubexponentialSAT
import Definitions.Def_OAIQ081S082
import Definitions.Def_OAIQ081S083
import Definitions.Def_OAIQ081S084
import Definitions.Def_OAIQ081S085

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SubexpBlockParameterProgram
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# Actual block-size and block-threshold arithmetic

The three input words contain `s`, `delta`, and `Q`.  The width `k` is part
of the fixed code.  Seven high stacks are a reusable empty work bank; the
fifteen low stacks retain inputs, constants, and computed intermediate words.
Every arithmetic operation below invokes a proved finite Boolean program.
-/

namespace SubexponentialSAT.SubexpBlockParameterProgram

open BitProgram StructuredCalls BinaryArithmetic

def work (m : ℕ) (hm : m ≤ 7) : Fin m ↪ Fin 22 where
  toFun i := ⟨15 + i.val, by omega⟩
  inj' := by
    intro i j h
    apply Fin.ext
    have := congrArg Fin.val h
    dsimp at this
    omega

theorem work_ne_port (m : ℕ) (hm : m ≤ 7) (i : Fin m) (j : Fin 15) :
    work m hm i ≠ port j := by
  intro h
  have he : 15 + i.val = j.val := congrArg (fun x : Fin 22 => x.val) h
  have := j.isLt
  omega

def arithmeticPorts (a b o : Fin 15) (hoa : o ≠ a) (hob : o ≠ b) :
    ArithmeticCalls.Ports 22 where
  left := port a
  right := port b
  out := port o
  work := work 5 (by decide)
  out_ne_left := by intro h; exact hoa ((Fin.castAdd_injective 15 7) h)
  out_ne_right := by intro h; exact hob ((Fin.castAdd_injective 15 7) h)
  work_ne_left := fun i => work_ne_port 5 (by decide) i a
  work_ne_right := fun i => work_ne_port 5 (by decide) i b
  work_ne_out := fun i => work_ne_port 5 (by decide) i o

abbrev addCmd (a b o : Fin 15) (hoa : o ≠ a) (hob : o ≠ b) : Cmd 8 22 :=
  ArithmeticCalls.addAt (arithmeticPorts a b o hoa hob)

abbrev multiplyCmd (a b o : Fin 15) (hoa : o ≠ a) (hob : o ≠ b) : Cmd 8 22 :=
  ArithmeticCalls.multiplyAt (arithmeticPorts a b o hoa hob)

abbrev loadCmd (o : Fin 15) (word : List Bool) : Cmd 8 22 :=
  ArithmeticExpressionSupport.pushWord (port o) word

end SubexponentialSAT.SubexpBlockParameterProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafParametersProgramBank
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.LeafParametersProgram.Bank

open BitProgram StructuredCalls BinaryArithmetic

theorem work_ne_port (m : ℕ) (hm : m ≤ 13) (i : Fin m) (j : Fin 64) :
    work m hm i ≠ port j := by
  intro h
  have he : 64 + i.val = j.val := congrArg (fun x : Fin 77 => x.val) h
  have := j.isLt
  omega

def arithmeticPorts (a b o : Fin 64) (hoa : o ≠ a) (hob : o ≠ b) :
    ArithmeticCalls.Ports 77 where
  left := port a
  right := port b
  out := port o
  work := work 5 (by decide)
  out_ne_left := by intro h; exact hoa ((Fin.castAdd_injective 64 13) h)
  out_ne_right := by intro h; exact hob ((Fin.castAdd_injective 64 13) h)
  work_ne_left := fun i => work_ne_port 5 (by decide) i a
  work_ne_right := fun i => work_ne_port 5 (by decide) i b
  work_ne_out := fun i => work_ne_port 5 (by decide) i o

def powerPorts (a b o : Fin 64) (hoa : o ≠ a) (hob : o ≠ b) :
    PowerCalls.Ports 77 where
  base := port a
  exponent := port b
  out := port o
  work := work 7 (by decide)
  out_ne_base := by intro h; exact hoa ((Fin.castAdd_injective 64 13) h)
  out_ne_exponent := by intro h; exact hob ((Fin.castAdd_injective 64 13) h)
  work_ne_base := fun i => work_ne_port 7 (by decide) i a
  work_ne_exponent := fun i => work_ne_port 7 (by decide) i b
  work_ne_out := fun i => work_ne_port 7 (by decide) i o

abbrev addCmd (a b o : Fin 64) (hoa : o ≠ a) (hob : o ≠ b) : Cmd 8 77 :=
  ArithmeticCalls.addAt (arithmeticPorts a b o hoa hob)

abbrev multiplyCmd (a b o : Fin 64) (hoa : o ≠ a) (hob : o ≠ b) : Cmd 8 77 :=
  ArithmeticCalls.multiplyAt (arithmeticPorts a b o hoa hob)

abbrev powerCmd (a b o : Fin 64) (hoa : o ≠ a) (hob : o ≠ b) : Cmd 8 77 :=
  PowerCalls.powerAt (powerPorts a b o hoa hob)

abbrev loadCmd (o : Fin 64) (word : List Bool) : Cmd 8 77 :=
  ArithmeticExpressionSupport.pushWord (port o) word


end SubexponentialSAT.SqrtLog.LeafParametersProgram.Bank

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafParametersProgramBankUnary
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.LeafParametersProgram.Bank

open BitProgram StructuredCalls BinaryArithmetic

def unaryStacks (a : Fin 64) : Fin 3 → Fin 77 :=
  ![port a, work 2 (by decide) 0, work 2 (by decide) 1]

abbrev unaryCmd (a : Fin 64) (body : Cmd 3 3) : Cmd 8 77 :=
  liftCommand (.seq resetLog body) 0 0 smallRegs (unaryStacks a)

def logSuccCmd (a : Fin 64) := unaryCmd a Setup.logSucc

def addConstCmd (a : Fin 64) (k : ℕ) := unaryCmd a (Setup.addConst k)

end SubexponentialSAT.SqrtLog.LeafParametersProgram.Bank

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafParametersProgramBankPred
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.LeafParametersProgram.Bank

open BitProgram StructuredCalls BinaryArithmetic

def predPorts (a : Fin 64) : CounterForPrograms.Ports 8 77 where
  register := ⟨smallRegs, Fin.castAdd_injective 3 5⟩
  counter := port a
  scratch := work 1 (by decide) 0
  counter_ne_scratch := (work_ne_port 1 (by decide) 0 a).symm

abbrev predCmd (a : Fin 64) : Cmd 8 77 := CounterPredProgram.predCmd (predPorts a)

/-- Two saturating predecessors followed by two explicit increments implement
max(2,a), including padded zero words. -/
abbrev maxTwoCmd (a : Fin 64) : Cmd 8 77 :=
  .seq (predCmd a) (.seq (predCmd a) (addConstCmd a 2))

end SubexponentialSAT.SqrtLog.LeafParametersProgram.Bank

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

namespace SubexponentialSAT.SqrtLog.LeafParametersProgram.Bank

open BitProgram StructuredCalls BinaryArithmetic

def quotientPorts (a b o : Fin 64) (hoa : o ≠ a) (hob : o ≠ b) :
    LeafParameterArithmetic.QuotientPorts 77 where
  left := port a
  right := port b
  out := port o
  work := work 6 (by decide)
  out_ne_left := by intro h; exact hoa ((Fin.castAdd_injective 64 13) h)
  out_ne_right := by intro h; exact hob ((Fin.castAdd_injective 64 13) h)
  work_ne_left := fun i => work_ne_port 6 (by decide) i a
  work_ne_right := fun i => work_ne_port 6 (by decide) i b
  work_ne_out := fun i => work_ne_port 6 (by decide) i o

abbrev quotientCmd (a b o : Fin 64) (hoa : o ≠ a) (hob : o ≠ b) : Cmd 8 77 :=
  LeafParameterArithmetic.quotientAt (quotientPorts a b o hoa hob)

def sqrtPorts (a o : Fin 64) (hoa : o ≠ a) : LeafParameterArithmetic.SqrtPorts 77 where
  input := port a
  out := port o
  work := work 13 (by decide)
  out_ne_input := by intro h; exact hoa ((Fin.castAdd_injective 64 13) h)
  work_ne_input := fun i => work_ne_port 13 (by decide) i a
  work_ne_out := fun i => work_ne_port 13 (by decide) i o

abbrev sqrtCmd (a o : Fin 64) (hoa : o ≠ a) : Cmd 8 77 :=
  LeafParameterArithmetic.sqrtAt (sqrtPorts a o hoa)

end SubexponentialSAT.SqrtLog.LeafParametersProgram.Bank


/- Component: SubexponentialSAT.SqrtLog.LeafParametersProgramDispatch -/

/-! A fixed ten-comparison bit guard. All operands are runtime binary words.
This module states their data relation separately from parameter production. -/

namespace SubexponentialSAT.SqrtLog.LeafParametersProgram.Circuit

open BitProgram StructuredCalls BinaryArithmetic Bank

def command : Instr → Cmd 8 77
  | .clear a => ArithmeticExpressionSupport.clearCmd (port a)
  | .load o bits => loadCmd o bits
  | .copy a o _ => copyCmd a o
  | .add a b o ha hb => addCmd a b o ha hb
  | .mul a b o ha hb => multiplyCmd a b o ha hb
  | .pow a b o ha hb => powerCmd a b o ha hb
  | .quot a b o ha hb => quotientCmd a b o ha hb
  | .sqrt a o h => sqrtCmd a o h
  | .logSucc a => logSuccCmd a
  | .addConst a k => addConstCmd a k
  | .pred a => predCmd a
  | .maxTwo a => maxTwoCmd a

end SubexponentialSAT.SqrtLog.LeafParametersProgram.Circuit


/- Component: SubexponentialSAT.SqrtLog.LeafParametersProgramCircuitRun -/

namespace SubexponentialSAT.SqrtLog.LeafParametersProgram.Circuit

open BitProgram StructuredCalls BinaryArithmetic Bank

def program : List Instr → Cmd 8 77
  | [] => .base .skip
  | i::is => .seq (command i) (program is)

end SubexponentialSAT.SqrtLog.LeafParametersProgram.Circuit


/- Component: SubexponentialSAT.SqrtLog.LeafParametersProgramLayout -/


end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_CodeParametersProgramUnary
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Production sparse-code parameter program. Fixed arithmetic, minimum,
metadata identities and unary materialization are checked in one unit. -/

/-! Arithmetic identities used by the physical sparse-code parameter program. -/


/-! A concrete minimum operation used between two straight-line arithmetic
stages. The comparison consumes only two explicitly copied temporary words. -/
namespace SubexponentialSAT.SqrtLog.CodeParametersProgram

open BitProgram StructuredCalls BinaryArithmetic LeafParametersProgram.Bank

abbrev minCommand : Cmd 8 77 :=
  .seq (copyCmd 0 62) <| .seq (copyCmd 8 63) <|
  .seq (.call (ProgramLinking.liftProgram SubexpGuardProgram.Compare.program id minComparePorts)) <|
  .ite 0 (copyCmd 0 9) (copyCmd 8 9)

end SubexponentialSAT.SqrtLog.CodeParametersProgram


/-! Fixed finite arithmetic instructions for all sparse-code search metadata.
Ports 0 and 1 contain m and B. Outputs: q=5, D=9, t=11, tD=12,
local distance=15, r=18, rD=19, N=21. Unary conversion is a separate,
explicitly paid stage. -/


/-! Explicit paid binary-to-unary copies for code-search metadata. -/
namespace SubexponentialSAT.SqrtLog.CodeParametersProgram

open BitProgram StructuredCalls BinaryArithmetic LeafParametersProgram.Bank

def unaryWords (w : Words) : Words :=
  unaryPairs.foldl (fun z p => Function.update z p.2 (List.replicate (BinaryArithmetic.toNat (w p.1)) true)) w

def unaryBudget (w : Words) : ℕ :=
  (unaryPairs.map (fun p => 7*(w p.1).length+6+CounterConversions.coreBound (w p.1))).sum

end SubexponentialSAT.SqrtLog.CodeParametersProgram

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

def prepareGraphWordCost (a : GraphSearchState) : ℕ :=
  7 * ((a.stacks 29).length + (a.stacks 30).length + (a.stacks 31).length + (a.stacks 32).length) +
    3 * (a.stacks 34).length + 31

def GraphWorkEmpty (a : GraphSearchState) : Prop := ∀ i : Fin 29, a.stacks (graphWordStacks i) = []

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

def prepareWordCost (a : SearchState) : ℕ :=
  7 * ((a.stacks 18).length + (a.stacks 19).length + (a.stacks 20).length) +
    3 * (a.stacks 22).length + 25

def WorkEmpty (a : SearchState) : Prop := ∀ i : Fin 18, a.stacks (wordStacks i) = []


end SubexponentialSAT.SqrtLog.CodeSearchProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_EarlyThreshold
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! A paid, fixed native producer of the early high-incidence threshold.
The source is the original ambient count in bank slot 0.  It is never replaced
by the residual count or by the later block-size parameter. -/

namespace SubexponentialSAT.SqrtLog.EarlyThreshold

open BitProgram StructuredCalls BinaryArithmetic
open LeafParametersProgram.Bank LeafParametersProgram.Circuit


/-- The standard isolated input bank contains only the original ambient
binary word.  Padding zero bits is allowed. -/
def inputWords (ambient : List Bool) : Words := fun a => if a = 0 then ambient else []

end SubexponentialSAT.SqrtLog.EarlyThreshold

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

namespace SubexponentialSAT.SqrtLog.HashParametersProgram

open BitProgram StructuredCalls BinaryArithmetic SubexpBlockParameterProgram

def inputWords (n m B : List Bool) : Words :=
  ![n,m,B,[],[],[],[],[],[],[],[],[],[],[],[]]

abbrev command : Cmd 8 22 :=
  .seq (copyClause) <|
  .seq (logCall) <|
  .seq (loadCmd 4 ([true,true] : List Bool)) <|
  .seq (loadCmd 5 ([false,false,false,false,false,true,false,false,false,true,true,true,false,false,true] : List Bool)) <|
  .seq (loadCmd 11 ([true] : List Bool)) <|
  .seq (multiplyCmd 2 2 6 (by decide) (by decide)) <|
  .seq (multiplyCmd 3 3 7 (by decide) (by decide)) <|
  .seq (multiplyCmd 6 7 8 (by decide) (by decide)) <|
  .seq (multiplyCmd 5 8 9 (by decide) (by decide)) <|
  .seq (addCmd 0 3 10 (by decide) (by decide)) <|
  .seq (addCmd 10 11 12 (by decide) (by decide)) <|
  .seq (addCmd 12 12 13 (by decide) (by decide)) <|
  multiplyCmd 1 4 14 (by decide) (by decide)

end SubexponentialSAT.SqrtLog.HashParametersProgram


/-! Exact metadata loading and selector-port installation. Metadata is outside
all fourteen selector ports. The fixed scratch bank is physically cleared. -/
namespace SubexponentialSAT.SqrtLog.HashParametersProgram.ABI

open BitProgram StructuredCalls SubexpSetupStorage

def coreProgram := compiled HashParametersProgram.command 0 14

abbrev command : Cmd 16 44 := isolated coreProgram registers stackMap 39 work inputs outputs

end SubexponentialSAT.SqrtLog.HashParametersProgram.ABI


/-! Polynomial step budget for the complete physical parameter setup. -/


/-! Exported fixed program and the selector's actual fourteen-port interface. -/

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_ExecutionHashParameters
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Relocation of the actual metadata arithmetic into a caller which also
holds the formula and ring context. Only binary n, m and B are supplied;
3m, the tuple depth and the number of hash rounds are computed by the fixed
parameter program. The empty-formula branch is handled by the leaf caller. -/

namespace SubexponentialSAT.SqrtLog.Execution.HashParameters

open BitProgram StructuredCalls

abbrev command {R S : ℕ} (p : Ports R S) : Cmd R S :=
  liftCommand HashParametersProgram.ABI.command 0 6 p.register p.stack

end SubexponentialSAT.SqrtLog.Execution.HashParameters

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

abbrev command : Cmd 8 19 := .seq decode (.seq count (.seq divide
  (.seq encode (.seq clearRemainder (.seq reverseField reset)))))

def program := compiled command (9 : Fin 19) 9

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

abbrev convert : Cmd 11 22 := .call (ProgramLinking.liftProgram
  SubexpLiteralChunkProgram.program convertRegisters convertStacks)

abbrev callback : Cmd 11 22 := .seq convert (.seq select emit)

abbrev scan : Cmd 11 22 := RecordPrograms.iterate ports callback

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

abbrev command : Cmd 11 22 := .seq initializeOutput (.seq scan
  (.seq seedSource (.seq reverse dedup)))

def program := compiled command (19 : Fin 22) 19

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

abbrev command : Cmd 11 22 := .seq initializeCmd (.seq flatten (.seq restore SubexpScopeProducer.command))
def program := compiled command 19 19

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

abbrev assembly : Cmd 11 46 := .call (ProgramLinking.liftProgram HashInputProgram.Loop.assembleProgram
  assemblyRegisters assemblyStacks)
abbrev extract : Cmd 11 46 := .call (ProgramLinking.liftProgram Single.program id scopeStacks)
abbrev command : Cmd 11 46 := .seq assembly (.seq Reset.all (.seq extract clearEll))
def program := compiled command 0 16

def finished (rf : Fin 11 → Bool) (width modulus master shape bits : List Bool) : Data :=
  ⟨rf,(extend (HashInputProgram.Loop.data (fun _ => false) [] width modulus master shape
    bits [] [] [] [])).stacks⟩

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

def data (rf : Fin 11 → Bool) (width modulus master shape out index flag clause ell pay : List Bool) : Data :=
  ⟨rf,tapes width modulus master shape out index flag clause ell pay⟩

abbrev extract : Cmd 11 80 := .call (ProgramLinking.liftProgram SubexpScopeProducer.program id scopeStacks)

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


abbrev process : Cmd 11 80 := .seq fetch (.seq prepareScope (.seq extract
  (.seq clearEll (.seq moveScope MarkedFrame.command))))

abbrev optional : Cmd 11 80 := .seq popFlag (.ite 8 process (.seq clearIndex MarkedFrame.fix))

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

abbrev call : Cmd 11 49 := .call (ProgramLinking.liftProgram FromTuple.program id callStacks)

abbrev callback : Cmd 11 49 := .seq takeInput (.seq Reset.all (.seq call (.seq takeOutput RawFrame.command)))

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



abbrev iterate : Cmd 11 49 := RecordPrograms.iterate ports callback

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

def data (rf : Fin 11 → Bool) (width modulus master shape source out index flag : List Bool) : Data :=
  ⟨rf,fun j => if j=46 then source else Marked.tapes width modulus master shape out index flag [] [] [] j⟩

def rowsProgram := compiled RawTable.iterate 46 48
abbrev runRows : Cmd 11 80 := .call (ProgramLinking.liftProgram rowsProgram id lowStacks)
abbrev runReverse : Cmd 11 80 := .call (ProgramLinking.liftProgram reverseProgram id lowStacks)

end SubexponentialSAT.SqrtLog.HashScopeProgram.Complete

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_HashScopeProgramMarkedTable
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Complete physical scope stream, including the optional marked factor.
The final row order is all raw hash rows followed by the marked clause if present. -/
namespace SubexponentialSAT.SqrtLog.HashScopeProgram.Complete
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls


abbrev command : Cmd 11 80 := .seq initializeCmd (.seq runRows (.seq Marked.optional (.seq seed runReverse)))
def program := compiled command 46 46

end SubexponentialSAT.SqrtLog.HashScopeProgram.Complete

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_Subexp_CandidateScoreProgram
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# Fixed-control candidate scoring

Score records are accumulated as reversed serialized bytes and reversed once
at the end, so output score order agrees with the input candidate order.
-/

namespace SubexponentialSAT.Subexp.CandidateScoreProgram

open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls

def resetLowState (a : State 16 36) : State 16 36 :=
  ⟨resetValues ((List.finRange 13).map lowRegisters) a.regs,a.stacks⟩

@[simp] theorem resetLow_register (a : State 16 36) (i : Fin 13) :
    (resetLowState a).regs (lowRegisters i) = false := by
  simp [resetLowState,resetValues_apply]

def reverseWritten (a : State 16 36) : State 16 36 :=
  ⟨Function.update (Function.update (Function.update a.regs 0 false) 1 false) 2 true,
    Function.update (Function.update a.stacks 18 []) 35
      ((TupleProgram.escaped (a.stacks 18)).reverse ++ a.stacks 35)⟩

def emittedScore (a : State 16 36) : State 16 36 :=
  TupleProgram.pushedState 35 0 false
    (reverseWritten (TupleProgram.pushedState 35 0 true a))

@[simp] theorem emittedScore_consumed (a : State 16 36) :
    (emittedScore a).stacks 18 = [] := by
  simp [emittedScore,TupleProgram.pushedState,reverseWritten]

structure Context where
  before : List (List Bool)
  old : List Bool
  after : List (List Bool)
  width : List Bool
  alphabet : List (List Bool)
  depth : List Bool
  index : List Bool
  candidates : List (List Bool)
  pairs : List PairScoreProgram.PlanPair

def pairContext (ctx : Context) (candidate : List Bool) : PairScoreProgram.Context :=
  ⟨ctx.before ++ candidate :: ctx.after,ctx.width,ctx.alphabet,ctx.depth⟩

def original (ctx : Context) : List Bool :=
  ctx.before.flatten ++ (ctx.old ++ ctx.after.flatten)

def candidateScore (ctx : Context) (candidate : List Bool) : ℕ :=
  PairScoreProgram.score (pairContext ctx candidate) ctx.pairs

def workState (ctx : Context) (regs : Fin 16 → Bool)
    (tail candidate current score pairSource builder : List Bool) : State 16 36 :=
  ⟨regs,fun j =>
    if j = 3 then ctx.width else if j = 13 then current else if j = 18 then score
    else if j = 19 then ProgramEncoding.encodeRecords ctx.alphabet
    else if j = 20 then pairSource else if j = 23 then ctx.depth
    else if j = 26 then original ctx else if j = 27 then candidate
    else if j = 28 then ctx.index else if j = 29 then tail
    else if j = 30 then ProgramEncoding.encodeRecords ctx.candidates
    else if j = 31 then PairScoreProgram.pairRecords ctx.pairs
    else if j = 35 then builder else []⟩

def baseState (ctx : Context) (regs : Fin 16 → Bool) (builder : List Bool) : State 16 36 :=
  workState ctx regs [] [] [] [] [] builder

def scoreRecords (ctx : Context) : List (List Bool) :=
  ctx.candidates.map fun candidate => UnaryCompare.encode (candidateScore ctx candidate)

def outputState (ctx : Context) (regs : Fin 16 → Bool) : State 16 36 :=
  ⟨regs,Function.update (baseState ctx regs []).stacks 32 (ProgramEncoding.encodeRecords (scoreRecords ctx))⟩

@[simp] theorem outputState_output (ctx : Context) (regs : Fin 16 → Bool) :
    (outputState ctx regs).stacks 32 = ProgramEncoding.encodeRecords (scoreRecords ctx) := by
  simp [outputState]

end SubexponentialSAT.Subexp.CandidateScoreProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_HeadIdentifierProgram
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Physical head-identifier selection uses the original ambient word array.
No packing-coverage predicate participates in the scan. -/
namespace SubexponentialSAT.SqrtLog.HeadIdentifierProgram
open SubexponentialSAT BitProgram StructuredCalls SubexpScanPrimitives

abbrev Data := State 16 64

end SubexponentialSAT.SqrtLog.HeadIdentifierProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_HighIncidenceProgramRank
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.FiniteField.fieldFintype _root_.OAI.Algorithms.SubexponentialSAT.MulticolorTypes.instFintypeJoint _root_.OAI.Algorithms.SubexponentialSAT.MulticolorTypes.instFintypeSide _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Rank semantics for the native all-visits Boolean odometer. These maps are
proof-level reindexings; the machine changes its physical tuple in place. -/
namespace SubexponentialSAT.SqrtLog.HighIncidenceProgram.Rank
open scoped BigOperators

def bitRank (h : ℕ) (a : Fin h → Bool) : Fin (2 ^ h) :=
  ⟨CounterPrograms.value (List.ofFn a), by
    simpa using ExecCNFTupleOdometer.value_lt_power_length (List.ofFn a)⟩

theorem bitRank_injective (h : ℕ) : Function.Injective (bitRank h) := by
  intro a b hab
  apply List.ofFn_injective
  apply ExecCNFTupleEnumeration.word_eq_of_length_value (by simp)
  exact congrArg Fin.val hab

noncomputable def rankEquiv (h : ℕ) : (Fin h → Bool) ≃ Fin (2 ^ h) :=
  Equiv.ofBijective (bitRank h)
    ((Fintype.bijective_iff_injective_and_card _).mpr ⟨bitRank_injective h, by simp⟩)

noncomputable def assignment (h : ℕ) (r : Fin (2 ^ h)) : Fin h → Bool :=
  (rankEquiv h).symm r

noncomputable def highEquiv {H : Type*} {h : ℕ} (order : Fin h ≃ H) :
    Fin (2 ^ h) ≃ (H → Bool) := (rankEquiv h).symm.trans (reindex order)

end SubexponentialSAT.SqrtLog.HighIncidenceProgram.Rank

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_RingTripleBridge
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! The input/output of the dynamic expander is exactly the k-major table and
triple stream used by the native ring contraction. `List.ofFn` below describes
the serialized input and theorem; the fixed program builds the repeated stream
by actual counted loops and paid source copies. -/
namespace SubexponentialSAT.SqrtLog.RingTriple

open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls
open SubexponentialSAT.SubexpQuarticRing

theorem xBits_map {B : ℕ} (rows : List (Row B)) :
    xBits rows = (rows.map fun r => r.1.val).flatten := by
  induction rows with
  | nil => rfl
  | cons r rows ih => simp only [xBits, List.map_cons, List.flatten_cons, ih]

theorem leftBits_map {B : ℕ} (pairs : List (Word B × Word B)) :
    leftBits pairs = (pairs.map fun p => p.1.val).flatten := by
  induction pairs with
  | nil => rfl
  | cons p pairs ih => simp only [leftBits, List.map_cons, List.flatten_cons, ih]

theorem rightBits_map {B : ℕ} (pairs : List (Word B × Word B)) :
    rightBits pairs = (pairs.map fun p => p.2.val).flatten := by
  induction pairs with
  | nil => rfl
  | cons p pairs ih => simp only [rightBits, List.map_cons, List.flatten_cons, ih]

theorem tableBits_map {B : ℕ} (rows : List (Row B)) :
    tableBits rows = (rows.map fun r => rightBits r.2).flatten := by
  induction rows with
  | nil => rfl
  | cons r rows ih => simp only [tableBits, List.map_cons, List.flatten_cons, ih]

theorem tripleBits_append {B : ℕ} (xs ys : List (RingScan.WordTriple B)) :
    RingScan.tripleBits (xs ++ ys) = RingScan.tripleBits xs ++ RingScan.tripleBits ys := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp [RingScan.tripleBits, ih, List.append_assoc]

end SubexponentialSAT.SqrtLog.RingTriple

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_IdempotentApplyProgramAdd
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Native normalized addition for the persistent polynomial registers used
by the indicator Horner loop. Both operand copies and result storage are paid. -/
namespace SubexponentialSAT.SqrtLog.IdempotentApplyProgram

open BitProgram StructuredCalls SubexpLiftRing SubexpQuarticRing
open HashCircuitProgram.Native
open MomentsProgram

abbrev addCore : Cmd 8 96 :=
  liftCommand Product.normalizePhase 4 42 id Memory.lowPort

abbrev add : Cmd 8 96 :=
  .seq (copy 67 4 70) (.seq (copy 61 42 70) (.seq addCore
    (.seq (clear 67) (.seq (clear 61) (.seq (copy 42 67 70) (clear 42))))))

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

/-- Two products and two sums evaluate one quadratic coefficient digit. -/
abbrev tripleStep : Cmd 8 96 := sequence
  [scalarConstant 67,
   copy 68 61 70, productAdapter product,
   scalarConstant 61, add,
   copy 68 61 70, productAdapter product,
   scalarConstant 61, add]

abbrev accumulatorStep : Cmd 8 96 := sequence
  [copy 67 85 70, clear 67,
   copy 87 67 70, clear 87,
   copy 86 61 70, productAdapter product,
   copy 85 61 70, clear 85, add,
   copy 67 87 70, clear 67]

/-- Exactly three scalar loads, three polynomial products and three sums.
The coefficient order is c,b,a because the whole coefficient tape is reversed. -/
abbrev hornerStep : Cmd 8 96 := .seq tripleStep (.seq accumulatorStep peekCoefficients)

end SubexponentialSAT.SqrtLog.IdempotentApplyProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_IdempotentApplyProgramMultiplierKernel
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Source component: IdempotentApplyProgramMultiplierArithmetic. -/

/-! Native construction of the cubic multiplier before its U shift. -/
namespace SubexponentialSAT.SqrtLog.IdempotentApplyProgram.Multiplier
open BitProgram StructuredCalls SubexpLiftRing SubexpQuarticRing
open HashCircuitProgram.Native
open MomentsProgram
open Steps

variable {p t n d : ℕ} [Fact p.Prime]

/-- A bounded native transition, with all Boolean registers allowed to change. -/
abbrev Runs (command : Cmd 8 96) (cost : ℕ) (low : Fin 56 → List Bool)
    (before after : Data) : Prop :=
  ∀ regs, ∃ k ≤ cost, ∃ rr, Eval command k
    (Memory.state regs low before) (Memory.state rr low after)

abbrev arithmetic : Cmd 8 96 := sequence
  [copy 68 61 70, complement,
   copy 61 85 70, copy 61 67 70, clear 61,
   copy 69 61 70, add,
   copy 85 61 70, productAdapter product, clear 85,
   copy 68 61 70, productAdapter product]

end SubexponentialSAT.SqrtLog.IdempotentApplyProgram.Multiplier

/-! Source component: IdempotentApplyProgramMultiplier. -/

/-! Concrete preparation of the stored multiplier used by native Horner evaluation. -/

/-! Source component: IdempotentApplyProgramMultiplierSemantics. -/

/-! The multiplier produced by the native preparation is U H(H-1)(H-2). -/

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

def readResult (d : Machine) (word tail : List Bool) : Machine :=
  ⟨readRegs d.regs 0 1 none,
    Function.update (Function.update d.stacks 79 tail) 80 word⟩

end SubexponentialSAT.SqrtLog.IdempotentApplyProgram.ReadScalar


end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_RingProgramTableStep
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.RingProgramTable

open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.StackRoutines
open SubexponentialSAT.SubexpLiftRing SubexponentialSAT.SubexpQuarticRing

def coefficient (p t : ℕ) [Fact p.Prime] (M : SubexpPreparedQuartic.Modulus p t)
    (tail c minusOne previous : Word (baseWidth p t)) : Word (baseWidth p t) :=
  (SubexpPreparedQuartic.wordAdd p t M
    (RingScan.tripleProduct p t M tail c minusOne) previous).1

end SubexponentialSAT.SqrtLog.RingProgramTable

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_RingProgramTableLoop
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.RingProgramTable

open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.StackRoutines
open SubexponentialSAT.SubexpLiftRing SubexponentialSAT.SubexpQuarticRing

abbrev Pairs (B : ℕ) := List (Word B × Word B)

end SubexponentialSAT.SqrtLog.RingProgramTable

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_RingProgramTableData
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.RingProgramTable

open SubexponentialSAT.SubexpLiftRing SubexponentialSAT.SubexpQuarticRing

/-- Materialized coefficient vector together with its cached final coefficient. -/
structure VectorData (B d : ℕ) where
  coefficients : List.Vector (Word B) d
  last : Word B

def wordBits {B : ℕ} (xs : List (Word B)) : List Bool := (xs.map Subtype.val).flatten

@[simp] theorem wordBits_length {B : ℕ} (xs : List (Word B)) :
    (wordBits xs).length = xs.length * B := by
  induction xs with
  | nil => simp [wordBits]
  | cons x xs ih =>
      simp only [wordBits, List.map_cons, List.flatten_cons, List.length_append,
        List.length_cons]
      change x.val.length + (wordBits xs).length = (xs.length + 1) * B
      rw [x.property, ih]
      ring

def outputWords (p t : ℕ) [Fact p.Prime] (M : SubexpPreparedQuartic.Modulus p t)
    (tail minusOne : Word (baseWidth p t)) : Pairs (baseWidth p t) → Word (baseWidth p t) → List (Word (baseWidth p t))
  | [], _ => []
  | (c,a) :: pairs, previous =>
    coefficient p t M tail c minusOne previous :: outputWords p t M tail minusOne pairs a

@[simp] theorem outputWords_length (p t : ℕ) [Fact p.Prime]
    (M : SubexpPreparedQuartic.Modulus p t) (tail minusOne : Word (baseWidth p t))
    (pairs : Pairs (baseWidth p t)) (previous : Word (baseWidth p t)) :
    (outputWords p t M tail minusOne pairs previous).length = pairs.length := by
  induction pairs generalizing previous with
  | nil => rfl
  | cons pair pairs ih => simpa [outputWords] using congrArg Nat.succ (ih pair.2)

def lastOutputWord (p t : ℕ) [Fact p.Prime] (M : SubexpPreparedQuartic.Modulus p t)
    (tail minusOne : Word (baseWidth p t)) : Pairs (baseWidth p t) → Word (baseWidth p t) → Word (baseWidth p t) → Word (baseWidth p t)
  | [], _, old => old
  | (c,a) :: pairs, previous, _ =>
    lastOutputWord p t M tail minusOne pairs a (coefficient p t M tail c minusOne previous)

def advance (p t : ℕ) [Fact p.Prime] (M : SubexpPreparedQuartic.Modulus p t)
    (zeroWord minusOne : Word (baseWidth p t)) {d : ℕ}
    (c : List.Vector (Word (baseWidth p t)) d) (v : VectorData (baseWidth p t) d) :
    VectorData (baseWidth p t) d :=
  let pairs := c.val.zip v.coefficients.val
  { coefficients := ⟨outputWords p t M v.last minusOne pairs zeroWord, by simp [pairs]⟩
    last := lastOutputWord p t M v.last minusOne pairs zeroWord zeroWord }

@[simp] theorem leftBits_zip {B d : ℕ} (x y : List.Vector (Word B) d) :
    RingScan.leftBits (x.val.zip y.val) = wordBits x.val := by
  have h (xs ys : List (Word B)) (hl : xs.length = ys.length) :
      RingScan.leftBits (xs.zip ys) = wordBits xs := by
    induction xs generalizing ys with
    | nil => cases ys <;> simp_all [RingScan.leftBits, wordBits]
    | cons x xs ih =>
      cases ys with
      | nil => simp at hl
      | cons y ys =>
        change x.val ++ RingScan.leftBits (xs.zip ys) = x.val ++ wordBits xs
        exact congrArg (x.val ++ ·) (ih ys (by simpa using hl))
  exact h _ _ (x.property.trans y.property.symm)

@[simp] theorem rightBits_zip {B d : ℕ} (x y : List.Vector (Word B) d) :
    RingScan.rightBits (x.val.zip y.val) = wordBits y.val := by
  have h (xs ys : List (Word B)) (hl : xs.length = ys.length) :
      RingScan.rightBits (xs.zip ys) = wordBits ys := by
    induction xs generalizing ys with
    | nil => cases ys <;> simp_all [RingScan.rightBits, wordBits]
    | cons x xs ih =>
      cases ys with
      | nil => simp at hl
      | cons y ys =>
        change y.val ++ RingScan.rightBits (xs.zip ys) = y.val ++ wordBits ys
        exact congrArg (y.val ++ ·) (ih ys (by simpa using hl))
  exact h _ _ (x.property.trans y.property.symm)

end SubexponentialSAT.SqrtLog.RingProgramTable

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_RingProgramTableInitial
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.RingProgramTable

open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.StackRoutines
open SubexponentialSAT.SubexpQuarticRing

abbrev literalBits {B : ℕ} : ℕ → Word B → Word B → List Bool
  | 0, _, _ => []
  | n+1, seed, zeroWord => seed.val ++ literalBits n zeroWord zeroWord

@[simp] theorem literalBits_length {B : ℕ} (n : ℕ) (seed zeroWord : Word B) :
    (literalBits n seed zeroWord).length = n*B := by
  induction n generalizing seed with
  | zero => simp [literalBits]
  | succ n ih =>
      simp only [literalBits, List.length_append, seed.property, ih]
      ring


def literalWords {B : ℕ} : ℕ → Word B → Word B → List (Word B)
  | 0, _, _ => []
  | n+1, seed, zeroWord => seed :: literalWords n zeroWord zeroWord

@[simp] theorem literalWords_length {B : ℕ} (n : ℕ) (seed zeroWord : Word B) :
    (literalWords n seed zeroWord).length = n := by
  induction n generalizing seed with
  | zero => rfl
  | succ n ih => simpa [literalWords] using congrArg Nat.succ (ih zeroWord)

end SubexponentialSAT.SqrtLog.RingProgramTable

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_RingProgramTablePowers
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.RingProgramTable

open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.StackRoutines
open SubexponentialSAT.SubexpLiftRing SubexponentialSAT.SubexpQuarticRing

def iterData (p t : ℕ) [Fact p.Prime] (M : SubexpPreparedQuartic.Modulus p t)
    (zeroWord minusOne : Word (baseWidth p t)) {d : ℕ}
    (c : List.Vector (Word (baseWidth p t)) d) : ℕ → VectorData (baseWidth p t) d → VectorData (baseWidth p t) d
  | 0, v => v
  | n+1, v => iterData p t M zeroWord minusOne c n (advance p t M zeroWord minusOne c v)

def generatedBits (p t : ℕ) [Fact p.Prime] (M : SubexpPreparedQuartic.Modulus p t)
    (zeroWord minusOne : Word (baseWidth p t)) {d : ℕ}
    (c : List.Vector (Word (baseWidth p t)) d) : ℕ → VectorData (baseWidth p t) d → List Bool
  | 0, _ => []
  | n+1, v =>
    let next := advance p t M zeroWord minusOne c v
    wordBits next.coefficients.val ++ generatedBits p t M zeroWord minusOne c n next

@[simp] theorem generatedBits_length (p t : ℕ) [Fact p.Prime]
    (M : SubexpPreparedQuartic.Modulus p t) {d : ℕ}
    (zeroWord minusOne : Word (baseWidth p t))
    (c : List.Vector (Word (baseWidth p t)) d) (n : ℕ) (v : VectorData (baseWidth p t) d) :
    (generatedBits p t M zeroWord minusOne c n v).length = n*d*baseWidth p t := by
  induction n generalizing v with
  | zero => simp [generatedBits]
  | succ n ih => simp [generatedBits, ih]; ring

end SubexponentialSAT.SqrtLog.RingProgramTable

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_RingTableLayoutProgramBridge
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.RingTableLayout

open SubexponentialSAT.BitProgram SubexponentialSAT.SubexpQuarticRing

/-- The input is power-major: all coefficients of P0, then P1, and so on. -/
def powerRecords {d B : ℕ} (P : ℕ → Fin d → Word B) (n : ℕ) : List (List Bool) :=
  (List.ofFn fun a : Fin n => List.ofFn fun k : Fin d => (P a.val k).val).flatten

theorem powerRecords_eq_ofFn {d B : ℕ} (P : ℕ → Fin d → Word B) (n : ℕ) :
    powerRecords P n =
      List.ofFn (fun x : Fin (n*d) => (P x.divNat.val x.modNat).val) := by
  rw [powerRecords, List.ofFn_mul]
  apply congrArg List.flatten
  apply congrArg List.ofFn
  funext a
  apply congrArg List.ofFn
  funext k
  have hd : 0 < d := (Nat.zero_le k.val).trans_lt k.isLt
  have hdiv : (a.val*d+k.val)/d = a.val := by
    rw [Nat.mul_comm a.val d, Nat.mul_add_div hd, Nat.div_eq_of_lt k.isLt]
    omega
  have hmod : (a.val*d+k.val)%d = k.val := by
    simp [Nat.mod_eq_of_lt k.isLt]
  simp only [Fin.divNat, Fin.modNat, hdiv]
  have hk : (⟨(a.val*d+k.val)%d, by omega⟩ : Fin d) = k := Fin.ext hmod
  simp only [hk]

@[simp] theorem powerRecords_length {d B : ℕ} (P : ℕ → Fin d → Word B) (n : ℕ) :
    (powerRecords P n).length = n*d := by simp [powerRecords_eq_ofFn]

end SubexponentialSAT.SqrtLog.RingTableLayout

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_Subexp_PairPreparationProgram
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# Preparing all selected pair plans once per assignment step

The fixed program preserves the full seed-index records, original pair
records, seed count, and processed counter. It computes the next cutoff,
builds each pair's actual selection table, and emits selected pair records.
The candidate value is not an input to this preparation phase.
-/

namespace SubexponentialSAT.Subexp.PairPreparationProgram

open BitProgram StructuredCalls StackRoutines

abbrev PlanPair := PairScoreProgram.PlanPair

end SubexponentialSAT.Subexp.PairPreparationProgram

end OAI.Algorithms
end


