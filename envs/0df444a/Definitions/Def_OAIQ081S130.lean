-- Prove2me | Definitions.Def_OAIQ081S130
-- name    : OAIQ081S130
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-29T22:40:09.672826+00:00
-- url     : https://prove2.me/theorems/4f0a6cde-b61d-4a8b-ab54-2165609a48f2
-- title:
--   Definitions bundle OAIQ081S130 of the split of OpenAI, The Exponential Time Hypothesis is False
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.exact_count_and_sat`, carved from OpenAI's openai/math development (OpenAI, *The Exponential Time Hypothesis is False*, OpenAI Math Release, October 25, 2026, result family 378, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 80 declarations of OpenAI's Lean: 61 definitions, 1 inductive type or structure and 18 theorems. The definitions and types are `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgram.SourceReady.rawLow`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafQueryFrontend.binary`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafQueryFrontend.cleaned`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafQueryFrontend.cleanupCost`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafQueryFrontend.convertStatistics`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafQueryFrontend.countHashes`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafQueryFrontend.finishCall`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafQueryFrontend.lowCall`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafQueryFrontend.lowMask`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafQueryFrontend.maskCall`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafQueryFrontend.numericStage`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafQueryFrontend.prepareScopes`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafQueryFrontend.rawCommand`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafQueryFrontend.scopeCall`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafQueryFrontend.sequence`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafQueryFrontend.statsCall`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafStatisticsProgram.Code`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafStatisticsProgram.accumulateLow`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafStatisticsProgram.boot`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafStatisticsProgram.command`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafStatisticsProgram.copied`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafStatisticsProgram.copy`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafStatisticsProgram.countDegree`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafStatisticsProgram.factorCount`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafStatisticsProgram.initial`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafStatisticsProgram.maximum`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafStatisticsProgram.neutralize`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafStatisticsProgram.peek`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafStatisticsProgram.peeked`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafStatisticsProgram.pop`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafStatisticsProgram.popped`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafStatisticsProgram.program`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafStatisticsProgram.pushTrue`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafStatisticsProgram.pushedTrue`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafStatisticsProgram.transfer`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafStatisticsProgram.transferred`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafStatisticsProgram.variableLoop`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafStatisticsProgram.variableScan`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafStatisticsProgram.variableState`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafStatisticsProgram.variableStep` and 22 more.
--
--   **Sources.** They come from these modules of lean/OAI/Algorithms, in whole or in part: `SubexponentialSAT_SqrtLog_LeafProgramSourceReadyArithmetic`, `SubexponentialSAT_SqrtLog_LeafQueryFrontendCalls`, `SubexponentialSAT_SqrtLog_LeafQueryFrontendCommand`, `SubexponentialSAT_SqrtLog_LeafQueryFrontendConvert`, `SubexponentialSAT_SqrtLog_LeafQueryFrontendFinish`, `SubexponentialSAT_SqrtLog_LeafQueryFrontendNumericRun`, `SubexponentialSAT_SqrtLog_LeafQueryFrontendRawRun`, `SubexponentialSAT_SqrtLog_LeafQueryFrontendScopeCall`, `SubexponentialSAT_SqrtLog_LeafRingSetupProgramNative`, `SubexponentialSAT_SqrtLog_LeafRingSetupProgramReplay`, `SubexponentialSAT_SqrtLog_LeafRingSetupProgramWords`, `SubexponentialSAT_SqrtLog_LeafStatisticsProgramBoot`, `SubexponentialSAT_SqrtLog_LeafStatisticsProgramPrimitives`, `SubexponentialSAT_SqrtLog_LeafStatisticsProgramVariables`, `SubexponentialSAT_SqrtLog_MomentsProgramDictionaryCode`, `SubexponentialSAT_SqrtLog_MomentsProgramNormalize`, `SubexponentialSAT_SqrtLog_MomentsProgramProduct`, `SubexponentialSAT_SqrtLog_MomentsReadoutProgramFetch`, `SubexponentialSAT_SqrtLog_MomentsReadoutProgramState`, `SubexponentialSAT_SqrtLog_NativePackingBounds`, `SubexponentialSAT_SqrtLog_NativePackingBoundsAddress`, `SubexponentialSAT_SqrtLog_NativePackingBoundsTail`, `SubexponentialSAT_SqrtLog_NodeTimeColumns`, `SubexponentialSAT_SqrtLog_PackingCallerProgramBasic`, `SubexponentialSAT_SqrtLog_PackingCallerProgramWide`, `SubexponentialSAT_SqrtLog_PackingCompletionScore`, `SubexponentialSAT_SqrtLog_PackingIncidenceInputNative`, `SubexponentialSAT_SqrtLog_PackingIncidenceProgramInputs`, `SubexponentialSAT_SqrtLog_RingCoefficientLiftProgramTable`, `SubexponentialSAT_Subexp_CandidateContextRefinement`, `SubexponentialSAT_Subexp_CandidateScoreProgram`, `SubexponentialSAT_Subexp_PairPreparationProgram`.
--
--   **Imports.** It imports the published bundle `Def_SubexponentialSAT`; the bundles `OAIQ081S100`, `OAIQ081S102`, `OAIQ081S103`, `OAIQ081S106`, `OAIQ081S107`, `OAIQ081S109` and `OAIQ081S110` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ081S141`, `OAIQ081S146`, `OAIQ081S147`, `OAIQ081S148`, `OAIQ081S149` and `OAIQ081S150`; the statements `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafQueryFrontend.convertStatistics_eval`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafQueryFrontend.lowMask_eval`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafQueryFrontend.maskCall_eval`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafQueryFrontend.rawCommand_eval`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafQueryFrontend.scopeCall_eval`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafQueryFrontend.statsCall_eval`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafStatisticsProgram.accumulateLow_eval` and `OAI.Algorithms.SubexponentialSAT.SqrtLog.MomentsReadoutProgram.fetchAdd_code`; the proofs of `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafQueryFrontend.convertStatistics_eval`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafQueryFrontend.lowMask_eval`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafQueryFrontend.maskCall_eval`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafQueryFrontend.rawCommand_eval`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafQueryFrontend.scopeCall_eval`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafQueryFrontend.statsCall_eval`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafStatisticsProgram.accumulateLow_eval`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.MomentsProgram.Dictionary.insert_code_eval` and `OAI.Algorithms.SubexponentialSAT.SqrtLog.MomentsReadoutProgram.fetchAdd_code`.
-- source:
--   OpenAI, The Exponential Time Hypothesis is False, OpenAI Math Release, October 25, 2026, https://github.com/openai/math (result family 378; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/The-Exponential-Time-Hypothesis-is-False-October-25-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Algorithms at commit 7ef5c0c

import Mathlib
import Definitions.Def_SubexponentialSAT
import Definitions.Def_OAIQ081S100
import Definitions.Def_OAIQ081S102
import Definitions.Def_OAIQ081S103
import Definitions.Def_OAIQ081S106
import Definitions.Def_OAIQ081S107
import Definitions.Def_OAIQ081S109
import Definitions.Def_OAIQ081S110

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafProgramSourceReadyArithmetic
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! The arithmetic half of physical source readiness is preserved by source
control copies. The source-count initializer uses R+1, independently of J. -/
namespace SubexponentialSAT.SqrtLog.LeafProgram.SourceReady
open SubexponentialSAT BitProgram StructuredCalls SubexpConvolutionControl DensePolynomialProgram
open SubexponentialSAT.SubexpLiftRing SubexponentialSAT.SubexpQuarticRing
open LayoutSourceRowsProgram
attribute [local simp] Fin.coe_ofNat_eq_mod

def rawLow (a : Data) : Fin 256 → List Bool := a.stacks ∘ localPort ∘ executorPorts

end SubexponentialSAT.SqrtLog.LeafProgram.SourceReady

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafStatisticsProgramPrimitives
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Fixed-register local operations for the actual residual statistics scan. -/
namespace SubexponentialSAT.SqrtLog.LeafStatisticsProgram
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls
abbrev Code := Cmd 10 21

def copy (src dst tmp : Fin 21) : Code :=
  .call (StackRoutines.copyProgram src dst tmp 0 1)
def copied (src dst : Fin 21) (a : Data) : Data :=
  ⟨readRegs a.regs 0 1 none, StackRoutines.copyStacks src dst a.stacks⟩

def transfer (src dst : Fin 21) : Code :=
  .call (StackRoutines.transferProgram src dst 0 1)
def transferred (src dst : Fin 21) (a : Data) : Data :=
  ⟨readRegs a.regs 0 1 none, StackRoutines.transferStacks src dst a.stacks⟩

def pushTrue (dst : Fin 21) : Code :=
  .seq (.base (.atom (.set 0 true))) (.base (.atom (.push dst 0)))
def pushedTrue (dst : Fin 21) (a : Data) : Data :=
  ⟨Function.update a.regs 0 true, Function.update a.stacks dst (true::a.stacks dst)⟩

def pop (src : Fin 21) : Code := .base (.atom (.pop src 0 1))
def popped (src : Fin 21) (a : Data) : Data :=
  ⟨readRegs a.regs 0 1 (a.stacks src).head?, Function.update a.stacks src (a.stacks src).tail⟩

def peek (src : Fin 21) : Code := .base (.atom (.peek src 0 1))
def peeked (src : Fin 21) (a : Data) : Data :=
  ⟨readRegs a.regs 0 1 (a.stacks src).head?,a.stacks⟩

def maximum : Code := .call (ProgramLinking.liftProgram Max.program maxRegs maxStacks)

end SubexponentialSAT.SqrtLog.LeafStatisticsProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafStatisticsProgramVariables
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Exact runtime accumulation of residual variable statistics. Each degree is
computed by scanning the serialized original scopes. -/
namespace SubexponentialSAT.SqrtLog.LeafStatisticsProgram
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls
def variableState (r : Fin 10 → Bool) (scopes : List (List ℕ))
    (v : ℕ) (mask master : List Bool) (t : Totals) : Data :=
  ⟨r, ![scopeBits scopes,unary scopes.length,unary v,[],[],[],[],[],[],[],[],[],[],
    mask,unary t.free,unary t.occurrence,unary t.incidences,unary t.uncovered,[],[],master]⟩

def countDegree : Code := .call (ProgramLinking.liftProgram
  SubexpIncidenceSlotProgram.program id countPorts)

def neutralize : Code := .seq (peek 3)
  (.ite 1 (.base .skip) (.seq (pushTrue 3) (pushTrue 17)))

def accumulateLow : Code := .seq (pushTrue 14) (.seq (pop 3)
  (.seq neutralize (.seq (copy 3 18 19) (.seq (transfer 3 16) maximum))))

def variableStep : Code := .seq countDegree (.seq (pop 13)
  (.seq (.ite 0 (WorkspaceCleanupProgram.command 0 1 [3]) accumulateLow)
    (.seq (pushTrue 2) (peek 13))))

def variableLoop : Code := .while 1 variableStep
def variableScan : Code := .seq (peek 13) variableLoop

end SubexponentialSAT.SqrtLog.LeafStatisticsProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafStatisticsProgramBoot
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! The variable scan is started from actual serialized scopes and a mask.
The factor count is obtained by a physical record scan, never supplied as data. -/
namespace SubexponentialSAT.SqrtLog.LeafStatisticsProgram
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls

def initial (r : Fin 10 → Bool) (scopes : List (List ℕ)) (mask : List Bool) : Data :=
  ⟨r, ![scopeBits scopes,[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],mask]⟩

def factorCount : Code := .call (ProgramLinking.liftProgram
  SubexpScopeCountSetup.counterProgram factorRegs factorStacks)

def boot : Code := .seq (copy 0 3 4) (.seq factorCount (copy 20 13 4))

def command : Code := .seq boot variableScan
def program := compiled command 0 16

end SubexponentialSAT.SqrtLog.LeafStatisticsProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafQueryFrontendCalls
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! The frontend calls only concrete finite machines. All state embeddings
below are specifications of actual calls, never free data transformations. -/
namespace SubexponentialSAT.SqrtLog.LeafQueryFrontend
open SubexponentialSAT BitProgram StructuredCalls

def maskCall : Code := .call (ProgramLinking.liftProgram HighIncidenceProgram.Mask.program r2 mask)
def statsCall : Code := .call (ProgramLinking.liftProgram LeafStatisticsProgram.program r10 stats)
def finishCall : Code := .call (ProgramLinking.liftProgram LeafStatisticsProgram.Finalize.program r3 finish)

end SubexponentialSAT.SqrtLog.LeafQueryFrontend

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafQueryFrontendScopeCall
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Scope-only parsing uses a fixed t=1,d=0 dummy scalar shape. It requires
no ring parameter input and retains every hash and optional marked row. -/
namespace SubexponentialSAT.SqrtLog.LeafQueryFrontend
open SubexponentialSAT BitProgram StructuredCalls

def scopeCall : Code := .call (ProgramLinking.liftProgram HashScopeProgram.Complete.program r11 scopes)

end SubexponentialSAT.SqrtLog.LeafQueryFrontend

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafQueryFrontendCommand
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Fixed native syntax from physical formula/row masters through the guarded
parameter bank. The only static input is the fixed formula-width bound k. -/
namespace SubexponentialSAT.SqrtLog.LeafQueryFrontend
open SubexponentialSAT BitProgram StructuredCalls

def sequence : List Code → Code
  | [] => .base .skip
  | c::cs => .seq c (sequence cs)

def prepareScopes : Code := sequence [copies scopeCopies,loadBits 515 [false,false],resetScopeRegs]

def binary (src dst : Fin 768) : Code :=
  .call (ProgramLinking.liftProgram LeafStatisticsProgram.Binary.program r3 (binaryPorts src dst))

def countHashes : Code := sequence [copy 701 647,
  .call (ProgramLinking.liftProgram SubexpScopeCountSetup.counterProgram r2 countPorts)]

def lowCall : Code := .call (ProgramLinking.liftProgram HeadIdentifierProgram.LowMask.program r2 lowPorts)
def lowMask : Code := .seq (copy 338 668) lowCall

end SubexponentialSAT.SqrtLog.LeafQueryFrontend

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafQueryFrontendConvert
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.LeafQueryFrontend
open SubexponentialSAT BitProgram StructuredCalls

def convertStatistics : Code := sequence [binary 626 341, binary 627 343, binary 642 344, binary 613 345, binary 628 347]

end SubexponentialSAT.SqrtLog.LeafQueryFrontend

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafQueryFrontendFinish
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.LeafQueryFrontend
open SubexponentialSAT BitProgram StructuredCalls
attribute [local simp] Fin.coe_ofNat_eq_mod

def cleaned (a : Data) : Data := ⟨readRegs a.regs 0 1 none,BankRoutines.clearBankStacks cleanupPorts a.stacks⟩
def cleanupCost (a : Data) := 2*(cleanupPorts.map (fun i => (a.stacks i).length)).sum+789

end SubexponentialSAT.SqrtLog.LeafQueryFrontend

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafQueryFrontendNumericRun
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.LeafQueryFrontend
open SubexponentialSAT BitProgram StructuredCalls
attribute [local simp] Fin.coe_ofNat_eq_mod
open LeafParametersProgram


def numericStage (k : ℕ) : Code := .seq (copies [(709,340),(707,342)])
  (.seq (loadBits 346 k.bits) convertStatistics)

end SubexponentialSAT.SqrtLog.LeafQueryFrontend

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafQueryFrontendRawRun
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! The raw scope call is fed by physical copies of the seven frontend masters. -/
namespace SubexponentialSAT.SqrtLog.LeafQueryFrontend
open SubexponentialSAT BitProgram StructuredCalls
attribute [local simp] Fin.coe_ofNat_eq_mod


def rawCommand : Code := .seq prepareScopes (.seq scopeCall (copy 546 718))

end SubexponentialSAT.SqrtLog.LeafQueryFrontend

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafRingSetupProgramWords
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Paid word movement and binary-to-unary conversion used by ring setup.
The helpers update actual tapes; a state equality is never used as a free
copy, clear, or counter conversion. -/
namespace SubexponentialSAT.SqrtLog.LeafRingSetupProgram

open BitProgram StructuredCalls StackRoutines

/-- The unary counter is generated by the actual bounded conversion loop.
The only cleared inputs required here are its destination and three local
scratch tapes; callers pay to establish those using `clear_eval`. -/
theorem unary_eval (src dst : Fin 640) (a : Data)
    (hs : src.val < 625) (hd : dst.val < 625) (hne : src ≠ dst)
    (h1 : a.stacks dst = []) (h11 : a.stacks 636 = [])
    (h12 : a.stacks 637 = []) (h13 : a.stacks 638 = []) :
    ∃ n ≤ LeafParametersProgram.Serialization.unaryCopyBound (a.stacks src)+1,
      Eval (unary src dst) n a
        (embedState unaryRegisters (unaryPorts src dst) a
          (SubexpClauseMastersProgram.write
            (projectState unaryRegisters (unaryPorts src dst) a) 1
            (List.replicate (BinaryArithmetic.toNat (a.stacks src)) true))) := by
  let d := projectState unaryRegisters (unaryPorts src dst) a
  obtain ⟨n, hn, he⟩ := LeafParametersProgram.Serialization.unaryCopy_eval 0 1 d
    (by decide) (by decide) (by decide) (by decide)
    (by simpa [d, projectState, unaryPorts] using h1)
    (by simpa [d, projectState, unaryPorts] using h11)
    (by simpa [d, projectState, unaryPorts] using h12)
    (by simpa [d, projectState, unaryPorts] using h13)
  refine ⟨n+1, ?_, ?_⟩
  · simpa [d, projectState, unaryPorts] using Nat.add_le_add_right hn 1
  · simpa [unary, d, projectState, unaryPorts] using
      eval_liftCommand_from_state (LeafParametersProgram.Serialization.unaryCopy 0 1)
        0 1 unaryRegisters (unaryPorts src dst) a unaryRegisters_injective
        (unaryPorts_injective src dst hs hd hne) he

end SubexponentialSAT.SqrtLog.LeafRingSetupProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_RingCoefficientLiftProgramTable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.RingCoefficientLiftProgram
open SubexponentialSAT.BitProgram

theorem modelCoefficientBits (t : ℕ) {d : ℕ} (a : RingModel.Data d) :
    RingProgramTable.wordBits
        (List.Vector.ofFn (RingProgram.liftCoefficientsRun t a.coefficients).1).val =
      RingProgram.flat (RingProgram.liftCoefficientsRun t a.coefficients).1 := by
  change (((List.Vector.ofFn (RingProgram.liftCoefficientsRun t a.coefficients).1).toList).map
    Subtype.val).flatten = _
  rw [List.Vector.toList_ofFn,List.map_ofFn]
  rfl

end SubexponentialSAT.SqrtLog.RingCoefficientLiftProgram

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
open BitProgram StructuredCalls

/-- A convenient stack-only form of the paid unary-conversion theorem. -/
theorem unary_eval_stacks (src dst : Fin 640) (a : Data)
    (hs : src.val < 625) (hd : dst.val < 625) (hne : src ≠ dst)
    (h1 : a.stacks dst = []) (h11 : a.stacks 636 = [])
    (h12 : a.stacks 637 = []) (h13 : a.stacks 638 = []) :
    ∃ n ≤ LeafParametersProgram.Serialization.unaryCopyBound (a.stacks src)+1,
      ∃ e : Data, Eval (unary src dst) n a e ∧
        e.stacks=Function.update a.stacks dst
          (List.replicate (BinaryArithmetic.toNat (a.stacks src)) true) := by
  obtain ⟨n,hn,he⟩ := unary_eval src dst a hs hd hne h1 h11 h12 h13
  refine ⟨n,hn,_,he,?_⟩
  change Function.extend (unaryPorts src dst)
    (Function.update (projectState unaryRegisters (unaryPorts src dst) a).stacks 1
      (List.replicate (BinaryArithmetic.toNat (a.stacks src)) true)) a.stacks = _
  rw [ProgramLinking.extend_update (unaryPorts_injective src dst hs hd hne)]
  have hb := congrArg StructuredProgram.State.stacks
    (embedState_project unaryRegisters (unaryPorts src dst) a
      unaryRegisters_injective (unaryPorts_injective src dst hs hd hne))
  change Function.extend (unaryPorts src dst)
    (projectState unaryRegisters (unaryPorts src dst) a).stacks a.stacks=a.stacks at hb
  rw [hb]
  rfl

end SubexponentialSAT.SqrtLog.LeafRingSetupProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafRingSetupProgramReplay
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms


/-! Syntactic no-read/no-write certificate for the existing native ring
producer.  Hidden collector tapes do not affect its exact execution time. -/
namespace SubexponentialSAT.SqrtLog.LeafRingSetupProgram.Replay
open BitProgram StructuredCalls ProgramTapeReplay

theorem reset {r s : ℕ} (H : Fin s → Prop) (ps : List (Fin r)) :
    AvoidsCmd H (RegisterResetProgram.clear ps) := by
  induction ps with
  | nil => trivial
  | cons p ps ih => exact ⟨trivial,ih⟩

theorem resetAll : AvoidsCmd hidden (RegisterResetProgram.all : Cmd 32 640) := reset _ _

theorem unary (src dst : Fin 640) (hs : ¬hidden src) (hd : ¬hidden dst) :
    AvoidsCmd hidden (LeafRingSetupProgram.unary src dst) := by
  apply avoids_call_lift_of_range
  intro i
  unfold unaryPorts
  split_ifs
  · exact hs
  · exact hd
  · apply visible
    right
    dsimp
    omega

end SubexponentialSAT.SqrtLog.LeafRingSetupProgram.Replay

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_MomentsProgramDictionaryCode
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.MomentsProgram.Dictionary
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.StackRoutines
open SubexponentialSAT.SubexpLiftRing SubexponentialSAT.SubexpQuarticRing

variable {K : Type*} [DecidableEq K]

def codePairs {B d : ℕ} (x y : RingProgram.Code (Word B) d) : List (Word B × Word B) :=
  List.ofFn fun i => (x i,y i)

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

def peeked (d : Data) : Data :=
  ⟨readRegs d.regs 0 7 (d.stacks 27).head?,d.stacks⟩

end SubexponentialSAT.SqrtLog.MomentsProgram.Normalize


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
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls
open SubexponentialSAT.SubexpLiftRing SubexponentialSAT.SubexpQuarticRing

def ready (regs : Fin 8 → Bool) (a : Store) : Data :=
  state (readRegs regs 0 7 a.left.head?) a

end SubexponentialSAT.SqrtLog.MomentsProgram.Product

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_MomentsReadoutProgramFetch
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! A paid dictionary scan followed by native vector addition. A missing
coefficient contributes zero and leaves the accumulator unchanged. -/
namespace SubexponentialSAT.SqrtLog.MomentsReadoutProgram
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.StackRoutines
open SubexponentialSAT.SubexpLiftRing SubexponentialSAT.SubexpQuarticRing
open MomentsProgram.Dictionary

variable {K : Type*} [DecidableEq K]

def addFetched (p e : ℕ) [Fact p.Prime] (M : SubexpPreparedQuartic.Modulus p e)
    (cache : RingProgram.ScalarCache p e) {d : ℕ}
    (entries : List (K × RingProgram.Code (Word (baseWidth p e)) d)) (k : K)
    (acc : RingProgram.Code (Word (baseWidth p e)) d) :=
  match entries.lookup k with
  | none => acc
  | some x => (RingProgram.addRun (RingProgram.scalarProgram p e M cache) acc x).1

end SubexponentialSAT.SqrtLog.MomentsReadoutProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_MomentsReadoutProgramState
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! A fixed forty-stack workspace for the two runtime readout counters. -/
namespace SubexponentialSAT.SqrtLog.MomentsReadoutProgram
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.StackRoutines
open SubexponentialSAT.SubexpLiftRing SubexponentialSAT.SubexpQuarticRing

def wcopied (d : WideData) (src dst : Fin 40) : WideData :=
  ⟨readRegs d.regs 0 1 none,copyStacks src dst d.stacks⟩
def wtransferred (d : WideData) (src dst : Fin 40) : WideData :=
  ⟨readRegs d.regs 0 1 none,transferStacks src dst d.stacks⟩
def wcleared (d : WideData) (src : Fin 40) : WideData :=
  ⟨readRegs d.regs 0 1 none,clearStacks src d.stacks⟩

def wpushed (d : WideData) (dst : Fin 40) (bit : Bool) : WideData :=
  ⟨Function.update d.regs 0 bit,Function.update d.stacks dst (bit::d.stacks dst)⟩

end SubexponentialSAT.SqrtLog.MomentsReadoutProgram


/-! Actual stack construction of the sparse key (u,z,empty support), followed
by the paid query cleanup and unary-index increment. -/


/-! One concrete (u,z) coefficient fetch, addition, and index advance. -/
namespace SubexponentialSAT.SqrtLog.MomentsReadoutProgram
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls
open SubexponentialSAT.SubexpLiftRing SubexponentialSAT.SubexpQuarticRing

def foldU {n d : ℕ} (p e : ℕ) [Fact p.Prime]
    (M : SubexpPreparedQuartic.Modulus p e) (cache : RingProgram.ScalarCache p e)
    (entries : List (Squarefree.Index (Fin n) × RingProgram.Code (Word (baseWidth p e)) d))
    (z : ℕ) : ℕ → ℕ → RingProgram.Code (Word (baseWidth p e)) d →
      RingProgram.Code (Word (baseWidth p e)) d
  | _,0,acc => acc
  | u,k+1,acc => foldU p e M cache entries z (u+1) k
      (addFetched p e M cache entries ⟨u,z,∅⟩ acc)

end SubexponentialSAT.SqrtLog.MomentsReadoutProgram


/-! The U loop is driven by a real unary stack. Every visit invokes the
concrete key builder and dictionary scan; no callback is left abstract. -/


/-! Seed one Z accumulator from the cached zero vector and append the
completed coefficient to the output, paying for every copy and reversal. -/


/-! Runtime Z enumeration. Completed fixed-width coefficients are prepended
in reverse and are restored once by the final output transfer. -/
namespace SubexponentialSAT.SqrtLog.MomentsReadoutProgram
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls
open SubexponentialSAT.SubexpLiftRing SubexponentialSAT.SubexpQuarticRing

def outputCodes {n d : ℕ} (p e : ℕ) [Fact p.Prime]
    (M : SubexpPreparedQuartic.Modulus p e) (cache : RingProgram.ScalarCache p e)
    (entries : List (Squarefree.Index (Fin n) × RingProgram.Code (Word (baseWidth p e)) d))
    (t : ℕ) (zero : RingProgram.Code (Word (baseWidth p e)) d) :
    ℕ → ℕ → List (RingProgram.Code (Word (baseWidth p e)) d)
  | _,0 => []
  | z,J+1 => foldU p e M cache entries z 0 t zero :: outputCodes p e M cache entries t zero (z+1) J

def outputBits {n d : ℕ} (p e : ℕ) [Fact p.Prime]
    (M : SubexpPreparedQuartic.Modulus p e) (cache : RingProgram.ScalarCache p e)
    (entries : List (Squarefree.Index (Fin n) × RingProgram.Code (Word (baseWidth p e)) d))
    (t : ℕ) (zero : RingProgram.Code (Word (baseWidth p e)) d) (z J : ℕ) : List Bool :=
  ((outputCodes p e M cache entries t zero z J).map RingProgram.flat).flatten

end SubexponentialSAT.SqrtLog.MomentsReadoutProgram


/-! Build the all-false support mask from the actual ambient shape stack.
The loop length is the ambient number of variables, including unused ones. -/

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

@[simp] theorem scoreRecords_length (ctx : Context) :
    (scoreRecords ctx).length = ctx.candidates.length := by simp [scoreRecords]

end SubexponentialSAT.Subexp.CandidateScoreProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_NativePackingBoundsTail
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# Bounds for the actual packing tail

All sizes below come from the represented input and generated records.
There is no assumed runtime certificate: the cost estimates apply to the
same leftover and inverse budgets used by `PackingExecution.program_trace`.
-/

namespace SubexponentialSAT.SqrtLog.NativePackingBounds

open SubexponentialSAT.Subexp SubexponentialSAT.Subexp.ConstructivePacking LayoutProgram LayoutProgram.NativePacking

variable {U : Type*} [DecidableEq U]

theorem word_length_le_encoded (words : List (List Bool))
    (word : List Bool) (hw : word ∈ words) :
    word.length ≤ (ProgramEncoding.encodeRecords words).length := by
  induction words with
  | nil => simp at hw
  | cons first rest ih =>
    have hlen : (ProgramEncoding.encodeRecords (first :: rest)).length =
        2 * first.length + 2 + (ProgramEncoding.encodeRecords rest).length := by
      exact Encoding.length_encodeList_cons id first rest
    rcases List.mem_cons.mp hw with rfl | hw
    · omega
    · have ht := ih hw
      omega

theorem encoded_vertices_length_le (s : Spec U) (vs : List (Fin s.suffix.params.D))
    (hn : vs.length ≤ s.suffix.params.D) :
    (ProgramEncoding.encodeRecords (vs.map s.suffix.encodeVertex)).length ≤ wordBound s.suffix.params.D := by
  have h := ProgramEncoding.encodeRecords_length_le (vs.map s.suffix.encodeVertex) s.suffix.params.D (by
    intro word hw
    obtain ⟨v, _, rfl⟩ := List.mem_map.mp hw
    simpa only [PackLabels.Spec.encodeVertex, List.length_replicate] using Nat.le_of_lt v.isLt)
  simp only [List.length_map] at h
  exact h.trans (Nat.add_le_add_left (Nat.mul_le_mul_left _ hn) 1)

theorem queries_length_le (D : ℕ) :
    (ProgramEncoding.encodeRecords (PackingProgram.inverseQueries D)).length ≤ wordBound D := by
  have h := ProgramEncoding.encodeRecords_length_le (PackingProgram.inverseQueries D) D (by
    intro word hw
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hw
    have hi' : i < D := by
      simpa only [List.mem_reverse, ← List.range_eq_range', List.mem_range] using hi
    simpa only [PackingMetadata.unary, List.length_replicate] using Nat.le_of_lt hi')
  simpa only [PackingProgram.inverseQueries, List.length_map, List.length_reverse,
    List.length_range', wordBound] using h

end SubexponentialSAT.SqrtLog.NativePackingBounds

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_NativePackingBounds
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Polynomial cost of the actual native address-plan suffix. -/
namespace SubexponentialSAT.SqrtLog.NativePackingBounds
open SubexponentialSAT.Subexp SubexponentialSAT.BitProgram LayoutProgram
variable {U : Type*} [DecidableEq U]

theorem block_count_le (s : NativePacking.Spec U) : s.suffix.packing.blockCount ≤ s.params.D := by
  rw [← PackLabels.minimum_eq s.suffix]
  exact PackingBucketTable.minimum_le _ _ _

end SubexponentialSAT.SqrtLog.NativePackingBounds

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_NativePackingBoundsAddress
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Explicit scalar envelope for the actual two-address packing call. -/
namespace SubexponentialSAT.SqrtLog.NativePackingBounds
open SubexponentialSAT.Subexp SubexponentialSAT.MulticolorTypes LayoutProgram

variable {D r Q : ℕ}

theorem address_plan_stream_le (words : List (Word r Q))
    (address : Fin D → Fin words.length × Fin words.length) :
    (ProgramEncoding.encodeRecords ((labelPlans words address).map PackingVertexLabels.planPayload)).length
      ≤ 1+(16*words.length+24)*D := by
  have hp : ∀ plan∈labelPlans words address,
      (PackingVertexLabels.planBytes plan).length ≤ 4*words.length+5 := by
    intro plan hm
    obtain ⟨i,hi,rfl⟩ := List.mem_map.mp hm
    have h1 := (address i).1.isLt
    have h2 := (address i).2.isLt
    simp only [PackingVertexLabels.planBytes,GatherProgram.encoded_plan_length,
      List.sum_cons,List.sum_nil,List.length_cons,List.length_nil]
    omega
  have h := ProgramEncoding.encodeRecords_length_le
    ((labelPlans words address).map PackingVertexLabels.planPayload) (8*words.length+11) (by
      intro p hm
      obtain ⟨plan,hplan,rfl⟩ := List.mem_map.mp hm
      have h := hp plan hplan
      simpa [PackingVertexLabels.planPayload,PackingVertexLabels.planBytes,
        Encoding.length_frame] using (show 2*(PackingVertexLabels.planBytes plan).length+1 ≤ 8*words.length+11 by omega))
  simp only [List.length_map,labelPlans,List.length_finRange] at h
  unfold labelPlans
  calc
    _ ≤ 1+(2*(8*words.length+11)+2)*D := h
    _ = 1+(16*words.length+24)*D := by ring

end SubexponentialSAT.SqrtLog.NativePackingBounds

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

def remaining (M processed : ℕ) (pair : PlanPair) : List ℕ :=
  ActivePlanProgram.active (List.range M) (pair.1.reverse ++ pair.2) (processed + 1)

def selectedPair (M processed : ℕ) (pair : PlanPair) : PlanPair :=
  (pair.1.map (ReadPlan.selectPosition M (remaining M processed pair)),
   pair.2.map (ReadPlan.selectPosition M (remaining M processed pair)))

def selectedPairs (M processed : ℕ) (pairs : List PlanPair) : List PlanPair :=
  pairs.map (selectedPair M processed)

end SubexponentialSAT.Subexp.PairPreparationProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_Subexp_CandidateContextRefinement
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Candidate contexts and selected plans refine the natural score evaluator. -/

namespace SubexponentialSAT.Subexp.CandidateScoreRefinement

open SubexponentialSAT.MulticolorTypes SubexponentialSAT.SlotAssignment

variable {V E : Type*} [DecidableEq V] [DecidableEq E] [Fintype V] [Fintype E]
variable {r Q Δ : ℕ}
  [NeZero r]
  (P : SubexponentialSAT.Factor.Pattern V E)

/-- Runtime width and processed-index bytes are preserved literally. Only
their lengths enter the semantics. -/
def candidateContext (alphabet : List (Word r Q)) (default : Word r Q)
    (fixed : List (Word r Q)) (remainingCount : ℕ) (width index : List Bool)
    (plans : List PairScoreProgram.PlanPair) : CandidateScoreProgram.Context where
  before := fixed.reverse.map ReadPlan.encodeWord
  old := ReadPlan.encodeWord default
  after := (List.replicate remainingCount default).map ReadPlan.encodeWord
  width := width
  alphabet := alphabet.map ReadPlan.encodeWord
  depth := List.replicate (2 * (Δ + 1)) true
  index := index
  candidates := alphabet.map ReadPlan.encodeWord
  pairs := plans


end SubexponentialSAT.Subexp.CandidateScoreRefinement

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_PackingIncidenceProgramInputs
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Raw incidence-address plans and the exact runtime active-support filter. -/
namespace SubexponentialSAT.SqrtLog.PackingIncidenceProgram
open SubexponentialSAT.MulticolorTypes SubexponentialSAT.LocalExpectation SubexponentialSAT.Subexp SubexponentialSAT.SqrtLog.Packing

section Support
variable {I V E : Type*} [Fintype I] [Fintype V] [Fintype E]
  [DecidableEq I] [DecidableEq V] [DecidableEq E]
  (ivar : I → V) (factor : I → E)

omit [Fintype I] [Fintype V] [Fintype E] [DecidableEq I] in
/-- The runtime cutoff and the mathematical unprocessed suffix coincide,
including repeated addresses caused by shared original-variable heads. -/
theorem remaining_eq_active {Q : ℕ} (indices : List (V ⊕ E))
    (processed n : ℕ) (hsize : n + 1 + processed = indices.length) (pair : I × I) :
    PairPreparationProgram.remaining indices.length processed
      (incidencePair ivar factor indices pair) =
    active (numberedScoreSupport (Q := Q) ivar factor indices (.inl pair))
      (List.range' (processed + 1) n) := by
  unfold PairPreparationProgram.remaining
  rw [ActivePlanProgram.active_range_eq]
  have hn : indices.length - (processed + 1) = n := by omega
  rw [hn]
  unfold active
  congr 1
  funext j
  apply Bool.eq_iff_iff.mpr
  simpa only [decide_eq_true_eq] using plan_support (Q := Q) ivar factor indices pair j

omit [Fintype I] [Fintype V] [Fintype E] [DecidableEq I] in
theorem selectedPair_eq {Q : ℕ} (indices : List (V ⊕ E))
    (processed n : ℕ) (hsize : n + 1 + processed = indices.length) (pair : I × I) :
    PairPreparationProgram.selectedPair indices.length processed
      (incidencePair ivar factor indices pair) =
    (ReadPlan.completionPlan indices.length
      (active (numberedScoreSupport (Q := Q) ivar factor indices (.inl pair))
        (List.range' (processed + 1) n)) (incidencePlan ivar factor indices pair.1),
     ReadPlan.completionPlan indices.length
      (active (numberedScoreSupport (Q := Q) ivar factor indices (.inl pair))
        (List.range' (processed + 1) n)) (incidencePlan ivar factor indices pair.2)) := by
  unfold PairPreparationProgram.selectedPair
  rw [remaining_eq_active ivar factor indices processed n hsize pair]
  rfl
end Support

end SubexponentialSAT.SqrtLog.PackingIncidenceProgram

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


/-! Calls to the fixed record mapper inside the native scope scan. -/


/-! One native low-variable step, including its uncovered neutral factor. -/


/-! Runtime high-mask loop for the original-address incidence stream. -/
namespace SubexponentialSAT.SqrtLog.PackingIncidenceInput.Loop
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.Subexp

def ports : UnaryForPrograms.Ports 16 32 := ⟨26,14,15⟩
end SubexponentialSAT.SqrtLog.PackingIncidenceInput.Loop


/-! Count the physical scope stream before constructing native incidence plans. -/
namespace SubexponentialSAT.SqrtLog.PackingIncidenceInput.Boot
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.Subexp
abbrev count : Cmd 16 32 := .call (ProgramLinking.liftProgram
  SubexpScopeCountSetup.counterProgram registers ports)
end SubexponentialSAT.SqrtLog.PackingIncidenceInput.Boot

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_PackingCompletionScore
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! The primitive raw-plan candidate score equals the packing incidence counter. -/
namespace SubexponentialSAT.SqrtLog.Packing
open SubexponentialSAT.MulticolorTypes SubexponentialSAT.LocalExpectation SubexponentialSAT.Subexp.LocalExpectation
open SubexponentialSAT.Subexp

section Scores
variable {I V E : Type*} [Fintype I] [Fintype V] [Fintype E]
  [DecidableEq I] [DecidableEq V] [DecidableEq E]
variable (ivar : I → V) (factor : I → E) {r Q : ℕ}

omit [Fintype I] [Fintype V] [Fintype E] [DecidableEq I] in
theorem incidenceScorer_pairCount (alphabet : List (Word r Q))
    (indices : List (V ⊕ E)) (hi : ∀ a, a ∈ indices) (default : Word r Q)
    (fixed : List (Word r Q)) (remaining : List ℕ) (hn : remaining.Nodup) (pair : I × I) :
    PairScoreProgram.pairCount (incidenceScorerContext alphabet indices default fixed)
      (incidenceScorerPlan (Q := Q) ivar factor indices remaining pair) =
      scaledCount alphabet (fun η => PackingProgram.incidenceIndicator ivar factor
        (.inl pair) (fun a => η (indexCode indices a)))
        (numberedScoreSupport (Q := Q) ivar factor indices (.inl pair)) 4 remaining
        (decode default fixed) := by
  simpa only [incidenceScorerContext, incidenceScorerPlan, PairScoreProgram.pairCount,
    PairScoreProgram.pairStream, generatedIncidenceLeaves, List.length_replicate,
    ReadPlan.currentArray_length, CollisionTupleProgram.tupleBytes] using
      generatedIncidencePair_count ivar factor alphabet indices hi default fixed
        remaining hn pair.1 pair.2

omit [Fintype I] [Fintype V] [Fintype E] [DecidableEq I] in
theorem incidenceScorer_score (alphabet : List (Word r Q)) (pairs : List (I × I))
    (indices : List (V ⊕ E)) (hi : ∀ a, a ∈ indices) (default : Word r Q)
    (fixed : List (Word r Q)) (remaining : List ℕ) (hn : remaining.Nodup) :
    PairScoreProgram.score (incidenceScorerContext alphabet indices default fixed)
      (pairs.map (incidenceScorerPlan (Q := Q) ivar factor indices remaining)) =
      (PackingProgram.unweightedCounts ivar factor alphabet (pairs.map Sum.inl)
        indices remaining (decode default fixed)).1 := by
  rw [PairScoreProgram.score_eq_sum, List.map_map]
  simp only [Function.comp_def, incidenceScorer_pairCount ivar factor alphabet indices hi
    default fixed remaining hn]
  simp only [PackingProgram.unweightedCounts, commonNumerator, List.map_map, Function.comp_def]

omit [Fintype I] [Fintype V] [Fintype E] [DecidableEq I] in
theorem incidenceScorerPlan_eq_selected (indices : List (V ⊕ E))
    (processed n : ℕ) (hsize : n + 1 + processed = indices.length) (pair : I × I) :
    PairPreparationProgram.selectedPair indices.length processed
      (PackingIncidenceProgram.incidencePair ivar factor indices pair) =
      incidenceScorerPlan (Q := Q) ivar factor indices (List.range' (processed + 1) n) pair := by
  rw [PackingIncidenceProgram.selectedPair_eq (Q := Q) ivar factor indices processed n hsize pair]
  rfl

omit [Fintype I] [Fintype V] [Fintype E] [DecidableEq I] in
theorem candidate_incidenceScore (alphabet : List (Word r Q)) (pairs : List (I × I))
    (indices : List (V ⊕ E)) (hi : ∀ a, a ∈ indices) (default candidate : Word r Q)
    (fixed : List (Word r Q)) (n : ℕ) (width index : List Bool)
    (hsize : n + 1 + fixed.length = indices.length)
    (hw : width.length = ReadPlan.wordWidth r Q) :
    CandidateScoreProgram.candidateScore
      (CandidateScoreRefinement.candidateContext (Δ := 1) alphabet default fixed n width index
        (PairPreparationProgram.selectedPairs indices.length fixed.length
          (pairs.map (PackingIncidenceProgram.incidencePair ivar factor indices))))
      (ReadPlan.encodeWord candidate) =
      (PackingProgram.unweightedCounts ivar factor alphabet (pairs.map Sum.inl)
        indices (List.range' (fixed.length + 1) n) (decode default (candidate :: fixed))).1 := by
  have hp : PairPreparationProgram.selectedPairs indices.length fixed.length
      (pairs.map (PackingIncidenceProgram.incidencePair ivar factor indices)) =
      pairs.map (incidenceScorerPlan (Q := Q) ivar factor indices
        (List.range' (fixed.length + 1) n)) := by
    simp only [PairPreparationProgram.selectedPairs, List.map_map, Function.comp_def,
      incidenceScorerPlan_eq_selected (Q := Q) ivar factor indices fixed.length n hsize]
  unfold CandidateScoreProgram.candidateScore
  rw [hp]
  rw [CandidateScoreRefinement.score_context_congr _
    (incidenceScorerContext alphabet indices default (candidate :: fixed))]
  · exact incidenceScorer_score ivar factor alphabet pairs indices hi default
      (candidate :: fixed) _ List.nodup_range'
  · change fixed.reverse.map ReadPlan.encodeWord ++ ReadPlan.encodeWord candidate ::
      (List.replicate n default).map ReadPlan.encodeWord = _
    change _ = (ReadPlan.currentArray default indices.length (candidate :: fixed)).map ReadPlan.encodeWord
    rw [CandidateScoreRefinement.currentArray_after_candidate default candidate indices.length
      fixed (by omega)]
    have hn : indices.length - (fixed.length + 1) = n := by omega
    simp only [hn, List.map_append, List.map_cons]
  · simpa only [CandidateScoreProgram.pairContext, CandidateScoreRefinement.candidateContext,
      incidenceScorerContext, List.length_replicate] using hw
  · rfl
  · rfl

end Scores
end SubexponentialSAT.SqrtLog.Packing

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_NodeTimeColumns
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.NodeTime
open SubexponentialSAT Subexp SubexpLiftRing SubexpSetupStorage
open LeafHeadSetupProgram LeafHeadSetupProgram.Bounds
open LayoutProgram RowSelectionProgram

structure InputBounds (s : Native.Inputs) (B : ℕ) : Prop where
  n : s.n ≤ B
  D : s.D ≤ B
  r : s.r ≤ B
  Q : s.Q ≤ B
  R : s.R ≤ B
  width : s.width.length ≤ B
  height : s.height.length ≤ B
  metadata : s.metadata.length ≤ B
  plans : (LayoutOwnerFiberProgram.stream s.plans).length ≤ B
  Qr : s.Q*s.r ≤ B

end SubexponentialSAT.SqrtLog.NodeTime

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_PackingCallerProgramBasic
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Framed local storage for the concrete packing caller. Ports53/54 retain
width/alphabet,55..59 parameters,60 scopes,61 plans,62 words,63 metadata. -/
namespace SubexponentialSAT.SqrtLog.PackingCallerProgram
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.SubexpSetupStorage
open PackingLoaderProgram
abbrev Small := State 16 48
abbrev Local := State 16 64

end SubexponentialSAT.SqrtLog.PackingCallerProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_PackingCallerProgramWide
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! The caller's private64-stack workspace lies after the live native
parameter bank340..416, which must survive until ring setup. -/
namespace SubexponentialSAT.SqrtLog.PackingCallerProgram.Wide
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls
abbrev Data := State 40 768
abbrev Local := State 16 768

end SubexponentialSAT.SqrtLog.PackingCallerProgram.Wide

end OAI.Algorithms
end


