-- Prove2me | Definitions.Def_OAIQ081S152
-- name    : OAIQ081S152
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-29T22:54:40.413146+00:00
-- url     : https://prove2.me/theorems/2535eaa7-54f0-43fb-8ee2-1fcf1b37842f
-- title:
--   Definitions bundle OAIQ081S152 of the split of OpenAI, The Exponential Time Hypothesis is False
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.exact_count_and_sat`, carved from OpenAI's openai/math development (OpenAI, *The Exponential Time Hypothesis is False*, OpenAI Math Release, October 25, 2026, result family 378, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 69 declarations of OpenAI's Lean: 65 definitions, 3 inductive types or structures and 1 theorem. The definitions and types are `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighQueryAdapter.CanonicalHigh.command`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighQueryAdapter.CanonicalHigh.prepare`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighQueryAdapter.CanonicalHigh.program`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighQueryAdapter.CanonicalHigh.reset`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighQueryAdapter.HeadSelect.body`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighQueryAdapter.HeadSelect.command`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighQueryAdapter.HeadSelect.drop`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighQueryAdapter.HeadSelect.keep`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighQueryAdapter.HeadSelect.loop`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighQueryAdapter.HeadSelect.program`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighQueryAdapter.NativeHeadSelect.command`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighQueryAdapter.NativeHeadSelect.copy`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighQueryAdapter.NativeHeadSelect.prepare`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighQueryAdapter.NativeHeadSelect.prepareProgram`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighQueryAdapter.NativeHeadSelect.reset`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighQueryAdapter.NativeHeadSelect.select`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighQueryAdapter.copyHighCounter`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighQueryAdapter.resetHigh`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighQueryExecution.canonicalize`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.Native.countingProgram`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.Native.outerCommand`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeCode.graphCall`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeCode.graphStage`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeCode.localCall`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeCode.localStage`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeCode.saveAndClearSteps`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeCode.savedAndCleared`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeCode.searches`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeCodeAssembly.afterMetadata`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeCodeAssembly.serialize`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeLeafPreparation.finishedWords`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeLeafRun.afterPreparation`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeLeafRun.roundsCommand`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.PairNativeSetup.expandCaller`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.PairNativeSetup.expandCommand`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.PairNativeSetup.expandResult`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.PairNativeSetup.fillCommand`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.PairNativeSetup.fillMiddle`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.PairNativeSetup.fillResult`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryAssembler.Nodes.beginNode` and 28 more.
--
--   **Sources.** They come from these modules of lean/OAI/Algorithms, in whole or in part: `SubexponentialSAT_SqrtLogSpace_HighQueryAdapter`, `SubexponentialSAT_SqrtLogSpace_HighQueryExecution`, `SubexponentialSAT_SqrtLogSpace_NativeCode`, `SubexponentialSAT_SqrtLogSpace_NativeCodeAssembly`, `SubexponentialSAT_SqrtLogSpace_NativeLeafPreparation`, `SubexponentialSAT_SqrtLogSpace_NativeLeafRun`, `SubexponentialSAT_SqrtLogSpace_NativeOuter`, `SubexponentialSAT_SqrtLogSpace_PairNativeSetup`, `SubexponentialSAT_SqrtLogSpace_QueryAssembler`, `SubexponentialSAT_SqrtLogSpace_QueryExecution`, `SubexponentialSAT_SqrtLogSpace_SignatureHeadPrepare`, `SubexponentialSAT_SqrtLogSpace_SignatureKeyPackingTransport`, `SubexponentialSAT_SqrtLogSpace_SignatureTupleNative`, `SubexponentialSAT_SqrtLogSpace_SignatureTupleProgram`, `SubexponentialSAT_SqrtLogSpace_SparseCodeSearch`.
--
--   **Imports.** It imports the bundles `OAIQ081S118`, `OAIQ081S119`, `OAIQ081S127`, `OAIQ081S131`, `OAIQ081S133`, `OAIQ081S135`, `OAIQ081S136` and `OAIQ081S137` of this split.
--
--   **Imported by** (directly, in this split): the bundle `OAIQ081S165`; the statements `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeCodeAssembly.afterMetadata_eval`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeCodeAssembly.metadata_searches`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeCode.graph_call`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeCode.local_call`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.Native.counting_primitive_from_entry`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.Native.outer_from_setup`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryVisitorFrames.tupleMultiply_not_mem_writes`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SignatureRescanBridge.probe_run_space`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SignatureTupleLoader.resume_candidate_ready`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SignatureTupleRefinement.advance_endpoint_bound`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SignatureTupleRefinement.duplicate_run_space`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SignatureTupleRefinement.fresh_leaf_run_space`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SignatureTupleRefinement.probe_endpoint_bound`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SignatureTupleRefinement.resume_loaded_storage`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SparseCodeSearch.graph_search_runs` and `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SparseCodeSearch.local_search_runs`; the proofs of `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeCodeAssembly.afterMetadata_eval`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeCodeAssembly.metadata_searches`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeCode.graph_call`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeCode.local_call`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.Native.counting_primitive_from_entry`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.Native.outer_from_setup`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryVisitorFrames.tupleMultiply_not_mem_writes`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SignatureRescanBridge.probe_run_space`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SignatureTupleLoader.resume_candidate_ready`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SignatureTupleRefinement.advance_endpoint_bound`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SignatureTupleRefinement.duplicate_run_space`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SignatureTupleRefinement.fresh_leaf_run_space`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SignatureTupleRefinement.probe_endpoint_bound`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SignatureTupleRefinement.resume_loaded_storage`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SparseCodeSearch.graph_search_runs` and `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SparseCodeSearch.local_search_runs`.
-- source:
--   OpenAI, The Exponential Time Hypothesis is False, OpenAI Math Release, October 25, 2026, https://github.com/openai/math (result family 378; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/The-Exponential-Time-Hypothesis-is-False-October-25-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Algorithms at commit 7ef5c0c

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_OAIQ081S118
import Definitions.Def_OAIQ081S119
import Definitions.Def_OAIQ081S127
import Definitions.Def_OAIQ081S131
import Definitions.Def_OAIQ081S133
import Definitions.Def_OAIQ081S135
import Definitions.Def_OAIQ081S136
import Definitions.Def_OAIQ081S137

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

/-- Cleanup is an actual finite program and accepts arbitrary old buffers. -/
def resetHigh : Code := .seq (.call (StackRoutines.clearProgram 702 0 1))
  (BankRoutines.clearCmd 702 0 1 highChanged)

namespace HeadSelect
open OAI.Algorithms.SubexponentialSAT.StackRoutines

def keep : Code := .seq (.base (.atom (.push 2 2))) (.base (.atom (.push 4 3)))
def drop : Code := .seq (.base (.atom (.copy 2 2))) (.base (.atom (.copy 3 3)))
def body : Code := .seq (.base (.atom (.pop 1 2 3))) (.seq (.ite 0 keep drop) pop)
def loop : Code := .while 1 body
def command : Code := .seq pop (.seq loop (.call (transferProgram 2 3 0 1)))
def program := compiled command 0 3

end HeadSelect

namespace NativeHeadSelect
open OAI.Algorithms.SubexponentialSAT.StackRoutines

def copy (src dst : Fin 896) : Code := .call (copyProgram src dst 880 0 1)
def select : Code := .call (ProgramLinking.liftProgram HeadSelect.program regs stackMap)
def command : Code := .seq (copy 858 878) (.seq (copy 670 879) select)

/-- Cleanup is an actual finite program and accepts arbitrary old buffers. -/
def reset : Code := .seq (.call (StackRoutines.clearProgram 880 0 1))
  (BankRoutines.clearCmd 880 0 1 changed)


def prepare : Code := .seq reset command
def prepareProgram := compiled prepare 858 867

end NativeHeadSelect

open OAI.Algorithms.SubexponentialSAT.StackRoutines

def copyHighCounter : Code := .seq (.call (clearProgram 330 0 1))
  (.seq (.call (clearProgram 792 0 1)) (.call (copyProgram 789 330 792 0 1)))

namespace CanonicalHigh
open DisjointReuse

def command : Code := .call (ProgramLinking.liftProgram
  CanonicalWordProgram.normalizeUnsignedProgram regMap stackMap)

open OAI.Algorithms.SubexponentialSAT.StackRoutines

def reset : Code := .seq (.call (clearProgram 793 0 1)) (.call (clearProgram 794 0 1))

def prepare : Code := .seq reset command
def program := compiled prepare 788 788

end CanonicalHigh


end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighQueryAdapter
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_HighQueryExecution
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! Concrete outer count execution. The final canonicalization and marked
return consume the entire accumulated binary count. Their compact boundary is
proved separately from the transient workspace used by the query. -/
namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighQueryExecution

open OAI BitProgram StructuredCalls HighQueryAdapter DisjointReuse
open HashGreedyProgram.NativeRound

/-- The actual unsigned normalizer is run once after all high assignments. -/
def canonicalize : Code := .call CanonicalHigh.program

open OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafOuterProgram OAI.Algorithms.SubexponentialSAT.StackRoutines

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighQueryExecution
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_SparseCodeSearch
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SparseCodeSearch

open BitProgram StructuredCalls CodeCandidateProgram

/-- Runtime preparation, all matrix attempts and final cleanup are fixed code.
The retained valid matrix stays at the concrete candidate's matrix port. -/
def command (candidate : Cmd 16 48) : Cmd 16 48 :=
  .seq (prepareSearch setupPorts) (.seq (.call (core candidate)) cleanup)


open OAI.Algorithms.SubexponentialSAT.SqrtLog OAI.Algorithms.SubexponentialSAT.SqrtLog.CodeSearchProgram CodeChecks

def localSearch : Cmd 16 48 := command localMatrixCandidate

def graphSearch : Cmd 16 48 := command graphMatrixCandidate

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SparseCodeSearch
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_NativeCode
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! Fixed physical stages for the streamed local-code and graph-code searches.
The retained search state is confined to the lower48 leaf stacks; selected
matrices are saved outside that bank before its paid cleanup. -/
namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeCode

open BitProgram StructuredCalls
open SqrtLog SqrtLog.LeafOuterProgram SqrtLog.CodeSearchProgram

def graphCall : Cmd 40 896 := .call
  (ProgramLinking.liftProgram (compiled SparseCodeSearch.graphSearch 46 29) registers stackMap)

def localCall : Cmd 40 896 := .call
  (ProgramLinking.liftProgram (compiled SparseCodeSearch.localSearch 46 18) registers stackMap)

def graphStage : Cmd 40 896 :=
  .seq (routes graphInputs) (.seq graphCall (.seq (route (29,816)) clearLower))

def localStage : Cmd 40 896 :=
  .seq (routes localInputs) (.seq localCall (.seq (route (18,815)) clearLower))

/-- Graph first, followed by the local code. The two matrices are retained in
physical815/816 while the same lower workspace is reused. -/
def searches : Cmd 40 896 := .seq graphStage localStage

def savedAndCleared (source target : Fin 896) (a : Data) : Data :=
  clearedLower (routed (source, target) a)

def saveAndClearSteps (source target : Fin 896) (a : Data) : ℕ :=
  routeCost (source, target) a + clearLowerSteps (routed (source, target) a)

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeCode
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_NativeCodeAssembly
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeCodeAssembly

open BitProgram StructuredCalls SqrtLog SqrtLog.LeafOuterProgram SubexpSetupStorage

def serialize : Cmd 40 896 :=
  stage rowInputs CodeRowsProgram.program regs16 stacks64 rowOutputs


def afterMetadata : Cmd 40 896 := .seq NativeCode.searches serialize

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeCodeAssembly
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_NativeLeafPreparation
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! Actual physical preparation of the streamed greedy selector. The final
suffix clears the argmin bank, preserves the serialized code history, and
constructs the single retained zero candidate using the runtime depth word. -/
namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeLeafPreparation

open BitProgram StructuredCalls SqrtLog SqrtLog.LeafOuterProgram
open HashGreedyProgram

/-- Complete physical store after the final preparation suffix. -/
def finishedWords (a : Data) : Fin 896 → List Bool :=
  Function.update (Function.update (Initialize.finishedStacks a) 778 (Initialize.zeroWord a)) 779 []

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeLeafPreparation
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_NativeLeafRun
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! Concrete leaf control: prepared code history, all physically staged greedy
rounds, and a separate history-only exact count. The query execution proofs
remain explicit development seams until the native query bodies instantiate them. -/
namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeLeafRun

open BitProgram StructuredCalls RecordPrograms SqrtLog LeafProgram
open HashGreedyProgram HashGreedyProgram.NativeRound HashGreedyRound
open HashMassAdapter HashGreedyExecution

/-- The same fixed marked query runs for every visited greedy candidate. -/
def roundsCommand (markedQuery : Cmd 40 896) : Cmd 40 896 :=
  NativeRound.rounds (HashMassStaged.command markedQuery)

def afterPreparation (markedQuery acceptedQuery : Cmd 40 896) : Cmd 40 896 :=
  .seq (roundsCommand markedQuery) (AcceptedQueryStage.command acceptedQuery)

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeLeafRun
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_NativeOuter
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! The fixed outer instruction sequence composes actual parameter setup,
disjoint counting DFS, and full-word positivity. The existing concrete-leaf
contract remains an explicit development obligation, not a final endpoint. -/

namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.Native

open BitProgram StructuredCalls DisjointReuse

def outerCommand (k : ℕ) (leaf : Cmd 80 1220) : Cmd 80 1220 :=
  .seq (.seq (setupAfterFrontend k) (DFSCountProgram.command k leaf)) answerCommand

noncomputable def countingProgram (cutoff k : ℕ) (leaf : Cmd 80 1220) :=
  entryProgram cutoff (outerCommand k leaf)

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.Native
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_PairNativeSetup
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! Physical pair traversal initialization and ambient-mask expansion. The
five low scratch ports325..329 are reclaimed before the caller returns; the
pair controller and persistent node/layout words are not scratch. -/
namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.PairNativeSetup
open OAI BitProgram StructuredCalls


open SubexpSetupStorage

def fillCommand (isE : Bool) : Command :=
  isolated OAI.Algorithms.SubexponentialSAT.SqrtLog.HighIncidenceProgram.Restriction.program fillRegister fillStack 329 scratch
    [(338,325),(fillInput isE,327)] [(328,fillOutput isE)]

noncomputable def fillMiddle (isE : Bool) (a : Data) (rf : Fin 4 → Bool) (word : List Bool) : Data :=
  embedState fillRegister fillStack (fillPrepared isE a)
    (OAI.Algorithms.SubexponentialSAT.SqrtLog.HighIncidenceProgram.Restriction.state rf [] [] [] word)

noncomputable def fillResult (isE : Bool) (a : Data) (rf : Fin 4 → Bool) (word : List Bool) : Data :=
  finishState scratch [(328,fillOutput isE)] (fillMiddle isE a rf word)



def expandCommand : Command := .seq (fillCommand true) (fillCommand false)

noncomputable def expandResult (a : Data) (rfE rfU : Fin 4 → Bool)
    (Eword Uword : List Bool) : Data :=
  fillResult false (fillResult true a rfE Eword) rfU Uword

def expandCaller : Cmd 40 896 := liftCommand expandCommand 338 857 callerRegister id

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.PairNativeSetup
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_SignatureTupleProgram
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-!
# Fixed-control interpreter for streaming signature tuples

The input-dependent depth is represented by an encoded stack of suspended
frames. `probe` tests one candidate against earlier assignments. A rejected
candidate advances at its current depth; only a fresh signature descends.
Thus this control table never traverses raw assignment tuples.

The subroutines are concrete finite commands, and all execution theorems use
their actual measured evaluations. Instantiating their frame, signature, and
counter invariants remains a separate native-program obligation.
-/

namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SignatureTupleProgram

open BitProgram StructuredCalls

noncomputable def advanceState (a : State 40 896) : State 40 896 :=
  (StructuredProgram.Atom.copy controllerPorts.available (remainingPorts.register 2)).eval
    (CounterForPrograms.nextState remainingPorts (Counters.incrementResult candidatePorts a))

def advanceTime (a : State 40 896) : ℕ :=
  (CounterPrograms.rippleCost true (a.stacks candidatePorts.counter) + 1) +
    (CounterForPrograms.advanceCost remainingPorts a + 1)

noncomputable def initialFuelState (a : State 40 896) : State 40 896 :=
  CounterForPrograms.install initialFuelPorts a false false (a.regs 2) []
    (List.replicate (a.stacks initialFuelPorts.counter).length false ++ [true])

noncomputable def resetState (a : State 40 896) : State 40 896 :=
  (StructuredProgram.Atom.set controllerPorts.fresh false).eval
    ((StructuredProgram.Atom.set controllerPorts.available true).eval
      (initialFuelState (copyState 651 (tupleStacks 4)
        (copyState 651 (tupleStacks 2) a))))

noncomputable def testAvailableState (a : State 40 896) : State 40 896 :=
  (StructuredProgram.Atom.copy controllerPorts.available (remainingPorts.register 2)).eval
    (CounterForPrograms.testResult remainingPorts a)

noncomputable def resetGeneratorState (a : State 40 896) : State 40 896 :=
  copyState 651 (tupleStacks 8) (resetState a)

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SignatureTupleProgram
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_QueryAssembler
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! Physical assembly of the streamed query. Arithmetic caches are installed
from retained produced words by paid finite commands. These local theorems do
not assert completion of the node, pair, or tuple evaluator. -/
namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryAssembler

open OAI BitProgram StructuredCalls
open OAI.Algorithms.SubexponentialSAT.SqrtLog
open OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryProgram
open OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryTupleVisitor

attribute [local simp] Fin.coe_ofNat_eq_mod

def clearPair : Code := liftCommand (SubexpSetupStorage.clearMany pairScratch) 0 0
  FactorEnvironment.registerMap id

def preparePair : Code := .seq clearPair
  (.seq FactorEnvironment.bootstrap (overwrite 211 34))

/-- The node accumulator consumes each completed pair dictionary immediately.
The finishing clear restores the same arithmetic workspace for the next pair. -/
def commitPair : Code := .seq preparePair (.seq pairUpdate clearPair)

def commitPairProgram := compiled commitPair 851 850

open SubexpLiftRing SubexpQuarticRing
open OAI.Algorithms.SubexponentialSAT.SqrtLog.MomentsProgram
open TruncatedRingProgram


/-! The interpolation-node cursor is the actual framed table emitted by the
ring producer. Its low-bank loader is embedded into the common leaf bank;
all high pair/tuple state is preserved by the injective port map. -/
namespace Nodes

def call (c : Cmd 40 768) : Code := liftCommand c 301 78 id lowPort

def initializeNodes : Code := .seq (call RingNodeSetup.initNodes)
  (NodeReadoutSpace.clearMany [850,851,863])

def beginNode : Code := .seq (NodeReadoutSpace.clearMany nodeResetPorts)
  (call RingNodeSetup.readNode)


end Nodes


/-! Native multiplication of one completed head sum into the tuple product.
The original accumulator is relocated only at its two persistent operands. -/
namespace TupleMultiply

open OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgram

def prepare : Code := .seq (NodeReadoutSpace.clearMany [61,70])
  (.seq clearPair FactorEnvironment.bootstrap)

def multiply : Code := liftCommand Factor.accumulate 67 151 id ports

/-- Consume the current head sum into the tuple product and reclaim the
arithmetic workspace. The input/retained dictionaries have empty formal support. -/
def command : Code := .seq prepare (.seq multiply clearPair)

def program := compiled command 853 852

end TupleMultiply

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryAssembler
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_QueryExecution
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! Composition of the concrete streamed query. The traversal resource lemma
keeps the per-head execution time separate from its prefix storage bound;
neither the number of assignments nor their running time is used as space. -/
namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryExecution

open OAI BitProgram StructuredCalls
open QueryTupleVisitor SignatureTupleProgram

namespace PairStart

/-- A new finite-difference pair begins with the actual zero dictionary and
the current reversed free-coordinate masks are expanded to ambient masks.
Neither a support family nor a tuple family is stored by this command. -/
def command : Code := .seq (clearWord 851) PairNativeSetup.expandCaller

end PairStart

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryExecution
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_SignatureHeadPrepare
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! Paid setup for one visited signature head. The physical key workspace,
old master words and selector outputs are cleared by the command itself. -/

namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SignatureHeadPrepare

open BitProgram StructuredCalls StackRoutines
open HighQueryAdapter QueryTupleVisitor
open OAI.Algorithms.SubexponentialSAT.SqrtLog.BucketProgram OAI.Algorithms.SubexponentialSAT.Subexp.MatrixProgramSupport

def command : Cmd 40 896 := .seq reset (.seq SignatureKeyNative.command
  (.seq masters (.call NativeHeadSelect.prepareProgram)))

def program := compiled command 838 866

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SignatureHeadPrepare
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_SignatureKeyPackingTransport
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! Exact incidence-index transport for the canonical native source factory.
The ordinary full-label equality bridge is independent of this transport. -/
namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SignatureKeySource
open OAI.Algorithms.SubexponentialSAT.SqrtLog
open OAI.Algorithms.SubexponentialSAT.MulticolorTypes OAI.Algorithms.SubexponentialSAT.Subexp.ConstructivePacking
variable {r Q n : ℕ}

/-- Changing the displayed incidence-list length preserves each natural
matrix address and transports only its typed owner index. -/
theorem literalNat_reindex {D E : ℕ} (h : D = E)
    (P : PackingData (Fin D) (UniversalType r Q 1)) (owner : Fin D → Fin n)
    (A R : ℕ) (t : Fin Q) (j v : ℕ) :
    LayoutProducedMatrix.literalNat (PackingIncidenceInput.reindexPacking h P)
        (owner ∘ Fin.cast h.symm) A R t j v =
      LayoutProducedMatrix.literalNat P owner A R t j v := by
  cases h
  rfl

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SignatureKeySource
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_SignatureTupleNative
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-!
# Concrete adapters for the attained-signature tuple controller

The cursor primitives are fixed in `SignatureTupleProgram`. This module
installs the actual head loader and predecessor predicate on the shared leaf
ABI, and relates their physical state to the attained-prefix traversal.
-/

namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SignatureTupleNative

open BitProgram StructuredCalls SignatureTupleProgram

noncomputable def probePreState (a : State 40 896) : State 40 896 :=
  initializeFreshState (testAvailableState a)

noncomputable def probePostState (a : State 40 896) (out : Fin 16 → Bool)
    (W : List Bool) (rows : List (List (List Bool))) (h : ℕ)
    (candidate : Fin (2 ^ h)) : State 40 896 :=
  (StructuredProgram.Atom.peek (rescanStacks 22) controllerPorts.fresh 0).eval
    (candidateOutput (probePreState a) out W rows h candidate)


noncomputable def advanceCandidateState (a : State 40 896) : State 40 896 :=
  clearState (tupleStacks 3) (advanceState a)

/-- The numeric candidate may reach2^h only at exhaustion. Its retained word
has at mosth+1 bits, and every candidate sent to the scanner has exactlyh. -/
structure CursorWords (a : State 40 896) (h candidate : ℕ) : Prop where
  range : candidate ≤ 2 ^ h
  value : CounterPrograms.value (a.stacks candidatePorts.counter) = candidate
  width : (a.stacks candidatePorts.counter).length ≤ h + 1
  exact : candidate < 2 ^ h →
    a.stacks candidatePorts.counter = ExecCNFTupleEnumeration.fixedBits h candidate
  remaining : a.stacks remainingPorts.counter =
    ExecCNFTupleEnumeration.fixedBits (h + 1) (2 ^ h - candidate)
  incrementScratch : a.stacks candidatePorts.scratch = []
  decrementScratch : a.stacks remainingPorts.scratch = []


section CursorStorage

open SignatureTupleDFS SignatureTupleTraversal

variable (h : ℕ → ℕ) {κ : ℕ → Type*}
  (key : (d : ℕ) → Fin (2 ^ h d) → κ d)

structure ScanStorage (levels base : ℕ) (depth : Fin levels)
    (ancestors : Prefix (Representatives key) depth.val) (candidate : ℕ)
    (a : State 40 896) : Prop extends
      AncestorStorage h key levels base depth.val ancestors a,
      CursorWords a (h depth.val) candidate where
  leaf : a.regs controllerPorts.leaf = false
  saved : a.stacks (tupleStacks 3) = []
  payload : a.stacks (tupleStacks 4) = []
  predecessor : a.stacks (tupleStacks 8) = List.replicate (h depth.val) false

/-- The same fixed controller state is related to scan, leaf, and halted
semantic cursors. Matrix/cache and accumulator facts are supplied separately
by their concrete program invariants. -/
inductive CursorStorage (levels base : ℕ) : Cursor key levels → State 40 896 → Prop
  | scan {depth ancestors candidate a} :
      ScanStorage h key levels base depth ancestors candidate a →
      CursorStorage levels base (.scan depth ancestors candidate) a
  | leaf {ancestors a} : LeafStorage h key levels base ancestors a →
      CursorStorage levels base (.leaf ancestors) a
  | halt {a} : a.regs controllerPorts.active = false → CursorStorage levels base .halt a


end CursorStorage

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SignatureTupleNative
end


