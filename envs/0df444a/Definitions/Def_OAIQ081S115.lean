-- Prove2me | Definitions.Def_OAIQ081S115
-- name    : OAIQ081S115
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-29T22:34:56.628455+00:00
-- url     : https://prove2.me/theorems/b55788dc-2610-41e8-9152-83b1d014b3aa
-- title:
--   Definitions bundle OAIQ081S115 of the split of OpenAI, The Exponential Time Hypothesis is False
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.exact_count_and_sat`, carved from OpenAI's openai/math development (OpenAI, *The Exponential Time Hypothesis is False*, OpenAI Math Release, October 25, 2026, result family 378, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 233 declarations of OpenAI's Lean: 196 definitions, 5 inductive types or structures, 6 instances and 26 theorems. The definitions and types are `OAI.Algorithms.SubexponentialSAT.SqrtLog.IdempotentApplyProgram.Multiplier.keyState`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafOuterProgram.inputWords`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.CodeChecks.rejectedRank`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.Dense`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.Dense.ofPolynomial`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.Dense.readout`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.BinaryClogProgram.Setup.io`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.BinaryClogProgram.Setup.logSucc`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.BinaryClogProgram.command`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.BinaryClogProgram.io`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.BinaryClogProgram.program`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.DisjointBranchProgram.command`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.DisjointBranchProgram.commandB`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.DisjointBranchProgram.program`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.DisjointBranchProgram.programB`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.ParametersProgram.clogCmd`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.SparseBudgetProgram.budgetTest`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.SparseBudgetProgram.command`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.SparseBudgetProgram.program`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.SparseBudgetProgram.search`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.SparseBudgetProgram.test`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.SparseDFSProgram.branch`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.SparseDFSProgram.splitCurrent`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.SparsePriorityProgram.Selector.Boundary`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.SparsePriorityProgram.Selector.ScanEffect`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.SparsePriorityProgram.Selector.ScanReady`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.SparsePriorityProgram.Selector.SearchHit`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.SparsePriorityProgram.Selector.parameterInit`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.SparsePriorityProgram.Selector.powerCall`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.SparsePriorityProgram.ThresholdPower.command`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FactorAssignmentBranches.identified`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FactorAssignmentProgram.Data`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FactorAssignmentProgram.cacheStart`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FactorAssignmentProgram.callbackInitial`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FactorAssignmentProgram.clearCallbackCost`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FactorAssignmentProgram.initializeCost`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FactorAssignmentProgram.initialized`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FactorAssignmentProgram.setup`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FactorAssignmentProgram.setupLocal`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FactorEnvironment.Data` and 161 more.
--
--   **Sources.** They come from these modules of lean/OAI/Algorithms, in whole or in part: `SubexponentialSAT_SqrtLogSpace_CommandStackTransport`, `SubexponentialSAT_SqrtLogSpace_DisjointReuse_BinaryClogProgram`, `SubexponentialSAT_SqrtLogSpace_DisjointReuse_ParameterBank`, `SubexponentialSAT_SqrtLogSpace_DisjointReuse_SparseBudgetProgram`, `SubexponentialSAT_SqrtLogSpace_DisjointReuse_SparseDFSProgram`, `SubexponentialSAT_SqrtLogSpace_DisjointReuse_SparsePriorityProgram`, `SubexponentialSAT_SqrtLogSpace_DisjointSparsifyProgram`, `SubexponentialSAT_SqrtLogSpace_FactorAssignmentBranches`, `SubexponentialSAT_SqrtLogSpace_FactorAssignmentProgram`, `SubexponentialSAT_SqrtLogSpace_FactorCacheProgram`, `SubexponentialSAT_SqrtLogSpace_FactorEnvironment`, `SubexponentialSAT_SqrtLogSpace_FactorTableDenotation`, `SubexponentialSAT_SqrtLogSpace_HashCandidateProgram`, `SubexponentialSAT_SqrtLogSpace_HashCandidateRank`, `SubexponentialSAT_SqrtLogSpace_HashCandidates`, `SubexponentialSAT_SqrtLogSpace_HashGreedyCNF`, `SubexponentialSAT_SqrtLogSpace_HashGreedyCandidate`, `SubexponentialSAT_SqrtLogSpace_HashGreedyProgram`, `SubexponentialSAT_SqrtLogSpace_HashMarkedQueryAdapter`, `SubexponentialSAT_SqrtLogSpace_HashMarkedReturn`, `SubexponentialSAT_SqrtLogSpace_HashMassAdapter`, `SubexponentialSAT_SqrtLogSpace_HashQueryEntry`, `SubexponentialSAT_SqrtLogSpace_HashQueryInputBounds`, `SubexponentialSAT_SqrtLogSpace_HashQueryResources`, `SubexponentialSAT_SqrtLogSpace_HashTrialStage`, `SubexponentialSAT_SqrtLogSpace_HeadEvaluationProgram`, `SubexponentialSAT_SqrtLogSpace_HeadSumProgram`, `SubexponentialSAT_SqrtLogSpace_HighFrontendSources`, `SubexponentialSAT_SqrtLogSpace_NativeCode`, `SubexponentialSAT_SqrtLogSpace_NativeEntry`, `SubexponentialSAT_SqrtLogSpace_NativeFrontend`, `SubexponentialSAT_SqrtLogSpace_NativeLeaf`, `SubexponentialSAT_SqrtLogSpace_NativeLeafDispatch`, `SubexponentialSAT_SqrtLogSpace_NativeLeafSemantics`, `SubexponentialSAT_SqrtLogSpace_NativeSetupSpace`, `SubexponentialSAT_SqrtLogSpace_NativeTerminal`, `SubexponentialSAT_SqrtLogSpace_NodeAppendSpace`, `SubexponentialSAT_SqrtLogSpace_NodeReadoutSpace`, `SubexponentialSAT_SqrtLogSpace_QueryEvaluation`, `SubexponentialSAT_SqrtLogSpace_QueryIncidenceCommand`, `SubexponentialSAT_SqrtLogSpace_QueryJetCanonical`, `SubexponentialSAT_SqrtLogSpace_QueryNodeFinish`, `SubexponentialSAT_SqrtLogSpace_QueryReconstruction`, `SubexponentialSAT_SqrtLogSpace_QueryTupleSum`, `SubexponentialSAT_SqrtLogSpace_QueryVisitorHead`, `SubexponentialSAT_SqrtLogSpace_ScheduleProgram`, `SubexponentialSAT_SqrtLogSpace_SignatureHeadLoader`, `SubexponentialSAT_SqrtLogSpace_SignatureTupleLoader`, `SubexponentialSAT_SqrtLogSpace_SignatureTupleNative`, `SubexponentialSAT_SqrtLogSpace_SignatureTupleProgram`, `SubexponentialSAT_SqrtLogSpace_SignatureTupleTraversal`, `SubexponentialSAT_SqrtLogSpace_SparseCodeProgram`, `SubexponentialSAT_SqrtLogSpace_SparseCodeSearch`, `SubexponentialSAT_SqrtLogSpace_TruncatedRing`, `SubexponentialSAT_SqrtLogSpace_TruncatedRingProgram`, `SubexponentialSAT_SqrtLog_IdempotentApplyProgramMultiplierKeyCore`, `SubexponentialSAT_SqrtLog_LeafOuterProgramParameters`, `SubexponentialSAT_SubexpCRTOuterControl`, `SubexponentialSAT_SubexpCRTOuterSetup`, `SubexponentialSAT_SubexpIntervalCoreProgram`, `SubexponentialSAT_SubexpIntervalFinishProgram`, `SubexponentialSAT_SubexpIntervalStartProgram`, `SubexponentialSAT_SubexpKernelControl`, `SubexponentialSAT_SubexpNormalizationProgram`.
--
--   **Imports.** It imports the published bundle `Def_SubexponentialSAT`; the bundles `OAIQ081S082`, `OAIQ081S083`, `OAIQ081S084`, `OAIQ081S085`, `OAIQ081S088`, `OAIQ081S091`, `OAIQ081S092`, `OAIQ081S095`, `OAIQ081S096`, `OAIQ081S098` and `OAIQ081S099` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ081S136`, `OAIQ081S137` and `OAIQ081S161`; the statements `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.DisjointBranchProgram.programB_runsIn`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.DisjointBranchProgram.program_runsIn`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.SparseDFSProgram.branch_execution_from_state`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.SparseDFSResource.branch_execution_space`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HashCandidateProgram.Leaf.prepare_eval`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HashGreedyCNF.history_mass_zero`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HashGreedyCNF.reference_covered`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HashGreedyCandidate.attempt_entry_of_query`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HashGreedyCode.candidate_raw_payload`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HashGreedyCode.history_raw_rows`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HashGreedyCode.history_raw_slots`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HashGreedyCode.supplied_history_raw_encoding`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HashGreedyCode.supplied_history_raw_resources`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HashGreedyCode.supplied_trial_raw_resources`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HashGreedyCode.supplied_trial_word_raw_encoding`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HashGreedyProgram.PadScore.leaf_eval`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeLeafDispatch.command_execution`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeLeafRun.common_bounds`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeLeafSemantics.history_count`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeTerminal.readyCommand_bounded`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.Native.budgetCall_eval`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.Native.entry_large_bounded_eval`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.Native.frontend_eval`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.Native.setupAfterFrontend_eval`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.Native.setupAfterFrontend_prepared_execution`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryTupleReadoutSemantics.grouped_dense_query_emitted`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.ReconstructionProgram.controller_run_framed` and `OAI.Algorithms.SubexponentialSAT.SubexpNormalizationProgram.program_runsIn`; the proofs of `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.CodeChecks.graph_stream_runs`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.CodeChecks.local_checker_runs`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.DisjointBranchProgram.programB_runsIn`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.DisjointBranchProgram.program_runsIn`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.SparseDFSProgram.branch_execution_from_state`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.SparseDFSResource.branch_execution_space`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HashCandidateProgram.Leaf.prepare_eval`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HashGreedyCNF.history_mass_zero`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HashGreedyCNF.reference_covered`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HashGreedyCandidate.attempt_entry_of_query`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HashGreedyCode.candidate_raw_payload`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HashGreedyCode.history_raw_rows`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HashGreedyCode.history_raw_slots`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HashGreedyCode.supplied_history_raw_encoding`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HashGreedyCode.supplied_history_raw_resources`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HashGreedyCode.supplied_trial_raw_resources`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HashGreedyCode.supplied_trial_word_raw_encoding`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeLeafDispatch.command_execution`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeLeafRun.common_bounds`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeLeafSemantics.history_count`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeTerminal.readyCommand_bounded`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.Native.budgetCall_eval`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.Native.entry_large_bounded_eval`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.Native.frontend_eval`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.Native.setupAfterFrontend_eval`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.Native.setupAfterFrontend_prepared_execution`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafParametersProgram.Interval.at_eval`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgram.Indicator.command_eval`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.ReconstructionProgram.CofactorOuter.command_run`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.ReconstructionProgram.Horner.command_run`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.ReconstructionProgram.Scalar.accumulate_run`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.ReconstructionProgram.Scalar.negative_run`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.ReconstructionProgram.controller_run_framed`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.ReconstructionProgram.initialize_run` and `OAI.Algorithms.SubexponentialSAT.SubexpNormalizationProgram.program_runsIn`.
-- source:
--   OpenAI, The Exponential Time Hypothesis is False, OpenAI Math Release, October 25, 2026, https://github.com/openai/math (result family 378; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/The-Exponential-Time-Hypothesis-is-False-October-25-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Algorithms at commit 7ef5c0c

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_SubexponentialSAT
import Definitions.Def_OAIQ081S082
import Definitions.Def_OAIQ081S083
import Definitions.Def_OAIQ081S084
import Definitions.Def_OAIQ081S085
import Definitions.Def_OAIQ081S088
import Definitions.Def_OAIQ081S091
import Definitions.Def_OAIQ081S092
import Definitions.Def_OAIQ081S095
import Definitions.Def_OAIQ081S096
import Definitions.Def_OAIQ081S098
import Definitions.Def_OAIQ081S099

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_CommandStackTransport
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! All-prefix resource transport for the existing exact-time tape replay.
The imported avoidance certificate excludes reads as well as writes, including
`peek`. Erasing hidden caller data is a proof construction only: the actual
instruction table and its measured number of steps remain unchanged. -/

namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.CommandStackTransport

open BitProgram StructuredCalls SqrtLog.ProgramTapeReplay

variable {r s l : ℕ}

/-- The local all-prefix bound is transported through the compiled command,
including its final halt. Hidden external words are restored unchanged. -/
theorem eval_shadow_prefix_bound (H : Fin s → Prop) [DecidablePred H]
    {command : Cmd r s} (hc : AvoidsCmd H command) (input output : Fin s)
    {steps bound frameBound : ℕ} {a b : State r s}
    (he : Eval command steps (rebaseState H (fun _ => []) a) b)
    (hsource : ∀ prefixSteps source, prefixSteps ≤ steps + 1 →
      Trace (compiled command input output) prefixSteps
        ((rebaseState H (fun _ => []) a).withPC
          (some (compiled command input output).entry)) source →
      ∀ i, ¬ H i → (source.stacks i).length ≤ bound)
    (hframe : ∀ i, H i → (a.stacks i).length ≤ frameBound) :
    ∀ prefixSteps intermediate, prefixSteps ≤ steps + 1 →
      Trace (compiled command input output) prefixSteps
        (a.withPC (some (compiled command input output).entry)) intermediate →
      ∀ i, (intermediate.stacks i).length ≤ max bound frameBound := by
  have h := trace_stack_bound H (avoids_compiled H command hc input output)
    a.stacks (compiled_halt_trace he input output) hsource hframe
  rw [rebaseCfg_withPC, rebaseState_restore] at h
  exact h

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.CommandStackTransport
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_DisjointReuse_BinaryClogProgram
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! Actual floor and ceiling logarithm bit programs, without packing or schedule imports. -/

namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.BinaryClogProgram.Setup

open BitProgram StructuredCalls
open CounterPrograms (value ripple)

abbrev io (xs : List Bool) : Data := StructuredProgram.ioState 0 xs

/-- The floor binary logarithm plus one, with zero mapped to one. -/
def logSucc : Cmd 3 3 := .seq logarithm increment


end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.BinaryClogProgram.Setup

namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.BinaryClogProgram

open BitProgram StructuredCalls
open CounterPrograms (value ripple)

abbrev io := Setup.io

def command : Cmd 3 3 := .seq decrement
  (.seq (CounterForPrograms.zeroCmd zeroPorts)
    (.ite 2 reset (.seq reset Setup.logSucc)))

def program := compiled command 0 0


end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.BinaryClogProgram
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_DisjointReuse_ParameterBank
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! Fixed Boolean-stack arithmetic in a 19-word data bank and 13 scratch stacks. -/

namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.ParametersProgram

open BitProgram StructuredCalls BinaryArithmetic

/-- The input word is preserved and the logarithm overwrites its fresh copy. -/
def clogCmd (a o : Fin 19) : Cmd 8 32 :=
  .seq (copyCmd a o) (.seq resetLogRegisters
    (.call (ProgramLinking.liftProgram
      OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.BinaryClogProgram.program logRegisters (logStacks o))))


end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.ParametersProgram
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_DisjointReuse_SparseBudgetProgram
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-!
Concrete finite-control construction of the Appendix A dyadic search.
The input budget is `1 / s`; the search uses only exact binary arithmetic.
This file separates command construction from theorems about its execution.
-/

namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.SparseBudgetProgram

open BitProgram StructuredCalls BinaryArithmetic
open ParametersProgram
open scoped BigOperators

/-- Computes `clog 2 (4*C*M)`, multiplies by Gamma and s, and tests `M < Gamma*h*s`.
Horner evaluation and all arithmetic are finite binary programs. -/
def budgetTest (k : ℕ) : Cmd 8 32 :=
  .seq (multiplyCmd 1 4 12 (by decide) (by decide))
    (.seq (horner (k - 1))
    (.seq (replaceCmd .multiply 2 6 2 3 (by decide) (by decide))
    (.seq (replaceCmd .multiply 2 1 2 3 (by decide) (by decide))
    (.seq (clogCmd 2 10)
    (.seq (multiplyCmd 10 7 11 (by decide) (by decide))
    (.seq (multiplyCmd 11 0 9 (by decide) (by decide))
    (.seq (copyCmd 1 8)
    (.seq (clearCmd 2)
    (.seq (clearCmd 10)
    (.seq (clearCmd 11)
    (.seq (clearCmd 12) (compareCmd 8 9))))))))))))

/-- First test the constant lower bound; the expensive logarithm is evaluated only
when `M >= Gamma`. Both branches return with every temporary word empty. -/
def test (k : ℕ) : Cmd 8 32 :=
  .seq (copyCmd 1 8) (.seq (copyCmd 7 9)
    (.seq (compareCmd 8 9) (.ite 0 (.base .skip) (budgetTest k))))

/-- The actual dyadic search. The natural-number minimizer appears only in its
specification, never as a machine instruction or a supplied runtime service. -/
def search (k : ℕ) : Cmd 8 32 :=
  .seq (initCmd k) (.seq (test k) (.while 0 (.seq double (test k))))

def command (k : ℕ) : Cmd 8 32 :=
  .seq (search k) (.seq (loadCmd 2 (4 : ℕ).bits) (.seq (boundPowers (k - 1))
    (.seq (clearCmd 4) (.seq (clearCmd 5) (.seq (clearCmd 6) (clearCmd 7))))))

def program (k : ℕ) : Program 8 32 (size (command k) + 1) :=
  compiled (command k) (port 0) (port 1)

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.SparseBudgetProgram
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_DisjointReuse_SparsePriorityProgram
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! Concrete components of the sharp clause/core search from Appendix A.
The guard counts actual framed literals and executes the preserving subset tester.
The complete search and its polynomial resource bound are developed separately below. -/


namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.SparsePriorityProgram

open OAI.Algorithms.SubexponentialSAT.BitProgram OAI.Algorithms.SubexponentialSAT.StructuredCalls

namespace ThresholdPower

/-- The exponent depends only on the fixed width/core-size pass, before input quantification. -/
def command (exponent : ℕ) : Cmd 8 9 :=
  .seq (ArithmeticExpressionSupport.pushWord 1 exponent.bits)
    (.seq (.call PowerPrograms.program) (ArithmeticExpressionSupport.clearCmd 1))

end ThresholdPower

namespace Selector

def powerCall (exponent : ℕ) : Code :=
  liftCommand (ThresholdPower.command exponent) 0 2 (Fin.castAdd 16) powerStack

def parameterInit (exponent : ℕ) (size : List Bool) : Code :=
  .seq (load 20 size) (.seq (powerCall exponent) (copy 18 14))

structure ScanReady (F : Formula) (width size threshold : List Bool) (d : Data) : Prop where
  width_word : d.stacks 16 = width
  size_word : d.stacks 20 = size
  threshold_word : d.stacks 17 = threshold
  family_word : d.stacks 18 = Filter.formulaCode F
  scratch : ∀ i : Fin 13, d.stacks (Fin.castAdd 11 i) = []

structure ScanEffect (F : Formula) (mask width size threshold bits : List Bool)
    (before after : Data) : Prop where
  shape : ∃ C ∈ F, bits = Filter.clauseCode C ∧
    after.stacks = Function.update (Function.update before.stacks 9
      (if accepted F C mask width size threshold then Filter.clauseCode (masked mask C) else [])) 12
      (if accepted F C mask width size threshold then
        Filter.formulaCode (selectedFamily F (masked mask C) width) else [])

structure Boundary (F : Formula) (base : List Bool) (d : Data) : Prop where
  formula_word : d.stacks 13 = Filter.formulaCode F
  parameter_word : d.stacks 19 = base
  scratch : ∀ i : Fin 24, i ≠ 13 → i ≠ 19 → d.stacks i = []

inductive SearchHit (F : Formula) (M : ℕ) (ps : List (ℕ × ℕ × List Bool)) (e : Data) : Prop
  | intro (before : List (ℕ × ℕ × List Bool)) (chosen : ℕ × ℕ × List Bool)
      (after : List (ℕ × ℕ × List Bool)) (clause : Clause)
      (split : ps = before ++ chosen :: after)
      (failed : ∀ p ∈ before, passFound F M p = false)
      (clause_mem : clause ∈ widthFamily F chosen.1.bits)
      (accepted : passCandidate F M chosen clause = true)
      (core_word : e.stacks 9 = Filter.clauseCode (masked chosen.2.2 clause))
      (family_word : e.stacks 12 = Filter.formulaCode (selectedRaw F chosen.1 (masked chosen.2.2 clause))) :
      SearchHit F M ps e

end Selector

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.SparsePriorityProgram
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SubexpNormalizationProgram
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!+# Fixed-control encoded CNF normalization

The common boundary uses stack 13 for the formula and empty work stacks.
Literal cleanup and tautology removal are lifted into that boundary here;
clause deduplication and strict-subset deletion use the same boundary.
-/

namespace SubexponentialSAT.SubexpNormalizationProgram

open BitProgram StructuredCalls

/-- The complete program contains only the three checked fixed-control stages. -/
abbrev command : Cmd 15 16 := .seq prefixCall absorbCommand

def program := compiled command 13 13

end SubexponentialSAT.SubexpNormalizationProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_DisjointSparsifyProgram
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! List-level outputs for the concrete disjoint splitter.
The declared variable universe is retained by the surrounding controller.
-/

namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.DisjointBranchProgram

open OAI.Algorithms.SubexponentialSAT.SAT

open BitProgram StructuredCalls

def commandB : Cmd 15 16 := .seq prepareB ExecPetalChildProgram.command

def programB := compiled commandB 13 13

open ExecBranchControllerSupport

def command : Cmd 15 23 :=
  .seq (buildChild ExecCoreChildProgram.program 0)
    (.seq (buildChild programB 1) (.seq cleanInputs RegisterResetProgram.all))

def program := compiled command 4 2

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.DisjointBranchProgram
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_DisjointReuse_SparseDFSProgram
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! Fixed finite control for the outer disjoint counting traversal.

The leaf command is an explicit piece of finite code chosen with `k`. Its
layout, reconstruction, input loading and output export are still
separate obligations until the concrete leaf implementation is substituted.
There is no oracle instruction or endpoint theorem in this module.
-/

namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.SparseDFSProgram

open BitProgram StructuredCalls SubexpPostfixControl

def splitCurrent : Code :=
  .call (ProgramLinking.liftProgram DisjointBranchProgram.program
    (registers 15 (by decide)) splitterStack)

def branch : Code := .seq splitCurrent pushChildren


end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.SparseDFSProgram
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

def state (v p : Bool) (source zero one : Word) (a : Accumulator) : State 3 8 :=
  ⟨SubexpHornerProgram.triple v p true,
    ![source, zero, one, a.output, [], a.outer, a.groups, a.terms]⟩

/-! The following induction rule accounts for actual executions of the fixed
payload body. Its premises will be proved for `termBody`, `groupBody`, and
`blockBody`; the exported whole-controller statement has no callback argument. -/

/-! ## Forward-output service boundary -/

end SubexponentialSAT.SubexpKernelControl

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_IdempotentApplyProgramMultiplierKeyCore
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Source component: IdempotentApplyProgramMultiplierKey. -/

/-! Construction and application of the U monomial by actual native instructions. -/
namespace SubexponentialSAT.SqrtLog.IdempotentApplyProgram.Multiplier
open BitProgram StructuredCalls
open HashCircuitProgram.Native


def keyState (regs : Fin 8 → Bool) (bank : Fin 96 → List Bool)
    (shape key output : List Bool) : State 8 96 :=
  ⟨regs,Function.update (Function.update (Function.update bank 89 shape) 91 key) 94 output⟩

end SubexponentialSAT.SqrtLog.IdempotentApplyProgram.Multiplier


end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_FactorCacheProgram
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! Physical reconstruction of the exact node caches, including the sparse
ring identity and ambient shape, before accepted assignment evaluation. -/
namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FactorAssignmentProgram

open OAI BitProgram StructuredCalls SubexpSetupStorage
open SqrtLog SqrtLog.LeafProgram

abbrev Data := State 40 896

/-- Clears stale copies, including ambient shape88, before reconstructing the
actual encoded ring identity69 and the idempotent coefficient tape143. -/
def setupLocal : Cmd 16 768 :=
  .seq (clearMany cachePorts) LeafNodeCacheProgram.localCommand

def setup : Code := liftCommand setupLocal 128 69 localRegister lowStack

def cacheStart (a : State 16 768) := clearManyState cachePorts a

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FactorAssignmentProgram
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_TruncatedRing
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.FiniteField.fieldFintype _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.labelFintype _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.variableFintype _root_.OAI.Algorithms.SubexponentialSAT.MulticolorTypes.instFintypeJoint _root_.OAI.Algorithms.SubexponentialSAT.MulticolorTypes.instFintypeSide _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingModel.Data.fieldFintype _root_.OAI.Algorithms.SubexponentialSAT.StackCompiler.stateFintype _root_.OAI.Algorithms.SubexponentialSAT.StructuredProgram.siteFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-!
# Dense lifting and Taylor coefficients

`Truncated R n` stores exactly `n` coefficients. Its multiplication is the
existing total-order convolution, and its ring laws follow from the surjective
coefficient projection from `R[X]`. Nesting the construction stores the shared
lifting marker outside the Taylor variable. The final marker readout is additive.
-/

namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace

open scoped BigOperators
open OAI.Algorithms.SubexponentialSAT.SqrtLog.TotalOrder

namespace Truncated

variable {R : Type*} {n : ℕ}

section Semiring

variable [CommSemiring R]

noncomputable section

@[simp] theorem ofPolynomial_pow (P : Polynomial R) (k : ℕ) :
    ofPolynomial n (P ^ k) = ofPolynomial n P ^ k := by
  induction k with
  | zero => exact ofPolynomial_one
  | succ k ih =>
      change ofPolynomial n (P ^ (k + 1)) = npowRec k (ofPolynomial n P) * ofPolynomial n P
      rw [pow_succ, ofPolynomial_mul, ih]
      rfl

@[simp] theorem ofPolynomial_natCast (k : ℕ) :
    ofPolynomial n (k : Polynomial R) = k := by
  ext j
  simp [Polynomial.coeff_natCast_ite]

instance instCommSemiring : CommSemiring (Truncated R n) :=
  ofPolynomial_surjective.commSemiring (ofPolynomial n)
    ofPolynomial_zero ofPolynomial_one ofPolynomial_add ofPolynomial_mul
    ofPolynomial_nsmul ofPolynomial_pow ofPolynomial_natCast

/-- Each stored coordinate is additive, but generally not multiplicative. -/
def coeffHom (j : Fin n) : Truncated R n →+ R where
  toFun a := a.coeff j
  map_zero' := rfl
  map_add' _ _ := rfl

@[simp] theorem coeff_sum {ι : Type*} (s : Finset ι) (a : ι → Truncated R n) (j : Fin n) :
    (∑ i ∈ s, a i).coeff j = ∑ i ∈ s, (a i).coeff j :=
  map_sum (coeffHom j) a s

/-- The quotient-ring projection is multiplicative; the marker readout is not. -/
def ofPolynomialHom (n : ℕ) : Polynomial R →+* Truncated R n where
  toFun := ofPolynomial n
  map_zero' := ofPolynomial_zero
  map_one' := ofPolynomial_one
  map_add' := ofPolynomial_add
  map_mul' := ofPolynomial_mul

/-- Add the coefficients of the chosen representative, after multiplication. -/
def readout : Truncated R n →+ R where
  toFun a := ∑ j : Fin n, a.coeff j
  map_zero' := by simp
  map_add' a b := by simp [Finset.sum_add_distrib]

end
end Semiring

section Ring

variable [CommRing R]

instance instNeg : Neg (Truncated R n) := ⟨fun a => ⟨fun j => -a.coeff j⟩⟩
instance instSub : Sub (Truncated R n) := ⟨fun a b => ⟨fun j => a.coeff j - b.coeff j⟩⟩
instance instSMulInt : SMul ℤ (Truncated R n) := ⟨fun k a => ⟨fun j => k • a.coeff j⟩⟩
instance instIntCast : IntCast (Truncated R n) := ⟨fun k => ⟨fun j => if j.val = 0 then k else 0⟩⟩

noncomputable section

@[simp] theorem ofPolynomial_neg (P : Polynomial R) :
    ofPolynomial n (-P) = -ofPolynomial n P := by
  ext j
  change (-P).coeff j.val = -P.coeff j.val
  simp

@[simp] theorem ofPolynomial_sub (P Q : Polynomial R) :
    ofPolynomial n (P - Q) = ofPolynomial n P - ofPolynomial n Q := by
  ext j
  change (P - Q).coeff j.val = P.coeff j.val - Q.coeff j.val
  simp

@[simp] theorem ofPolynomial_zsmul (k : ℤ) (P : Polynomial R) :
    ofPolynomial n (k • P) = k • ofPolynomial n P := by
  ext j
  change (k • P).coeff j.val = k • P.coeff j.val
  simp

@[simp] theorem ofPolynomial_intCast (k : ℤ) :
    ofPolynomial n (k : Polynomial R) = k := by
  ext j
  change (k : Polynomial R).coeff j.val = if j.val = 0 then (k : R) else 0
  rw [← Polynomial.C_eq_intCast, Polynomial.coeff_C]

instance instCommRing : CommRing (Truncated R n) :=
  ofPolynomial_surjective.commRing (ofPolynomial n)
    ofPolynomial_zero ofPolynomial_one ofPolynomial_add ofPolynomial_mul
    ofPolynomial_neg ofPolynomial_sub ofPolynomial_nsmul ofPolynomial_zsmul
    ofPolynomial_pow ofPolynomial_natCast ofPolynomial_intCast

@[simp] theorem coeff_neg (a : Truncated R n) (j : Fin n) :
    (-a).coeff j = -a.coeff j := rfl

@[simp] theorem coeff_sub (a b : Truncated R n) (j : Fin n) :
    (a - b).coeff j = a.coeff j - b.coeff j := rfl

@[simp] theorem coeff_zsmul (k : ℤ) (a : Truncated R n) (j : Fin n) :
    (k • a).coeff j = k • a.coeff j := rfl

end
end Ring
end Truncated

/-- `t * J` scalar slots: shared lifting marker outside, Taylor variable inside. -/
abbrev Dense (R : Type*) (t J : ℕ) := Truncated (Truncated R J) t

namespace Dense

variable {R : Type*} [CommSemiring R] {t J : ℕ}

noncomputable section

/-- First project Taylor coefficients, then truncate the shared marker. -/
def ofPolynomial (t J : ℕ) : Polynomial (Polynomial R) →+* Dense R t J :=
  (Truncated.ofPolynomialHom t).comp
    (Polynomial.mapRingHom (Truncated.ofPolynomialHom J))

@[simp] theorem coeff_ofPolynomial (P : Polynomial (Polynomial R)) (u : Fin t) (z : Fin J) :
    ((ofPolynomial t J P).coeff u).coeff z = (P.coeff u.val).coeff z.val := by
  simp [ofPolynomial, Truncated.ofPolynomialHom]

/-- Final additive shared-marker readout; a Taylor array remains. -/
def readout : Dense R t J →+ Truncated R J := Truncated.readout

@[simp] theorem coeff_readout (a : Dense R t J) (z : Fin J) :
    (readout a).coeff z = ∑ u : Fin t, (a.coeff u).coeff z := by
  exact Truncated.coeff_sum Finset.univ a.coeff z

end
end Dense
end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_TruncatedRingProgram
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-!
# Native arithmetic after immediate Boolean specialization

The existing finite sparse-product program is used with empty formal support.
Its keys still carry the ambient input coordinate type; this does not compress
the declared variables. There are at most `u * J` retained entries, including
zero cutoffs. Polynomial local time therefore bounds all its source prefixes,
including the table, inputs, output, normalization copies and arithmetic scratch.
-/

namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.TruncatedRingProgram

open scoped BigOperators
open OAI OAI.Algorithms.SubexponentialSAT.SqrtLog OAI.Algorithms.SubexponentialSAT.SubexpLiftRing OAI.Algorithms.SubexponentialSAT.SubexpQuarticRing
open MomentsProgram BitProgram

/- The two fields coincide with LeafProgram.NativeSemantics.Good. The
arithmetic layer states them transparently to avoid importing the factor
interpreter. Conversion in either direction supplies `valid` and `nodup`.
The proof bodies below are the original finite-program validity arguments. -/

variable {V R : Type*} [DecidableEq V] [CommRing R]

noncomputable section

/-- The semantic projection for already-specialized correction variables. -/
def jetProjection (u J : ℕ) : Squarefree.Jet V R →+* Dense R u J :=
  (Dense.ofPolynomial u J).comp (Squarefree.evalJet (fun _ => 0) (by simp))

@[simp] theorem jetProjection_canonical (u J : ℕ) (P : Squarefree.Jet V R) :
    jetProjection u J (Squarefree.canonical u J P) = jetProjection u J P := by
  ext i j
  simp [jetProjection, Squarefree.coeff_evalJet, Squarefree.coeff_canonical, i.isLt, j.isLt]

@[simp] theorem jetProjection_jetScalar (u J : ℕ) (P : Moments.ScalarJet R) :
    jetProjection (V := V) u J (Moments.jetScalar P) = Dense.ofPolynomial u J P := by
  ext i j
  simp only [jetProjection, RingHom.comp_apply, Dense.coeff_ofPolynomial,
    Squarefree.coeff_evalJet, Moments.jetScalar, Polynomial.coe_mapRingHom,
    Polynomial.coeff_map]
  change Squarefree.evalHom (fun _ : V => 0) (by simp)
    (Squarefree.monomial ∅ ((P.coeff i.val).coeff j.val)) = (P.coeff i.val).coeff j.val
  simp [Squarefree.weight]

end

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.TruncatedRingProgram
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_QueryIncidenceCommand
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! Fixed native incidence command and its physical port ABI. The definitions
are extracted unchanged from the same emitter-specializer composition. -/
namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryProducerSpace
open OAI BitProgram StructuredCalls
open OAI.Algorithms.SubexponentialSAT.SqrtLog MomentsProgram
open SubexpScanPrimitives SubexpSetupStorage

namespace Native

def loaded (a : State 16 294) : State 16 294 :=
  afterTransfer (afterTransfer (copyManyState loadPairs a) 217 292 0 1) 292 284 0 1

def movedOutput (a : State 16 294) : State 16 294 :=
  afterTransfer (afterTransfer a 271 292 0 1) 292 217 0 1

end Native
end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryProducerSpace
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_FactorAssignmentProgram
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! The accepted-assignment factor product uses the original finite-ring
indicator and clause programs after the concrete specialized table producer.
Every cache is rebuilt from persistent source words by paid native copies;
neutral factor IDs leave the running multiplicative identity unchanged. -/
namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FactorAssignmentProgram

open OAI BitProgram StructuredCalls SubexpSetupStorage
open SqrtLog SqrtLog.LeafProgram
noncomputable section

noncomputable def callbackInitial (a : Data) : Data :=
  embedState localRegister lowStack a
    (clearManyState callbackScratch (projectState localRegister lowStack a))

def clearCallbackCost (a : Data) : ℕ :=
  clearManyCost callbackScratch (projectState localRegister lowStack a) + 1

noncomputable def initialized (a : Data) : Data :=
  embedState localRegister id a
    (clearManyState entryScratch (projectState localRegister id a))

def initializeCost (a : Data) : ℕ :=
  clearManyCost entryScratch (projectState localRegister id a) + 1

end
end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FactorAssignmentProgram
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_FactorEnvironment
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! The seven fixed persistent cache words are physically copied into the
native arithmetic environment. Cleanup clears those seven copies; both
commands frame all other stacks, including the query buffers. -/
namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FactorEnvironment

open OAI BitProgram StructuredCalls
open SubexpSetupStorage SqrtLog.MomentsProgram

abbrev Data := State 40 896

noncomputable def bootstrapResult (a : Data) : Data :=
  embedState registerMap id a (copyManyState pairs (projectState registerMap id a))

noncomputable def resetResult (a : Data) : Data :=
  embedState registerMap id a (clearManyState environmentPorts (projectState registerMap id a))

def bootstrapCost (a : Data) : ℕ := copyManyCost pairs (projectState registerMap id a) + 1

def resetCost (a : Data) : ℕ := clearManyCost environmentPorts (projectState registerMap id a) + 1

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FactorEnvironment
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_FactorAssignmentBranches
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! Actual ordinary and marked factor branches. The physical factor ID is
converted to the unary source counter, then the specialized table is produced
before the original finite-ring arithmetic is run. -/
namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FactorAssignmentBranches

open OAI BitProgram StructuredCalls SubexpLiftRing SubexpQuarticRing
open SqrtLog SqrtLog.LeafProgram HashCircuitProgram HashCircuitProgram.Native
open IdempotentApplyProgram.Steps MomentsProgram
open FactorAssignmentProgram
open Subexp.ConstructivePacking MulticolorTypes LayoutProgram DensePolynomialProgram

/-- Exact state after the paid factor-ID copy and its guarded pop. -/
noncomputable def identified (a : FactorAssignmentProgram.Data) (factor : ℕ) : FactorAssignmentProgram.Data :=
  embedState id lowStack a (FactorID.output (projectState id lowStack a) factor)

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FactorAssignmentBranches
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_QueryEvaluation
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! Exact natural-valued query semantics. These identities preserve the ambient
assignment type, including coordinates absent from every clause. -/
namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryEvaluation

open OAI.Algorithms.SubexponentialSAT.SqrtLog
open scoped BigOperators

section SquarefreeBridge

variable {V R : Type*} [DecidableEq V] [CommRing R]

/-- Substitute correction variables immediately and retain only the two
bounded scalar coefficient indices. -/
noncomputable def specializeDense (t J : ℕ) (x : V → Bool) :
    Squarefree.Jet V R →+* Dense R t J :=
  (Dense.ofPolynomial t J).comp
    (Squarefree.evalJet (Squarefree.boolValue x) (Squarefree.boolValue_idempotent x))

@[simp] theorem coeff_specializeDense (t J : ℕ) (x : V → Bool)
    (f : Squarefree.Jet V R) (u : Fin t) (z : Fin J) :
    ((specializeDense t J x f).coeff u).coeff z =
      Squarefree.evalBool x ((f.coeff u.val).coeff z.val) := by
  simp [specializeDense, Squarefree.coeff_evalJet, Squarefree.evalBool]

end SquarefreeBridge

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryEvaluation
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_QueryJetCanonical
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! Canonical cutoff identities for immediate Boolean scalarization. These
identities retain precisely the same lifting and Taylor coefficient ranges. -/

namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryJetSemantics

open Polynomial OAI OAI.Algorithms.SubexponentialSAT.SqrtLog

section CanonicalSpecialization
variable {V R : Type*} [DecidableEq V] [CommRing R]

/-- The actual scalar specialization retains exactly the source cutoffs. -/
@[simp] theorem specializeDense_canonical (t J : ℕ) (x : V → Bool)
    (f : Squarefree.Jet V R) :
    QueryEvaluation.specializeDense t J x (Squarefree.canonical t J f) =
      QueryEvaluation.specializeDense t J x f := by
  ext u z
  simp [QueryEvaluation.coeff_specializeDense, Squarefree.coeff_canonical, u.isLt, z.isLt]

end CanonicalSpecialization

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryJetSemantics
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_FactorTableDenotation
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! The actual normalized incidence payload has the canonical scalarized
source denotation. Source arrays are witnesses produced by the finite source
machine; their full polynomial meanings identify one fixed incidence jet. -/
namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FactorTableDenotation
open OAI OAI.Algorithms.SubexponentialSAT.SqrtLog OAI.Algorithms.SubexponentialSAT.SubexpLiftRing OAI.Algorithms.SubexponentialSAT.SubexpQuarticRing
open MomentsProgram TruncatedRingProgram DensePolynomialProgram
open OAI.Algorithms.SubexponentialSAT.Subexp.ConstructivePacking OAI.Algorithms.SubexponentialSAT.MulticolorTypes LayoutProgram
open scoped BigOperators
noncomputable section
variable {R : Type*} [CommRing R]

/-- The exact correction word is interpreted on the declared ambient type. -/
def specializedJet {n : ℕ} (u J : ℕ) (mask : List Bool)
    (jet : Squarefree.Jet (Fin n) R) : Squarefree.Jet (Fin n) R :=
  Squarefree.canonical u J (Moments.jetScalar (Moments.jetEval
    (fun v => if v ∈ Squarefree.decodeMask n mask then (1 : R) else 0)
    (by intro v; split <;> simp) jet))

end
end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FactorTableDenotation
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_HashCandidates
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-!
The hash stream visits binary payloads in increasing unsigned order and reduces
each indexed ternary digit modulo3*m before the existing row assembler. Every
original candidate is attained and unchanged by normalization. Extra normalized
duplicates preserve the minimum. Visits are bounded by the square of the old family.
-/

namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HashCandidates

open OAI.Algorithms.SubexponentialSAT.SqrtLog OAI.Algorithms.SubexponentialSAT.SqrtLog.HashFamily

/-- Proof-level accessor for the word present at a binary odometer rank. -/
def payload (m depth : ℕ) (i : Fin (2 ^ payloadWidth m depth)) : List Bool :=
  (ExecCNFTupleEnumeration.fixedBits (payloadWidth m depth) i.val).reverse

@[simp] theorem payload_length (m depth : ℕ) (i : Fin (2 ^ payloadWidth m depth)) :
    (payload m depth i).length = payloadWidth m depth := by
  simp [payload]

@[simp] theorem payload_value (m depth : ℕ) (i : Fin (2 ^ payloadWidth m depth)) :
    CounterPrograms.value (payload m depth i).reverse = i.val := by
  simpa [payload] using ExecCNFTupleEnumeration.fixedBits_value _ _ i.isLt

@[simp] theorem zero_depth_payload (m : ℕ) (i : Fin (2 ^ payloadWidth m 0)) :
    payload m 0 i = [] := by
  simp [payload, payloadWidth, ExecCNFTupleEnumeration.fixedBits]


@[simp] theorem normalize_length (m depth : ℕ) (raw : List Bool) :
    (normalize m depth raw).length = payloadWidth m depth := by
  simp [normalize, List.length_flatten, List.map_map, payloadWidth,
    Function.comp_def]


end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HashCandidates
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_HashCandidateProgram
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HashCandidateProgram

open OAI.Algorithms.SubexponentialSAT.BitProgram OAI.Algorithms.SubexponentialSAT.StructuredCalls OAI.Algorithms.SubexponentialSAT.SqrtLog

def data (regs : Fin 8 → Bool) (next best : BinaryArgmin.Entry)
    (queue counter : List Bool) : State 8 11 :=
  ⟨regs, ![next.payload, next.score, best.payload, best.score,
    [], [], [], [], queue, counter, []]⟩

/-- One bounded current-record load. The entire family is never an input. -/
def load : Cmd 8 11 :=
  .seq (.call (StackRoutines.copyProgram 9 8 10 0 1))
    (.seq (HashSelectProgram.parse core) (.call (StackRoutines.clearProgram 8 0 1)))

/-- Actual fixed finite table for one candidate load, suitable for relocation
into the selector bank. Its time is polynomial in one retained candidate. -/
def loadProgram := compiled load 9 0

namespace Normalize

open OAI.Algorithms.SubexponentialSAT.SubexpScanPrimitives

/-- Ports 0..7 are the existing modular arithmetic bank. The remaining
ports hold unread bits, the accumulated normalized payload and take scratch. -/
def state (regs : Fin 8 → Bool) (chunk modulus unread result : List Bool) : State 8 12 :=
  ⟨regs, ![chunk, [], [], [], [], modulus, [], [], unread, result, [], []]⟩

def digit : Cmd 8 12 := .call
  (ProgramLinking.liftProgram ModularRingPrograms.wordAddProgram id arithmeticPorts)

def take : Cmd 8 12 := takeWord 5 10 11 8 0 0 1

def emit : Cmd 8 12 := .call (StackRoutines.transferProgram 0 9 0 1)

def step : Cmd 8 12 := .seq take (.seq digit emit)


def probe : Cmd 8 12 := .base (.atom (.peek 8 0 1))

def loop : Cmd 8 12 := .while 1 (.seq step probe)

/-- Normalization scans one retained payload. It has polynomial bit time;
therefore the local all-stack prefix rule applies to every invocation. -/
def command : Cmd 8 12 := .seq probe loop



def prepare : Cmd 8 12 := .call (StackRoutines.reverseProgram 8 0 1 0 1)

def normalize : Cmd 8 12 := .seq prepare command

def budget (m depth : ℕ) : ℕ :=
  9 * HashCandidates.payloadWidth m depth +
    depth * (5000 * (HashCandidates.digitWidth m + 1) ^ 2 + 4) + 11

def program := compiled normalize 8 9


end Normalize

namespace ZeroCounter

open OAI.Algorithms.SubexponentialSAT.Subexp.TupleProgram

/-- The retained modulus is port3; the binary depth is port2. Ports0,4,5
are scratch and port1 is the current framed counter under construction. -/
def state (regs : Fin 3 → Bool) (scan output count modulus : List Bool) : State 3 6 :=
  ⟨regs, ![scan, output, count, modulus, [], []]⟩

def peek : Cmd 3 6 := .base (.atom (.peek 0 0 1))

def bit : Cmd 3 6 := .seq (.base (.atom (.pop 0 0 1)))
  (.seq (pushConst 1 0 false) (.seq (pushConst 1 0 true) peek))

def bitsLoop : Cmd 3 6 := .while 1 bit

def bits : Cmd 3 6 := .seq peek bitsLoop

def body : Cmd 3 6 := .seq (.call (StackRoutines.copyProgram 3 0 5 0 1)) bits

def ports : CounterForPrograms.Ports 3 6 where
  register := ⟨id, Function.injective_id⟩
  counter := 2
  scratch := 4
  counter_ne_scratch := by decide

def loop : Cmd 3 6 := CounterForPrograms.forCmd ports body

/-- Initialization adds the list/frame terminators; finalization adds the
leading list marker and clears the exhausted binary depth word. -/
def command : Cmd 3 6 :=
  .seq (pushConst 1 0 false) (.seq (pushConst 1 0 false)
    (.seq loop (.seq (pushConst 1 0 true) (.call (StackRoutines.clearProgram 2 0 1)))))

def budget (count modulus : List Bool) : ℕ :=
  50 * (CounterPrograms.value count + 1) * (modulus.length + count.length + 1)

def program := compiled command 2 1

end ZeroCounter

namespace Leaf

open OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafOuterProgram
open scoped BigOperators

def loader : Cmd 40 896 := .call
  (ProgramLinking.liftProgram loadProgram registers loaderStacks)

def clearLow : Cmd 40 896 := BankRoutines.clearCmd 767 0 1 lowPorts

def normalizer : Cmd 40 896 :=
  .seq (route (768,8)) (.seq (route (780,5))
    (.seq (.call (ProgramLinking.liftProgram Normalize.program registers normalizerStacks))
      (.seq (route (9,768)) clearLow)))

def prepare : Cmd 40 896 := .seq loader normalizer

def budget (m depth : ℕ) : ℕ := Normalize.budget m depth +
  200 * (HashCandidates.payloadWidth m depth + HashCandidates.digitWidth m + 1)

end Leaf

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HashCandidateProgram
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_HashCandidateRank
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HashCandidateRank

open OAI.Algorithms.SubexponentialSAT.BitProgram OAI.Algorithms.SubexponentialSAT.StructuredCalls

/-- Proof-level rank of the actual retained word, including leading zeroes. -/
def wordRank {m depth : ℕ} (word : List Bool)
    (hlen : word.length = HashCandidates.payloadWidth m depth) :
    Fin (2 ^ HashCandidates.payloadWidth m depth) :=
  ⟨CounterPrograms.value word, by
    simpa only [hlen] using ExecCNFTupleOdometer.value_lt_power_length word⟩

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HashCandidateRank
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_HashGreedyProgram
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! The actual fixed binary comparison/update used by the streaming selector.
Its queue port is a bounded iterator frame, not a list of candidate records. -/

namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HashGreedyProgram

open OAI.Algorithms.SubexponentialSAT.BitProgram OAI.Algorithms.SubexponentialSAT.StructuredCalls
open OAI.Algorithms.SubexponentialSAT.SqrtLog
open scoped BigOperators


/-- Bootstrap from the separately paid first score. -/
def installProgram := compiled BinaryArgmin.installFirst 8 2

def appendWinner : Cmd 8 10 :=
  .seq (Subexp.TupleProgram.pushConst 9 0 false)
    (.seq (Subexp.TupleProgram.escape appendPorts)
      (.seq (Subexp.TupleProgram.pushConst 9 0 true)
        (.call (StackRoutines.clearProgram 3 0 1))))

/-- Only selected rows occur in this proof-level serialization. -/
def encodedHistory (rows : List (List Bool)) : List Bool :=
  Encoding.encodeList id (rows.map List.reverse)

def appendProgram := compiled appendWinner 2 9


namespace PadScore

open ModularPrograms ModularArithmetic

/-- The fixed-width shape is copied before padding, and survives every score.
Only the actual canonical mass word is padded; the final exact count has its
own canonical output path. -/
def command : Cmd 8 5 :=
  .seq (.call (StackRoutines.copyProgram 1 2 4 0 1))
    (.seq (.call (ProgramLinking.liftProgram paddingLEProgram id pads))
      (.seq (.call (StackRoutines.copyProgram 2 0 4 0 1))
        (.call (StackRoutines.clearProgram 2 0 1))))

def program := compiled command 0 0

def leafCommand : Cmd 40 896 :=
  .call (ProgramLinking.liftProgram program leafRegisters leafStacks)

end PadScore

namespace Initialize

open LeafOuterProgram

def normalize : Cmd 40 896 :=
  .call (ProgramLinking.liftProgram CounterNormalizeProgram.program registers normalizeStacks)

def unary : Cmd 40 896 :=
  .call (ProgramLinking.liftProgram CounterConversions.unaryProgram registers unaryStacks)

def transfer : Cmd 40 896 := .call (StackRoutines.transferProgram 0 781 0 1)

/-- Three measured parameter copies, positive modulus normalization, and the
actual conversion from binary round count to the unary loop controller. -/
def command : Cmd 40 896 :=
  .seq (routes savedRoutes) (.seq normalize (.seq unary transfer))

def clearCore : Cmd 40 896 := BankRoutines.clearCmd 767 0 1 corePorts

/-- Preserve the initial unary round count as a fixed score width before the
round controller starts consuming its own copy. This is separate from numeric
preparation because initial deterministic rows must be serialized at the same
canonical width before the argmin core is cleared. -/
def saveShape : Cmd 40 896 := route (781,818)

/-- Invoke only after the initial deterministic history is constructed using
the canonical width. This stage never repeats numerical preparation. -/
def finishSetup : Cmd 40 896 := .seq saveShape clearCore

def zeroCommand : Cmd 40 896 :=
  .seq (.call (StackRoutines.clearProgram 778 0 1))
    (.seq (route (817,0))
      (.call (ProgramLinking.liftProgram HashCandidateProgram.ZeroCounter.program
        registers zeroStacks)))

end Initialize

namespace NativeRound

def install : Cmd 40 896 :=
  .call (ProgramLinking.liftProgram HashGreedyProgram.installProgram registers coreStacks)

/-- Every attempted candidate, including every loser, performs preparation,
exact mass evaluation, and physical fixed-width score padding. `mass` is fixed
finite syntax; its implementation proof remains an integration obligation. -/
def attempt (mass : Cmd 40 896) : Cmd 40 896 :=
  .seq HashCandidateProgram.Leaf.prepare (.seq mass PadScore.leafCommand)

def body (mass : Cmd 40 896) : Cmd 40 896 :=
  .seq (attempt mass) (HashSelectProgram.update core)

def append : Cmd 40 896 :=
  .call (ProgramLinking.liftProgram appendProgram registers historyStacks)

/-- The outer unary controller reads a preserved counter stack. Resetting its
flag after the inner scan is an actual charged instruction. -/
def resetGuard : Cmd 40 896 := .base (.atom (.set 9 true))

end NativeRound

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HashGreedyProgram
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_HashGreedyCandidate
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! Exact reference values for the payload and full natural score physically
produced by the native candidate attempt. These accessors are proof objects;
the executable program retains only the current word and running minimum. -/
namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HashGreedyCandidate

open BitProgram StructuredCalls SqrtLog
open HashGreedyProgram HashGreedyProgram.NativeRound

/-- The actual parser reverses the binary odometer word before canonicalizing
its indexed ternary digits. -/
def candidate (m depth rank : ℕ) : List Bool :=
  HashCandidates.normalize m depth
    (ExecCNFTupleEnumeration.fixedBits (HashCandidates.payloadWidth m depth) rank).reverse

@[simp] theorem candidate_length (m depth rank : ℕ) :
    (candidate m depth rank).length = HashCandidates.payloadWidth m depth := by
  simp [candidate]

/-- Full natural mass is encoded in the common retained score width. -/
def entry {X : Type*} [Fintype X] (rowAccept : List Bool → X → Bool) (weight : X → ℕ)
    (n m depth : ℕ) (rows : List (List Bool)) (rank : ℕ) : BinaryArgmin.Entry :=
  ⟨candidate m depth rank, ExecCNFTupleEnumeration.fixedBits (HashSelect.loopCap n m)
    (HashSelect.mass rowAccept weight (candidate m depth rank :: rows))⟩

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HashGreedyCandidate
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_HashGreedyCNF
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.MulticolorTypes.instFintypeJoint _root_.OAI.Algorithms.SubexponentialSAT.MulticolorTypes.instFintypeSide _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingModel.Data.fieldFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! The concrete streamed selector uses the original ternary row semantics.
Its exact scores and normalized reference coverage discharge the greedy
contraction hypotheses. These statements concern the deterministic history
refined by the native run; native query and resource closure remain separate. -/
namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HashGreedyCNF

open SqrtLog
open scoped BigOperators

noncomputable section

def entry {n m : ℕ} (clauses : Fin m → SAT.Clause (Fin n)) (depth : ℕ) :=
  HashGreedyCandidate.entry (rowAccept clauses) (HashInput.violationWeight clauses) n m depth

def history {n m : ℕ} (clauses : Fin m → SAT.Clause (Fin n)) (depth : ℕ)
    (initial : List (List Bool)) (rounds : ℕ) : List (List Bool) :=
  HashSelectProgram.iter
    (HashGreedyRound.nextRows (entry clauses depth) (HashCandidates.payloadWidth m depth))
    rounds initial

end
end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HashGreedyCNF
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_HashMassAdapter
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! The actual marked-clause collector generalized to the frozen 40/896 leaf
bank. Its parser and adder are the original measured finite programs. All
marked queries are executed; their integer results are added before argmin.
The temporary query execution premise must be discharged by the concrete
optional-mark evaluator, including its high-assignment loop and cleanup. -/
namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HashMassAdapter

open BitProgram StructuredCalls RecordPrograms SqrtLog LeafProgram

abbrev Code := Cmd 40 896

def callback (query : Code) : Code := .seq query (LeafProgram.Mass.invoke massPorts)
def command (query : Code) : Code := LeafProgram.foldCommand recordPorts (callback query)
def program (query : Code) := compiled (command query) 320 322

variable {X Row : Type*} [Fintype X] {m : ℕ}

def normalize : Code := .call (ProgramLinking.liftProgram
  DisjointReuse.CanonicalWordProgram.normalizeUnsignedProgram normalizeRegisters normalizeStacks)

/-- Paid handoff of the aggregate, with its old accumulator reclaimed. -/
def finish : Code := .seq normalize
  (.seq (LeafOuterProgram.route (322,769)) (.call (StackRoutines.clearProgram 322 0 1)))


open LeafOuterProgram

open scoped BigOperators


end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HashMassAdapter
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_HashMarkedQueryAdapter
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! Actual per-mark staging and return adapters. Each reference is copied and
reversed into the frontend marker words. Each completed high-assignment count
is moved to the marked collector, with its temporary words reclaimed and parser
registers reset by real instructions. Fresh high-query setup remains mandatory. -/
namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HashMarkedQueryAdapter

open BitProgram StructuredCalls SqrtLog LeafOuterProgram

abbrev Code := Cmd 40 896

def resetParser : Code := .base (SubexpParameterProgram.atoms
  [.set 16 false, .set 17 true, .set 18 false])

def finish : Code := .seq (route (788,323))
  (.seq (BankRoutines.clearCmd 767 0 1 cleanupPorts) resetParser)

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HashMarkedQueryAdapter
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_HashMarkedReturn
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! Concrete return from a completed marked high-assignment count. All fresh
query workspace is reclaimed, the complete count is moved to323, and the
collector parser registers are reset after cleanup. The compact boundary cap
is distinct from the transient query cap. -/
namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HashMarkedReturn

open BitProgram StructuredCalls RecordPrograms SqrtLog
open HashMarkedQueryAdapter
open HashGreedyProgram.NativeRound

def upperClear : Code := BankRoutines.clearCmd 767 0 1 upperPorts

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HashMarkedReturn
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_HashTrialStage
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! Exact finite staging extracted from `SqrtLog.LeafOuterNativeStage` for the
space-aware hash pipeline. Semantic query provenance remains in the original
module, while these declarations live in the stronger development's namespace. -/
namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.LeafOuterNative
open OAI BitProgram StructuredCalls SqrtLog.LeafOuterProgram
open Subexp

def prefixed (a : Data) : Data :=
  TupleProgram.pushedState 701 0 true
    (TupleProgram.escapedState trialPorts
      (TupleProgram.pushedState 701 0 false (routed (768,702) a)))

def prefixCost (a : Data) : ℕ := routeCost (768,702) a+5*(a.stacks 768).length+7

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.LeafOuterNative
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_NativeLeaf
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! Actual adapters for the streamed counting leaf. Both initial code rows
and newly generated rows use the canonical modulus word's exact width. -/

namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeLeaf

open BitProgram StructuredCalls
open SqrtLog.LeafOuterProgram

def canonicalRowState (a : Data) : Data := routed (780, 783) (routed (780, 768) a)

def canonicalRowSteps (a : Data) : ℕ :=
  2 * (a.stacks 768).length + 2 * (a.stacks 783).length +
    14 * (a.stacks 780).length + 16

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeLeaf
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_NativeTerminal
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! Actual outer-CNF terminal handling. The ambient unary header is retained;
an empty formula emits its full count 2^n, and an empty clause emits zero. -/

namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeTerminal

open BitProgram StructuredCalls
open scoped BigOperators

def classifier : Cmd 80 1220 :=
  .call (ProgramLinking.liftProgram SqrtLog.LeafProgram.Trivial.program
    (Fin.castAdd 70) classifierStacks)

/-- Nonterminal leaves pass through with both classifier flags available. -/
def command : Cmd 80 1220 :=
  .seq classifier (.ite 0 zero (.ite 7 (.base .skip) power))

def readyCommand : Cmd 80 1220 := .seq prepare command


open DisjointReuse.DFSVisit

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeTerminal
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_NativeLeafSemantics
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FiniteFallback.literalFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! The leaf's serialized raw clauses and the selector's indexed clauses
have exactly the same ambient models. Repeated clauses or literals are not
assigned extra model multiplicity. -/
namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeLeafSemantics

open SqrtLog DisjointReuse
open scoped BigOperators

/-- Literal codes for each actual serialized clause, without sorting or
removing raw occurrences. The dependent index cast changes only its proof. -/
def recordIndex {n : ℕ} (F : RawCNF n) (i : Fin (NativeTerminal.clauseRecords F).length) :
    Fin F.length := ⟨i.val, by simpa [NativeTerminal.clauseRecords] using i.isLt⟩

def recordCodes {n : ℕ} (F : RawCNF n) (i : Fin (NativeTerminal.clauseRecords F).length) :
    List ℕ := (F.get (recordIndex F i)).map Encoding.literalCode

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeLeafSemantics
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SubexpIntervalCoreProgram
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! The multiplication and predecessor prefix of the actual interval-start
initializer. All widths refer to physical input words, including padding. -/

namespace SubexponentialSAT.SubexpIntervalCoreProgram

open BitProgram StructuredCalls BinaryArithmetic

attribute [local simp] Fin.coe_ofNat_eq_mod

def inputWords (r Q R : List Bool) : Words := ![r, Q, R, [], [], [], [], [], [], []]

end SubexponentialSAT.SubexpIntervalCoreProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SubexpIntervalFinishProgram
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Actual long division and scratch cleanup for the interval initializer. -/

namespace SubexponentialSAT.SubexpIntervalFinishProgram

open BitProgram StructuredCalls BinaryArithmetic SubexpIntervalCoreProgram

attribute [local simp] Fin.coe_ofNat_eq_mod

def clearedWords : List (Fin 10) → Words → Words
  | [], w => w
  | i :: is, w => clearedWords is (Function.update w i [])

end SubexponentialSAT.SubexpIntervalFinishProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SubexpIntervalStartProgram
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# Physical binary initialization of the centered interval start

Three preserved input words encode r, Q, and R on ports 0, 1, and 2.
The fixed program computes ((Q-1)*(r-1)-R*r)/(2*r) using saturated
predecessors, products, saturated subtraction, and binary long division.
Only output port 3 differs on return; ports 4 through 31 are empty again.
-/

namespace SubexponentialSAT.SubexpIntervalStartProgram

open BitProgram StructuredCalls BinaryArithmetic
open SubexpIntervalCoreProgram

attribute [local simp] Fin.coe_ofNat_eq_mod

def initialState (regs : Regs) (r Q R : List Bool) : Data :=
  state regs (inputWords r Q R)

def finalState (regs : Regs) (r Q R output : List Bool) : Data :=
  state regs (Function.update (inputWords r Q R) 3 output)

end SubexponentialSAT.SubexpIntervalStartProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_HighFrontendSources
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FiniteFallback.literalFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! Typed source and empty-workspace relations follow from the actual trial
and accepted source stages. Changing the marked clause does not change the
immutable source words; its scope and high mask are recomputed by the frontend. -/
namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighFrontendSources

open OAI BitProgram StructuredCalls
open OAI.Algorithms.SubexponentialSAT.SqrtLog
open HighMarkedFrontend

/-- A proof-side description of precisely the native raw records and source
words. The runtime receives the existing encoded masters, not this record. -/
def rawQuery {n : ℕ} (F : DisjointReuse.RawCNF n)
    (rows : HashScopeProgram.RawTable.Rows (NativeTerminal.clauseRecords F).length)
    (mark : Option (Fin (NativeTerminal.clauseRecords F).length))
    (index width modulus ambient : List Bool) : LeafQueryFrontend.Query where
  clauses := NativeTerminal.clauseRecords F
  codes := NativeLeafSemantics.recordCodes F
  rows := rows
  mark := mark
  index := index
  width := width
  modulus := modulus
  ambient := ambient

theorem recordLength {n : ℕ} (F : DisjointReuse.RawCNF n) :
    F.length=(NativeTerminal.clauseRecords F).length := by simp [NativeTerminal.clauseRecords]

def recordRows {n : ℕ} (F : DisjointReuse.RawCNF n)
    (rows : HashScopeProgram.RawTable.Rows F.length) := castRows (recordLength F) rows

def recordMark {n : ℕ} (F : DisjointReuse.RawCNF n) (mark : Option (Fin F.length)) :=
  mark.map (Fin.cast (recordLength F))

/-- Actual selected rows and marked indices keep their literal numeric bytes
when related to the serialized clause-record indexing. -/
def rawQueryFromRows {n : ℕ} (F : DisjointReuse.RawCNF n)
    (rows : HashScopeProgram.RawTable.Rows F.length) (mark : Option (Fin F.length))
    (index width modulus ambient : List Bool) : LeafQueryFrontend.Query :=
  rawQuery F (recordRows F rows) (recordMark F mark) index width modulus ambient

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighFrontendSources
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_HashQueryResources
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FiniteFallback.literalFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! Concrete scope resources of the actual serialized raw-formula query.
The dependent clause-index cast preserves every repeated or zero raw slot;
these results use no identity with the former materialized selector. -/
namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HashQueryResources

open SqrtLog HighFrontendSources HashGreedyCode
open DisjointReuse

@[simp] theorem recordRows_length {n : ℕ} (F : RawCNF n)
    (rows : HashScopeProgram.RawTable.Rows F.length) :
    (recordRows F rows).length = rows.length := by simp [recordRows, castRows]

@[simp] theorem recordRows_slots {n : ℕ} (F : RawCNF n)
    (rows : HashScopeProgram.RawTable.Rows F.length) :
    LeafScopeResourceBounds.slots (recordRows F rows) = LeafScopeResourceBounds.slots rows := by
  simp [LeafScopeResourceBounds.slots, recordRows, castRows, List.map_map, Function.comp_def]

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HashQueryResources
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_SparseCodeProgram
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingModel.Data.fieldFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-!
# Sparse rows from the candidates actually selected by the search

The construction below consumes the selected shifts and local matrix explicitly. Its
proofs need their checked Walsh and distance properties, not identity with the old
materialized search's selected candidates. The finite list of final rows is polynomial
size and can be retained; lists of all candidates and all test words cannot.
-/

namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.CodeChecks

open OAI.Algorithms.SubexponentialSAT.BitProgram OAI.Algorithms.SubexponentialSAT.StructuredCalls
open OAI.Algorithms.SubexponentialSAT.SqrtLog OAI.Algorithms.SubexponentialSAT.SqrtLog.CodeSearchProgram

/-- A proof-only predicate on the odometer rank. The native callback computes
this predicate by conversion and the arithmetic checks; it is never an oracle. -/
noncomputable def rejectedRank {p d : ℕ} [Fact p.Prime]
    (reject : (Fin d → ZMod p) → Prop) (rank : ℕ) : Bool := by
  classical
  exact decide (∃ x, CounterPrograms.value (CodeCandidates.fieldWords x).flatten = rank ∧ reject x)

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.CodeChecks
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

def cleanup : Cmd 16 48 :=
  .seq (.call (StackRoutines.clearProgram 40 0 1))
    (.call (StackRoutines.clearProgram 42 0 1))


open OAI.Algorithms.SubexponentialSAT.SqrtLog OAI.Algorithms.SubexponentialSAT.SqrtLog.CodeSearchProgram CodeChecks

def leafCall (routine : Cmd 16 48) (output : Fin 48) : Cmd 40 896 :=
  .call (ProgramLinking.liftProgram (compiled routine 46 output) leafRegisters leafStacks)

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

def clearLower : Cmd 40 896 := BankRoutines.clearCmd 767 0 1 lowerPorts

def saveAndClear (source target : Fin 896) : Cmd 40 896 :=
  .seq (route (source, target)) clearLower

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeCode
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafOuterProgramParameters
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! The actual outer-leaf parameter stage: input copies, native arithmetic,
output copies, and complete worker cleanup, with every command charged. -/
namespace SubexponentialSAT.SqrtLog.LeafOuterProgram
open SubexponentialSAT BitProgram StructuredCalls BinaryArithmetic
open LeafParametersProgram.Bank

def inputWords (a : Data) : Words :=
  fun i => if i=0 then a.stacks 782 else if i=1 then a.stacks 786 else []

end SubexponentialSAT.SqrtLog.LeafOuterProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_HashQueryEntry
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FiniteFallback.literalFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! The actual normalizer, trial source stage and marked-record parser supply
the literal query sources. These proofs impose no length cap on the suspended
reference tail or mass accumulator, and execute no extra marker stage. -/
namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HashQueryEntry

open BitProgram StructuredCalls SqrtLog
open HighFrontendSources HashGreedyCode

noncomputable def trialRows {n B : ℕ} (F : DisjointReuse.RawCNF n) (hm : 0 < F.length)
    (shifts : SparseCode.SuppliedShifts F.length B) (Q : SparseCode.SuppliedLocal F.length B)
    (rounds : ℕ) (word : List Bool) : HashScopeProgram.RawTable.Rows F.length :=
  (HashGreedyCandidate.candidate F.length (SparseCode.distanceDenom F.length B)
      (CounterPrograms.value word) ::
    HashGreedyCNF.history (NativeLeafSemantics.indexed F)
      (SparseCode.distanceDenom F.length B) (initial shifts Q) rounds).map (raw F.length hm)

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HashQueryEntry
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_HashQueryInputBounds
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! Physical input bounds for all attained greedy histories and every trial,
including losing candidates. All bounds concern literal retained words and
raw slots. No execution-time or successful-query bound is used. -/
namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HashQueryInputBounds

open BitProgram StructuredCalls SqrtLog
open HashGreedyProgram HashGreedyCNF HashGreedyCode

@[simp] theorem trial_bytes (payload : List Bool) (rows : List (List Bool)) :
    (encodedHistory (payload :: rows)).length =
      (encodedHistory rows).length + 2 * payload.length + 2 := by
  simp only [encodedHistory, List.map_cons, Encoding.encodeList, id_eq, List.length_cons,
    List.length_append, Encoding.length_frame, List.length_reverse]
  omega

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HashQueryInputBounds
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_HeadEvaluationProgram
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! Concrete correction-mask checking for a head rescan. This local routine
preserves its input masters and charges every stack at every source prefix. -/

namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HeadEvaluationProgram.CorrectionGate
open OAI BitProgram StructuredCalls StackRoutines
open OAI.Algorithms.SubexponentialSAT.SqrtLog LeafWeightProgram.Native

def command : Cmd 8 10 := .seq (copy 0 5)
  (.seq (copy 1 6) (.seq (copy 2 7) scan))

def program := compiled command 0 0

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HeadEvaluationProgram.CorrectionGate

namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HeadEvaluationProgram.HeadGate
open OAI BitProgram StructuredCalls
open OAI.Algorithms.SubexponentialSAT.SqrtLog.BucketProgram
open OAI.Algorithms.SubexponentialSAT.Subexp.MatrixProgramSupport

abbrev Data := State 16 32
abbrev Code := Cmd 16 32

def correctionCall : Code := .call (ProgramLinking.liftProgram
  CorrectionGate.program keyRegisters correctionStacks)

def clearKey : Code := .call (StackRoutines.clearProgram 14 (0:Fin 16) 1)

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HeadEvaluationProgram.HeadGate

namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HeadEvaluationProgram.StagedGate
open OAI BitProgram StructuredCalls StackRoutines
open OAI.Algorithms.SubexponentialSAT.Subexp.MatrixProgramSupport
open OAI.Algorithms.SubexponentialSAT.SqrtLog.BucketProgram

abbrev Data := State 40 896

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HeadEvaluationProgram.StagedGate
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_HeadSumProgram
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! The head rescan retains one raw Boolean assignment and a binary countdown.
The full-key/correction gate is executed for every candidate. Accepted values
are accumulated before the cursor advances, including the empty-head case. -/

namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HeadSumProgram

open OAI BitProgram StructuredCalls CounterPrograms

abbrev Data := State 40 896


open OAI.Algorithms.SubexponentialSAT.SqrtLog OAI.Algorithms.SubexponentialSAT.SqrtLog.MomentsProgram OAI.Algorithms.SubexponentialSAT.SubexpLiftRing
open OAI.Algorithms.SubexponentialSAT.SubexpQuarticRing TruncatedRingProgram


open OAI.Algorithms.SubexponentialSAT.Subexp.MatrixProgramSupport
open OAI.Algorithms.SubexponentialSAT.SqrtLog.BucketProgram

open scoped BigOperators

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HeadSumProgram
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_NativeFrontend
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.Native

open BitProgram StructuredCalls

def normalizationCommand : Cmd 80 1220 :=
  .call (ProgramLinking.liftProgram SubexpNormalizationProgram.program
    normalizationRegisters normalizationStacks)

def frontendCommand : Cmd 80 1220 :=
  .seq headerCommand (.seq normalizationCommand (.seq placeBodyCommand ambientCommand))


end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.Native
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_NativeEntry
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! The canonical frontend and actual fixed-cutoff dispatcher share one finite
program. The large command is supplied by the subsequent concrete integration. -/

namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.Native

open BitProgram StructuredCalls

noncomputable def entryCommand (cutoff : ℕ) (large : Cmd 80 1220) : Cmd 80 1220 :=
  .seq frontendCommand (FiniteFallback.dispatchCommand cutoff large)

noncomputable def entryProgram (cutoff : ℕ) (large : Cmd 80 1220) :=
  compiled (entryCommand cutoff large) ABI.countStack ABI.answerStack

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.Native
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_NativeLeafDispatch
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! Actual terminal dispatch for the disjoint counting DFS. The retained ambient
dimension determines the empty-formula count. The nonterminal command is composed
after the same concrete classifier and must supply its own execution proof. -/

namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeLeafDispatch

open BitProgram StructuredCalls DisjointReuse DFSVisit

def command (nonterminal : Cmd 80 1220) : Cmd 80 1220 :=
  .seq NativeTerminal.readyCommand
    (.ite 0 (.base .skip) (.ite 7 nonterminal (.base .skip)))

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeLeafDispatch
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_ScheduleProgram
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! Actual binary construction of the disjoint-sparsification parameter.
All arithmetic uses fixed finite programs; the input numeral is runtime stack data. -/

namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.ScheduleProgram

open BitProgram StructuredCalls
open BinaryArithmetic (toNat)

def clogAt (port : Fin 32) : Cmd 8 32 :=
  .seq reset (.call (ProgramLinking.liftProgram DisjointReuse.BinaryClogProgram.program
    (Fin.castAdd 5) (clogStacks port)))

/-- Ports0..5 retain n, lambda, nu, nu squared, sqrt lambda, and s.
Scratch6..18 is reused and restored by each actual subroutine. -/
def command : Cmd 8 32 :=
  .seq (ArithmeticCalls.copyAt 0 1 6)
    (.seq (clogAt 1)
      (.seq (ArithmeticCalls.copyAt 1 2 6)
        (.seq (clogAt 2)
          (.seq (ArithmeticCalls.multiplyAt squarePorts)
            (.seq (SqrtLog.LeafParameterArithmetic.sqrtAt sqrtPorts)
              (SqrtLog.LeafParameterArithmetic.quotientAt quotientPorts))))))


def program := compiled command 0 5

def sharedCall : Cmd 80 1220 :=
  .call (ProgramLinking.liftProgram program (Fin.castAdd 72) sharedStacks)

def readySharedCall : Cmd 80 1220 := .seq resetShared sharedCall

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.ScheduleProgram
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_NativeSetupSpace
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! Concrete canonical startup through the disjoint sparsification parameters.
The only large-instance premises concern the numeric schedule. All parsing,
normalization, arithmetic, clearing, and caller storage belong to one run. -/

namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.Native

open BitProgram StructuredCalls BinaryArithmetic

def budgetCall (k : ℕ) : Cmd 80 1220 :=
  .call (ProgramLinking.liftProgram (DisjointReuse.SparseBudgetProgram.program k)
    (Fin.castAdd 72) budgetStacks)

def setupAfterFrontend (k : ℕ) : Cmd 80 1220 :=
  .seq (.seq ScheduleProgram.readySharedCall clearSchedule) (budgetCall k)

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.Native
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_NodeReadoutSpace
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! Actual node-array readout after all finite-difference pairs. The fixed
cleanup pays for transient lower words and clears the old output. Preserved
masters supply the coefficient zero vector and both truncation bounds. -/

namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NodeReadoutSpace

open OAI BitProgram StructuredCalls SqrtLog SubexpLiftRing SubexpQuarticRing
open MomentsProgram TruncatedRingProgram

abbrev Data := State 40 896

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NodeReadoutSpace
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_NodeAppendSpace
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NodeAppendSpace
open OAI BitProgram StructuredCalls SqrtLog SubexpLiftRing SubexpQuarticRing
open MomentsProgram TruncatedRingProgram

abbrev Data := State 40 896

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NodeAppendSpace
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_QueryNodeFinish
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! Actual node readout and loop continuation. The emitted coefficient stream
retains its order. Node temporaries are physically reclaimed before refreshing
the outer guard, and every completed node restores one fixed boundary bound. -/

namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryNodeFinish

open OAI BitProgram StructuredCalls SqrtLog SubexpLiftRing SubexpQuarticRing
open MomentsProgram TruncatedRingProgram

abbrev Data := State 40 896

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryNodeFinish
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SubexpCRTOuterControl
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Concrete tape operations and traversal assertions for the outer CRT.
All operations in this module are fixed finite programs. Arithmetic is supplied
by the separately defined concrete CRT service commands. -/

namespace SubexponentialSAT.SubexpCRTOuterProgram

open BitProgram StructuredCalls SubexpScanPrimitives

def sweepState (regs : Fin 16 → Bool) (frame : Fin 320 → List Bool) (w : SweepWords) :
    Data := ⟨regs, sweepStore frame w⟩

end SubexponentialSAT.SubexpCRTOuterProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SubexpCRTOuterSetup
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Actual initialization for the outer CRT tape controller. Widths and the
binary dimension are computed by fixed programs from the retained runtime
inputs. In particular, neither a binary exponent nor a jet-width word is
provided for free. -/

namespace SubexponentialSAT.SubexpCRTOuterProgram

open BitProgram StructuredCalls SubexpScanPrimitives

abbrev moved (d : Data) (src dst : Fin 320) : Data :=
  ⟨readRegs d.regs 0 1 none,
    Function.update (Function.update d.stacks src []) dst (d.stacks src)⟩

abbrev threeReset (d : Data) : Data :=
  ⟨Function.update (Function.update (Function.update d.regs 0 false) 1 false) 2 false,
    d.stacks⟩

abbrev jetWidthState (d : Data) (D : ℕ) : Data :=
  ⟨(threeReset (afterCopy d 243 279 0 1)).regs,
    Function.update d.stacks 277
      (Subexp.BlockCopyProgram.copies D (d.stacks 104) ++ d.stacks 277)⟩

end SubexponentialSAT.SubexpCRTOuterProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_QueryReconstruction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! The actual streamed-jet handoff, scratch preparation, and canonical count
reconstruction. Readiness is derived from the produced ring masters. The target
and jets are mathematical properties of the actual query output; no evaluator
or readiness service is accepted by the produced-input theorem. -/
namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryReconstruction

open OAI BitProgram StructuredCalls SubexpLiftRing SubexpQuarticRing OAI.Algorithms.SubexponentialSAT.SqrtLog
open DensePolynomialProgram LeafProgram
open LeafParametersProgram
attribute [local simp] Fin.coe_ofNat_eq_mod

abbrev Data := State 40 896
abbrev CoreData := State 40 768

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryReconstruction
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_QueryTupleSum
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! Concrete unsigned tuple accumulation. The complete head product on852
is normalized into the pair accumulator851. Physical caches are copied from
retained masters and every native peripheral scratch word is paid for. -/
namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryTupleSum

open OAI BitProgram StructuredCalls SqrtLog SubexpLiftRing SubexpQuarticRing
open MomentsProgram TruncatedRingProgram

abbrev Data := State 40 896
end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryTupleSum
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

/-- Each field is a finite instruction table, rather than a semantic oracle.
`ascend` restores the parent's cursor and advances it once. `descend` saves
the current cursor and starts the child at its first Boolean assignment. -/
structure Routines (r s : ℕ) where
  setup : Cmd r s
  probe : Cmd r s
  descend : Cmd r s
  advance : Cmd r s
  ascend : Cmd r s
  visit : Cmd r s

def body {r s : ℕ} (p : Ports r) (q : Routines r s) : Cmd r s :=
  .ite p.leaf (.seq q.visit q.ascend)
    (.seq q.probe (.ite p.available (.ite p.fresh q.descend q.advance) q.ascend))

def loop {r s : ℕ} (p : Ports r) (q : Routines r s) : Cmd r s :=
  .while p.active (body p q)

def command {r s : ℕ} (p : Ports r) (q : Routines r s) : Cmd r s :=
  .seq q.setup (loop p q)

/-- Preserving copy uses one fixed empty scratch stack and two low registers. -/
def copyWord (src dst tmp : Fin 896) : Cmd 40 896 :=
  .call (StackRoutines.copyProgram src dst tmp 0 1)

def pushWordCommand (src dst : Fin 896) (h : src ≠ dst) : Cmd 40 896 :=
  .call (ProgramLinking.liftProgram pushFrameProgram frameRegisters (wordPorts src dst h))

def popWordCommand (src dst : Fin 896) (h : src ≠ dst) : Cmd 40 896 :=
  .call (ProgramLinking.liftProgram ParserProgram.frameProgram frameRegisters (wordPorts src dst h))

/-- A suspended head retains exactly its cursor and remaining count. Matrix
rows and keys are reconstructed when the head resumes. -/
def saveCursorCommand : Cmd 40 896 :=
  .seq (pushWordCommand (tupleStacks 2) (tupleStacks 0) (by decide))
    (pushWordCommand (tupleStacks 7) (tupleStacks 0) (by decide))

def restoreCursorCommand : Cmd 40 896 :=
  .seq (popWordCommand (tupleStacks 0) (tupleStacks 7) (by decide))
    (popWordCommand (tupleStacks 0) (tupleStacks 2) (by decide))

/-- Retain one emitted representative, with deepest head first on the physical
stack. The callback reconstructs its key from the exact retained assignment. -/
def recordRepresentativeCommand : Cmd 40 896 :=
  .seq (copyWord (tupleStacks 2) (tupleStacks 4) (tupleStacks 5))
    (pushWordCommand (tupleStacks 4) (tupleStacks 1) (by decide))

/-- The remaining head count and physical color address are unary polynomial
words. They occupy two persistent ports, independent of the number of heads. -/
def descendLevelCommand : Cmd 40 896 :=
  .base (.seq (.atom (.pop (tupleStacks 6) 0 1))
    (.seq (.atom (.set 0 true)) (.seq (.atom (.push (tupleStacks 9) 0))
      (.seq (.atom (.peek (tupleStacks 6) 0 1))
        (.atom (.bnot controllerPorts.leaf 1))))))

def ascendLevelCommand : Cmd 40 896 :=
  .base (.seq (.atom (.pop (tupleStacks 9) 0 1))
    (.seq (.atom (.set 0 true)) (.seq (.atom (.push (tupleStacks 6) 0))
      (.atom (.set controllerPorts.leaf false)))))

/-- Clear a current-head word before reusing its physical stack. -/
def clearWord (src : Fin 896) : Cmd 40 896 :=
  .call (StackRoutines.clearProgram src 0 1)

/-- The list specifies finitely many fixed physical ports in the control table;
it is never computed from or proportional to the assignment count. -/
def clearWords : List (Fin 896) → Cmd 40 896
  | [] => .base .skip
  | src :: rest => .seq (clearWord src) (clearWords rest)

def leaveHeadCommand : Cmd 40 896 := clearWords currentHeadPorts

/-- Discard exactly one recorded representative after its subtree finishes. -/
def dropRepresentativeCommand : Cmd 40 896 :=
  .seq (popWordCommand (tupleStacks 1) (tupleStacks 4) (by decide))
    (clearWord (tupleStacks 4))

/-- Root detection uses the presence bit of the frame stack; a zero-bit or
empty payload frame is still present because it has an encoded delimiter. -/
def testParentCommand : Cmd 40 896 :=
  .base (.atom (.peek (tupleStacks 0) 0 controllerPorts.active))

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SignatureTupleProgram
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_SignatureHeadLoader
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! The concrete head-loader is specialized to actual node bootstrap data.
All physical entry contracts are discharged by the native cache producer. -/
noncomputable section
namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SignatureHeadLoader
open OAI BitProgram StructuredCalls OAI.Algorithms.SubexponentialSAT.SqrtLog
open OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafHeadSetupProgram
open OAI.Algorithms.SubexponentialSAT.SubexpSetupStorage

/-- Fresh node caches depend only on fixed source parameters, independently
of the retained caller frame and of the number of previous node calls. -/
def bootstrapOutputBound (s : Native.Inputs) : ℕ :=
  s.Q*s.r+s.r+s.D+s.R*s.width.length+s.width.length+s.height.length+s.R+3

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SignatureHeadLoader
end
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_QueryVisitorHead
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! The concrete one-head visitor composes its actual loader, paid key setup,
restricted head rescan and tuple multiplication. Exponential work is kept
separate from the reusable boundary and all-prefix storage bounds. -/
namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryVisitorHead
open OAI BitProgram StructuredCalls SqrtLog SqrtLog.LeafProgram SqrtLog.MomentsProgram
open SubexpLiftRing SubexpQuarticRing TruncatedRingProgram HeadIdentifierProgram
open BucketTupleProgram.Concrete QueryTupleState SubexpSetupStorage
open scoped BigOperators
noncomputable section

def factorIds (s : LeafHeadSetupProgram.Native.Inputs) (g : Fin s.r) : List ℕ :=
  LeafHeadFactorsProgram.chosenIds
    (LeafHeadFactorsProgram.predicate s.rows s.n (s.node.val*s.r+g.val)) s.N

end
end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryVisitorHead
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_SignatureTupleTraversal
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-!
# Cursor semantics for the attained-signature tuple controller

The cursor stores an attained prefix and one numeric candidate. Suspended
ancestors are first occurrences, so the tree branches over attained keys only.
The traces and finite sums below are mathematical specifications; the actual
controller retains neither a trace nor a family of assignments or tuples.
-/

namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SignatureTupleTraversal

open scoped BigOperators
open SignatureTupleDFS

open Classical

variable {N : ℕ → ℕ} {κ : ℕ → Type*}

section Frames

open ExecCNFTupleEnumeration SignatureTupleProgram

variable (h : ℕ → ℕ) {κ : ℕ → Type*}
  (key : (d : ℕ) → Fin (2 ^ h d) → κ d)

/-- Exactly one bounded binary assignment word per retained ancestor. -/
def representativeWords (depth : ℕ) (ancestors : Prefix (Representatives key) depth) :
    List (List Bool) :=
  List.ofFn fun i : Fin depth => fixedBits (h i.val) (ancestors i).val.val

/-- The deepest ancestor is first on physical representative stack 837. -/
def representativeFrames (depth : ℕ) (ancestors : Prefix (Representatives key) depth) :
    List Bool := suspendedFrames (representativeWords h key depth ancestors).reverse

/-- The frame order is the actual save-cursor command's order: remaining
first, then candidate. Both values use fixed polynomial word lengths. -/
def cursorFrame (width candidate : ℕ) : List Bool :=
  Encoding.frame (fixedBits (width + 1) (2 ^ width - candidate)).reverse ++
    Encoding.frame (fixedBits width candidate).reverse

def cursorFrames (depth : ℕ) (ancestors : Prefix (Representatives key) depth) : List Bool :=
  (List.ofFn fun i : Fin depth => cursorFrame (h i.val) (ancestors i).val.val).reverse.flatten

end Frames

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SignatureTupleTraversal
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

/-- Copy the runtime palette size and initial physical head address into two
persistent controller tapes. The active flag is set even for zero heads, so
the empty tuple reaches the callback exactly once. -/
def initializeLevelsCommand : Cmd 40 896 :=
  .seq (copyWord 130 (tupleStacks 6) (tupleStacks 5))
    (.seq (copyWord 649 (tupleStacks 9) (tupleStacks 5))
      (.base (.seq (.atom (.peek (tupleStacks 6) 0 1))
        (.seq (.atom (.bnot controllerPorts.leaf 1))
          (.atom (.set controllerPorts.active true))))))

/-- A real one-bit latch initializer, charged on every predicate call. It
also covers the first call after the loader has cleared its scratch bank. -/
def initializeFreshCommand : Cmd 40 896 :=
  .seq (clearWord (rescanStacks 22))
    (.base (.seq (.atom (.set 0 false)) (.atom (.push (rescanStacks 22) 0))))

/-- On return to a parent, only the predecessor zero word is reset. The saved
candidate and remaining counter are restored and then advanced exactly once. -/
def resetPredecessorCommand : Cmd 40 896 :=
  copyWord 651 (tupleStacks 8) (tupleStacks 5)

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SignatureTupleNative
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_SignatureTupleLoader
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! Concrete head reloads for the attained-signature DFS.  The matrix comes
from the fixed native integer-entry machine, and each reload restores one
fixed retained-word bound before the next candidate scan. -/

noncomputable section
namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SignatureTupleLoader
open OAI BitProgram StructuredCalls OAI.Algorithms.SubexponentialSAT.SqrtLog
open SignatureTupleProgram SignatureTupleNative
open LeafHeadSetupProgram OAI.Algorithms.SubexponentialSAT.SubexpSetupStorage

/-- This is the literal signed owner-sum matrix, with every ambient head
coordinate retained in the actual ascending identifier order. -/
def integerMatrix (s : Native.Inputs) (owner : Fin s.D → Fin s.n) (z : ℕ) :
    Fin s.D → Fin (selectedHeads s.n s.rows s.low z).length → ℤ :=
  fun j i => LayoutProducedMatrix.literalNat s.packing owner s.height.length s.R s.node
    j.val ((selectedHeads s.n s.rows s.low z).get i)

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SignatureTupleLoader
end
end


