-- Prove2me | Definitions.Def_OAIQ081S099
-- name    : OAIQ081S099
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-29T22:19:27.223139+00:00
-- url     : https://prove2.me/theorems/955f2055-34db-4829-8c9f-a28898888538
-- title:
--   Definitions bundle OAIQ081S099 of the split of OpenAI, The Exponential Time Hypothesis is False
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.exact_count_and_sat`, carved from OpenAI's openai/math development (OpenAI, *The Exponential Time Hypothesis is False*, OpenAI Math Release, October 25, 2026, result family 378, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 305 declarations of OpenAI's Lean: 277 definitions, 12 inductive types or structures and 16 theorems. The definitions and types are `OAI.Algorithms.SubexponentialSAT.SqrtLog.PolynomialExecutorProgram.plainData`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DifferencePairsRelational.CallbackSpec`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.BinaryClogProgram.decrement`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.BinaryClogProgram.reset`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.BinaryClogProgram.zeroPorts`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.CanonicalWordProgram.Data`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.CanonicalWordProgram.dropBody`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.CanonicalWordProgram.dropLoop`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.CanonicalWordProgram.emitZero`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.CanonicalWordProgram.finish`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.CanonicalWordProgram.normalizeUnsigned`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.CanonicalWordProgram.normalizeUnsignedProgram`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.CanonicalWordProgram.reset`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.CanonicalWordProgram.state`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.CanonicalWordProgram.test`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.CanonicalWordProgram.tested`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.CanonicalWordProgram.transferred`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.DFSStartup.Prepared`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.DFSStartup.startup`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.DFSVisit.BoundedEval`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.DFSVisit.LeafContract`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.DFSVisit.LeafDone`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.DFSVisit.LeafReady`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.DisjointBranchProgram.inputFront`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.DisjointBranchProgram.inputState`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.DisjointBranchProgram.outputFront`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.DisjointBranchProgram.outputState`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.DisjointBranchProgram.prepareB`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.NegatedCoreProgram.callback`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.NegatedCoreProgram.command`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.NegatedCoreProgram.program`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.ParametersProgram.Data`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.ParametersProgram.addCmd`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.ParametersProgram.arithmeticPorts`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.ParametersProgram.clearCmd`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.ParametersProgram.compareCmd`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.ParametersProgram.compareStacks`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.ParametersProgram.copyCmd`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.ParametersProgram.loadCmd`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.ParametersProgram.logStacks` and 249 more.
--
--   **Sources.** They come from these modules of lean/OAI/Algorithms, in whole or in part: `SubexponentialSAT_SqrtLogSpace_CommandStackTransport`, `SubexponentialSAT_SqrtLogSpace_CountDFS`, `SubexponentialSAT_SqrtLogSpace_DifferencePairsRelational`, `SubexponentialSAT_SqrtLogSpace_DisjointReuse_BinaryClogProgram`, `SubexponentialSAT_SqrtLogSpace_DisjointReuse_CanonicalWordProgram`, `SubexponentialSAT_SqrtLogSpace_DisjointReuse_DFSStartup`, `SubexponentialSAT_SqrtLogSpace_DisjointReuse_DFSVisit`, `SubexponentialSAT_SqrtLogSpace_DisjointReuse_NegatedCoreProgram`, `SubexponentialSAT_SqrtLogSpace_DisjointReuse_ParameterBank`, `SubexponentialSAT_SqrtLogSpace_DisjointReuse_SparseAccumulatorProgram`, `SubexponentialSAT_SqrtLogSpace_DisjointReuse_SparseBudgetProgram`, `SubexponentialSAT_SqrtLogSpace_DisjointReuse_SparseDFSProgram`, `SubexponentialSAT_SqrtLogSpace_DisjointReuse_SparseFrontierProgram`, `SubexponentialSAT_SqrtLogSpace_DisjointReuse_SparsePriorityPrimitives`, `SubexponentialSAT_SqrtLogSpace_DisjointReuse_SparsePriorityProgram`, `SubexponentialSAT_SqrtLogSpace_DisjointSparsifyProgram`, `SubexponentialSAT_SqrtLogSpace_FactorAssignmentProgram`, `SubexponentialSAT_SqrtLogSpace_FactorCacheProgram`, `SubexponentialSAT_SqrtLogSpace_FactorTableBudgets`, `SubexponentialSAT_SqrtLogSpace_FiniteFallback`, `SubexponentialSAT_SqrtLogSpace_HashCandidateProgram`, `SubexponentialSAT_SqrtLogSpace_HashGreedyCode`, `SubexponentialSAT_SqrtLogSpace_HashGreedyProgram`, `SubexponentialSAT_SqrtLogSpace_HashTrialStage`, `SubexponentialSAT_SqrtLogSpace_HeadSpecializationProgram`, `SubexponentialSAT_SqrtLogSpace_HeadSumBudgets`, `SubexponentialSAT_SqrtLogSpace_HighBranchSpace`, `SubexponentialSAT_SqrtLogSpace_HighCountInit`, `SubexponentialSAT_SqrtLogSpace_HighCountSeed`, `SubexponentialSAT_SqrtLogSpace_HighMarkedCleanup`, `SubexponentialSAT_SqrtLogSpace_HighQueryAdapter`, `SubexponentialSAT_SqrtLogSpace_NativeFrontend`, `SubexponentialSAT_SqrtLogSpace_NativeLeaf`, `SubexponentialSAT_SqrtLogSpace_NativeLeafDispatch`, `SubexponentialSAT_SqrtLogSpace_NativeLeafExecution`, `SubexponentialSAT_SqrtLogSpace_NativeProgram`, `SubexponentialSAT_SqrtLogSpace_NativeSetupSpace`, `SubexponentialSAT_SqrtLogSpace_NativeTerminal`, `SubexponentialSAT_SqrtLogSpace_PairNativeSetup`, `SubexponentialSAT_SqrtLogSpace_QueryEvaluation`, `SubexponentialSAT_SqrtLogSpace_QueryHeadBudgets`, `SubexponentialSAT_SqrtLogSpace_QueryVisitorBudgets`, `SubexponentialSAT_SqrtLogSpace_ReconstructionNative`, `SubexponentialSAT_SqrtLogSpace_RingNodeSetup`, `SubexponentialSAT_SqrtLogSpace_ScheduleProgram`, `SubexponentialSAT_SqrtLogSpace_SignatureTupleProgram`, `SubexponentialSAT_SqrtLogSpace_StreamedQueryMeasuredCost`, `SubexponentialSAT_SqrtLogSpace_TupleRunBudgets`, `SubexponentialSAT_SqrtLog_PolynomialExecutorProgramFlatten`, `SubexponentialSAT_SubexpCeilingProgram`, `SubexponentialSAT_SubexpChunkRecordMap`, `SubexponentialSAT_SubexpConvolutionPair`, `SubexponentialSAT_SubexpFactorCountSetup`, `SubexponentialSAT_SubexpKernelControl`, `SubexponentialSAT_SubexpLiteralChunkProgram`, `SubexponentialSAT_SubexpNodeIndexProgram`, `SubexponentialSAT_SubexpNormalizationPrefixProgram`, `SubexponentialSAT_SubexpNormalizationProgram`, `SubexponentialSAT_SubexpRowPostfixContext`, `SubexponentialSAT_SubexpRowPostfixInterpreter`, `SubexponentialSAT_SubexpScopeCountSetup`, `SubexponentialSAT_SubexpTautologyFilterProgram`, `SubexponentialSAT_Subexp_ConstraintEntryCompare`, `SubexponentialSAT_Subexp_GlobalBasisEntryCore`, `SubexponentialSAT_Subexp_GlobalBasisMetadata`.
--
--   **Imports.** It imports the published bundle `Def_SubexponentialSAT`; the bundles `OAIQ081S066`, `OAIQ081S067`, `OAIQ081S069`, `OAIQ081S071`, `OAIQ081S073`, `OAIQ081S075`, `OAIQ081S076`, `OAIQ081S077`, `OAIQ081S079`, `OAIQ081S080` and `OAIQ081S081` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ081S109` and `OAIQ081S115`; the statements `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.SparseDFSRefinement.accumulate_after_leaf`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.SparseDFSRefinement.popCurrent_boundary`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeLeafExecution.call_export_execution`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeTerminal.power_bounded`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.Native.loadLeaf_input_bound`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.HashScopeProgram.Single.program_runsIn`, `OAI.Algorithms.SubexponentialSAT.SubexpNormalizationProgram.prefixCall_eval`, `OAI.Algorithms.SubexponentialSAT.SubexpRowPostfixInterpreter.global_complete_runsIn`, `OAI.Algorithms.SubexponentialSAT.SubexpScopeProducer.command_eval` and `OAI.Algorithms.SubexponentialSAT.SubexpTautologyFilterProgram.filter_eval`; the proofs of `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.SparseDFSRefinement.accumulate_after_leaf`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.SparseDFSRefinement.popCurrent_boundary`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighQueryCorrect.accepted`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighQueryCorrect.marked`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighQueryCount.run`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeHashQueries.accepted_replay`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeHashQueries.marked_replay`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeLeafExecution.call_export_execution`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeQueryTimeBounds.physicalCap_polynomial`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeTerminal.power_bounded`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.Native.loadLeaf_input_bound`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.DensePolynomialProgram.Pair.command_run`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.HashScopeProgram.Marked.optional_eval`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.HashScopeProgram.RawTable.call_eval`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.HashScopeProgram.Single.program_runsIn`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.HighIncidenceProgram.Prepare.cutoff_eval`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutOwnerFiberProgram.callback_eval`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgram.EntryBankFrame.lookup_lifted`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgram.TypeCompare.command_eval`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutSourcePlanLookup.Scan.command_eval_found`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafOuterProgram.clauseCount_eval`, `OAI.Algorithms.SubexponentialSAT.SubexpNormalizationProgram.prefixCall_eval`, `OAI.Algorithms.SubexponentialSAT.SubexpRowPostfixInterpreter.global_complete_runsIn`, `OAI.Algorithms.SubexponentialSAT.SubexpScopeProducer.command_eval` and `OAI.Algorithms.SubexponentialSAT.SubexpTautologyFilterProgram.filter_eval`.
-- source:
--   OpenAI, The Exponential Time Hypothesis is False, OpenAI Math Release, October 25, 2026, https://github.com/openai/math (result family 378; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/The-Exponential-Time-Hypothesis-is-False-October-25-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Algorithms at commit 7ef5c0c

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_SubexponentialSAT
import Definitions.Def_OAIQ081S066
import Definitions.Def_OAIQ081S067
import Definitions.Def_OAIQ081S069
import Definitions.Def_OAIQ081S071
import Definitions.Def_OAIQ081S073
import Definitions.Def_OAIQ081S075
import Definitions.Def_OAIQ081S076
import Definitions.Def_OAIQ081S077
import Definitions.Def_OAIQ081S079
import Definitions.Def_OAIQ081S080
import Definitions.Def_OAIQ081S081

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

/-- The shadow state retains only visible inputs. Its storage bound does not
contain the size of the hidden collector or incumbent. -/
theorem shadow_stack_bound (H : Fin s → Prop) [DecidablePred H]
    (a : State r s) (bound : ℕ)
    (ha : ∀ i, ¬ H i → (a.stacks i).length ≤ bound) :
    ∀ i, ((rebaseState H (fun _ => []) a).stacks i).length ≤ bound := by
  intro i
  by_cases hi : H i
  · simp [rebaseState, rebaseStacks, hi]
  · simpa only [rebaseState, rebaseStacks_of_not_mem H (fun _ => []) a.stacks i hi]
      using ha i hi

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.CommandStackTransport
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_DisjointReuse_CanonicalWordProgram
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! Canonical unsigned binary output by a fixed finite word program.
The program reverses its input, removes high zeroes, reverses back, and emits
one false bit in the empty case. All source stack prefixes have a linear local
bound. No algebraic construction is imported to implement normalization. -/

namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.CanonicalWordProgram

open BitProgram StructuredCalls CounterPrograms

abbrev Data := StructuredProgram.State 3 3

def state (regs : Fin 3 → Bool) (input output : List Bool) : Data :=
  ⟨regs, ![input, output, []]⟩

def reset : Cmd 3 3 := .base
  (.seq (.atom (.set 0 false)) (.seq (.atom (.set 1 false)) (.atom (.set 2 false))))

def test : Cmd 3 3 := .base
  (.seq (.atom (.peek 1 0 1))
    (.seq (.atom (.bnot 2 0)) (.atom (.band 2 2 1))))

def tested (xs : List Bool) : Data :=
  state (counterRegs (xs.headD false) (!xs.isEmpty) ((!xs.headD false) && !xs.isEmpty)) [] xs

def dropBody : Cmd 3 3 := .seq (.base (.atom (.pop 1 0 1))) test

def dropLoop : Cmd 3 3 := .while 2 dropBody

def transferred (d : Data) (src dst : Fin 3) : Data :=
  ⟨readRegs d.regs 0 1 none, StackRoutines.transferStacks src dst d.stacks⟩

def emitZero : Cmd 3 3 := .seq
  (.base (.seq (.atom (.set 0 false)) (.atom (.push 0 0)))) reset

def finish : Cmd 3 3 := .seq (.base (.atom (.peek 0 0 1))) (.ite 1 reset emitZero)

/-- A single fixed finite control table, independent of input length/value. -/
def normalizeUnsigned : Cmd 3 3 :=
  .seq (.call (StackRoutines.transferProgram 0 1 0 1))
    (.seq test (.seq dropLoop (.seq (.call (StackRoutines.transferProgram 1 0 0 1)) finish)))

def normalizeUnsignedProgram : Program 3 3 (StructuredCalls.size normalizeUnsigned + 1) :=
  StructuredCalls.compiled normalizeUnsigned 0 0

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.CanonicalWordProgram
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_DisjointReuse_SparseAccumulatorProgram
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! A fixed finite binary accumulator with actual source traces and local prefixSteps bounds. -/

namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.SparseCountProgram.Accumulator

open BitProgram StructuredCalls

def state (regs : Fin 8 → Bool) (left right : List Bool) : StructuredProgram.State 8 3 :=
  ⟨regs, BinaryPrograms.Add.stackState left right []⟩

/-- One fixed bit program adds and immediately canonicalizes the accumulator.
The output occupies stack zero; both temporary stacks are empty at return. -/
def command : Cmd 8 3 :=
  .seq (.base (.atom (.set 0 false)))
    (.seq (.call BinaryPrograms.Add.littleEndianProgram)
      (.call (ProgramLinking.liftProgram CanonicalWordProgram.normalizeUnsignedProgram
        registers id)))

def program : Program 8 3 (StructuredCalls.size command + 1) :=
  StructuredCalls.compiled command 0 0

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.SparseCountProgram.Accumulator
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_DisjointReuse_SparseFrontierProgram
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! Concrete LIFO storage for normalized formula bodies.

Stack zero is the current body, stack two is the framed pending list, and stack
three is scratch. Stack one is preserved and may hold the declared variable
count. The list's final false bit is retained; emptiness is tested by peeking,
so an empty frontier never causes an unguarded removal of a sentinel.
-/

namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.SparseFrontierProgram

open BitProgram StructuredCalls SubexpPostfixControl

abbrev state := SubexpNormalizeProgram.filterState

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.SparseFrontierProgram
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_DisjointReuse_SparsePriorityPrimitives
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! Concrete record-count and emission primitives extracted from supplied sources.
No sparsification schedule or formula evaluator is imported. Provenance is recorded
in verification/counting-draft/worker04/extraction.json. -/

namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.SparsePriorityPrimitives

open BitProgram StructuredCalls BinaryArithmetic

namespace Tuple
abbrev Data := State 13 9

def copied (src dst : Fin 9) (d : Data) : Data :=
  ⟨readRegs d.regs 0 1 none, StackRoutines.copyStacks src dst d.stacks⟩

def cleared (port : Fin 9) (d : Data) : Data :=
  ⟨readRegs d.regs 0 1 none, StackRoutines.clearStacks port d.stacks⟩

end Tuple

namespace Count

open OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.SparsePriorityPrimitives.Tuple
  (Data copied copy cleared clear )

def counted (records : List (List Bool)) (d : Data) : Data :=
  ⟨readRegs d.regs 0 1 none,
    Function.update (Function.update d.stacks 5 []) 7 (Encoding.encodeNat records.length)⟩

def resetState (d : Data) : Data :=
  ⟨Function.update (Function.update (Function.update d.regs 0 false) 1 false) 2 false, d.stacks⟩

end Count

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.SparsePriorityPrimitives
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

namespace Guard

/-- Only input-sized words are copied: the clause, its width, and the core. -/
def copyClause : Cmd 13 11 := .call (StackRoutines.copyProgram 9 5 0 0 1)

def width : Cmd 13 11 :=
  liftCommand (SparsePriorityPrimitives.Count.countTest 0) 5 5 id widthStack

end Guard

namespace Filter

def state (regs : Regs) (core width source output payload clause : List Bool) : Data :=
  ⟨regs, ![[], [], [], [], [], [], [], [], core, clause, width, source, output, payload]⟩

def transfer (source target : Fin 14) : Cmd 16 14 :=
  .call (StackRoutines.transferProgram source target 0 1)

def emit : Cmd 16 14 := .call
  (ProgramLinking.liftProgram SparsePriorityPrimitives.Filter.emitIfSelectedProgram emitReg emitStack)

structure Ready (H : Clause) (width : List Bool) (d : Data) : Prop where
  shape : ∃ regs source output payload,
    d = state regs (clauseCode H) width source output payload []

def keep (H : Clause) (width bits : List Bool) : Bool :=
  match decodeClause bits with
  | some C => decide (C.length = BinaryArithmetic.toNat width) && ExecCNF.subset H C
  | none => false

@[simp] theorem keep_clauseCode (H C : Clause) (width : List Bool) :
    keep H width (clauseCode C) =
      (decide (C.length = BinaryArithmetic.toNat width) && ExecCNF.subset H C) := by
  simp [keep]

def records (F : Formula) : List (List Bool) := F.map clauseCode


def startOutput : Cmd 16 14 :=
  .seq (.base (.atom (.set 0 false))) (.base (.atom (.push 12 0)))


end Filter

namespace CountThreshold

abbrev Data := SparsePriorityPrimitives.Tuple.Data

def command : Cmd 13 9 :=
  .seq (.call SparsePriorityPrimitives.Count.countProgram)
    (.seq SparsePriorityPrimitives.Count.toBinary
      (.seq (SparsePriorityPrimitives.Count.less 6 4)
        (.seq (.base (.atom (.bnot 4 0))) (SparsePriorityPrimitives.Tuple.clear 6))))

end CountThreshold

namespace Mask

def applyMask : Cmd 8 4 := liftCommand (.call CoreMaskProgram.program) 0 3 regPort id

def command (mask : List Bool) : Cmd 8 4 :=
  .seq (ArithmeticExpressionSupport.pushWord 1 mask)
    (.seq applyMask (ArithmeticExpressionSupport.clearCmd 1))

end Mask

namespace Selector

/-- The primitive word operations use one fixed empty copy buffer. -/
def copy (source target : Fin 24) : Code :=
  .call (StackRoutines.copyProgram source target 8 0 1)

def transfer (source target : Fin 24) : Code :=
  .call (StackRoutines.transferProgram source target 0 1)

def move (source target : Fin 24) : Code := .seq (transfer source 8) (transfer 8 target)

def clear (port : Fin 24) : Code := .call (StackRoutines.clearProgram port 0 1)

def load (port : Fin 24) (word : List Bool) : Code :=
  liftCommand (ArithmeticExpressionSupport.pushWord port word) port port (Fin.castAdd 16) id

def maskCall (mask : List Bool) : Code :=
  liftCommand (Mask.command mask) 0 3 (Fin.castAdd 16) maskStack

def sizeCall : Code :=
  liftCommand (SparsePriorityPrimitives.Count.countTest 0) 5 5 (Fin.castAdd 11) sizeStack

def thresholdCall : Code :=
  liftCommand CountThreshold.command 5 5 (Fin.castAdd 11) thresholdStack

/-- A failed candidate leaves both output ports empty; a successful one retains
its core and selected family. The surrounding parser owns ports 14 and 15. -/
def prepareCandidate (mask : List Bool) : Code :=
  .seq (transfer 15 10) (.seq (maskCall mask) (.seq (copy 9 5) sizeCall))

def prepareCandidateBound (C : Clause) (mask size : List Bool) : ℕ :=
  3 * (Filter.clauseCode C).length + 3 +
    (CoreMaskProgram.runtimeBound C + 4 * mask.length + 5) +
    (7 * (Filter.clauseCode (masked mask C)).length + 5) +
    (200 * ((Filter.clauseCode (masked mask C)).length + size.length + 1) ^ 2 + 1)

def selectedFamily (F : Formula) (H : Clause) (width : List Bool) : Formula :=
  (Filter.result F H width).reverse

def checkCandidateBound (F : Formula) (H : Clause) (width threshold : List Bool) : ℕ :=
  7 * (Filter.formulaCode F).length + 5 +
    (600 * ((Filter.clauseCode H).length + (Filter.formulaCode F).length + width.length + 1) ^ 3 + 3) +
    (7 * (Filter.formulaCode (selectedFamily F H width)).length + 5) +
    (300 * ((Filter.formulaCode (selectedFamily F H width)).length + threshold.length + 1) ^ 2 + 1)

def accepted (F : Formula) (C : Clause) (mask width size threshold : List Bool) : Bool :=
  decide ((masked mask C).length = BinaryArithmetic.toNat size) &&
    decide (BinaryArithmetic.toNat threshold ≤ (Filter.result F (masked mask C) width).length)

def candidateBound (F : Formula) (C : Clause) (mask width size threshold : List Bool) : ℕ :=
  prepareCandidateBound C mask size + checkCandidateBound F (masked mask C) width threshold +
    4 * (Filter.clauseCode (masked mask C)).length +
    2 * (Filter.formulaCode (selectedFamily F (masked mask C) width)).length + 20


/-- All three parameters are encoded in finite control before the input is supplied. -/
def widthFamily (F : Formula) (width : List Bool) : Formula :=
  (Filter.result F [] width).reverse

def familyInitBound (F : Formula) (width : List Bool) : ℕ :=
  3 + (2 * width.length + 1) + (7 * (Filter.formulaCode F).length + 5) +
    (600 * ((Filter.formulaCode F).length + width.length + 2) ^ 3 + 3) +
    5 + (6 * (Filter.formulaCode (widthFamily F width)).length + 6)

def clearMany : List (Fin 24) → Code
  | [] => .base .skip
  | port :: rest => .seq (clear port) (clearMany rest)

def cleanup : Code := clearMany [14, 18, 16, 20, 17]


def scanTest (F : Formula) (mask width size threshold bits : List Bool) : Bool :=
  match Filter.decodeClause bits with
  | some C => accepted F C mask width size threshold
  | none => false

def scanCost (F : Formula) (mask width size threshold bits : List Bool) : ℕ :=
  match Filter.decodeClause bits with
  | some C => candidateBound F C mask width size threshold
  | none => 0

def phaseVolume (F : Formula) (base : List Bool) (c h : ℕ) (mask : List Bool) : ℕ :=
  2 * (Filter.formulaCode (widthFamily F c.bits)).length + mask.length + c.bits.length +
    h.bits.length + (1 + (c - h) * base.length) + 1

def phaseBound (F : Formula) (base : List Bool) (c h : ℕ) (mask : List Bool) : ℕ :=
  familyInitBound F c.bits +
    parameterInitBound (c - h) h.bits base (Filter.formulaCode (widthFamily F c.bits)) +
    3000 * phaseVolume F base c h mask ^ 4 + 5 * (2 * phaseVolume F base c h mask + 3)

def passCandidate (F : Formula) (M : ℕ) (p : ℕ × ℕ × List Bool) (C : Clause) : Bool :=
  decide ((masked p.2.2 C).length = p.2.1) &&
    decide (M ^ (p.1 - p.2.1) ≤ (selectedRaw F p.1 (masked p.2.2 C)).length)

def passFound (F : Formula) (M : ℕ) (p : ℕ × ℕ × List Bool) : Bool :=
  (widthFamily F p.1.bits).any (passCandidate F M p)

def chainBudget (F : Formula) (base : List Bool) (ps : List (ℕ × ℕ × List Bool)) : ℕ :=
  (ps.map fun p => phaseBound F base p.1 p.2.1 p.2.2).sum + 2 * ps.length

end Selector

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.SparsePriorityProgram
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SubexpTautologyFilterProgram
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# Actual tautological-clause filtering

The outer record loop runs the checked clause-tautology machine on each clause,
emits exactly the clauses that it rejects as tautologies, and restores their
original list order. The Boolean predicates below specify this concrete code;
they are not instructions available to the machine.
-/

namespace SubexponentialSAT.SubexpTautologyFilterProgram

open BitProgram StructuredCalls

def emitProgram := ProgramLinking.liftProgram
  SubexpNormalizeProgram.emitIfSelectedProgram emitRegister emitStack

abbrev emitCall : Cmd 13 11 := .call emitProgram

abbrev callback : Cmd 13 11 :=
  .seq (transfer 1 3) (.seq coreCall (.seq (transfer 5 1)
    (.seq (clear 4) (.seq (RecordPrograms.atom (.bnot 12 9)) emitCall))))

abbrev scan : Cmd 13 11 := RecordPrograms.iterate ports callback

def reverseProgram := ProgramLinking.liftProgram
  SubexpNormalizeProgram.reverseRecordsProgram emitRegister reverseStack

abbrev reverseCall : Cmd 13 11 := .call reverseProgram

abbrev filter : Cmd 13 11 := .seq (pushFalse 2) (.seq scan (.seq (pushFalse 0) reverseCall))

end SubexponentialSAT.SubexpTautologyFilterProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SubexpNormalizationPrefixProgram
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!+# Actual literal cleanup followed by tautology removal

This is a fixed program on the original declared variable universe. Its two
stages use the same input/output port and restore empty work stacks. The exact
list order and the length bound are retained for subsequent clause absorption.
-/

namespace SubexponentialSAT.SubexpNormalizationPrefixProgram

open BitProgram StructuredCalls

abbrev command : Cmd 13 11 :=
  .seq ExecCleanLiteralsProgram.clean SubexpTautologyFilterProgram.filter

def program := compiled command 0 0

end SubexponentialSAT.SubexpNormalizationPrefixProgram

end OAI.Algorithms
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

def prefixProgram := ProgramLinking.liftProgram
  SubexpNormalizationPrefixProgram.program prefixRegister prefixStack

abbrev prefixCall : Cmd 15 16 := .call prefixProgram

end SubexponentialSAT.SubexpNormalizationProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_DisjointReuse_NegatedCoreProgram
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! Concrete negated singleton generation for the disjoint B child.
The fixed routine consumes a unary literal-record list on stack 0 and prepends
its negated singleton clauses to the encoded formula on stack 2. -/

namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.NegatedCoreProgram

open BitProgram StructuredCalls

def callback : Cmd 10 8 := .seq copyQuery (.seq (ExecCNFSubset.clear 1)
  (.seq SubexpTautologyProgram.negateQuery (.seq (ExecCNFSubset.clear 7)
    (.seq seed (.seq innerEmit (.seq transferClause (.seq select
      ExecLiteralDedupProgram.emitCall)))))))

def command : Cmd 10 8 := RecordPrograms.iterate ports callback
def program := compiled command 0 2

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.NegatedCoreProgram
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

def prepareB : Cmd 15 16 := .seq copyCore
  (.call (ProgramLinking.liftProgram NegatedCoreProgram.program unitRegister unitStack))

open ExecBranchControllerSupport

def inputFront (pending header : List Bool) (F S : List (List ℕ)) (H : List ℕ) : Front :=
  ![pending, header, [], [], ExecCoreChildProgram.formulaCode F,
    ExecCoreChildProgram.clauseCode H, ExecCoreChildProgram.formulaCode S]

def outputFront (pending header childA childB : List Bool) : Front :=
  ![pending, header, ExecWorklistProgram.record childA,
    ExecWorklistProgram.record childB, [], [], []]

def inputState (regs : Regs) (pending header : List Bool)
    (F S : List (List ℕ)) (H : List ℕ) : Data :=
  idle regs (inputFront pending header F S H)

def outputState (pending header : List Bool) (F S : List (List ℕ)) (H : List ℕ) : Data :=
  idle (fun _ => false) (outputFront pending header
    (ExecCoreChildProgram.formulaCode (ExecCoreChildProgram.result F S H))
    (ExecCoreChildProgram.formulaCode (resultB SubexpFrontend.negateCode F S H)))

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

abbrev Data := State 80 1220
abbrev Code := Cmd 80 1220

def startFrontier : Code :=
  .call (ProgramLinking.liftProgram SparseFrontierProgram.initFrontierProgram
    (registers 3 (by decide)) frontierStack)

def popCurrent : Code :=
  .call (ProgramLinking.liftProgram SparseFrontierProgram.popIfPresentProgram
    (registers 3 (by decide)) frontierStack)

def pushChildren : Code :=
  .call (ProgramLinking.liftProgram SparseFrontierProgram.pushPairProgram
    (registers 4 (by decide)) pairStack)

def accumulate : Code :=
  .call (ProgramLinking.liftProgram SparseCountProgram.Accumulator.program
    (registers 8 (by decide)) countStack)

def clearPort (port : Fin 1220) : Code :=
  .call (StackRoutines.clearProgram port 0 1)

/-- The finite list is part of the instruction table, never a stored work list. -/
def clearPorts : List (Fin 1220) → Code
  | [] => .base .skip
  | port :: rest => .seq (clearPort port) (clearPorts rest)

def clearLow : Code := clearPorts lowPorts

/-- Every iteration re-reads the physical pending tag after all callbacks. -/
def testPending : Code := .base (.atom (.peek 257 2 1))

/-- The total stack is empty on entry and becomes canonical binary zero. -/
def startTotal : Code :=
  .base (.seq (.atom (.set 0 false)) (.atom (.push 260 0)))

/-- Explicitly discard the current body and every low workspace port before
retesting the frontier. No callback cleanup or register persistence is implicit. -/
def finishVisit : Code :=
  .seq (clearPort 265) (.seq clearLow testPending)

/-- Physically clear the external word and copy scratch before preserving bit
order in the final canonical output. Retained raw input is charged here. -/
def exportCount : Code :=
  .seq (clearPort 0) (.seq (clearPort 256)
    (.call (StackRoutines.copyProgram 260 256 0 0 1)))


end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.SparseDFSProgram
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_CountDFS
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! Typed refinement of the concrete streaming frontier.

Depths and derivation trees below are proof indices. The physical pending tape
contains only formula bodies, and every formula keeps the same declared `Fin n`.
The selector and leaf execution contracts must still be supplied by their actual
finite programs; this module does not postulate a final counting service.
-/

namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.SparseDFSRefinement

open SAT SparsePriorityProgram BitProgram StructuredCalls

variable {n : ℕ}

/-- The loop boundary charges original input and parameter words separately.
Only the invariant ports needed by the count/frontier refinement appear here. -/
structure Boundary (M : List Bool) (s : Frontier n) (d : SparseDFSProgram.Data) : Prop where
  pending : d.stacks 257 = pendingBytes s.pending
  header : d.stacks 258 = Encoding.encodeNat n
  threshold : d.stacks 259 = M
  total : d.stacks 260 = binaryNat s.total
  left_empty : d.stacks 261 = []
  right_empty : d.stacks 262 = []
  leaf_empty : d.stacks 263 = []
  current_empty : d.stacks 265 = []
  low_empty : ∀ i : Fin 1220, i.val < 256 → d.stacks i = []
  continue_flag : d.regs 2 = !s.pending.isEmpty


/-- Persistent words after a concrete branch or count addition. Scratch and
current-formula cleanup is performed by the real finishVisit command. -/
structure AfterVisit (threshold : List Bool) (s : Frontier n)
    (d : SparseDFSProgram.Data) : Prop where
  pending : d.stacks 257 = pendingBytes s.pending
  header : d.stacks 258 = Encoding.encodeNat n
  threshold_word : d.stacks 259 = threshold
  total : d.stacks 260 = binaryNat s.total
  left_empty : d.stacks 261 = []
  right_empty : d.stacks 262 = []
  leaf_empty : d.stacks 263 = []

open SparseDFSProgram

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.SparseDFSRefinement
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_DifferencePairsRelational
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! Relational accumulator correctness for the existing four-stack pair DFS.
Only the proof invariant is generalized: the actual commands, branch order,
callback states and all-prefix space theorem are unchanged. -/
namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DifferencePairsRelational

open BitProgram StructuredCalls DifferencePairsProgram
open StructuredProgram (Atom)

variable {r s : ℕ} {α : Type*}

/-- The callback returns an actual dictionary representing the next semantic
value. No uniform choice of dictionary bytes is required. -/
structure CallbackSpec (p : Ports r s) (callback : Cmd r s)
    (visit : List (Option Bool) → α → α) (C N : ℕ)
    (I : α → State r s → Prop) : Prop where
  stable : ∀ value d e,
    (∀ o, (∀ i, o ≠ p.stack i) → e.stacks o = d.stacks o) → I value d → I value e
  run : ∀ J pre value d, pre.length = N → Cursor p 0 (J+1) pre true d → I value d →
    ∃ t e, t ≤ C ∧ Eval callback t (popped p 0 2 d) e ∧
      (∀ i, e.stacks (p.stack i) = d.stacks (p.stack i)) ∧ I (visit pre value) e

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DifferencePairsRelational
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_DisjointReuse_BinaryClogProgram
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! Actual floor and ceiling logarithm bit programs, without packing or schedule imports. -/

namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.BinaryClogProgram

open BitProgram StructuredCalls
open CounterPrograms (value ripple)

def decrement : Cmd 3 3 :=
  .call (ProgramLinking.liftProgram (CounterPrograms.rippleProgram false)
    id Setup.incrementPorts)

def zeroPorts : CounterForPrograms.Ports 3 3 where
  register := Function.Embedding.refl _
  counter := 0
  scratch := 1
  counter_ne_scratch := by decide

def reset : Cmd 3 3 := .base (Floor.atoms
  [.set 0 false, .set 1 false, .set 2 false])


end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.BinaryClogProgram
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_DisjointReuse_DFSStartup
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! Concrete startup for the shared 80-register, 1220-stack DFS ABI.
The input frame already contains the normalized body and actual parameter words.
This module proves only startup; it does not assume or claim a completed DFS run.
-/

namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.DFSStartup

open BitProgram StructuredCalls SparseDFSProgram SparseDFSRefinement

variable {n : ℕ}

structure Prepared (M : List Bool) (F : RawCNF n) (d : Data) : Prop where
  pending : d.stacks 257 = []
  header : d.stacks 258 = Encoding.encodeNat n
  threshold : d.stacks 259 = M
  total : d.stacks 260 = []
  left_empty : d.stacks 261 = []
  right_empty : d.stacks 262 = []
  leaf_empty : d.stacks 263 = []
  current : d.stacks 265 = SparseCountProgram.encodeBody F
  low_empty : ∀ i : Fin 1220, i.val < 256 → d.stacks i = []

def startup : Code := .seq startFrontier (.seq startTotal testPending)

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.DFSStartup
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_DisjointReuse_DFSVisit
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FiniteFallback.literalFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! One complete native DFS visit. The leaf callback below is an intermediate
implementation contract for a fixed finite command, not a final theorem premise.
The actual streamed leaf program must instantiate it at integration.
-/
namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.DFSVisit

open BitProgram StructuredCalls SparseDFSProgram SparseDFSRefinement

structure BoundedEval (command : Code) (steps : ℕ) (a b : Data) (bound : ℕ) : Prop where
  eval : Eval command steps a b
  space : ∀ prefixSteps c, prefixSteps ≤ steps →
    Trace (compiled command 256 256) prefixSteps
      (a.withPC (some (compiled command 256 256).entry)) c →
    ∀ i, (c.stacks i).length ≤ bound

variable {n : ℕ}

structure LeafReady (k : ℕ) (threshold : List Bool) (parameterBound : ℕ)
    (F : RawCNF n) (d : Data) : Prop where
  current : d.stacks 265 = SparseCountProgram.encodeBody F
  dimension : BinaryArithmetic.toNat (d.stacks 264) = 4 * BinaryArithmetic.toNat threshold ^ (k - 1)
  ambient : BinaryArithmetic.toNat (d.stacks 267) = n
  occurrence_length : (d.stacks 264).length ≤ parameterBound
  dimension_length : (d.stacks 267).length ≤ n + 1
  header : d.stacks 258 = Encoding.encodeNat n
  threshold : d.stacks 259 = threshold
  left_empty : d.stacks 261 = []
  right_empty : d.stacks 262 = []
  leaf_empty : d.stacks 263 = []
  low_empty : ∀ i : Fin 1220, i.val < 256 → d.stacks i = []

structure LeafDone (F : RawCNF n) (d e : Data) : Prop where
  count : e.stacks 263 = binaryNat (rawCount F)
  scratch : e.stacks 30 = []
  persistent : ∀ i, i ∈ ([256, 257, 258, 259, 260, 261, 262, 264, 266, 267] : List (Fin 1220)) →
    e.stacks i = d.stacks i

/-- The bound is uniform over all actual leaf inputs; time is separate. -/
structure LeafContract (k : ℕ) (threshold : List Bool) (parameterBound : ℕ)
    (leaf : Code) (time space : ℕ) : Prop where
  execution : ∀ (F : RawCNF n) (d : Data), Valid k F → LeafReady k threshold parameterBound F d →
    SparsePriority.select (ExecCNF.formulaSet F) (BinaryArithmetic.toNat threshold) = none →
    (∀ i, (d.stacks i).length ≤ space) →
    ∃ t ≤ time, ∃ e, BoundedEval leaf t d e space ∧ LeafDone F d e

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.DFSVisit
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

abbrev Data := StructuredProgram.State 8 32

def state (r : Regs) (w : Words) : Data :=
  ⟨r, fun i => if h : i.val < 19 then w ⟨i.val, h⟩ else []⟩

@[simp] theorem state_regs (r : Regs) (w : Words) : (state r w).regs = r := rfl

@[simp] theorem state_port (r : Regs) (w : Words) (i : Fin 19) :
    (state r w).stacks (port i) = w i := by simp [state, port]

def work (m : ℕ) (hm : m ≤ 13) : Fin m ↪ Fin 32 where
  toFun i := ⟨19 + i.val, by omega⟩
  inj' := by
    intro i j h
    apply Fin.ext
    have := congrArg Fin.val h
    dsimp at this
    omega

@[simp] theorem work_val (m : ℕ) (hm : m ≤ 13) (i : Fin m) :
    (work m hm i).val = 19 + i.val := rfl

@[simp] theorem work_ne_port (m : ℕ) (hm : m ≤ 13) (i : Fin m) (j : Fin 19) :
    work m hm i ≠ port j := by
  intro h
  have he : 19 + i.val = j.val := congrArg (fun x : Fin 32 => x.val) h
  have := j.isLt
  omega

@[simp] theorem port_ne_work (m : ℕ) (hm : m ≤ 13) (i : Fin m) (j : Fin 19) :
    port j ≠ work m hm i := (work_ne_port m hm i j).symm

@[simp] theorem work_inj {m : ℕ} (hm hm' : m ≤ 13) {i j : Fin m} :
    work m hm i = work m hm' j ↔ i = j := by
  constructor
  · intro h
    apply Fin.ext
    have hv := congrArg (fun x : Fin 32 => x.val) h
    simpa using hv
  · rintro rfl
    rfl

def arithmeticPorts (a b o : Fin 19) (hoa : o ≠ a) (hob : o ≠ b) :
    ArithmeticCalls.Ports 32 where
  left := port a
  right := port b
  out := port o
  work := work 5 (by decide)
  out_ne_left := by intro h; exact hoa ((Fin.castAdd_injective 19 13) h)
  out_ne_right := by intro h; exact hob ((Fin.castAdd_injective 19 13) h)
  work_ne_left := fun i => work_ne_port 5 (by decide) i a
  work_ne_right := fun i => work_ne_port 5 (by decide) i b
  work_ne_out := fun i => work_ne_port 5 (by decide) i o

def addCmd (a b o : Fin 19) (hoa : o ≠ a) (hob : o ≠ b) : Cmd 8 32 :=
  ArithmeticCalls.addAt (arithmeticPorts a b o hoa hob)

def multiplyCmd (a b o : Fin 19) (hoa : o ≠ a) (hob : o ≠ b) : Cmd 8 32 :=
  ArithmeticCalls.multiplyAt (arithmeticPorts a b o hoa hob)

def loadCmd (o : Fin 19) (word : List Bool) : Cmd 8 32 :=
  ArithmeticExpressionSupport.pushWord (port o) word




def copyCmd (a o : Fin 19) : Cmd 8 32 :=
  ArithmeticCalls.copyAt (port a) (port o) (work 1 (by decide) 0)


def clearCmd (a : Fin 19) : Cmd 8 32 :=
  ArithmeticExpressionSupport.clearCmd (port a)

def logStacks (a : Fin 19) : Fin 3 → Fin 32 :=
  ![port a, work 2 (by decide) 0, work 2 (by decide) 1]

/-- Reset the local logarithm program's three Boolean registers. -/
def resetLogRegisters : Cmd 8 32 :=
  .seq (.base (.atom (.set 0 false)))
    (.seq (.base (.atom (.set 1 false))) (.base (.atom (.set 2 false))))

def zeroLogRegs (r : Regs) : Regs :=
  Function.update (Function.update (Function.update r 0 false) 1 false) 2 false

def compareStacks (a b : Fin 19) : Fin 2 → Fin 32 := ![port a, port b]

/-- Consumes both selected words and returns their strict comparison in register zero. -/
def compareCmd (a b : Fin 19) : Cmd 8 32 :=
  .call (ProgramLinking.liftProgram OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.BinaryCompareProgram.Compare.program id
    (compareStacks a b))


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

def Arithmetic.command (op : Arithmetic) (a b o : Fin 19)
    (hoa : o ≠ a) (hob : o ≠ b) : Cmd 8 32 :=
  match op with
  | .add => addCmd a b o hoa hob
  | .multiply => multiplyCmd a b o hoa hob

/-- The temporary is emptied before returning; the destination may be an operand. -/
def replaceCmd (op : Arithmetic) (a b o tmp : Fin 19)
    (hta : tmp ≠ a) (htb : tmp ≠ b) : Cmd 8 32 :=
  .seq (op.command a b tmp hta htb)
    (.seq (clearCmd o) (.seq (copyCmd tmp o) (clearCmd tmp)))

/-- One Horner step for `sum (3*M)^j`, using data 12 for `3*M` and data 5 for one. -/
def hornerStep : Cmd 8 32 :=
  .seq (replaceCmd .multiply 2 12 2 3 (by decide) (by decide))
    (replaceCmd .add 2 5 2 3 (by decide) (by decide))

def horner : ℕ → Cmd 8 32
  | 0 => .base .skip
  | j + 1 => .seq (horner j) hornerStep

def prepared (k : ℕ) (s M : List Bool) : Words :=
  fun i => if i = 0 then s else if i = 1 then M else if i = 4 then (3 : ℕ).bits
    else if i = 5 then [true] else if i = 6 then (16 : ℕ).bits
    else if i = 7 then (SparseCharging.rightConstant k).bits else []

def dyadicWord : ℕ → List Bool
  | 0 => [true]
  | e + 1 => false :: dyadicWord e

@[simp] theorem dyadicWord_value (e : ℕ) : toNat (dyadicWord e) = 2 ^ e := by
  induction e with
  | zero => simp [dyadicWord, BinaryArithmetic.toNat, BinaryArithmetic.bitVal]
  | succ e ih =>
      simp [dyadicWord, BinaryArithmetic.bitVal, ih, pow_succ,
        Nat.mul_comm]

@[simp] theorem dyadicWord_length (e : ℕ) : (dyadicWord e).length = e + 1 := by
  induction e with
  | zero => rfl
  | succ e ih => simp [dyadicWord, ih]

def double : Cmd 8 32 :=
  .seq (.base (.atom (.set 0 false))) (.base (.atom (.push (port 1) 0)))

/-- These constants are part of the fixed instruction table chosen from k. -/
def initCmd (k : ℕ) : Cmd 8 32 :=
  .seq (loadCmd 1 [true]) (.seq (loadCmd 4 (3 : ℕ).bits)
    (.seq (loadCmd 5 [true]) (.seq (loadCmd 6 (16 : ℕ).bits)
      (loadCmd 7 (SparseCharging.rightConstant k).bits))))

def inputWords (s : List Bool) : Words := fun i => if i = 0 then s else []

def searchCost (k : ℕ) (s : List Bool) : ℕ :=
  let N := SparseBudget.chooseExponent k 1 (toNat s) (by decide)
  (N + 3) * (12000 * (k + 1) * candidateWidth k s (dyadicWord N) ^ 2 +
    2 * (SparseCharging.rightConstant k).bits.length + 21)

/-- Fixed-k multiplication computes the safe occurrence bound `4*M^(k-1)`. -/
def boundPowers : ℕ → Cmd 8 32
  | 0 => .base .skip
  | j + 1 => .seq (boundPowers j)
      (replaceCmd .multiply 2 1 2 3 (by decide) (by decide))

def outputWords (s M B : List Bool) : Words :=
  fun i => if i = 0 then s else if i = 1 then M else if i = 2 then B else []

def commandCost (k : ℕ) (s : List Bool) : ℕ :=
  searchCost k s + 600 * k *
    (5 + k * (SparseBudget.chooseExponent k 1 (toNat s) (by decide) + 2)) ^ 2 +
      2 * (SparseCharging.rightConstant k).bits.length + 50

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.SparseBudgetProgram
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

abbrev Data := State 5 7

def state (regs : Fin 5 → Bool)
    (query master source payload work tmp count : List Bool) : Data :=
  ⟨regs, store query master source payload work tmp count⟩

def cleared (d : Data) (src : Fin 7) : Data :=
  ⟨readRegs d.regs 0 1 none, Function.update d.stacks src []⟩

def invariant (query master : List Bool) (d : Data) : Prop :=
  ∃ regs count, d = state regs query master [] [] [] [] count

def effect (query key : List Bool) (a b : Data) : Prop :=
  b.stacks 6 = if key = query then a.stacks 6 else true :: a.stacks 6

end Internal

end SubexponentialSAT.SubexpNodeIndexProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_Subexp_GlobalBasisMetadata
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# Physical packing metadata lookup

The raw packing table and query remain on stacks 0 and 1. A successful lookup
returns either a block/type pair on 2/3, or a leftover rank on 4. Register 4
distinguishes those cases; all other registers and stacks 5 through 11 are
cleared. Keys, indices, and type encodings are runtime words.
-/

namespace SubexponentialSAT.Subexp.GlobalBasisMetadata

open BitProgram StructuredCalls SubexpScanPrimitives


abbrev Data := State 5 12

def work (regs : Regs) (master query source payload saved : List Bool) : Data :=
  ⟨regs, ![master, query, [], [], [], source, payload, saved, [], [], [], []]⟩

def inputState (regs : Regs) (master query : List Bool) : Data :=
  work regs master query [] [] []

def outputState (master query : List Bool) (m : Metadata) : Data :=
  ⟨![false, false, false, false, m.coveredFlag],
    ![master, query, m.block, m.typeCode, m.rank, [], [], [], [], [], [], []]⟩

def cleared (src : Fin 12) (d : Data) : Data :=
  ⟨reset d.regs, Function.update d.stacks src []⟩

def framed (d : Data) (src dst : Fin 12) (bits rest : List Bool) : Data :=
  ⟨readRegs d.regs 0 1 (some false),
    Function.update (Function.update d.stacks src rest) dst (bits.reverse ++ d.stacks dst)⟩

def headed (d : Data) : Data :=
  (StructuredProgram.Atom.pop (5 : Fin 12) (4 : Fin 5) 0).eval d

end SubexponentialSAT.Subexp.GlobalBasisMetadata

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

def lowState (d : Data) : State 16 128 := ⟨d.regs, d.stacks ∘ lowPort⟩

end SubexponentialSAT.SubexpConvolutionPair

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SubexpRowPostfixInterpreter
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! The source-row postfix interpreter on the fixed 256-stack workspace.
Only port names change; the checked dispatcher and all service transitions
are retained. Parameters such as R and the field remain encoded data. -/

namespace SubexponentialSAT.SubexpRowPostfixInterpreter

open BitProgram
open SubexpPostfixControl (serializeCode operandDepth)
open SubexpPostfixInterpreter (cfg)
open SubexpPostfixGlobal (reindexCfg )
open SubexpProjectedInterpreter (exprCost LoadImplements ImplementsOn Validity)

/-- Arithmetic tables act only on values reachable after projection. -/
abbrev ImplementsOnGlobal {R : Type*} {l : ℕ} (valid : R → Prop) (encode : R → List Bool)
    (operation : R → R → R) (isMul : Bool)
    (service : Program 16 256 l) (bound : R → R → ℕ)
    (context : Fin 252 → List Bool) : Prop :=
  ∀ (x y : R), valid x → valid y → ∀ (xs : List R) (code depth : List Bool),
    RunsIn service (bound x y)
      (physicalCfg (some service.entry) true true isMul code depth
        (Encoding.encodeList encode (y :: x :: xs)) context)
      (physicalCfg none false false false code depth
        (Encoding.encodeList encode (operation x y :: xs)) context)

/-- The actual unary service acts on the newly pushed raw operand. -/
abbrev LoadImplementsGlobal {R : Type*} {l : ℕ} (encode : R → List Bool)
    (project : R → R) (service : Program 16 256 l) (bound : R → ℕ)
    (context : Fin 252 → List Bool) : Prop :=
  ∀ (x : R) (xs : List R) (code depth : List Bool) (op : Bool),
    RunsIn service (bound x)
      (physicalCfg (some service.entry) true false op code depth
        (Encoding.encodeList encode (x :: xs)) context)
      (physicalCfg none false false false code depth
        (Encoding.encodeList encode (project x :: xs)) context)


end SubexponentialSAT.SubexpRowPostfixInterpreter

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SubexpRowPostfixContext
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Stored arithmetic data for the row interpreter. Readiness is stated on
the fixed context alone, and proved invariant when source, operand, and
temporary argument ports change. No arithmetic trace is assumed here. -/

namespace SubexponentialSAT.SubexpRowPostfixContext

open BitProgram StructuredCalls
open SubexpLiftRing SubexpQuarticRing
open SubexpConvolutionControl (Store bufferPorts)
open SubexpRowPostfixInterpreter (physicalCfg )

def operandStore (context : Fin 252 → List Bool) (code depth operands : List Bool) : Store :=
  (physicalCfg (l := 1) none false false false code depth operands context).stacks

def preparedStore (context : Fin 252 → List Bool)
    (code depth operands left right tail : List Bool) : Store :=
  SubexpRowPostfixServices.prepared (operandStore context code depth operands) left right tail

end SubexponentialSAT.SubexpRowPostfixContext

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_PolynomialExecutorProgramFlatten
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Generic native extraction adapter for a completed postfix interpreter. -/
namespace SubexponentialSAT.SqrtLog.PolynomialExecutorProgram
open SubexponentialSAT BitProgram StructuredCalls SubexpConvolutionControl
open SubexponentialSAT.SubexpRowPostfixInterpreter (physicalCfg )
open SubexponentialSAT.SubexpRowPostfixContext (operandStore )

def plainData (context : Fin 252 → List Bool) (code depth operands : List Bool) : Data :=
  ⟨fun _ => false,operandStore context code depth operands⟩

end SubexponentialSAT.SqrtLog.PolynomialExecutorProgram

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

abbrev Data := State 16 32

end SubexponentialSAT.Subexp.GlobalBasisEntryCore

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

def parserState (v p : Bool) (src dst : Word) : State 2 2 :=
  ⟨ParserProgram.pair v p, ParserProgram.pair src dst⟩

def captureState (v p : Bool) (src out : Word) : State 2 3 :=
  ⟨ParserProgram.pair v p, SubexpHornerProgram.triple src [] out⟩

def literalState (v p : Bool) (payload out : Word) : State 3 3 :=
  ⟨SubexpHornerProgram.triple v p true, SubexpHornerProgram.triple payload out []⟩

/-! The following induction rule accounts for actual executions of the fixed
payload body. Its premises will be proved for `termBody`, `groupBody`, and
`blockBody`; the exported whole-controller statement has no callback argument. -/

/-! ## Forward-output service boundary -/

end SubexponentialSAT.SubexpKernelControl

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_Subexp_ConstraintEntryCompare
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Compare the two preserved universal-type byte arrays without changing
the scalar result or any input stack of the matrix-entry service. -/

namespace SubexponentialSAT.Subexp.ConstraintEntryCompare

open BitProgram StructuredCalls StackRoutines

abbrev Data := State 10 46

def copied (a : Data) (src dst : Fin 46) : Data :=
  ⟨readRegs a.regs 0 1 none, copyStacks src dst a.stacks⟩

end SubexponentialSAT.Subexp.ConstraintEntryCompare

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

abbrev Data := StructuredProgram.State 8 8

def state (regs : Regs) (remainder modulus input quotient : List Bool) : Data :=
  ⟨regs, ModularQuotientPrograms.quotientStacks remainder modulus input quotient⟩

def inputState (regs : Regs) (modulus input : List Bool) : Data :=
  state regs [] modulus input []

def Output (modulus input : List Bool) (d : Data) : Prop :=
  BinaryArithmetic.toNat (d.stacks 7) = ChunkPartition.count (BinaryArithmetic.toNat input) (BinaryArithmetic.toNat modulus) ∧
  (d.stacks 7).length ≤ input.length + 1 ∧
  ∀ j : Fin 8, j ≠ 7 → d.stacks j =
    ModularQuotientPrograms.quotientStacks (divide modulus input).2 modulus []
      (divide modulus input).1 j

end SubexponentialSAT.SubexpCeilingProgram

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

abbrev Code := Cmd 40 896

def liftLow (c : Cmd 40 768) (input output : Fin 768) : Code :=
  liftCommand c input output id lowStack

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FactorAssignmentProgram
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_HeadSpecializationProgram
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! Immediate Boolean specialization using the actual dictionary scanner. -/

/-! The dictionary framing, key rewrite and record traversal follow the actual
MomentsProjectionProgramNative implementation. The replacement comparator tests
support inclusion, so this scan implements evaluation at a Boolean correction
assignment. Numeric-key collisions are intentionally left for normalization. -/
namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HeadEvaluationProgram.Specialization
open OAI BitProgram StructuredCalls
open OAI.Algorithms.SubexponentialSAT.SqrtLog MomentsProjectionProgram

def record : Cmd 5 10 := .seq (readFrame 0 2) (.seq (readFrame 0 3)
  (.seq rewriteKey (.seq compare (.ite 4 hit miss))))
def recordBody : Cmd 5 10 := .seq record (.base (.atom (.peek 0 0 3)))
def records : Cmd 5 10 := .while 3 recordBody

def project : Cmd 5 10 := .seq (readFrame 0 1)
  (.seq (.base (.atom (.peek 0 0 3))) (.seq records (transfer 8 9)))
def program := compiled project 0 9


open Squarefree

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HeadEvaluationProgram.Specialization
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

def «initialize_» : Code := liftCommand (clearMany entryScratch) 175 854 localRegister id

end
end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FactorAssignmentProgram
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_FactorTableBudgets
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! Fixed polynomial bounds for the actual factor-table service. The scalar
allowance includes physical signed-word lengths; it never bounds the integer
value of an exponential modulus or numerator in unary. All ambient source
rows and every specialized incidence record are included. -/
namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FactorTableBudgets
open OAI.Algorithms.SubexponentialSAT.SqrtLog OAI.Algorithms.SubexponentialSAT.SubexpLiftRing
open OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgram OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutSourceRowsProgram
open OAI.Algorithms.SubexponentialSAT.SqrtLog.CostAssembly.Polynomial
open OAI.Algorithms.SubexponentialSAT.Subexp
open FactorTableNative

def uniformEnvelope (S : ℕ) : ℕ :=
  LayoutSourceValuesProgram.Native.polynomialBudget S S S S S S S S +
    (UniversalRowMismatchTypes.extractBudget (r := S) (Q := S) (0 : Fin 1)+
      UniversalRowMismatchBound.mismatchBound (S+1)+8*(S*S)+13)+
    14*S+224*workspaceEnvelope S+UniversalRowSourceBound.sourceBound (workspaceEnvelope S)+281

/-- State-independent allowance for every actual ambient source row. -/
def sourceEnvelope (S : ℕ) : ℕ :=
  let B := 2*S
  let W := (S+1)*(S*B)
  let K := 800*(2*S+1)^2+uniformEnvelope S+200*S+302+12*S+12
  LayoutSourceRowsProgramInitialize.budget (S+1) (S*B)+1000*(4*S+1)^2+
    S*(rowBudgetPolynomial K (UniversalRowSourceBound.sourceLengthBound S)
      (S+1) S B S+45*W+83)+2*S+23+
    1000000000000*(S+(67108864*S+1+W+(S+1)+S*(2*W+2)+1)+1)

def literalEnvelope (S : ℕ) : ℕ :=
  7*S+(10*S+9*S+18+(10*S+42*S+29*(S*(2*S))+109)+
    (sourceEnvelope S+1+(7*S+5+specializationEnvelope S)))+
    22*(S+1)+19*payloadEnvelope S+
    2*(S*(2*((S+1)*(S*(2*S)))+2)+1)+54

/-- Includes the complete ambient loop, its growing table and export cleanup. -/
def tableEnvelope (S : ℕ) : ℕ :=
  1000000*(S+S+literalEnvelope S+payloadEnvelope S+1)^2

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FactorTableBudgets
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_NativeProgram
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.MulticolorTypes.decidableMemJoint _root_.OAI.Algorithms.SubexponentialSAT.MulticolorTypes.decidableMemSide _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! Actual finite count-word positivity suffix. The counting body is integrated
separately; this suffix never interprets the least significant bit as SAT. -/

namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.Native

open BitProgram StructuredCalls

def positivity {r s : ℕ} (ports : CounterForPrograms.Ports r s)
    (answer : Fin s) : Cmd r s :=
  .seq (CounterForPrograms.testCmd ports)
    (.base (.atom (.push answer (ports.register 2))))

noncomputable def positivityResult {r s : ℕ} (ports : CounterForPrograms.Ports r s)
    (answer : Fin s) (a : State r s) : State r s :=
  (StructuredProgram.Atom.push answer (ports.register 2)).eval
    (CounterForPrograms.testResult ports a)

def positivityPorts : CounterForPrograms.Ports 80 1220 where
  register := ABI.positivityRegisters
  counter := ABI.countStack
  scratch := ABI.positivityScratch
  counter_ne_scratch := by decide

def clearOutput (port : Fin 1220) : Cmd 80 1220 :=
  .call (StackRoutines.clearProgram port 72 73)

def clearOutputState (port : Fin 1220) (a : State 80 1220) : State 80 1220 :=
  ⟨readRegs a.regs 72 73 none, Function.update a.stacks port []⟩

def answerReady (a : State 80 1220) : State 80 1220 :=
  clearOutputState ABI.positivityScratch (clearOutputState ABI.answerStack a)

noncomputable def answerResult (a : State 80 1220) : State 80 1220 :=
  positivityResult positivityPorts ABI.answerStack (answerReady a)

def answerCommand : Cmd 80 1220 :=
  .seq (clearOutput ABI.answerStack)
    (.seq (clearOutput ABI.positivityScratch) (positivity positivityPorts ABI.answerStack))

def answerProgram := compiled answerCommand ABI.countStack ABI.answerStack

def answerSteps (a : State 80 1220) : ℕ :=
  2 * (a.stacks ABI.answerStack).length + 2 * (a.stacks ABI.positivityScratch).length +
    8 * (a.stacks ABI.countStack).length + 15

/-- Each unary header bit contributes one zero; the initial one is retained. -/
def powerBody : Cmd 2 2 :=
  .base (.seq (.atom (.set 0 false))
    (.seq (.atom (.push 1 0)) (.atom (.pop 0 0 1))))

def powerSeed : Cmd 2 2 :=
  .base (.seq (.atom (.set 0 true))
    (.seq (.atom (.push 1 0)) (.atom (.pop 0 0 1))))

def powerCommand : Cmd 2 2 := .seq powerSeed (.while 0 powerBody)

def powerProgram := compiled powerCommand 0 1

def powerState (flag : Bool) (unread output : List Bool) : State 2 2 :=
  ⟨![flag, true], ![unread, output]⟩

def powerBoundary (n : ℕ) (output : List Bool) : State 2 2 :=
  match n with
  | 0 => powerState false [] output
  | n + 1 => powerState true (Encoding.encodeNat n) output

def copyInput : Cmd 80 1220 :=
  .call (StackRoutines.copyProgram ABI.countStack 1218 1219 72 73)

def copiedInput (input : List Bool) : State 80 1220 :=
  ⟨fun _ => false, Function.update (StructuredProgram.ioState (r := 80) ABI.countStack input).stacks
    1218 input⟩

def headerCommand : Cmd 80 1220 := .seq copyInput
  (.call (ProgramLinking.liftProgram FrontendProgram.initializeProgram
    ABI.positivityRegisters headerStacks))

noncomputable def headerResult (input body binary : List Bool) : State 80 1220 :=
  embedState ABI.positivityRegisters headerStacks (copiedInput input)
    (StructuredProgram.State.ofCfg (FrontendProgram.cfg none false false body [] binary []))

def copyWord (src dst scratch : Fin 1220) : Cmd 80 1220 :=
  .call (StackRoutines.copyProgram src dst scratch 72 73)

def copiedWord (src dst : Fin 1220) (a : State 80 1220) : State 80 1220 :=
  ⟨readRegs a.regs 72 73 none, StackRoutines.copyStacks src dst a.stacks⟩

/-- This list is fixed finite control, never an input-dependent work list. -/
def clearSequence : List (Fin 1220) → Cmd 80 1220
  | [] => .base .skip
  | port :: rest => .seq (clearOutput port) (clearSequence rest)

def clearLeaf : Cmd 80 1220 := clearSequence leafPorts

def resetRegisters : List (Fin 80) → Cmd 80 1220
  | [] => .base .skip
  | i :: rest => .seq (.base (.atom (.set i false))) (resetRegisters rest)

def resetRegisterState (ports : List (Fin 80)) (a : State 80 1220) : State 80 1220 :=
  ⟨fun i => if i ∈ ports then false else a.regs i, a.stacks⟩

def resetLeafRegisters : Cmd 80 1220 := resetRegisters leafRegisterPorts

def resetLeafState (a : State 80 1220) : State 80 1220 :=
  resetRegisterState leafRegisterPorts a

def loadLeaf : Cmd 80 1220 :=
  .seq clearLeaf (.seq resetLeafRegisters (.seq (clearOutput 1219)
    (.seq (copyWord 265 1104 1219)
      (.seq (copyWord 267 1105 1219) (copyWord 264 1106 1219)))))

def exportLeaf : Cmd 80 1220 :=
  .seq (clearOutput 263) (.seq (clearOutput 1219)
    (.seq (copyWord 1108 263 1219) clearLeaf))

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.Native
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_FiniteFallback
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.FiniteField.fieldFintype _root_.OAI.Algorithms.SubexponentialSAT.MulticolorTypes.instFintypeJoint _root_.OAI.Algorithms.SubexponentialSAT.MulticolorTypes.instFintypeSide _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingModel.Data.fieldFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! Generic finite scanner selectively adapted from the reviewed canceled source
`CountingDraft/FiniteWordScanner.lean`; no obsolete endpoint or rate is imported.

Fixed finite control for bounded input prefixes and complete binary output words.
The transition table is chosen before any runtime input. -/

namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FiniteFallback

open BitProgram Scanner
open scoped BigOperators

open StructuredCalls

def resetScanner : Cmd 80 1220 :=
  .base (.seq (.atom (.set 0 false)) (.atom (.set 1 false)))

def scannerState (a : State 80 1220) (word : List Bool) : State 80 1220 :=
  ⟨resetScannerRegs a.regs, Function.update a.stacks ABI.countStack word⟩

noncomputable def framedCountCommand (B : ℕ) : Cmd 80 1220 :=
  .seq resetScanner (.call (ProgramLinking.liftProgram (countProgram B)
    (Fin.castAdd 78) (fun _ : Fin 1 => ABI.countStack)))

noncomputable def framedCommand (B : ℕ) : Cmd 80 1220 :=
  .seq (framedCountCommand B) Native.answerCommand

noncomputable def framedResult (a : State 80 1220) (word : List Bool) : State 80 1220 :=
  Native.answerResult (scannerState a word)

def cutoffPrepare : Cmd 80 1220 :=
  .seq (Native.clearOutput 270) (Native.clearOutput 271)

def cutoffPrepared (a : State 80 1220) : State 80 1220 :=
  Native.clearOutputState 271 (Native.clearOutputState 270 a)

def cutoffCopied (a : State 80 1220) : State 80 1220 :=
  Native.copiedWord 258 270 (cutoffPrepared a)

noncomputable def cutoffScanned (a : State 80 1220) (flag : Bool) : State 80 1220 :=
  embedState cutoffRegs (fun _ : Fin 1 => (270 : Fin 1220)) (cutoffCopied a)
    (StructuredProgram.ioState 0 [flag])

noncomputable def cutoffResult (a : State 80 1220) (flag : Bool) : State 80 1220 :=
  (StructuredProgram.Atom.pop 270 75 76).eval (cutoffScanned a flag)

noncomputable def cutoffCommand (B : ℕ) : Cmd 80 1220 :=
  .seq cutoffPrepare (.seq (Native.copyWord 258 270 271)
    (.seq (.call (ProgramLinking.liftProgram (cutoffScanner B) cutoffRegs
      (fun _ : Fin 1 => (270 : Fin 1220)))) (.base (.atom (.pop 270 75 76)))))

/-- The small/large choice is made by the actual cutoff flag. The large branch
is a finite command selected before the input; no execution service is assumed. -/
noncomputable def dispatchCommand (B : ℕ) (large : Cmd 80 1220) : Cmd 80 1220 :=
  .seq (cutoffCommand B) (.ite 75 (framedCommand B) large)


end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FiniteFallback
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

/-- The original argmin bank occupies ports 0 through 8. Port 9 is the
persistent current candidate and port 10 is preserving-copy scratch. -/
def core : HashSelectProgram.Ports 8 11 where
  register := id
  stack := Fin.castAdd 2
  register_injective := Function.injective_id
  stack_injective := Fin.castAdd_injective 9 2

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HashCandidateProgram
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

namespace NativeRound

def core : HashSelectProgram.Ports 40 896 where
  register := registers
  stack := coreStacks
  register_injective := Fin.castAdd_injective 8 32
  stack_injective := by decide

end NativeRound

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HashGreedyProgram
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

def data (regs : Fin 8 → Bool) (ell unary binary remainder quotient payload encoded : List Bool) : Data :=
  ⟨regs, tapes ell unary binary remainder quotient payload encoded⟩

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

def data (v pr found : Bool) (ell source output payload : List Bool) : Data :=
  ⟨regs v pr found, tapes ell source output payload⟩

def Invariant (ell : List Bool) (d : Data) : Prop :=
  ∃ output, d = data false false false ell [] output []

def effect (ell bits : List Bool) (a b : Data) : Prop :=
  b.stacks 20 = true :: (Encoding.frame (mappedBits ell bits) ++ a.stacks 20)

end SubexponentialSAT.SubexpChunkRecordMap

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_HashGreedyCode
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! Actual supplied-code row payloads initialize_ the streamed selector. Raw
slot bounds retain repeated indices and zero coefficients, as the physical
assembler does; they do not substitute semantic support for retained data. -/
namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HashGreedyCode

open SqrtLog
open scoped BigOperators
open HashGreedyCNF

noncomputable section

abbrev raw (m : ℕ) (hm : 0 < m) :=
  LeafScopeResourceBounds.rawDecode m (HashCandidates.digitWidth m) hm

end
end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HashGreedyCode
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

def stageTrial : Cmd 40 896 := .seq stageFinal prefixTrial

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.LeafOuterNative
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

/-- A proof-only multilinear representative of the existing squarefree algebra.
The evaluator never builds this multivariate polynomial or its support list. -/
noncomputable def squarefreePolynomial (f : Squarefree.Poly V R) : MvPolynomial V R :=
  ∑ s ∈ f.coeff.support,
    MvPolynomial.C (f.coeff s) * ∏ v ∈ s.vars, MvPolynomial.X v

end SquarefreeBridge

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryEvaluation
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

def afterLength (d : Data) (exponent : List Bool) : Data :=
  ⟨fun j => if j.val < 3 then false else d.regs j,
    Function.update (Function.update d.stacks 4 []) 2 exponent⟩

def lengthInput (d : Data) : State 3 3 :=
  ⟨CounterPrograms.counterRegs (d.regs 0) (d.regs 1) false,
    CounterPrograms.lengthStacks (d.stacks 4) [] []⟩

def lengthOutput (exponent : List Bool) : State 3 3 :=
  ⟨fun _ => false, fun j => if j = 1 then exponent else []⟩

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

abbrev Data := State 8 15

end SubexponentialSAT.SubexpScopeCountSetup

end OAI.Algorithms
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

namespace CountFalse

abbrev Data := State 3 2

end CountFalse


open SubexpSetupStorage
abbrev Data := State 16 896

def countPrepared (a : Data) : Data := prepareState 329 scratch [(338,325)] a

def fillPrepared (isE : Bool) (a : Data) : Data :=
  prepareState 329 scratch [(338,325),(fillInput isE,327)] a



abbrev CallerData := State 40 896

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.PairNativeSetup
end

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

namespace NativeHeadSelect
open OAI.Algorithms.SubexponentialSAT.StackRoutines

abbrev Data := State 40 896

end NativeHeadSelect

open OAI.Algorithms.SubexponentialSAT.StackRoutines

namespace Overlay
open OAI.Algorithms.SubexponentialSAT.StackRoutines

abbrev Data := State 8 12

end Overlay

namespace NativeOverlay
open OAI.Algorithms.SubexponentialSAT.StackRoutines

abbrev Data := State 40 896

end NativeOverlay


end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighQueryAdapter
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

def descendLevelState (a : State 40 896) : State 40 896 :=
  (StructuredProgram.Atom.bnot controllerPorts.leaf 1).eval
    ((StructuredProgram.Atom.peek (tupleStacks 6) 0 1).eval
      ((StructuredProgram.Atom.push (tupleStacks 9) 0).eval
        ((StructuredProgram.Atom.set 0 true).eval
          ((StructuredProgram.Atom.pop (tupleStacks 6) 0 1).eval a))))

def ascendLevelState (a : State 40 896) : State 40 896 :=
  (StructuredProgram.Atom.set controllerPorts.leaf false).eval
    ((StructuredProgram.Atom.push (tupleStacks 6) 0).eval
      ((StructuredProgram.Atom.set 0 true).eval
        ((StructuredProgram.Atom.pop (tupleStacks 9) 0 1).eval a)))

def testParentState (a : State 40 896) : State 40 896 :=
  (StructuredProgram.Atom.peek (tupleStacks 0) 0 controllerPorts.active).eval a

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SignatureTupleProgram
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_RingNodeSetup
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! Paid traversal of the actual framed node table. The remaining cursor and
unary index are physical stacks, and the decoded node is transferred to the
original factor port. No list of semantic nodes is manufactured by the machine. -/

namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.RingNodeSetup

open OAI BitProgram StructuredCalls StackRoutines
open OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafNodeSamplesProgram

theorem state_storeOf (a : Data) : state a.regs (storeOf a) = a := by
  have hs : tapes (storeOf a) = a.stacks := by
    funext i
    have choose (j : Fin 768) {tail : List Bool} (ht : tail = a.stacks i) :
        (if i = j then a.stacks j else tail) = a.stacks i := by
      split
      · rename_i h
        exact congrArg a.stacks h.symm
      · exact ht
    unfold tapes
    apply choose 301
    apply choose 302
    apply choose 303
    apply choose 304
    apply choose 305
    apply choose 307
    apply choose 78
    apply choose 102
    apply choose 104
    apply choose 256
    apply choose 265
    rfl
  change ⟨a.regs, tapes (storeOf a)⟩ = a
  rw [hs]

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.RingNodeSetup
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_HeadSumBudgets
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! Explicit compact boundary, source and arithmetic caps for the actual head
sum. Their fixed polynomial certificates depend on source dimensions and
physical word lengths, independently of the number of head assignments. -/
namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HeadSumBudgets
open OAI.Algorithms.SubexponentialSAT.SqrtLog OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgram OAI.Algorithms.SubexponentialSAT.SubexpLiftRing
open OAI.Algorithms.SubexponentialSAT.SqrtLog.CostAssembly.Polynomial
open FactorTableBudgets

def callbackEnvelope (A : ℕ) : ℕ :=
  FactorAssignmentProgram.callbackScratch.length*(2*compactCap A+3)+
  128*compactCap A+200+tableEnvelope (tableScalarCap A)+
  2000*(arithmeticCap A)^3+14000000*(arithmeticCap A)^9

def bodyEnvelope (A : ℕ) : ℕ :=
  3040000*(FactorAssignmentProgram.entryScratch.length+A+2*A+A+A+A+
    compactCap A+callbackEnvelope A+1)^10

def prefixCap (A : ℕ) : ℕ := bodyEnvelope A+9*(A+1)+8

def iterationEnvelope (A : ℕ) : ℕ :=
  2*bodyEnvelope A+126*prefixCap A+54*A+286

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HeadSumBudgets
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_HighCountInit
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! Paid entry to one disjoint high-assignment count. Internal empty binary
words represent zero; the final CanonicalHigh routine emits canonical [false].
The high odometer is copied from the actual encoded seed, never reconstructed
from an assumed family of successful branch states. -/
namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighCountInit

open BitProgram StructuredCalls StackRoutines HighQueryAdapter

abbrev Data := State 40 896

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighCountInit
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_HighBranchSpace
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! Actual high-condition staging uses a fixed local ten-stack footprint.
The independent physical cap is never identified with a sum of caller words. -/
namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighBranchSpace

open OAI BitProgram StructuredCalls StackRoutines HighQueryAdapter
open OAI.Algorithms.SubexponentialSAT.SqrtLog
open OAI.Algorithms.SubexponentialSAT.SqrtLog.HighIncidenceProgram

abbrev Data := State 40 896

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighBranchSpace
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_HighCountSeed
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! Each marked count regenerates its own zero high-assignment odometer from
its current physical mask. No common high set or retained previous seed is
assumed. The original two-stack branch initializer is executed concretely. -/
namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighCountSeed

open OAI BitProgram StructuredCalls StackRoutines HighQueryAdapter
open OAI.Algorithms.SubexponentialSAT.SqrtLog.HighIncidenceProgram

abbrev Data := State 40 896

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighCountSeed
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_HighMarkedCleanup
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
/-! Actual lower-workspace reclamation in the shared leaf ABI. Source masters,
collector, count and upper caller words are preserved by the paid cleanup. -/
namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighMarkedFrontend
open OAI BitProgram StructuredCalls
open OAI.Algorithms.SubexponentialSAT.SqrtLog
abbrev Data := State 40 896
def project (a : Data) : LeafProgram.Query.Data := projectState id stackMap a
noncomputable def result (a : Data) (b : LeafProgram.Query.Data) : Data := embedState id stackMap a b

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighMarkedFrontend
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

def seedUnary : Cmd 80 1220 :=
  .base (.seq (.atom (.set 72 false)) (.atom (.push 258 72)))

def seededUnary (a : State 80 1220) : State 80 1220 :=
  ⟨Function.update a.regs 72 false, Function.update a.stacks 258 (false :: a.stacks 258)⟩

def ambientCommand : Cmd 80 1220 :=
  .seq (copyWord ABI.countStack 1218 1219)
    (.seq seedUnary (.seq (.call (ProgramLinking.liftProgram ParserProgram.natProgram
      unaryRegisters unaryStacks)) (clearOutput 1218)))

noncomputable def parsedAmbient (a : State 80 1220) (n : ℕ) (body : List Bool) :
    State 80 1220 :=
  embedState unaryRegisters unaryStacks (seededUnary (copiedWord ABI.countStack 1218 a))
    (StructuredProgram.State.ofCfg
      (ParserProgram.cfg (l := 5) none false true body (Encoding.encodeNat n)))

noncomputable def ambientResult (a : State 80 1220) (n : ℕ) (body : List Bool) :
    State 80 1220 := clearOutputState 1218 (parsedAmbient a n body)

def placeBodyCommand : Cmd 80 1220 :=
  .seq (copyWord 1218 265 1219) (clearOutput 1218)

def placedBody (a : State 80 1220) : State 80 1220 :=
  clearOutputState 1218 (copiedWord 1218 265 a)

structure FrontendReady {n : ℕ} (F : SAT.CNF (Fin n)) (binary : List Bool)
    (a : State 80 1220) : Prop where
  input : a.stacks ABI.countStack = Encoding.encodeCNF F
  header : a.stacks 258 = Encoding.encodeNat n
  body : a.stacks 265 = SubexpNormalizationCorrectness.normalizedBody F
  dimension : a.stacks 267 = binary
  blank : ∀ i, i ≠ ABI.countStack → i ≠ 258 → i ≠ 265 → i ≠ 267 → a.stacks i = []


end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.Native
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

def canonicalRowWidth : Cmd 40 896 := .seq (route (780, 768)) (route (780, 783))

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeLeaf
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_NativeTerminal
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.MulticolorTypes.decidableMemJoint _root_.OAI.Algorithms.SubexponentialSAT.MulticolorTypes.decidableMemSide _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! Actual outer-CNF terminal handling. The ambient unary header is retained;
an empty formula emits its full count 2^n, and an empty clause emits zero. -/

namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeTerminal

open BitProgram StructuredCalls
open scoped BigOperators

abbrev Data := State 80 1220

noncomputable def classified (a : Data) (records : List (List Bool)) : Data :=
  embedState (Fin.castAdd 70) classifierStacks a
    (SqrtLog.LeafProgram.Trivial.result
      (projectState (Fin.castAdd 70) classifierStacks a) records)

structure Ready (a : Data) : Prop where
  low : ∀ i : Fin 1220, i.val < 5 → a.stacks i = []
  scratch : a.stacks 8 = []

def power : Cmd 80 1220 :=
  .seq (Native.copyWord 258 268 269)
    (.call (ProgramLinking.liftProgram Native.powerProgram powerRegs powerStacks))

noncomputable def powered (a : Data) (n : ℕ) : Data :=
  embedState powerRegs powerStacks (Native.copiedWord 258 268 a)
    (Native.powerState false [] (countWord (2 ^ n)))

def zero : Cmd 80 1220 :=
  .seq (.base (.atom (.set 72 false))) (.base (.atom (.push 263 72)))

def zeroed (a : Data) : Data :=
  ⟨Function.update a.regs 72 false, Function.update a.stacks 263 (false :: a.stacks 263)⟩

noncomputable def result (a : Data) (n : ℕ) (records : List (List Bool)) : Data :=
  if [false] ∈ records then zeroed (classified a records)
  else if records = [] then powered (classified a records) n
  else classified a records

/-- Dispatcher-local temporary cleanup is executed, not assumed at the DFS boundary. -/
def prepare : Cmd 80 1220 :=
  .seq (Native.clearOutput 263)
    (.seq (Native.clearOutput 268) (Native.clearOutput 269))

def prepared (a : Data) : Data :=
  Native.clearOutputState 269 (Native.clearOutputState 268 (Native.clearOutputState 263 a))

@[simp] theorem prepared_output (a : Data) : (prepared a).stacks 263 = [] := by
  simp [prepared, Native.clearOutputState]

@[simp] theorem prepared_work (a : Data) : (prepared a).stacks 268 = [] := by
  simp [prepared, Native.clearOutputState]

@[simp] theorem prepared_scratch (a : Data) : (prepared a).stacks 269 = [] := by
  simp [prepared, Native.clearOutputState]

noncomputable def readyResult (a : Data) (n : ℕ) (records : List (List Bool)) : Data :=
  result (prepared a) n records

def powerCall : Cmd 80 1220 :=
  .call (ProgramLinking.liftProgram Native.powerProgram powerRegs powerStacks)


open DisjointReuse.DFSVisit

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeTerminal
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

abbrev Data := State 80 1220

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeLeafDispatch
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_NativeLeafExecution
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! Concrete shared-ABI loading, local execution and whole-count export for a
DFS leaf. The local command remains explicit; its actual execution proof is
supplied by the streamed leaf construction. No new machine service is defined. -/

namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeLeafExecution

open BitProgram StructuredCalls DisjointReuse DFSVisit

abbrev Data := State 80 1220
abbrev LocalData := State 40 896

def command (localCommand : Cmd 40 896) : Cmd 80 1220 :=
  .seq Native.loadLeaf
    (.seq (ABI.leafCall (compiled localCommand 784 788)) Native.exportLeaf)

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeLeafExecution
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

abbrev Data := State 8 32

def reset : Cmd 8 32 := .base
  (.seq (.atom (.set 0 false)) (.seq (.atom (.set 1 false)) (.atom (.set 2 false))))

def initialData (input : List Bool) : Data := ⟨fun _ => false, slots (initialWords input)⟩

def resetPorts : List (Fin 80) → Cmd 80 1220
  | [] => .base .skip
  | i :: rest => .seq (.base (.atom (.set i false))) (resetPorts rest)

def resetPortsState (ports : List (Fin 80)) (a : State 80 1220) : State 80 1220 :=
  ⟨fun i => if i ∈ ports then false else a.regs i, a.stacks⟩

/-- Eight fixed register writes discharge the concrete native caller's
arbitrary register contents before entering the schedule subroutine. -/
def resetShared : Cmd 80 1220 := resetPorts ((List.finRange 8).map (Fin.castAdd 72))

def resetSharedState (a : State 80 1220) : State 80 1220 :=
  resetPortsState ((List.finRange 8).map (Fin.castAdd 72)) a

@[simp] theorem resetSharedState_stacks (a : State 80 1220) :
    (resetSharedState a).stacks = a.stacks := rfl

@[simp] theorem resetSharedState_register (a : State 80 1220) (i : Fin 8) :
    (resetSharedState a).regs (Fin.castAdd 72 i) = false := by
  simp [resetSharedState, resetPortsState]

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

def clearSchedule : Cmd 80 1220 := clearSequence [1, 2, 3, 4]

structure SetupReady (k : ℕ) {n : ℕ} (F : SAT.CNF (Fin n))
    (a : State 80 1220) : Prop where
  input : a.stacks ABI.countStack = Encoding.encodeCNF F
  header : a.stacks 258 = Encoding.encodeNat n
  body : a.stacks 265 = SubexpNormalizationCorrectness.normalizedBody F
  dimension : toNat (a.stacks 267) = n
  dimension_length : (a.stacks 267).length ≤ n + 1
  schedule : toNat (a.stacks 266) = sparsifySchedule n
  threshold : toNat (a.stacks 259) =
    DisjointReuse.SparseBudget.chooseM k 1 (sparsifySchedule n) (by decide)
  occurrence : toNat (a.stacks 264) = 4 * toNat (a.stacks 259) ^ (k - 1)
  blank : ∀ i, i ≠ ABI.countStack → i ≠ 258 → i ≠ 265 → i ≠ 267 →
    i ≠ 266 → i ≠ 259 → i ≠ 264 → a.stacks i = []

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.Native
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_QueryHeadBudgets
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! A concrete numerical HeadBounds certificate for the actual visitor.
Source columns are bounded from its stored native input, all incidence rows
remain present, and the compact endpoint cap is separate from transient space. -/
namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryHeadBudgets
open OAI BitProgram StructuredCalls SubexpSetupStorage SubexpLiftRing
open SqrtLog SqrtLog.LeafProgram SqrtLog.LeafHeadSetupProgram
open HeadSumBudgets FactorTableBudgets
open OAI.Algorithms.SubexponentialSAT.SqrtLog.CostAssembly.Polynomial

def transient (A : ℕ) : ℕ := prefixCap (scalarCap A)

/-- Covers the complete visitor's polynomial time coefficient and its
all-prefix max bound, including load, preparation, head scan and multiplication. -/
def visitorEnvelope (A : ℕ) : ℕ :=
  QueryVisitorLoad.runEnvelope A (compact A)+100*compact A+200+
    HeadSumBudgets.iterationEnvelope (scalarCap A)+multiplyEnvelope A+
    996*compact A+200+transient A+896*compact A

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryHeadBudgets
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_QueryVisitorBudgets
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! Polynomial overhead and prefix space for the complete actual tuple
visitor. The number of heads and the proved maximum head-size exponent stay
explicit; the empty-head/empty-tuple term is retained. -/
namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryVisitorBudgets
open OAI SqrtLog SubexpLiftRing SubexpSetupStorage
open LeafHeadSetupProgram
open OAI.Algorithms.SubexponentialSAT.SqrtLog.CostAssembly.Polynomial

/-- One uniform local coefficient covers both representative passes and the
final shared-U readout/addition, as well as their complete source prefix bound. -/
def envelope (A : ℕ) : ℕ :=
  tailEnvelope A+2400*(QueryHeadBudgets.compact A+1)+baselineEnvelope A+
    QueryHeadBudgets.visitorEnvelope A+20

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryVisitorBudgets
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_ReconstructionNative
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! One concrete lower-workspace recovery tail: native Hermite reconstruction,
canonical complete binary readback, and paid cache reclamation. All retained
caller stacks enter its local prefix bound; the endpoint changes only count323.
The physical jet and semantic target hypotheses must be produced by the query. -/
namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.ReconstructionNative

open OAI BitProgram StructuredCalls SubexpLiftRing SubexpQuarticRing OAI.Algorithms.SubexponentialSAT.SqrtLog
open DensePolynomialProgram
open LeafProgram.Count

abbrev Data := State 40 768

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.ReconstructionNative
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_TupleRunBudgets
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! The same compact endpoint cap supports the actual tuple controller and
its visitor. Transient scanner/reload work is bounded separately; none of it
is fed back into the retained frame cap between pairs. -/
namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.TupleRunBudgets
open OAI.Algorithms.SubexponentialSAT.SqrtLog.CostAssembly.Polynomial
open SignatureTupleComplete SignatureTupleLoader

/-- A single fixed coefficient covers local controller events, callback
coefficients and prefix space. The balanced-head exponential stays external. -/
def envelope (A : ℕ) : ℕ := eventEnvelope A+QueryVisitorBudgets.envelope A

/-- Includes the empty-head unit-addition path and the two final setup/guard
steps; it is independent of the number of attained tuples. -/
def runCoefficient (A : ℕ) : ℕ :=
  5*envelope A+2496*QueryHeadBudgets.compact A+QueryVisitorBudgets.tailEnvelope A+1602

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.TupleRunBudgets
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_StreamedQueryMeasuredCost
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! The measured callback pays native mask setup, the complete attained-tuple
run (including ascent), and the signed commit. Its finite-difference iterator
is compared to the original explicit resource record with one fixed power. -/
namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.StreamedQueryMeasuredCost

open OAI SqrtLog SubexpLiftRing SubexpQuarticRing
open SignatureTupleTraversal SignatureTupleDFS
open CostAssembly.Polynomial
open scoped BigOperators

def coefficient (A : ℕ) : ℕ := localEnvelope A+TupleRunBudgets.runCoefficient A

/-- The explicit pair-loop coefficient has a fixed polynomial degree before
the source, the node, the supports or the attained signatures are chosen. -/
def pairCoefficient (A : ℕ) : ℕ := (coefficient A+46)*(A+1)*(3*A+1)

/-- The actual source-prefix bound contains only local polynomial work and
the retained words. Neither attained counts nor an exponential time occurs. -/
def pairSpaceEnvelope (A : ℕ) : ℕ := coefficient A+896*QueryHeadBudgets.compact A+13

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.StreamedQueryMeasuredCost
end


