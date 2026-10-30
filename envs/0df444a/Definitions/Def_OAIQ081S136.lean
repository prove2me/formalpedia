-- Prove2me | Definitions.Def_OAIQ081S136
-- name    : OAIQ081S136
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-29T22:45:51.272032+00:00
-- url     : https://prove2.me/theorems/84665827-2726-461c-8326-b0e29837b0e3
-- title:
--   Definitions bundle OAIQ081S136 of the split of OpenAI, The Exponential Time Hypothesis is False
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.exact_count_and_sat`, carved from OpenAI's openai/math development (OpenAI, *The Exponential Time Hypothesis is False*, OpenAI Math Release, October 25, 2026, result family 378, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 264 declarations of OpenAI's Lean: 258 definitions, 4 inductive types or structures and 2 theorems. The definitions and types are `OAI.Algorithms.SubexponentialSAT.SqrtLog.PerturbationAssembly.finishTarget`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.PerturbationAssembly.lowBudget`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.PerturbationAssembly.lowWorkPolynomial`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.PerturbationAssembly.makeLiteralKey`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.PerturbationAssembly.pairChoice`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.PerturbationAssembly.pairedRows`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.PerturbationAssembly.restoreCache`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.PerturbationAssembly.rowLoop`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.PerturbationAssembly.rowPorts`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.PerturbationAssembly.saveReplace`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.PerturbationAssembly.scanRows`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.PerturbationAssembly.sourceCallData`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.PerturbationAssembly.tableRecord`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.PerturbationAssembly.tableResult`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.PerturbationBetaProgram.Coeff`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.PerturbationBetaProgram.peekReady`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.PerturbationBetaProgram.ready`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.PerturbationBetaProgram.rowsBits`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.PolynomialExecutorProgram.addValue`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.PolynomialExecutorProgram.evaluate`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.PolynomialExecutorProgram.loadValue`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.PolynomialExecutorProgram.mulValue`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.PolynomialExecutorProgram.sourceExpr`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.ProducedQueryRank.labelRows`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.ReconstructionProgram.InputReady.base`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.ReconstructionProgram.InputReady.lowFrame`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.ReconstructionProgram.LocalValue.factorCode`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.ReconstructionProgram.Native.Coeff`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.ReconstructionProgram.Native.budget`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.ReconstructionProgram.Native.middleBudget`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.ReconstructionProgram.Native.term`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.ReconstructionProgram.NativeState.arithmeticBase`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.Squarefree.Program.keepCoefficient`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.Squarefree.Program.replaceData`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.Squarefree.Program.replaceDone`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.Squarefree.ScaleProgram.copied`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.Squarefree.ScaleProgram.environment`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.Squarefree.ScaleProgram.state`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.AcceptedQueryStage.cleanup`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.AcceptedQueryStage.command` and 222 more.
--
--   **Sources.** They come from these modules of lean/OAI/Algorithms, in whole or in part: `SubexponentialSAT_SqrtLogSpace_AcceptedQueryStage`, `SubexponentialSAT_SqrtLogSpace_AttainedSignatureProgram`, `SubexponentialSAT_SqrtLogSpace_AttainedSignatureRescan`, `SubexponentialSAT_SqrtLogSpace_DisjointReuse_DFSCountProgram`, `SubexponentialSAT_SqrtLogSpace_DisjointReuse_SparseDFSProgram`, `SubexponentialSAT_SqrtLogSpace_DisjointReuse_SparsePriorityProgram`, `SubexponentialSAT_SqrtLogSpace_FactorArithmeticProgram`, `SubexponentialSAT_SqrtLogSpace_FactorAssignmentBoundary`, `SubexponentialSAT_SqrtLogSpace_FactorAssignmentLoop`, `SubexponentialSAT_SqrtLogSpace_FactorAssignmentProgram`, `SubexponentialSAT_SqrtLogSpace_FactorCacheProgram`, `SubexponentialSAT_SqrtLogSpace_FactorTableNative`, `SubexponentialSAT_SqrtLogSpace_FactorTableSpecialization`, `SubexponentialSAT_SqrtLogSpace_HashGreedyExecution`, `SubexponentialSAT_SqrtLogSpace_HashGreedyProgram`, `SubexponentialSAT_SqrtLogSpace_HashGreedyRound`, `SubexponentialSAT_SqrtLogSpace_HashMarkedQueryAdapter`, `SubexponentialSAT_SqrtLogSpace_HashMassAdapter`, `SubexponentialSAT_SqrtLogSpace_HashMassStaged`, `SubexponentialSAT_SqrtLogSpace_HashQueryEntry`, `SubexponentialSAT_SqrtLogSpace_HashTrialStage`, `SubexponentialSAT_SqrtLogSpace_HeadEvaluationProgram`, `SubexponentialSAT_SqrtLogSpace_HeadSpecializationProgram`, `SubexponentialSAT_SqrtLogSpace_HeadSumAssembly`, `SubexponentialSAT_SqrtLogSpace_HeadSumProgram`, `SubexponentialSAT_SqrtLogSpace_HighCountInit`, `SubexponentialSAT_SqrtLogSpace_HighCountSeed`, `SubexponentialSAT_SqrtLogSpace_HighMarkedCleanup`, `SubexponentialSAT_SqrtLogSpace_HighQueryAdapter`, `SubexponentialSAT_SqrtLogSpace_HighQueryDecode`, `SubexponentialSAT_SqrtLogSpace_HighQueryExecution`, `SubexponentialSAT_SqrtLogSpace_HighQueryLocalBounds`, `SubexponentialSAT_SqrtLogSpace_HighQueryProgram`, `SubexponentialSAT_SqrtLogSpace_HighQueryStart`, `SubexponentialSAT_SqrtLogSpace_NativeCode`, `SubexponentialSAT_SqrtLogSpace_NativeLayoutLoad`, `SubexponentialSAT_SqrtLogSpace_NodeAppendSpace`, `SubexponentialSAT_SqrtLogSpace_NodeReadoutSpace`, `SubexponentialSAT_SqrtLogSpace_PairNativeSetup`, `SubexponentialSAT_SqrtLogSpace_QueryExecution`, `SubexponentialSAT_SqrtLogSpace_QueryIncidenceCommand`, `SubexponentialSAT_SqrtLogSpace_QueryNodeFinish`, `SubexponentialSAT_SqrtLogSpace_QueryProducerSpace`, `SubexponentialSAT_SqrtLogSpace_QueryProgram`, `SubexponentialSAT_SqrtLogSpace_QueryStreamProgram`, `SubexponentialSAT_SqrtLogSpace_QueryTupleInit`, `SubexponentialSAT_SqrtLogSpace_QueryTupleSum`, `SubexponentialSAT_SqrtLogSpace_QueryTupleVisitor`, `SubexponentialSAT_SqrtLogSpace_QueryVisitorProgram`, `SubexponentialSAT_SqrtLogSpace_ReconstructionNative`, `SubexponentialSAT_SqrtLogSpace_ReconstructionSpace`, `SubexponentialSAT_SqrtLogSpace_SignatureHeadLoaderCore`, `SubexponentialSAT_SqrtLogSpace_SignatureHeadPrepare`, `SubexponentialSAT_SqrtLogSpace_SignatureKeyNative`, `SubexponentialSAT_SqrtLogSpace_SignatureTupleNative`, `SubexponentialSAT_SqrtLogSpace_SignatureTupleProgram`, `SubexponentialSAT_SqrtLogSpace_SparseCodeProgram`, `SubexponentialSAT_SqrtLogSpace_SparseCodeSearch`, `SubexponentialSAT_SqrtLog_PerturbationAssemblyConstants`, `SubexponentialSAT_SqrtLog_PerturbationAssemblyLow`, `SubexponentialSAT_SqrtLog_PerturbationAssemblyLowBounds`, `SubexponentialSAT_SqrtLog_PerturbationAssemblyOuter`, `SubexponentialSAT_SqrtLog_PerturbationAssemblyPreparation`, `SubexponentialSAT_SqrtLog_PerturbationAssemblyRelInput`, `SubexponentialSAT_SqrtLog_PerturbationAssemblyScan`, `SubexponentialSAT_SqrtLog_PerturbationAssemblySourceCall`, `SubexponentialSAT_SqrtLog_PerturbationAssemblyTarget`, `SubexponentialSAT_SqrtLog_PerturbationBetaProgramLoop`, `SubexponentialSAT_SqrtLog_PerturbationBetaProgramStep`, `SubexponentialSAT_SqrtLog_PolynomialExecutorProgramBasic`, `SubexponentialSAT_SqrtLog_PolynomialExecutorProgramSource`, `SubexponentialSAT_SqrtLog_ProducedQueryRankProvenance`, `SubexponentialSAT_SqrtLog_ProducedQueryRankSchedule`, `SubexponentialSAT_SqrtLog_ReconstructionProgramLocalValue`, `SubexponentialSAT_SqrtLog_ReconstructionProgramModel`, `SubexponentialSAT_SqrtLog_ReconstructionProgramModelMiddle`, `SubexponentialSAT_SqrtLog_ReconstructionProgramReady`, `SubexponentialSAT_SqrtLog_ReconstructionProgramState`, `SubexponentialSAT_SqrtLog_SquarefreeProgramReplace`, `SubexponentialSAT_SqrtLog_SquarefreeScaleProgram`.
--
--   **Imports.** It imports the published bundle `Def_SubexponentialSAT`; the bundles `OAIQ081S100`, `OAIQ081S101`, `OAIQ081S102`, `OAIQ081S105`, `OAIQ081S107`, `OAIQ081S108`, `OAIQ081S109`, `OAIQ081S110`, `OAIQ081S111`, `OAIQ081S113`, `OAIQ081S114` and `OAIQ081S115` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ081S150`, `OAIQ081S151` and `OAIQ081S152`; the statements `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.AttainedSignatureProgram.Rescan.body_eval`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.AttainedSignatureProgram.Rescan.boundary_after_body`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.AttainedSignatureProgram.Rescan.candidate_stack_bound`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.AttainedSignatureProgram.Rescan.command_eval`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.AttainedSignatureProgram.Rescan.prepareKey_eval`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.AttainedSignatureProgram.Rescan.visits_exists`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.CodeChecks.graph_matrix_candidate_valid`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.DFSCountProgram.command_execution`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.DFSLoop.execute`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.DFSNative.normalized_loop`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.DFSVisit.body_refinement`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.SparsePriorityProgram.Selector.checkCandidate_eval`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.SparsePriorityProgram.Selector.command_eval`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.SparsePriorityProgram.Selector.familyInit_eval`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.SparseSelectorRefinement.selectCurrent_execution`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HashGreedyRound.scan_minimum`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HashGreedyScanSpace.rounds_halt_space`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HashGreedyScanSpace.scan_halt_space`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HashGreedyScanSpace.visits_space`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HeadEvaluationProgram.HeadGate.keyCall_eval`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HeadEvaluationProgram.StagedGate.bodyBudget_uniform`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighQueryLoop.add_rank`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighQueryLoop.advance_resources`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.LeafOuterNative.stageTrial_eval`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.Native.canonical_dfs_execution`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.ReconstructionNative.canonical_wide_read`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.ReconstructionSpace.reconstruct_run_space`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SignatureHeadLoader.shift_eval`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SignatureKeyNative.run`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SparseCodeSearch.core_runs`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.HashCircuitProgram.WeightedCore.command_eval`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutSourceExpression.typed_row_contract`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.MomentsProgram.Product.scalePhase_eval`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.PolynomialExecutorProgram.evaluate_correct`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.PolynomialExecutorProgram.evaluate_full`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.ReconstructionProgram.LocalValue.corrected_denote`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.ReconstructionProgram.Native.command_value`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.ReconstructionProgram.Native.middle_run`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.ReconstructionProgram.Native.program_correct` and `OAI.Algorithms.SubexponentialSAT.SqrtLog.Squarefree.Program.dictionaryReplace_trace`; the proofs of `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.AttainedSignatureProgram.Rescan.body_eval`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.AttainedSignatureProgram.Rescan.boundary_after_body`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.AttainedSignatureProgram.Rescan.candidate_stack_bound`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.AttainedSignatureProgram.Rescan.command_eval`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.AttainedSignatureProgram.Rescan.prepareKey_eval`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.AttainedSignatureProgram.Rescan.visits_exists`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.CodeChecks.graph_matrix_candidate_valid`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.DFSCountProgram.command_execution`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.DFSLoop.execute`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.DFSNative.normalized_loop`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.DFSVisit.body_refinement`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.SparsePriorityProgram.Selector.checkCandidate_eval`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.SparsePriorityProgram.Selector.command_eval`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.SparsePriorityProgram.Selector.familyInit_eval`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.SparseSelectorRefinement.selectCurrent_execution`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HashGreedyProgram.PadScore.leaf_eval`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HashGreedyRound.scan_minimum`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HashGreedyScanSpace.rounds_halt_space`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HashGreedyScanSpace.scan_halt_space`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HashGreedyScanSpace.visits_space`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HeadEvaluationProgram.HeadGate.keyCall_eval`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HeadEvaluationProgram.Specialization.raw_dictionary_runsIn`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HeadEvaluationProgram.StagedGate.bodyBudget_uniform`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighQueryCorrect.accepted`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighQueryCorrect.marked`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighQueryCount.run`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.LeafOuterNative.stageTrial_eval`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeHashQueries.accepted_replay`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeHashQueries.marked_replay`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.Native.canonical_dfs_execution`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.ReconstructionNative.canonical_wide_read`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.ReconstructionSpace.reconstruct_run_space`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SignatureHeadLoader.shift_eval`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SignatureKeyNative.run`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SparseCodeSearch.core_runs`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.HashCircuitProgram.WeightedCore.command_eval`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutSourceExpression.typed_row_contract`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.MomentsProgram.Dictionary.finish_eval`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.MomentsProgram.Product.scalePhase_eval`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.PolynomialExecutorProgram.evaluate_correct`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.PolynomialExecutorProgram.evaluate_full`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.ReconstructionProgram.LocalValue.corrected_denote`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.ReconstructionProgram.Native.command_value`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.ReconstructionProgram.Native.middle_run`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.ReconstructionProgram.Native.program_correct` and `OAI.Algorithms.SubexponentialSAT.SqrtLog.Squarefree.Program.dictionaryReplace_trace`.
-- source:
--   OpenAI, The Exponential Time Hypothesis is False, OpenAI Math Release, October 25, 2026, https://github.com/openai/math (result family 378; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/The-Exponential-Time-Hypothesis-is-False-October-25-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Algorithms at commit 7ef5c0c

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_SubexponentialSAT
import Definitions.Def_OAIQ081S100
import Definitions.Def_OAIQ081S101
import Definitions.Def_OAIQ081S102
import Definitions.Def_OAIQ081S105
import Definitions.Def_OAIQ081S107
import Definitions.Def_OAIQ081S108
import Definitions.Def_OAIQ081S109
import Definitions.Def_OAIQ081S110
import Definitions.Def_OAIQ081S111
import Definitions.Def_OAIQ081S113
import Definitions.Def_OAIQ081S114
import Definitions.Def_OAIQ081S115

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_HashGreedyProgram
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.MulticolorTypes.instFintypeJoint _root_.OAI.Algorithms.SubexponentialSAT.MulticolorTypes.instFintypeSide _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingModel.Data.fieldFintype
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


/-- Read the actual retained candidate and its full binary score. -/
def readEntry {r s : ℕ} (payload score : Fin s) (a : State r s) : BinaryArgmin.Entry :=
  ⟨a.stacks payload, a.stacks score⟩


namespace PadScore

open ModularPrograms ModularArithmetic

def data (regs : Fin 8 → Bool) (score shape : List Bool) : State 8 5 :=
  ⟨regs, ![score,shape,[],[],[]]⟩

end PadScore

namespace Initialize

open LeafOuterProgram

def resultStacks (a : Data) : Fin 896 → List Bool :=
  Function.update (Function.update (Function.update a.stacks 817 (a.stacks 773))
    780 (CounterNormalizeProgram.normalized (a.stacks 768)))
    781 (List.replicate (CounterPrograms.value (a.stacks 774)) true)

def coreCleared (a : Data) : Data :=
  ⟨readRegs a.regs 0 1 none, BankRoutines.clearBankStacks corePorts a.stacks⟩

def finishedStacks (a : Data) : Fin 896 → List Bool :=
  BankRoutines.clearBankStacks corePorts (Function.update a.stacks 818 (a.stacks 781))

def zeroWord (a : Data) : List Bool :=
  Encoding.encodeList id [List.replicate
    (CounterPrograms.value (a.stacks 817) * (a.stacks 780).length) false]

end Initialize

namespace NativeRound

def counter : CounterForPrograms.Ports 40 896 where
  register := ⟨![0,1,9], by decide⟩
  counter := 778
  scratch := 779
  counter_ne_scratch := by decide

/-- The four arithmetic scratch words and exhausted parser queue are empty at
candidate boundaries; retained best words are not part of this condition. -/
structure CoreClean (a : State 40 896) : Prop where
  scratch772 : a.stacks 772 = []
  scratch773 : a.stacks 773 = []
  scratch774 : a.stacks 774 = []
  scratch775 : a.stacks 775 = []
  queue776 : a.stacks 776 = []

def stored (a : State 40 896) (winner : BinaryArgmin.Entry) : Fin 896 → List Bool :=
  Function.update (Function.update (Function.update (Function.update a.stacks
    768 []) 769 []) 770 winner.payload) 771 winner.score

def appendedStacks (a : State 40 896) : Fin 896 → List Bool :=
  Function.update (Function.update (Function.update a.stacks 770 []) 771 []) 777
    (true :: (Encoding.frame (a.stacks 770).reverse ++ a.stacks 777))

def guardSet (a : State 40 896) : State 40 896 :=
  ⟨Function.update a.regs 9 true, a.stacks⟩

/-- One seed evaluation is paid before the full overflow-controlled scan.
The scan also visits zero; strict comparison makes the repeated seed harmless.
No exponential candidate list is present in the instruction sequence. -/
def round (mass : Cmd 40 896) : Cmd 40 896 :=
  .seq (attempt mass) (.seq install
    (.seq (ExecCNFTupleEnumeration.enumerate counter (body mass))
      (.seq append resetGuard)))

/-- Every primitive source-table prefix of a stage, including every stack.
The bound is uniform across calls; it contains no completed-visit counter. -/
structure StageSpace (command : Cmd 40 896) (steps : ℕ)
    (a : State 40 896) (bound : ℕ) : Prop where
  bound : ∀ k c, k ≤ steps →
    Trace (compiled command 778 777) k
      (a.withPC (some (compiled command 778 777).entry)) c →
    ∀ i, (c.stacks i).length ≤ bound

def rounds (mass : Cmd 40 896) : Cmd 40 896 := HashSelectProgram.rounds outer (round mass)

end NativeRound

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HashGreedyProgram
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_HashGreedyRound
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! Concrete streamed greedy rounds. The query seam below consists of actual
executions of the fixed attempt command; it must be instantiated by the native
exact-query implementation before an endpoint theorem can use these results. -/

namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HashGreedyRound

open BitProgram StructuredCalls SqrtLog
open HashGreedyProgram HashGreedyProgram.NativeRound

/-- Only the incumbent and two odometer ports vary across candidate boundaries.
The candidate/score ports are restored to the initial empty words. -/
structure Boundary (base : State 40 896) (B C : ℕ) (a : State 40 896) : Prop where
  frame : ∀ i : Fin 896, i ≠ 770 → i ≠ 771 → i ≠ 778 → i ≠ 779 →
    a.stacks i = base.stacks i
  fits : BinaryArgmin.Fits B C (readEntry 770 771 a)

/-- The history and remaining unary count are the only words changed by outer
round control. All other retained parameters keep their literal contents. -/
structure RowBoundary (base : State 40 896) (rows : List (List Bool))
    (a : State 40 896) : Prop where
  frame : ∀ i : Fin 896, i ≠ 777 → i ≠ 781 → a.stacks i = base.stacks i
  history : a.stacks 777 = encodedHistory rows

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HashGreedyRound
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

variable {X Row : Type*} [Fintype X] {m : ℕ}


open LeafOuterProgram

def references : Cmd 40 896 := .seq (route (782,0))
  (liftCommand LeafOuterNative.References.command 0 7 referenceRegisters referenceStacks)

open scoped BigOperators

/-- One fixed mass command generates all clause references, folds the actual
marked query over them, canonicalizes the aggregate, and hands it to769. -/
def mass (query : Code) : Code := .seq references (.seq (.call (program query)) finish)


end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HashMassAdapter
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

def trialStaged (a : Data) : Data := prefixed (finalStaged a)
def stageTrialCost (a : Data) : ℕ := stageFinalCost a+prefixCost (finalStaged a)

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.LeafOuterNative
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_HashMassStaged
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! Paid physical source assembly precedes all marked queries. The candidate
is prepended to a copied history stream; neither retained word is changed.
The temporary source masters are cleared after the complete natural mass. -/
namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HashMassStaged

open BitProgram StructuredCalls RecordPrograms SqrtLog LeafProgram LeafOuterProgram
open HashMassAdapter

def command (query : Cmd 40 896) : Cmd 40 896 :=
  .seq LeafOuterNative.stageTrial (.seq (mass query) cleanup)

def stagingBudget (a : State 40 896) : ℕ :=
  LeafOuterNative.stageTrialCost a + cleanupCost (LeafOuterNative.trialStaged a)

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HashMassStaged
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_AcceptedQueryStage
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! The accepted query physically receives the saved history, without a trial
candidate prefix. All routing, scratch reset and source reclamation are paid
commands. The query is composed through its actual evaluation and prefix proof. -/
namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.AcceptedQueryStage

open BitProgram StructuredCalls StackRoutines
open OAI.Algorithms.SubexponentialSAT.SqrtLog LeafOuterProgram

def stage : Cmd 40 896 := .seq clearTemporary LeafOuterNative.stageFinal

/-- Reuse the six-port reclamation shared with the marked mass adapter. -/
def cleanup : Cmd 40 896 := .seq clearTemporary HashMassStaged.cleanup

def command (query : Cmd 40 896) : Cmd 40 896 := .seq stage (.seq query cleanup)

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.AcceptedQueryStage
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_AttainedSignatureProgram
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-!
# Native full-key computation for the resumable attained-signature scan

One invocation preserves the assignment and all raw integer constraint rows.
Its local polynomial-time bound controls every scratch stack at every source
prefix. The generator retains candidate and predecessor cursors separately.
-/

namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.AttainedSignatureProgram

open OAI.Algorithms.SubexponentialSAT.BitProgram OAI.Algorithms.SubexponentialSAT.StructuredCalls OAI.Algorithms.SubexponentialSAT.Subexp.MatrixProgramSupport
open OAI.Algorithms.SubexponentialSAT.SqrtLog.BucketProgram

def command : Code :=
  .seq (copy 15 13 11)
    (.call (ProgramLinking.liftProgram signatureProgram id signaturePorts))

def program := compiled command 12 14

namespace Rescan

def keyCall : Code := .call (ProgramLinking.liftProgram
  AttainedSignatureProgram.program signatureRegisters signatureStacks)

def equalityCall : Code := .call (ProgramLinking.liftProgram
  KeyEquality.program equalityRegisters equalityStacks)

def clear (i : Fin 24) : Code := .call (StackRoutines.clearProgram i 0 1)
def copy (i j : Fin 24) : Code := .call (StackRoutines.copyProgram i j 21 0 1)

def storeFresh (b : Bool) : Code := .seq (clear 22)
  (.base (.seq (.atom (.set 0 b)) (.atom (.push 22 0))))

/-- Reject only a duplicate full key; keep scanning to charge and complete all
predecessor work independently of success. -/
def updateFresh : Code := .ite 4 (storeFresh false) (.base .skip)

/-- One predecessor is processed by actual full-signature and byte-equality
programs; the assignment counter is incremented only after all scratch is free. -/
def body : Code :=
  .seq (copy 18 12) (.seq keyCall (.seq equalityCall
    (.seq updateFresh (.seq (clear 12) (.seq (clear 14)
      (Counters.incrementCmd predecessorPorts))))))

end Rescan

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.AttainedSignatureProgram
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_AttainedSignatureRescan
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! Actual bounded-word predecessor rescan and its uniform source-prefix storage. -/

namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.AttainedSignatureProgram

open OAI.Algorithms.SubexponentialSAT.BitProgram OAI.Algorithms.SubexponentialSAT.StructuredCalls OAI.Algorithms.SubexponentialSAT.Subexp.MatrixProgramSupport
open OAI.Algorithms.SubexponentialSAT.SqrtLog.BucketProgram

namespace Rescan

def setup : Code := .seq (copy 16 19) (storeFresh true)

def cleanup : Code := .seq (clear 18) (.call (StackRoutines.transferProgram 19 18 0 1))

/-- The candidate word supplies the binary predecessor count. Its width is h;
the final zero countdown word resets the predecessor without a family table. -/
def command : Code := .seq setup
  (.seq (CounterForPrograms.forCmd countdownPorts body) cleanup)

/-- Compute the candidate's whole key once and retain it through the rescan. -/
def prepareKey : Code := .seq (copy 16 12) (.seq keyCall
  (.seq (copy 14 17) (.seq (clear 12) (clear 14))))

def candidateCommand : Code := .seq prepareKey command

def candidateProgram := compiled candidateCommand 16 22


end Rescan

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.AttainedSignatureProgram
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

/-- The core is on stack 8, clause on 9, and exact binary width on 10.
All eight work stacks are empty at both boundaries; register 12 receives the result. -/
def command : Cmd 13 11 :=
  .seq copyClause (.seq width (.seq (.base (.atom (.copy 12 4)))
    (.seq subset (.base (.atom (.band 12 12 9))))))

end Guard

namespace Filter

def guard : Cmd 16 14 := liftCommand Guard.command 9 9 guardReg guardStack

def callback : Cmd 16 14 := .seq (transfer 13 9) (.seq guard
  (.seq (.base (.atom (.copy 15 12))) (.seq (transfer 9 13) emit)))

def scan : Cmd 16 14 := RecordPrograms.iterate ports callback

def command : Cmd 16 14 := .seq startOutput scan


end Filter

namespace Selector

def filterCall : Code := liftCommand Filter.command 11 12 (Fin.castAdd 8) filterStack

def checkCandidate : Code :=
  .seq (copy 18 10) (.seq filterCall (.seq (copy 12 5) thresholdCall))

def testedCandidate (mask : List Bool) : Code :=
  .seq (prepareCandidate mask)
    (.seq (.ite 4 (.seq checkCandidate retainCandidate)
      (.seq (clear 9) (atom (.set 23 false)))) resetCandidateFlags)


def candidate (mask : List Bool) : Code := testedCandidate mask

def familyInit (width : List Bool) : Code :=
  .seq (load 9 [false]) (.seq (load 16 width) (.seq (copy 13 10)
    (.seq filterCall (.seq (clear 9) (move 12 18)))))


def phase (width coreSize : ℕ) (mask : List Bool) : Code :=
  .seq (familyInit width.bits)
    (.seq (parameterInit (width - coreSize) coreSize.bits)
      (.seq (RecordPrograms.iterate ports (candidate mask)) cleanup))

/-- One finite ordinary Boolean-stack program for each fixed width bound.
The outstanding proof obligations concern this concrete code, not an oracle callback. -/
def command (k : ℕ) : Code :=
  .seq (atom (.set 23 false))
    (chain ((passes k).map fun p => phase p.1 p.2.1 p.2.2))

def program (k : ℕ) := compiled (command k) 13 12

end Selector

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.SparsePriorityProgram
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

def selectCurrent (k : ℕ) : Code :=
  .call (ProgramLinking.liftProgram (SparsePriorityProgram.Selector.program k)
    (registers 24 (by decide)) selectorStack)

/-- `leaf` includes the actual charged leaf loaders, computation, result
export to stack263, and cleanup. It must preserve the persistent outer frame. -/
def body (k : ℕ) (leaf : Code) : Code :=
  .seq popCurrent
    (.seq (selectCurrent k)
      (.seq (.ite 23 branch (.seq leaf accumulate)) finishVisit))

def loop (k : ℕ) (leaf : Code) : Code := .while 2 (body k leaf)


end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.SparseDFSProgram
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_DisjointReuse_DFSCountProgram
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! Concrete count command including startup and physical full-word export.
The actual positivity suffix is appended by the shared native integration.
-/
namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.DFSCountProgram

open BitProgram StructuredCalls SparseDFSProgram SparseDFSRefinement DFSVisit
variable {n : ℕ}

def command (k : ℕ) (leaf : Code) : Code :=
  .seq DFSStartup.startup (.seq (loop k leaf) exportCount)

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.DFSCountProgram
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_SquarefreeProgramReplace
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Actual dictionary replacement: delete all old matching keys, then prepend
one supplied coefficient. This is the storage phase of additive insertion;
the coefficient addition itself is a separately measured ring operation. -/
namespace SubexponentialSAT.SqrtLog.Squarefree.Program
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls

def keepCoefficient (d : StorageData) (coeff : List Bool) : ReplaceData :=
  ⟨d.regs, ![d.stacks 0,d.stacks 1,d.stacks 2,d.stacks 3,d.stacks 4,d.stacks 5,d.stacks 6,coeff]⟩

def replaceData (regs : Fin 5 → Bool) (entries : List ByteRecord) (query coeff : List Bool) : ReplaceData :=
  keepCoefficient (eraseData regs (rawEntries entries) query [] []) coeff.reverse

def replaceDone (regs : Fin 5 → Bool) (output : List Bool) : ReplaceData :=
  keepCoefficient (eraseData regs [] [] output []) []

end SubexponentialSAT.SqrtLog.Squarefree.Program

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_SquarefreeScaleProgram
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Base stage. -/
/-! Fixed physical ABI for scaling all coefficients in a sparse dictionary.
The low 32 stacks are the common coefficient-ring service. The eight high
stacks hold source, reversed output, scalar, key, coefficient staging, frame
staging, final output, and a preserved copy of the unary degree. -/

namespace SubexponentialSAT.SqrtLog.Squarefree.ScaleProgram

open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.StackRoutines

def state (regs : Fin 8 → Bool) (s : Store) : Data := ⟨regs, tapes s⟩

def copied (d : Data) (src dst : Fin 40) : Data :=
  ⟨readRegs d.regs 0 1 none, copyStacks src dst d.stacks⟩

end SubexponentialSAT.SqrtLog.Squarefree.ScaleProgram

/-! Moves stage. -/

/-! Emit stage. -/

/-! Native stage. -/
namespace SubexponentialSAT.SqrtLog.Squarefree.ScaleProgram
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls
open SubexponentialSAT.SubexpLiftRing SubexponentialSAT.SubexpQuarticRing

def environment (p t : ℕ) [Fact p.Prime] (M : SubexpPreparedQuartic.Modulus p t)
    (cache : RingProgram.ScalarCache p t) {d : ℕ}
    (table : Fin d → Fin d → Fin d → Word (baseWidth p t))
    (scalar : RingProgram.Code (Word (baseWidth p t)) d) (degree width : List Bool) : Environment :=
  ⟨M.bits, width, cache.zero.val, RingTriple.tableEncoding table, RingProgram.flat scalar, degree⟩

end SubexponentialSAT.SqrtLog.Squarefree.ScaleProgram

/-! Loop stage. -/

/-! Cost stage. -/

/-! Semantics stage. -/

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_PolynomialExecutorProgramBasic
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Executable coefficient-array meaning of the row postfix interpreter.
Literal padding and all arithmetic operate on stored coefficient words. -/
namespace SubexponentialSAT.SqrtLog.PolynomialExecutorProgram
open SubexponentialSAT.SubexpSymbolicCost

def addValue {C : Type*} (ops : RingProgram C) (P Q : List C) : List C :=
  (SubexponentialSAT.SubexpDensePolynomial.addProgram ops P Q).1

def mulValue {C : Type*} (ops : RingProgram C) (J : ℕ) (P Q : List C) : List C :=
  DensePolynomialProgram.result ops J P Q

def loadValue {C : Type*} (ops : RingProgram C) (J : ℕ) (P : List C) : List C :=
  SubexponentialSAT.SubexpDensePaddingSpec.padCells ops.zeroRun.1 J P

def evaluate {C : Type*} (ops : RingProgram C) (J : ℕ)
    (e : SubexponentialSAT.Algorithm.Expr (List C)) : List C :=
  SubexponentialSAT.SubexpDensePaddingSpec.evalWith (loadValue ops J) (addValue ops) (mulValue ops J) e

end SubexponentialSAT.SqrtLog.PolynomialExecutorProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_PolynomialExecutorProgramSource
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! The physical row-source emitter's bytes are exactly the input accepted by
the generic coefficient-array interpreter. Scalar literals are single cells;
the formal variable has the two-cell representation [zero, one]. -/
namespace SubexponentialSAT.SqrtLog.PolynomialExecutorProgram
open SubexponentialSAT SubexpSymbolicCost
open SubexponentialSAT.Subexp.UniversalRowProgram

def sourceExpr {C : Type*} (ops : RingProgram C) (r : Row C) : Algorithm.Expr (List C) :=
  letI : Zero (List C) := ⟨[ops.zeroRun.1]⟩
  letI : One (List C) := ⟨[ops.oneRun.1]⟩
  rowExpression [ops.zeroRun.1,ops.oneRun.1] (mapRow (fun c => [c]) r)

end SubexponentialSAT.SqrtLog.PolynomialExecutorProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_PerturbationAssemblyScan
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Fixed native traversal of the actual runtime-framed row list. -/
namespace SubexponentialSAT.SqrtLog.PerturbationAssembly
open SubexponentialSAT BitProgram StructuredCalls SubexpConvolutionControl SubexpScanPrimitives

def rowPorts : UnaryForPrograms.Ports 16 256 := ⟨231,0,1⟩
def rowLoop (body : Code) : Code := UnaryForPrograms.forCmd rowPorts body

/-- Masters205/212 are copied, scanned and retained. Only dictionary217 changes. -/
def scanRows (body : Code) : Code := .seq (copy 205 230) (.seq (copy 212 231)
  (.seq (rowLoop body) (.seq (clear 230) (clear 218))))


end SubexponentialSAT.SqrtLog.PerturbationAssembly

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_PerturbationAssemblyConstants
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Paid construction of the polynomial Horner point and seed. -/
namespace SubexponentialSAT.SqrtLog.PerturbationAssembly
open SubexponentialSAT BitProgram StructuredCalls SubexpConvolutionControl SubexpPolynomialConstructor
open DensePolynomialProgram (Coeff)
open DensePolynomialProgram.Constructor

/-- Any protected cache can be replaced while its old value is preserved in a
fresh high backup port. Both copies are ordinary finite tape programs. -/
def saveReplace (src dst backup : Fin 256) : Code :=
  .seq (copy dst backup) (CRTLocalProgram.replace src dst)

/-- Restoring a protected cache consumes the backup and clears the new value. -/
def restoreCache (dst backup : Fin 256) : Code := .seq (clear dst) (move backup dst)

end SubexponentialSAT.SqrtLog.PerturbationAssembly

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_PerturbationAssemblyTarget
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Dynamic target-jet cache installation. Full source-degree metadata at210
is untouched while the arithmetic count is temporarily changed to213. -/
namespace SubexponentialSAT.SqrtLog.PerturbationAssembly
open SubexponentialSAT BitProgram StructuredCalls SubexpConvolutionControl
open DensePolynomialProgram.Constructor

/-- Restore all three original caches and release the point and scalar zero. -/
def finishTarget : Code := .seq (restoreCache 192 236)
  (.seq (restoreCache 193 237) (.seq (restoreCache 243 238)
    (.seq (clear 247) (clear 254))))


end SubexponentialSAT.SqrtLog.PerturbationAssembly

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_PerturbationBetaProgramStep
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.PerturbationBetaProgram
open SubexponentialSAT BitProgram StructuredCalls SubexpConvolutionControl
open SubexpScanPrimitives SubexpLiftRing SubexpQuarticRing
open CRTLocalProgram (LowFrame lowFrame_update lowFrame_refl)

abbrev Coeff (t d : ℕ) := RingProgram.Code (RingProgram.ScalarCode 3 t) d

def rowsBits {t d : ℕ} (rows : List (List (Coeff t d) × Bool)) : List Bool :=
  Encoding.encodeList (HornerProgram.encodePolynomial RingProgram.flat) (rows.map Prod.fst)

def ready {t d : ℕ} (base : Store) (rows : List (List (Coeff t d) × Bool))
    (acc : Coeff t d) : Store :=
  Function.update (Function.update (Function.update base 230 (rowsBits rows))
    231 (rows.map Prod.snd)) 220 (RingProgram.flat acc)

end SubexponentialSAT.SqrtLog.PerturbationBetaProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_PerturbationBetaProgramLoop
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Paid outer traversal. Every row frame and matching assignment bit is
consumed; selected rows call the actual scalar Horner and addition programs. -/
namespace SubexponentialSAT.SqrtLog.PerturbationBetaProgram
open SubexponentialSAT BitProgram StructuredCalls SubexpConvolutionControl
open SubexpScanPrimitives SubexpLiftRing SubexpQuarticRing

def peekReady {t d : ℕ} (regs : Fin 16 → Bool) (base : Store)
    (rows : List (List (Coeff t d) × Bool)) (acc : Coeff t d) : Data :=
  ⟨readRegs regs 0 1 (rowsBits rows).head?,ready base rows acc⟩

end SubexponentialSAT.SqrtLog.PerturbationBetaProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_PerturbationAssemblyPreparation
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Executable incidence preparation. The inner worker has no arithmetic,
mask, beta, shifted-polynomial or dictionary oracle. Source generation is
composed as a fixed command in the outer768-stack frame. -/
namespace SubexponentialSAT.SqrtLog.PerturbationAssembly
open SubexponentialSAT BitProgram StructuredCalls SubexpConvolutionControl SubexpPolynomialConstructor

/-- The lower source generator consumes the bare original ID on233. The
interpreter table key215 contains the same ID with its unary terminator. -/
def makeLiteralKey : Code := .seq (Subexp.TupleProgram.pushConst 215 0 false) (copy 233 215)

end SubexponentialSAT.SqrtLog.PerturbationAssembly

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_PerturbationAssemblyLow
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Closed low-variable incidence preparation from physical coefficient rows.
Beta evaluation, point construction, polynomial Horner, sparse emission, and
cache restoration are all performed by fixed finite commands. -/
namespace SubexponentialSAT.SqrtLog.PerturbationAssembly
open SubexponentialSAT BitProgram StructuredCalls SubexpConvolutionControl
open DensePolynomialProgram
open SubexponentialSAT.SubexpSymbolicCost SubexponentialSAT.SubexpLiftRing SubexponentialSAT.SubexpQuarticRing

def lowBudget (s : Store) (n N J t d : ℕ) : ℕ :=
  PerturbationBetaProgram.runBudget s n N t d + (33*n+20*(d*baseWidth 3 t)+83) +
    targetBudget s J (d*baseWidth 3 t) +
    (7*(s 205).length+9*n+n*(nativeRowBudget N J n (d*baseWidth 3 t)
      (nativeMulBudget J d (baseWidth 3 t)) (AddService.budget d (baseWidth 3 t) J J)+2)+20) +
    (2*(2*(J*(d*baseWidth 3 t))+2*J+d*baseWidth 3 t)+
      6*((s 192).length+(s 193).length+(s 243).length)+33) +
    (2*(d*baseWidth 3 t)+3)

def pairedRows {B d N : ℕ} (rows : List (Fixed.Array B d N × Bool)) :
    List (List (Coeff B d) × Bool) := rows.map (fun row => (row.1.val,row.2))

end SubexponentialSAT.SqrtLog.PerturbationAssembly

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_PerturbationAssemblyOuter
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Relocation and the finite total-variable table traversal. -/
namespace SubexponentialSAT.SqrtLog.PerturbationAssembly
open SubexponentialSAT BitProgram StructuredCalls SubexpConvolutionControl SubexpScanPrimitives

attribute [local simp] Fin.coe_ofNat_eq_mod

def tableRecord (payload : ℕ → List Bool) (j : ℕ) : List Bool :=
  Encoding.frame (Encoding.encodeNat j) ++ Encoding.frame (payload j)

def tableResult (payload : ℕ → List Bool) : ℕ → List Bool → List Bool
  | 0,acc => acc
  | n+1,acc => tableResult payload n (tableRecord payload n ++ acc)

end SubexponentialSAT.SqrtLog.PerturbationAssembly

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_FactorArithmeticProgram
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! Fixed arithmetic commands used by the specialized assignment evaluator.
Their execution and Good-empty support bounds are proved separately. -/
namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FactorEvaluationSpace
open OAI BitProgram StructuredCalls SqrtLog SqrtLog.LeafProgram
noncomputable section

def markedArithmetic : Cmd 40 768 :=
  .seq Clause.caller (.seq (Factor.clear 62) Factor.accumulate)

end
end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FactorEvaluationSpace
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

def setupLocalCost (a : State 16 768) : ℕ :=
  clearManyCost cachePorts a + LeafNodeCacheProgram.localBudget (cacheStart a)

def setupCost (a : Data) : ℕ :=
  setupLocalCost (projectState localRegister lowStack a) + 1

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

namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HeadEvaluationProgram.Subset
open OAI BitProgram StructuredProgram

def data (r : Fin 5 → Bool) (mask query saved : List Bool) : State 5 3 :=
  ⟨r,![mask,query,saved]⟩

def ready (r : Fin 5 → Bool) (mask query saved : List Bool) : State 5 3 :=
  data (readRegs r 0 1 mask.head?) mask query saved

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HeadEvaluationProgram.Subset

/-! The dictionary framing, key rewrite and record traversal follow the actual
MomentsProjectionProgramNative implementation. The replacement comparator tests
support inclusion, so this scan implements evaluation at a Boolean correction
assignment. Numeric-key collisions are intentionally left for normalization. -/
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_QueryProducerSpace
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! Immediate Boolean specialization followed by the actual additive dictionary
normalizer. The input is a polynomial-size origin/singleton incidence stream;
no multivariate product is materialized before specialization. -/

namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryProducerSpace

open OAI BitProgram StructuredCalls
open OAI.Algorithms.SubexponentialSAT.SqrtLog OAI.Algorithms.SubexponentialSAT.SubexpLiftRing OAI.Algorithms.SubexponentialSAT.SubexpQuarticRing
open MomentsProgram TruncatedRingProgram
open scoped BigOperators

def scanCall : Cmd 8 38 :=
  .call (ProgramLinking.liftProgram HeadEvaluationProgram.Specialization.program
    scanRegisters scanPorts)

def handoff : Cmd 8 38 :=
  .seq (.call (StackRoutines.transferProgram 37 36 0 1))
    (.call (StackRoutines.transferProgram 36 27 0 1))

def normalizeCall : Cmd 8 38 :=
  .call (ProgramLinking.liftProgram Normalize.program id normalizePorts)

def command : Cmd 8 38 := .seq scanCall (.seq handoff normalizeCall)

def program := compiled command 28 15

/-- The public producer takes separate forward raw dictionary and mask words;
the escaped prefix is constructed by actual stack instructions. -/
def prepare : Cmd 8 38 :=
  .seq (.call (StackRoutines.transferProgram 29 35 0 1)) (.base framer)

/-- The public producer includes the physical framing loop in its fixed code. -/
def preparedCommand : Cmd 8 38 := .seq prepare (.call program)

def preparedProgram := compiled preparedCommand 28 15

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryProducerSpace
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

def loadCommand : Cmd 16 294 :=
  .seq (copyMany 292 loadPairs)
    (.seq (.call (StackRoutines.transferProgram 217 292 0 1))
      (.call (StackRoutines.transferProgram 292 284 0 1)))

def outputMove : Cmd 16 294 :=
  .seq (.call (StackRoutines.transferProgram 271 292 0 1))
    (.call (StackRoutines.transferProgram 292 217 0 1))

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

def copy (src dst : Fin 896) : Code :=
  .call (StackRoutines.copyProgram src dst 159 0 1)

def clear (src : Fin 896) : Code := .call (StackRoutines.clearProgram src 0 1)

def move (src dst : Fin 896) : Code := .seq (copy src dst) (clear src)

def clearCallbackLocal : Cmd 16 768 := clearMany callbackScratch

def clearCallback : Code := liftCommand clearCallbackLocal 149 149 localRegister lowStack

def returnToRecords : Code :=
  .seq (.base (.atom (.set 13 false)))
    (.seq (.base (.atom (.set 14 true))) (.base (.atom (.set 15 false))))

end
end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FactorAssignmentProgram
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_PerturbationAssemblyLowBounds
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Explicit polynomial cost of the complete low-variable producer. Incoming
cache size is charged even when the source and target cutoffs differ. -/
namespace SubexponentialSAT.SqrtLog.PerturbationAssembly
open SubexponentialSAT BitProgram StructuredCalls SubexpConvolutionControl
open DensePolynomialProgram SubexponentialSAT.SubexpSymbolicCost SubexponentialSAT.SubexpLiftRing SubexponentialSAT.SubexpQuarticRing

def lowWorkPolynomial (n N J t d E : ℕ) : ℕ :=
  let B := baseWidth 3 t
  let W := d*B
  1000000*(n+1)*(N+1)*(d+1)^3*(B+1)^2 + (33*n+20*W+83) +
  (9*E+14*J+9*(J*W)+7*W+440*(J+1)*(W+1)+47) +
  (7*(n*(2*(N*W)+2)+1)+9*n+n*(rowWorkPolynomial N J n d B+2)+20) +
  (2*(2*(J*W)+2*J+W)+6*E+33) + (2*W+3)

end SubexponentialSAT.SqrtLog.PerturbationAssembly

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_PerturbationAssemblyRelInput
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Common physical input invariant, independent of whichever exact source
arrays are returned by the next native source execution. -/
namespace SubexponentialSAT.SqrtLog.PerturbationAssembly
open SubexponentialSAT BitProgram StructuredCalls DensePolynomialProgram SubexpConvolutionControl
open SubexponentialSAT.SubexpSymbolicCost SubexponentialSAT.SubexpLiftRing SubexponentialSAT.SubexpQuarticRing
attribute [local simp] Fin.coe_ofNat_eq_mod

def pairChoice {B d N : ℕ} (xs : List (Fixed.Array B d N)) (choice : List Bool) := xs.zip choice

theorem pairChoice_length {B d N : ℕ} (xs : List (Fixed.Array B d N)) (choice : List Bool)
    (h : xs.length=choice.length) : (pairChoice xs choice).length=xs.length := by
  simp [pairChoice,List.length_zip,h]

end SubexponentialSAT.SqrtLog.PerturbationAssembly

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_PerturbationAssemblySourceCall
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! The actual literal-loop call changes only its key, index and accumulated
table. All physical source masters and blank working cells are preserved. -/
namespace SubexponentialSAT.SqrtLog.PerturbationAssembly
open SubexponentialSAT BitProgram StructuredCalls
open SubexponentialSAT.SubexpLiftRing SubexponentialSAT.SubexpQuarticRing
attribute [local simp] Fin.coe_ofNat_eq_mod

def sourceCallData (s : OuterStore) (j : ℕ) (acc : List Bool) (regs : Fin 16 → Bool) : OuterData :=
  ⟨regs,Function.update (literalReady s (List.replicate j true) acc) 555 (Encoding.encodeNat j)⟩

end SubexponentialSAT.SqrtLog.PerturbationAssembly

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_FactorTableSpecialization
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! Proof-side correctness of the unchanged immediately specialized incidence
call. Operational command definitions remain in FactorTableProgram. -/
namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FactorTableProgram
open OAI.Algorithms.SubexponentialSAT.SqrtLog
open OAI BitProgram StructuredCalls SubexpConvolutionControl SubexpScanPrimitives
open SubexpPolynomialConstructor PerturbationAssembly OAI.Algorithms.SubexponentialSAT.SubexpLiftRing

attribute [local simp] Fin.coe_ofNat_eq_mod

def specializeBudget (t d u J N n count rawLength : ℕ)
    (low : Fin 256 → List Bool) : ℕ :=
  QueryProducerSpace.Native.combinedBudget
    (PerturbationAssembly.lowWorkPolynomial n N J t d
      ((low 192).length + (low 193).length + (low 243).length))
    ((low 194).length + (low 202).length + (low 204).length)
    rawLength n (baseWidth 3 t) d u J count

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FactorTableProgram
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_FactorTableNative
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! Physical source preparation for the specialized factor table. The old
master-word argument is generalized to the actually selected unary factor,
then transported through the fixed protected-port embedding. -/
namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FactorTableNative
open OAI BitProgram StructuredCalls SubexpLiftRing SubexpQuarticRing
open OAI.Algorithms.SubexponentialSAT.SqrtLog OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgram
open PerturbationAssembly LayoutProgram SubexpSetupStorage DensePolynomialProgram
open OAI.Algorithms.SubexponentialSAT.Subexp OAI.Algorithms.SubexponentialSAT.Subexp.ConstructivePacking OAI.Algorithms.SubexponentialSAT.MulticolorTypes
attribute [local simp] Fin.coe_ofNat_eq_mod

variable {r Q d n J S f : ℕ}
  {ps : List (ℕ × ℕ)}
  {P : PackingData (Fin ps.length) (UniversalType r Q 1)}
  {a : SourceReady.Data}

def specializedWorkPolynomial (t d u J N n S : ℕ) : ℕ :=
  3200000 * (lowWorkPolynomial n N J t d (3*S) + 3*S +
    specializedRawBound n u J (baseWidth 3 t) d + n + baseWidth 3 t + d + u + J +
    (1+n*(J-1)) + 1)^10

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FactorTableNative
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_FactorAssignmentLoop
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! Relational execution of the fixed specialized factor-record loop. This
adapts the original FactorLoop reader/while proof to the shared 896-stack ABI
and empty-support dictionaries. The explicit callback premise must be proved
for the actual callback before this component can close an algorithm endpoint. -/
namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FactorAssignmentLoop
attribute [local simp] Fin.coe_ofNat_eq_mod
open OAI BitProgram StructuredCalls SqrtLog SqrtLog.LeafProgram MomentsProgram

def productBudget (n B d u J C : ℕ) (ids : List ℕ) : ℕ :=
  7*(ProgramEncoding.encodeRecords (records ids)).length+
    16*byteBound n B d u J+loopBudget C ids+18

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FactorAssignmentLoop
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

def ports : UnaryForPrograms.Ports 3 2 := ⟨0,0,1⟩

def body : Cmd 3 2 :=
  .ite 0 (.base .skip) (.base (.atom (.push 1 2)))

def command : Cmd 3 2 :=
  .seq (.base (.atom (.set 2 true))) (UnaryForPrograms.forCmd ports body)

def program := compiled command 0 1

end CountFalse


open SubexpSetupStorage
abbrev Command := Cmd 16 896

def countCommand : Command :=
  isolated CountFalse.program countRegister countStack 329 scratch [(338,325)] [(326,832)]

def setupCommand : Command :=
  .seq countCommand (.seq (clearMany [833,834,835]) (copyCmd 243 833 329))

def setupCaller : Cmd 40 896 := liftCommand setupCommand 338 832 callerRegister id

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.PairNativeSetup
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

abbrev Code := Cmd 40 896

def clearOne (i : Fin 896) : Code := .call (StackRoutines.clearProgram i 0 1)

def clearMany : List (Fin 896) → Code
  | [] => .base .skip
  | i :: is => .seq (clearOne i) (clearMany is)

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

abbrev Code := Cmd 40 896

def transfer (src dst : Fin 896) : Code := .call (StackRoutines.transferProgram src dst 0 1)

def append : Code := .seq (transfer 863 89) (.seq (transfer 862 89) (transfer 89 863))

def copy (src dst : Fin 896) : Code := .call (StackRoutines.copyProgram src dst 89 0 1)

def prepare : Code := .seq (NodeReadoutSpace.clearMany [89,5,12,39])
  (.seq (copy 194 5) (.seq (copy 202 12) (copy 204 39)))

/-- Final paid handoff from the complete interpolation stream to the actual CRT
jet input. Two transfers retain the byte order. -/
def handoff : Code := .seq (NodeReadoutSpace.clearOne 265)
  (.seq (transfer 863 89) (transfer 89 265))

def handoffProgram := compiled handoff 863 265

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NodeAppendSpace
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_HighQueryAdapter
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.FiniteField.fieldFintype _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingModel.Data.fieldFintype
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

/-- Durable outer high counter and exact-count accumulator. Query reconstruction
returns its whole conditioned count on323, which the real adder consumes. -/
def highPorts : LeafBranchProgram.Ports 40 896 where
  counter := {
    register := ⟨fun i => ⟨19+i.val,by omega⟩,
      by intro i j h; apply Fin.ext; simpa using congrArg Fin.val h⟩
    counter := 789
    scratch := 790
    counter_ne_scratch := by decide }
  mass := {
    register := Fin.castAdd 32
    stack := ![788,323,791]
    register_injective := Fin.castAdd_injective 8 32
    stack_injective := by decide }
  disjoint_counter := by decide
  disjoint_scratch := by decide

open OAI.Algorithms.SubexponentialSAT.StackRoutines


end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighQueryAdapter
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_QueryProgram
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! Concrete bit primitives for streamed finite-difference queries. -/
namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryProgram

open OAI BitProgram
open scoped BigOperators

open StructuredCalls

def scanCall {s : ℕ} (src : Fin s) : Cmd 3 s :=
  .call (ProgramLinking.liftProgram parityProgram id (fun _ => src))

/-- Finite table for the sign of a streamed pair. Both masks are preserved;
only one scan buffer and one copy temporary are needed. -/
def pairSign : Cmd 3 4 :=
  .seq (.base (.atom (.set 2 false)))
    (.seq (.call (StackRoutines.copyProgram 0 2 3 0 1))
      (.seq (scanCall 2)
        (.seq (.call (StackRoutines.copyProgram 1 2 3 0 1))
          (.seq (scanCall 2) (.base (.atom (.push 2 2)))))))

def pairSignProgram := compiled pairSign 0 2

def pairSignCall : Cmd 40 896 :=
  .call (ProgramLinking.liftProgram pairSignProgram pairRegisters pairStacks)

section SignedArray

attribute [local simp] Fin.coe_ofNat_eq_mod

open OAI.Algorithms.SubexponentialSAT.SqrtLog OAI.Algorithms.SubexponentialSAT.SubexpLiftRing OAI.Algorithms.SubexponentialSAT.SubexpQuarticRing
open MomentsProgram TruncatedRingProgram

/-- A positive sign transfers unchanged bytes; a negative sign invokes the
original actual ternary scalar multiplier with its cached negative unit. -/
def signedScale : Cmd 8 41 :=
  .seq (.base (.atom (.peek 40 6 7)))
    (.ite 6 (.call (ProgramLinking.liftProgram Squarefree.ScaleProgram.program id scalePorts))
      (.seq (.call (StackRoutines.transferProgram 32 33 0 1))
        (.call (StackRoutines.transferProgram 33 38 0 1))))

def signedScaleProgram := compiled signedScale 32 38

/-- One actual signed finite-difference term is added to the retained node
array. Neither call constructs a support family or an assignment product. -/
def signedAccumulate : Cmd 40 896 :=
  .seq (.call (ProgramLinking.liftProgram signedScaleProgram leafArithmeticRegs leafScalePorts))
    (.call (ProgramLinking.liftProgram Normalize.program leafArithmeticRegs leafNormalizePorts))

/-- Update the node accumulator for a completed pair and clear its sign cell
before the next pair. The pair masks themselves are read and restored. -/
def pairUpdate : Cmd 40 896 :=
  .seq pairSignCall (.seq signedAccumulate (.base (.atom (.pop 848 0 1))))

end SignedArray

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryProgram
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

def candidatePorts : CounterForPrograms.Ports 40 896 where
  register := Fin.castLEEmb (by decide)
  counter := tupleStacks 2
  scratch := tupleStacks 10
  counter_ne_scratch := by decide

def remainingPorts : CounterForPrograms.Ports 40 896 where
  register := Fin.castLEEmb (by decide)
  counter := tupleStacks 7
  scratch := tupleStacks 5
  counter_ne_scratch := by decide

/-- One actual candidate advance. There is no construction of an assignment
list: both the cursor and remaining count are binary words. -/
def advanceCommand : Cmd 40 896 :=
  .seq (Counters.incrementCmd candidatePorts)
    (.seq (CounterForPrograms.advanceCmd remainingPorts)
      (.base (.atom (.copy controllerPorts.available (remainingPorts.register 2)))))

/-- The prepared head's unary size is copied as an all-zero initial assignment.
The length witness is consumed to initialize_ the binary remaining count. -/
def initialFuelPorts : CounterForPrograms.Ports 40 896 where
  register := Fin.castLEEmb (by decide)
  counter := tupleStacks 4
  scratch := tupleStacks 7
  counter_ne_scratch := by decide

def initialFuelCommand : Cmd 40 896 :=
  .call (ProgramLinking.liftProgram Counters.powerTwoProgram
    initialFuelPorts.register (CounterForPrograms.stackPorts initialFuelPorts))

def resetCommand : Cmd 40 896 :=
  .seq (copyWord 651 (tupleStacks 2) (tupleStacks 5))
    (.seq (copyWord 651 (tupleStacks 4) (tupleStacks 5))
      (.seq initialFuelCommand
        (.seq (.base (.atom (.set controllerPorts.available true)))
          (.base (.atom (.set controllerPorts.fresh false))))))

/-- Exact full-word test used before the candidate predicate is invoked. -/
def testAvailableCommand : Cmd 40 896 :=
  .seq (CounterForPrograms.testCmd remainingPorts)
    (.base (.atom (.copy controllerPorts.available (remainingPorts.register 2))))

/-- A current-head reset initializes the predecessor cursor to the same
fixed-width zero word, preserving the freshly initialized candidate and fuel. -/
def resetGeneratorCommand : Cmd 40 896 :=
  .seq resetCommand (copyWord 651 (tupleStacks 8) (tupleStacks 5))

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SignatureTupleProgram
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_QueryTupleVisitor
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! The representative tuple is already a polynomial-length stack of escaped
frames, deepest head first. These fixed commands copy that stack, extract one
actual representative, and decrement its unary physical head address. They do
not enumerate assignments or construct a Cartesian product. -/
namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryTupleVisitor

open OAI BitProgram StructuredCalls
open SignatureTupleProgram

abbrev Code := Cmd 40 896

/-- Parsing restores the original little-endian representative, including
zero-width heads. The address pop is justified by its nonempty input below. -/
def readHead : Code :=
  .seq (popWordCommand 840 838 (by decide)) (.base (.atom (.pop 843 0 1)))

/-- Overwriting pays for removing the old word before copying the new one.
It is used for the persistent ambient representative baseline. -/
def overwrite (src dst : Fin 896) : Code :=
  .seq (.call (StackRoutines.clearProgram dst 0 1)) (copyWord src dst 841)

/-- A peek checks whether another escaped frame exists. A zero-width head
still occupies its frame terminator and therefore enters the loop once. -/
def testFrames : Code := .base (.atom (.peek 840 0 1))

/-- The callback may consume or retain its parsed representative; clearing is
explicit and the next test is recomputed after its arbitrary register use. -/
def finishHead : Code := .seq (.call (StackRoutines.clearProgram 838 0 1)) testFrames

/-- The instruction table is fixed; only the retained frame stack controls
its number of head visits. The same controller is used for both passes. -/
def headBody (work : Code) : Code := .seq readHead (.seq work finishHead)
def headLoop (work : Code) : Code := .while 1 (headBody work)

/-- Starting a second pass clears the previous node offset before installing
its past-the-end address. The retained representatives are copied unchanged. -/
def restart : Code := .seq (overwrite 837 840) (overwrite 845 843)

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryTupleVisitor
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_QueryTupleInit
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! Concrete initialization of one attained-signature tuple product. The
multiplicative identity is built by the native cache routine, and every stale
output and borrowed word is cleared by an actual command. -/
namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryTupleInit

open OAI BitProgram StructuredCalls SubexpSetupStorage
open SqrtLog SqrtLog.LeafProgram

abbrev Code := Cmd 40 896

def clearBank (ports : List (Fin 896)) : Code :=
  liftCommand (clearMany ports) 841 841 FactorAssignmentProgram.localRegister id

def finish : Code := .seq (QueryTupleVisitor.overwrite 69 852)
  (.seq (QueryTupleVisitor.overwrite 703 869) (clearBank lowPorts))

def command : Code := .seq (clearBank entryPorts)
  (.seq FactorAssignmentProgram.setup finish)


open CommandRegisterFrames

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryTupleInit
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

abbrev Code := Cmd 40 896

def prepare : Code := .seq NodeAppendSpace.prepare (NodeReadoutSpace.clearMany scratchPorts)

def command : Code := .seq prepare
  (.call (ProgramLinking.liftProgram Normalize.program registers ports))

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryTupleSum
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

abbrev Code := Cmd 40 896

/-- Re-read the existing representative stack for either of the two passes.
Both destination words are replaced by paid commands, including on the
second pass after the first has decremented its address to the node offset. -/
def replay (work : Code) : Code := .seq restart (.seq testFrames (headLoop work))

namespace TupleEnd

open OAI.Algorithms.SubexponentialSAT.SqrtLog SubexpLiftRing SubexpQuarticRing MomentsProgram TruncatedRingProgram

/-- Return all borrowed current-head words before the attained-signature DFS
resumes. Ancestor frames and the emitted representatives are retained. -/
def cleanup : Code := QueryTupleInit.clearBank currentHeadPorts

def command : Code := .seq QueryTupleSum.command cleanup

end TupleEnd

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryExecution
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_FactorAssignmentBoundary
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! The real initializer and paid cache setup establish the physical boundary
for the actual stored-ID fold. Bounds are fixed before that fold; the current
Good-empty-support seed is serialized on151, the unread suffix on150 and the
reversed original ID on149. No execution service is a field below. -/
namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FactorAssignmentBoundary
open OAI BitProgram StructuredCalls SubexpSetupStorage
open OAI.Algorithms.SubexponentialSAT.SqrtLog OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgram HashCircuitProgram HashCircuitProgram.Native
open IdempotentApplyProgram.Steps MomentsProgram
open OAI.Algorithms.SubexponentialSAT.SubexpLiftRing OAI.Algorithms.SubexponentialSAT.SubexpQuarticRing
open FactorAssignmentProgram

noncomputable section
attribute [local simp] Fin.coe_ofNat_eq_mod

/-- This is the actual prefix of assignment, before copying the ID stream. -/
def prepare : Code := .seq «initialize_» setup

def prepareCost (a : FactorAssignmentProgram.Data) : ℕ :=
  initializeCost a + setupCost (initialized a)

end
end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FactorAssignmentBoundary
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_HashGreedyExecution
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! The actual candidate attempt is the fixed normalizer, all-clause mass
collector, and paid fixed-width padding. The only remaining query execution
premise is the concrete per-mark evaluator, including its exact caller frame. -/
namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HashGreedyExecution

open BitProgram StructuredCalls RecordPrograms SqrtLog LeafProgram
open HashGreedyProgram HashGreedyProgram.NativeRound HashMassAdapter

def trialState (a : State 40 896) (m depth : ℕ) (word : List Bool) : State 40 896 :=
  ⟨a.regs, Function.update a.stacks 768 (HashCandidates.normalize m depth word.reverse)⟩

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HashGreedyExecution
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

abbrev Data := State 40 896
def parserReset (a : Data) : Data := SubexpParameterProgram.runAtoms
  [.set 16 false, .set 17 true, .set 18 false] a

def clearState (a : Data) : Data :=
  ⟨readRegs a.regs 0 1 none, BankRoutines.clearBankStacks cleanupPorts a.stacks⟩

def finishState (a : Data) : Data := parserReset (clearState (routed (788,323) a))
def finishSteps (a : Data) : ℕ := routeCost (788,323) a +
  (2 * (cleanupPorts.map fun i => ((routed (788,323) a).stacks i).length).sum +
    3 * cleanupPorts.length + 3 + 3)

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HashMarkedQueryAdapter
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
abbrev Code := Cmd 40 896

def cleanupLocalProgram := compiled LeafProgram.Query.cleanup 699 323

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighMarkedFrontend
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_SparseCodeProgram
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
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

/-- The branch accepts only properly encoded matrices; the actual checker
then decides its algebraic property by its inner complete word scan. -/
def matrixCandidate (ternary : Bool) (matrix : Fin 48)
    (checker : Cmd 16 40) (input output : Fin 40) : Cmd 16 48 :=
  .seq (copyConvertCommand ternary 40 43 44 45) <|
  .ite 4
    (.seq (SubexpSetupStorage.clearCmd 44) (.base (.atom (.set 15 false))))
    (.seq (installMatrix 44 matrix) (liftChecker checker input output))

def localMatrixCandidate : Cmd 16 48 := matrixCandidate true 18 localChecker 21 25

def graphMatrixCandidate : Cmd 16 48 := matrixCandidate false 29 graphChecker 33 37

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

/-- The finite outer-search ABI is shared by local ternary matrices and
binary graph matrices. Only the current framed tuple and first witness persist. -/
def counterPorts : CounterForPrograms.Ports 16 48 where
  register := ⟨Fin.castAdd 13, Fin.castAdd_injective _ _⟩
  counter := 40
  scratch := 41
  counter_ne_scratch := by decide

def selection (candidate : Cmd 16 48) : Cmd 16 48 :=
  firstSuccess candidate 12 15 13 14 40 42 45

def core (candidate : Cmd 16 48) :=
  ExecCNFTupleEnumeration.program counterPorts (selection candidate)


open OAI.Algorithms.SubexponentialSAT.SqrtLog OAI.Algorithms.SubexponentialSAT.SqrtLog.CodeSearchProgram CodeChecks

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

def clearedLower (a : Data) : Data :=
  ⟨readRegs a.regs 0 1 none, BankRoutines.clearBankStacks lowerPorts a.stacks⟩

def clearLowerSteps (a : Data) : ℕ :=
  2 * (lowerPorts.map (fun i => (a.stacks i).length)).sum + 147

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeCode
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_HashQueryEntry
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
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

abbrev Data := State 40 896

def recordState (a : Data) (tail bits : List Bool) : Data :=
  RecordPrograms.state HashMassAdapter.recordPorts a false true false tail bits.reverse

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HashQueryEntry
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

namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HeadEvaluationProgram.HeadGate
open OAI BitProgram StructuredCalls
open OAI.Algorithms.SubexponentialSAT.SqrtLog.BucketProgram
open OAI.Algorithms.SubexponentialSAT.Subexp.MatrixProgramSupport

def state (regs : Fin 16 → Bool) (W bits : List Bool)
    (rows : List (List (List Bool))) (key wanted E H : List Bool) : Data :=
  ⟨regs,![W,[],[],[],[],[],[],[],[],[],[],[],bits,[],key,words (rows.map words),
    wanted,E,H,[],[],[],[],[],[],[],[],[],[],[],[],[]]⟩

def keyCall : Code := .call (ProgramLinking.liftProgram
  AttainedSignatureProgram.program keyRegisters keyStacks)

def equalityCall : Code := .call (ProgramLinking.liftProgram
  AttainedSignatureProgram.KeyEquality.program equalityRegisters equalityStacks)

/-- Every candidate pays for the complete key comparison and correction scan.
Only the final Boolean register selects whether its factor value is added. -/
def command : Code := .seq keyCall (.seq equalityCall
  (.seq (.base (.atom (.copy 15 4))) (.seq correctionCall
    (.seq (.base (.atom (.band 15 15 6))) clearKey))))

def program := compiled command 12 12

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HeadEvaluationProgram.HeadGate

namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HeadEvaluationProgram.StagedGate
open OAI BitProgram StructuredCalls StackRoutines
open OAI.Algorithms.SubexponentialSAT.Subexp.MatrixProgramSupport
open OAI.Algorithms.SubexponentialSAT.SqrtLog.BucketProgram

def copy (src dst : Fin 896) : Code := .call (copyProgram src dst 31 (0:Fin 40) 1)
def clear (src : Fin 896) : Code := .call (clearProgram src (0:Fin 40) 1)
def copyState (d : Data) (src dst : Fin 896) : Data :=
  ⟨readRegs d.regs 0 1 none,copyStacks src dst d.stacks⟩
def clearState (d : Data) (src : Fin 896) : Data :=
  ⟨readRegs d.regs 0 1 none,clearStacks src d.stacks⟩

def callGate : Code := .call (ProgramLinking.liftProgram HeadGate.program registers stackMap)
def stage : Code := .seq (copy 864 0) (.seq (copy 859 12) (.seq (copy 865 15)
  (.seq (copy 866 16) (.seq (copy 867 17) (copy 868 18)))))
def cleanup : Code := .seq (clear 0) (.seq (clear 12) (.seq (clear 15)
  (.seq (clear 16) (.seq (clear 17) (clear 18)))))
def command : Code := .seq stage (.seq callGate cleanup)

def sourceLength (d : Data) : ℕ :=
  (d.stacks 864).length+(d.stacks 859).length+(d.stacks 865).length+
    (d.stacks 866).length+(d.stacks 867).length+(d.stacks 868).length

def staged (d : Data) : Data :=
  copyState (copyState (copyState (copyState (copyState (copyState d 864 0)
    859 12) 865 15) 866 16) 867 17) 868 18

def cleaned (d : Data) : Data :=
  clearState (clearState (clearState (clearState (clearState (clearState d 0)
    12) 15) 16) 17) 18

def lowLength (d : Data) : ℕ :=
  (d.stacks 0).length+(d.stacks 12).length+(d.stacks 15).length+
    (d.stacks 16).length+(d.stacks 17).length+(d.stacks 18).length

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

def cursorPorts : CounterForPrograms.Ports 40 896 where
  register := ⟨Fin.castAdd 37, by intro a b h; exact Fin.ext (congrArg (fun x : Fin 40 => x.val) h)⟩
  counter := 859
  scratch := 861
  counter_ne_scratch := by decide

def fuelPorts : CounterForPrograms.Ports 40 896 where
  register := ⟨Fin.castAdd 37, by intro a b h; exact Fin.ext (congrArg (fun x : Fin 40 => x.val) h)⟩
  counter := 860
  scratch := 861
  counter_ne_scratch := by decide

open HeadEvaluationProgram.StagedGate (copy copyState clear clearState )


open OAI.Algorithms.SubexponentialSAT.SqrtLog OAI.Algorithms.SubexponentialSAT.SqrtLog.MomentsProgram OAI.Algorithms.SubexponentialSAT.SubexpLiftRing
open OAI.Algorithms.SubexponentialSAT.SubexpQuarticRing TruncatedRingProgram


open OAI.Algorithms.SubexponentialSAT.Subexp.MatrixProgramSupport
open OAI.Algorithms.SubexponentialSAT.SqrtLog.BucketProgram

open scoped BigOperators

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HeadSumProgram
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_HeadSumAssembly
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! Concrete head-sum assembly. The first head gate receives a physically
cleared arithmetic bank; persistent source parameters remain outside that bank.
Accepted assignments continue through dense addition and workspace reclamation,
including empty factor products and zero-valued products. -/

namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HeadSumAssembly

open OAI BitProgram StructuredCalls StackRoutines
open HeadEvaluationProgram.StagedGate

abbrev Data := State 40 896
abbrev Code := Cmd 40 896

def clearWork : Code := .seq (clear 31) (BankRoutines.clearCmd 31 0 1 workPorts)

open CommandRegisterFrames

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HeadSumAssembly
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

abbrev Code := Cmd 40 896

def reset : Code := .seq (.call (clearProgram 792 0 1))
  (BankRoutines.clearCmd 792 0 1 changed)

def copy : Code := .call (copyProgram 330 789 792 0 1)

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighCountInit
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

abbrev Code := Cmd 40 896

def reset : Code := .seq (.call (clearProgram 791 0 1))
  (BankRoutines.clearCmd 791 0 1 changed)

def copy : Code := .call (copyProgram 338 792 791 0 1)

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighCountSeed
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_HighQueryDecode
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! The actual current-high decoder, kept independent of the complete query
and high-loop composition so the fixed stream can consume its proved run. -/
namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighQueryLoop

open OAI BitProgram StructuredCalls SqrtLog LeafProgram LeafBranchProgram
open HighQueryAdapter PreparedBranchCount
open HashGreedyProgram.NativeRound

abbrev Data := State 40 896

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighQueryLoop
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

abbrev Data := State 40 896
abbrev Code := Cmd 40 896

open OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafOuterProgram OAI.Algorithms.SubexponentialSAT.StackRoutines

/-- Reuse the complete cleanup, then physically put the canonical word back on
788 for the final unmarked query. The temporary marked-output word is erased. -/
def installAccepted : Code := .seq (route (323,788)) (.call (clearProgram 323 0 1))

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighQueryExecution
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_HighQueryLocalBounds
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! Source-only local costs for the physical high-count controller. Retained
caller words, including the outer marked accumulator322, do not enter them. -/
namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighQueryLocalBounds
open OAI BitProgram StructuredCalls StackRoutines HighQueryAdapter

abbrev Data := State 40 896

open HashGreedyProgram.NativeRound

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighQueryLocalBounds
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_ReconstructionProgramReady
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Static readiness obtained from the physically prepared input tapes.
No arithmetic, program trace, or canonicality hypothesis is hidden here. -/
namespace SubexponentialSAT.SqrtLog.ReconstructionProgram.InputReady

open SubexponentialSAT BitProgram StructuredCalls SubexpCRTOuterProgram
open SubexpLiftRing SubexpQuarticRing

/-- Definitionally the same store as `NativeState.arithmeticBase`. -/
def base (input : Data) : Fin 256 → List Bool :=
  (Function.update (Entry.prepared input.stacks) 104 (input.stacks 280)) ∘ localPorts

/-- The six unmodified low frame cells are unrestricted input bytes. -/
def lowFrame (input : Data) (i : Fin 6) : List Bool :=
  input.stacks ⟨14+i.val, by omega⟩

end SubexponentialSAT.SqrtLog.ReconstructionProgram.InputReady

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_NativeLayoutLoad
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! Paid node-start loading of the parked source bank. Only the original
layout copy program is called; no head enumeration is imported or executed. -/
namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeLayoutLoad

open OAI BitProgram StructuredCalls SubexpSetupStorage SqrtLog
open LeafProgram LeafHeadSetupProgram

abbrev Code := Cmd 40 896

def prepare : Code := liftCommand (clearMany clearPorts) 730 128 registers id

def command : Code := .seq prepare
  (liftCommand LayoutMasters.load 730 128 id stackMap)

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeLayoutLoad
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

abbrev Code := Cmd 40 896

/-- The outer node loop refreshes its guard after all inner controllers. -/
def guardCursor : Code := .base (.atom (.peek 301 37 38))

def advanceIndex : Code := .seq (.base (.atom (.set 0 true))) (.base (.atom (.push 307 0)))

/-- Called after actual node readout and append. The retained node accumulator
and theta are reclaimed before the next node, then the index and guard advance. -/
def finishNode : Code := .seq (NodeReadoutSpace.clearMany [78,850])
  (.seq advanceIndex guardCursor)

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryNodeFinish
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_ReconstructionProgramLocalValue
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! The physical local factor and correction have the canonical Hermite
meaning independently of the encoded representative of their head word. -/
namespace SubexponentialSAT.SqrtLog.ReconstructionProgram.LocalValue

open SubexponentialSAT Polynomial
open SubexpSymbolicCost DensePolynomialProgram
open CRTLocalProgram

variable {B d J Q : ℕ} {R : Type*} [CommRing R]

def factorCode (ops : RepresentedRing (Coeff B d) R) (minusOne : Coeff B d)
    (nodes : Fin Q → Coeff B d) (J : ℕ) (i : Fin Q) : Model.Poly B d J :=
  ((List.ofFn nodes).eraseIdx i.val).foldl
    (localUpdate (Model.scalarMul ops) (Model.scalarAdd ops) (Fixed.mul ops.program)
      (fun c => Model.linear ops.zeroRun.1 ops.oneRun.1 c J) (nodes i) minusOne J)
    (Model.constant ops.zeroRun.1 ops.oneRun.1 J)

end SubexponentialSAT.SqrtLog.ReconstructionProgram.LocalValue

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_ReconstructionProgramModelMiddle
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.MulticolorTypes.instFintypeJoint _root_.OAI.Algorithms.SubexponentialSAT.MulticolorTypes.instFintypeSide _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! The actual model-specific native Hermite iteration. Every arithmetic
service and every local correction trace is discharged here. -/
namespace SubexponentialSAT.SqrtLog.ReconstructionProgram.Native

open SubexponentialSAT BitProgram StructuredCalls SubexpCRTOuterProgram
open SubexpLiftRing SubexpQuarticRing
open DensePolynomialProgram

abbrev Coeff (t d : ℕ) := DensePolynomialProgram.Coeff (baseWidth 3 t) d

noncomputable def term {d Q : ℕ} (t : ℕ) (ht : 0 < t) (hd : 0 < d)
    (a : RingModel.Data d) (M : SubexpPreparedQuartic.Modulus 3 t)
    (cache : RingProgram.ScalarCache 3 t) (nodes : Fin Q → Coeff t d)
    (J : ℕ) (jets : Fin Q → CRTLocalProgram.Model.Poly (baseWidth 3 t) d J) (i : Fin Q) : a.O t :=
  let ops := RingProgram.modelRing t ht hd a M cache
  let theta := fun j => ops.decode (nodes j)
  (JetCRT.cofactor theta J i).eval 0 *
    (TruncatedInverse.correction theta J (LocalValue.inverse theta (3^d) t J)
      (fun j => CRTLocalProgram.Model.denote ops.decode (jets j)) i).eval (-theta i)

end SubexponentialSAT.SqrtLog.ReconstructionProgram.Native

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_ReconstructionProgramState
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! The concrete caller frame seen at every loaded Hermite node. -/

namespace SubexponentialSAT.SqrtLog.ReconstructionProgram.NativeState

open SubexponentialSAT BitProgram StructuredCalls SubexpCRTOuterProgram

/-- The native arithmetic context after the paid cache and width preparation. -/
def arithmeticBase (input : Data) : Fin 256 → List Bool :=
  (Function.update (Entry.prepared input.stacks) 104 (input.stacks 280)) ∘ localPorts

end SubexponentialSAT.SqrtLog.ReconstructionProgram.NativeState

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_ReconstructionProgramModel
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Complete execution of the fixed native CRT table in the actual searched
ring model. The hypotheses describe input bytes and clean workspace only. -/
namespace SubexponentialSAT.SqrtLog.ReconstructionProgram.Native

open SubexponentialSAT BitProgram StructuredCalls SubexpCRTOuterProgram
open SubexpLiftRing SubexpQuarticRing
open DensePolynomialProgram

def middleBudget (Q J t d : ℕ) : ℕ :=
  Middle.budget Q J (d*baseWidth 3 t)
    (HornerProgram.Services.mulBudget (baseWidth 3 t) d)
    (HornerProgram.Services.addBudget (baseWidth 3 t) d)
    (CRTLocalProgram.Native.budget Q Q (3^d) t d J)

def budget (Q J t d modulusBits widthTokens : ℕ) : ℕ :=
  Entry.budget modulusBits widthTokens +
    controllerBudget (d*baseWidth 3 t) J Q (middleBudget Q J t d)

end SubexponentialSAT.SqrtLog.ReconstructionProgram.Native

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_ReconstructionSpace
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! Concrete CRT reconstruction and full-word modular readback. The same actual
native traces satisfy correctness, polynomial local time, and every-prefix
bounds on all source stacks, including the persistent caller frame. -/

namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.ReconstructionSpace

open OAI BitProgram StructuredCalls SubexpCRTOuterProgram
open SubexpLiftRing SubexpQuarticRing OAI.Algorithms.SubexponentialSAT.SqrtLog
open DensePolynomialProgram ReconstructionProgram.Native

def normalizeReadback : Cmd 8 8 :=
  .call (ProgramLinking.liftProgram
    DisjointReuse.CanonicalWordProgram.normalizeUnsignedProgram
    normalizationPorts normalizationPorts)

/-- A fixed reader followed by the actual unsigned normalizer. Zero has the
canonical one-bit output `[false]`, and positive counts retain all their bits. -/
def canonicalReadback : Cmd 8 8 :=
  .seq (.call LeafProgram.Readback.countProgram) normalizeReadback

def canonicalReadbackProgram := compiled canonicalReadback 0 0

/-- The existing query ABI is retained: reconstructed coefficients enter on
261, the canonical count leaves on 323, and 324 is the transfer scratch. -/
def canonicalQueryReadCommand : Cmd 19 330 :=
  .call (ProgramLinking.liftProgram canonicalReadbackProgram
    LeafProgram.QueryReadback.regMap LeafProgram.QueryReadback.stackMap)

def canonicalQueryCommand : Cmd 19 330 :=
  .seq canonicalQueryReadCommand LeafProgram.QueryReadback.moveCommand

def canonicalQueryProgram := compiled canonicalQueryCommand 261 323

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.ReconstructionSpace
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

def canonicalWideRead : Cmd 40 768 :=
  .call (ProgramLinking.liftProgram ReconstructionSpace.canonicalQueryProgram
    LeafProgram.QueryReadback.Wide.regMap LeafProgram.QueryReadback.Wide.stackMap)

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.ReconstructionNative
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_SignatureKeyNative
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-!
# One full integer signature on the leaf ABI

All port numbers here are leaf-local. The actual key-only machine preserves
the assignment, shifted matrix and every unrelated caller word; it has no
predecessor, countdown, or signature-table input.
-/

namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SignatureKeyNative

open BitProgram StructuredCalls AttainedSignatureProgram
open OAI.Algorithms.SubexponentialSAT.SqrtLog.BucketProgram OAI.Algorithms.SubexponentialSAT.Subexp.MatrixProgramSupport

def machine := ProgramLinking.liftProgram AttainedSignatureProgram.program registers stackPorts

def command : Cmd 40 896 := .call machine

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SignatureKeyNative
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

def reset : Cmd 40 896 := .seq (.call (clearProgram 841 0 1))
  (BankRoutines.clearCmd 841 0 1 cleared)

def masters : Cmd 40 896 := .seq (overwrite 141 864)
  (.seq (overwrite 847 865) (overwrite 671 175))

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SignatureHeadPrepare
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_SignatureHeadLoaderCore
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! The fixed head-loader table uses the actual integer entry program. Its
physical matrix view follows LeafHeadSetupProgramHead/MatrixRun exactly, while
its controller emits one matrix and never constructs assignment tables. -/
noncomputable section
namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SignatureHeadLoader
open OAI BitProgram StructuredCalls OAI.Algorithms.SubexponentialSAT.SqrtLog
open OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafHeadSetupProgram
open OAI.Algorithms.SubexponentialSAT.SubexpSetupStorage

def shiftCommand : Code :=
  stage BucketProgram.preMatrixProgram shiftRegs (by decide) shiftInputs shiftOutputs

def exportMatrix : Cmd 16 896 :=
  .seq (clearCmd 659) (.seq (copyCmd 668 847 659) (clearMany [668,669,846]))
/-- A fixed alternate address tape supports reverse head visits without
changing the DFS's retained address845. -/
def importAddressFrom (src : Fin 896) : Cmd 16 896 :=
  .seq (clearMany [649,659,846,847]) (copyCmd src 649 659)

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SignatureHeadLoader
end
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_QueryVisitorProgram
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! Fixed two-pass visit of one emitted attained-signature tuple. The first
pass reconstructs the entire ambient representative assignment; the second
rescans the assignments in each head against those fixed foreign values.
Every concrete subroutine is fixed here, without an evaluator argument. -/
namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryVisitorProgram

open BitProgram StructuredCalls
noncomputable section

abbrev Code := Cmd 40 896

end
end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryVisitorProgram
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

/-- A completed duplicate step clears its saved key before the next predicate.
Thus every scan boundary has an empty output key tape. -/
def advanceCandidateCommand : Cmd 40 896 :=
  .seq advanceCommand (clearWord (tupleStacks 3))

/-- The candidate predicate runs only when the complete remaining word is
nonzero. Its one-bit result is copied from the actual latch, not from a key. -/
def probeWith (predicate : Cmd 40 896) : Cmd 40 896 :=
  .seq testAvailableCommand
    (.ite controllerPorts.available
      (.seq initializeFreshCommand
        (.seq predicate (.base (.atom (.peek (rescanStacks 22) controllerPorts.fresh 0)))))
      (.base .skip))

/-- A child starts after one emitted representative is recorded and its
parent's bounded cursor is suspended. All current head arrays are cleared. -/
def descendWith (loadHead : Cmd 40 896) : Cmd 40 896 :=
  .seq recordRepresentativeCommand
    (.seq saveCursorCommand
      (.seq descendLevelCommand
        (.seq leaveHeadCommand
          (.ite controllerPorts.leaf (.base .skip)
            (.seq loadHead resetGeneratorCommand)))))

/-- The parent cursor is restored without rerunning its preceding candidate
scans. Only its polynomial-size matrix is reconstructed before the advance. -/
def resumeParentWith (loadHead : Cmd 40 896) : Cmd 40 896 :=
  .seq dropRepresentativeCommand
    (.seq restoreCursorCommand
      (.seq ascendLevelCommand
        (.seq loadHead (.seq resetPredecessorCommand advanceCandidateCommand))))

def ascendWith (loadHead : Cmd 40 896) : Cmd 40 896 :=
  .seq leaveHeadCommand
    (.seq testParentCommand
      (.ite controllerPorts.active (resumeParentWith loadHead) (.base .skip)))

/-- Clear every tuple controller tape once at entry. The fixed list has twelve
ports, independent of the input, assignment count, and number of signatures. -/
def setupWith (loadHead : Cmd 40 896) : Cmd 40 896 :=
  .seq (clearWords (List.ofFn tupleStacks))
    (.seq initializeLevelsCommand
      (.ite controllerPorts.leaf (.base .skip) (.seq loadHead resetGeneratorCommand)))

/-- Finite-command assembly used by the concrete loader/predicate adapters.
The exact callback is instantiated by the query evaluator. These arguments
are syntactic programs; this constructor is not the final correctness theorem. -/
def assembleRoutines (loadHead predicate visit : Cmd 40 896) : Routines 40 896 where
  setup := setupWith loadHead
  probe := probeWith predicate
  descend := descendWith loadHead
  advance := advanceCandidateCommand
  ascend := ascendWith loadHead
  visit := visit


/-- The complete predecessor predicate, on the fixed shared leaf ABI. The
program computes its candidate key before rescanning earlier assignments. -/
def candidateMachine := ProgramLinking.liftProgram
  AttainedSignatureProgram.Rescan.candidateProgram rescanRegisters rescanStacks

def candidateCall : Cmd 40 896 := .call candidateMachine

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SignatureTupleNative
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_QueryStreamProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! The fixed streaming query runs the actual pair DFS, attained-signature
DFS, two-pass visitor, node readout and canonical count reconstruction. Its
finite command tables have no callback or evaluator parameters. -/
namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryStreamProgram

open OAI BitProgram StructuredCalls
open SignatureTupleProgram SignatureTupleNative
noncomputable section

abbrev Code := Cmd 40 896

end
end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryStreamProgram
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_HighQueryProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! Fixed finite syntax for both marked and final accepted queries. The only
program parameter is the fixed clause width. Every mark regenerates its own
physical high mask and zero counter. The semantic proof must establish that
the actual frontend guard holds on every reachable input. -/
namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighQueryProgram

open OAI BitProgram StructuredCalls HighQueryAdapter
noncomputable section

abbrev Code := Cmd 40 896

/-- The failed guard does no ring allocation. It clears the count word before
the common canonical return. Correctness on reachable inputs proves guard8 true;
this syntactic alternative is not used as a count-correctness argument. -/
def reject : Code := .call (StackRoutines.clearProgram 788 0 1)

open HashGreedyProgram.NativeRound

end
end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighQueryProgram
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_HighQueryStart
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! Actual entry to each high-assignment count. The current frontend mask
survives concrete packing/arithmetic and drives the fixed zero-seed program.
The compact returned boundary is separate from the transient prefix bound. -/
namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighQueryStart

open OAI BitProgram StructuredCalls SqrtLog LeafParametersProgram
open LeafProgram.Query HashGreedyProgram.NativeRound

abbrev Data := State 40 896
abbrev Lower := State 40 768

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighQueryStart
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_ProducedQueryRankProvenance
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! The rank certificate refers to the packing and word table actually
produced by the native packing caller, with its original incidence order. -/
noncomputable section
namespace SubexponentialSAT.SqrtLog.ProducedQueryRank
open scoped BigOperators
open SubexponentialSAT.MulticolorTypes SubexponentialSAT.Subexp.ConstructivePacking
open PackingCallerProgram

theorem head_row (p : Problem) (a : Word p.r p.Q) (tail : List (Word p.r p.Q))
    (v : Fin p.n) :
    (rows p a tail).getD v.val []=SubexponentialSAT.Subexp.ReadPlan.encodeWord (words p a tail (.inl v)) := by
  have hv : v.val < (p.words a tail).length := by rw [p.words_length]; omega
  unfold rows
  rw [List.getD_eq_getElem _ _ (by simpa using hv),List.getElem_map]
  rfl

end SubexponentialSAT.SqrtLog.ProducedQueryRank

end

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_ProducedQueryRankSchedule
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Scheduled rank of the literal native packing. The intermediate scan
premises are discharged for produced queries in the final certificate. -/
noncomputable section
namespace SubexponentialSAT.SqrtLog.ProducedQueryRank
open scoped BigOperators
open SubexponentialSAT.MulticolorTypes SubexponentialSAT.Subexp.ConstructivePacking
open PackingCallerProgram LeafParametersProgram
open BucketProgram.ProducedRank

/-- This finite maximum uses all actual node indices and all actual heads. -/
def labelRows (p : Problem) (a : Word p.r p.Q) (tail : List (Word p.r p.Q))
    (R : ℕ) (low : List Bool) : ℕ :=
  CostAssembly.maxTotalRank Finset.univ (actualRank (packing p a tail) (owner p)
    (SubexponentialSAT.Subexp.TailInterval.intervalStart p.r p.Q R) R (rows p a tail) low)

end SubexponentialSAT.SqrtLog.ProducedQueryRank

end

end OAI.Algorithms
end


