-- Prove2me | Definitions.Def_OAIQ081S191
-- name    : OAIQ081S191
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-29T23:49:17.905232+00:00
-- url     : https://prove2.me/theorems/26eaf87d-1b8a-4c5f-ba4b-294c5dff37b4
-- title:
--   Definitions bundle OAIQ081S191 of the split of OpenAI, The Exponential Time Hypothesis is False
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.exact_count_and_sat`, carved from OpenAI's openai/math development (OpenAI, *The Exponential Time Hypothesis is False*, OpenAI Math Release, October 25, 2026, result family 378, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 30 declarations of OpenAI's Lean: 30 definitions. The definitions and types are `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FactorAssignmentProgram.assignment`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FactorAssignmentProgram.product`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FactorAssignmentProgram.program`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HeadAcceptedCorrect.budget`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HeadAcceptedProgram.program`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HeadSumAssembly.accepted`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryPairEvaluation.callbackBudget`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryStreamProgram.nodeBody`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryStreamProgram.nodeLoop`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryStreamProgram.nodes`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryStreamProgram.pairCallback`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryStreamProgram.pairs`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryVisitorHead.sumBudget`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryVisitorHead.timeCoefficient`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryVisitorProgram.baselineHead`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryVisitorProgram.evaluateHead`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryVisitorProgram.evaluateLoadedHead`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryVisitorProgram.loadHead`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryVisitorProgram.visitor`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryVisitorSemantics.evaluationCost`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryVisitorSemantics.visitorCoefficient`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryVisitorSemantics.visitorCost`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SignatureHeadLoader.programFrom`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SignatureHeadLoader.programFromLabels`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SignatureHeadLoader.smallProgramFrom`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SignatureTupleComplete.command`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SignatureTupleComplete.routines`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SignatureTupleLoader.loadHead`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SignatureTupleRun.leafCost`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SignatureTupleRun.runTime`.
--
--   **Sources.** They come from these modules of lean/OAI/Algorithms, in whole or in part: [`SubexponentialSAT_SqrtLogSpace_FactorAssignmentProgram`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLogSpace/FactorAssignmentProgram.lean), [`SubexponentialSAT_SqrtLogSpace_HeadAcceptedCorrect`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLogSpace/HeadAcceptedCorrect.lean), [`SubexponentialSAT_SqrtLogSpace_HeadAcceptedProgram`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLogSpace/HeadAcceptedProgram.lean), [`SubexponentialSAT_SqrtLogSpace_QueryPairEvaluation`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLogSpace/QueryPairEvaluation.lean), [`SubexponentialSAT_SqrtLogSpace_QueryStreamProgram`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLogSpace/QueryStreamProgram.lean), [`SubexponentialSAT_SqrtLogSpace_QueryVisitorHead`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLogSpace/QueryVisitorHead.lean), [`SubexponentialSAT_SqrtLogSpace_QueryVisitorProgram`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLogSpace/QueryVisitorProgram.lean), [`SubexponentialSAT_SqrtLogSpace_QueryVisitorSemantics`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLogSpace/QueryVisitorSemantics.lean), [`SubexponentialSAT_SqrtLogSpace_SignatureHeadLoaderCore`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLogSpace/SignatureHeadLoaderCore.lean), [`SubexponentialSAT_SqrtLogSpace_SignatureTupleCommand`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLogSpace/SignatureTupleCommand.lean), [`SubexponentialSAT_SqrtLogSpace_SignatureTupleLoadCommand`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLogSpace/SignatureTupleLoadCommand.lean), [`SubexponentialSAT_SqrtLogSpace_SignatureTupleRun`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLogSpace/SignatureTupleRun.lean).
--
--   **Imports.** It imports the bundle `OAIQ081S189` of this split.
--
--   **Imported by** (directly, in this split): the bundle `OAIQ081S193`; the statements `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FactorAssignmentCorrect.assignment_eval_correct`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FactorAssignmentCorrect.prepared_product_eval_correct`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HeadAcceptedCorrect.accepted_eval`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HeadAcceptedProgram.register_frame`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QuerySelectorFrames.pairs_avoids`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryStreamCorrect.node_run`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryStreamCorrect.nodes_run`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryStreamFrames.accepted_assignment_avoids`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryStreamFrames.nodes_avoids`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryStreamFrames.pairs_avoids`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryStreamFrames.visitor_avoids_of_loader`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryVisitorHead.head_multiply_run`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryVisitorHead.prepare_head_multiply_run`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryVisitorLoad.load_run_polynomial`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryVisitorSemantics.baseline_head`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryVisitorSemantics.baseline_pass`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SignatureHeadLoader.native_leafFrom_run_space`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SignatureTupleComplete.ascend_leaf`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SignatureTupleComplete.duplicate_step`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SignatureTupleComplete.exhausted_successor_step`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SignatureTupleComplete.fresh_internal_step`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SignatureTupleComplete.nonleaf_rel_step`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SignatureTupleComplete.setup_rel_run`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SignatureTupleLoader.ascend_native_run`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SignatureTupleLoader.descend_native_run`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SignatureTupleLoader.load_run_polynomial`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SignatureTupleLoader.setup_native_run`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SignatureTupleRun.nonleaf_iteration_masterFrame`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SignatureTupleRun.setup_masterFrame`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.StreamedQueryMeasuredCost.pair_cost_le_assembled` and `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.TupleRunBudgets.run_bounds`; the proofs of `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FactorAssignmentCorrect.assignment_eval_correct`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FactorAssignmentCorrect.prepared_product_eval_correct`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HeadAcceptedCorrect.accepted_eval`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HeadAcceptedProgram.register_frame`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QuerySelectorFrames.pairs_avoids`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryStreamCorrect.nodes_run`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryStreamFrames.accepted_assignment_avoids`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryStreamFrames.nodes_avoids`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryStreamFrames.pairs_avoids`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryStreamFrames.visitor_avoids_of_loader`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryVisitorHead.head_multiply_run`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryVisitorHead.prepare_head_multiply_run`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryVisitorLoad.load_run_polynomial`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryVisitorSemantics.baseline_head`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryVisitorSemantics.baseline_pass`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SignatureHeadLoader.native_leafFrom_run_space`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SignatureTupleComplete.ascend_leaf`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SignatureTupleComplete.duplicate_step`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SignatureTupleComplete.exhausted_successor_step`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SignatureTupleComplete.fresh_internal_step`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SignatureTupleComplete.nonleaf_rel_step`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SignatureTupleComplete.setup_rel_run`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SignatureTupleLoader.ascend_native_run`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SignatureTupleLoader.descend_native_run`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SignatureTupleLoader.load_run_polynomial`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SignatureTupleLoader.setup_native_run`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SignatureTupleRun.nonleaf_iteration_masterFrame`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SignatureTupleRun.setup_masterFrame`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.StreamedQueryMeasuredCost.pair_cost_le_assembled` and `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.TupleRunBudgets.run_bounds`.
-- source:
--   OpenAI, The Exponential Time Hypothesis is False, OpenAI Math Release, October 25, 2026, https://github.com/openai/math (result family 378; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/The-Exponential-Time-Hypothesis-is-False-October-25-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Algorithms at commit 7ef5c0c

import Mathlib
import Definitions.Def_OAIQ081S189

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

/-- Factor IDs are an explicitly stored polynomial-size input list. No head
assignment Cartesian product is materialized by this native record traversal. -/
def product : Code := .seq (copy 175 150)
  (.seq (copy 69 151) (.seq loop (move 151 854)))

/-- A single accepted ambient assignment145 is evaluated. The complete group
product is placed on854 for the head-sum addition; the arithmetic environment
remains installed for that addition. -/
def assignment : Code := .seq «initialize_» (.seq setup product)

def program := compiled assignment 175 854

end
end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FactorAssignmentProgram
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_HeadAcceptedProgram
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

noncomputable section

/-! The fixed accepted-head path first constructs the actual ambient assignment,
then evaluates its selected factor records, adds the resulting dense array to
the head accumulator, and reclaims the arithmetic environment. Zero-valued and
empty factor products follow the same addition/reset path. -/

namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HeadSumAssembly

/-- This concrete command has no callback or evaluator parameter. -/
def accepted : HeadSumProgram.Code :=
  .seq HighQueryAdapter.NativeOverlay.prepare
    (.seq FactorAssignmentProgram.assignment HeadSumProgram.accumulate)

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HeadSumAssembly

namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HeadAcceptedProgram

/-- One fixed head rescan includes entry cleanup, every candidate, and final
counter cleanup. Its dimensions and parameters are read from physical words. -/
def program := HeadSumAssembly.headProgram HeadSumAssembly.accepted

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HeadAcceptedProgram

end
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_HeadAcceptedCorrect
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! The fixed accepted branch physically overlays the current assignment,
computes its whole specialized factor product, and adds that same dictionary
to the head sum. Its compact return cap is independent of its transient cost. -/
namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HeadAcceptedCorrect

open OAI BitProgram StructuredCalls SubexpSetupStorage
open OAI.Algorithms.SubexponentialSAT.SqrtLog OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgram MomentsProgram
open OAI.Algorithms.SubexponentialSAT.SubexpLiftRing OAI.Algorithms.SubexponentialSAT.SubexpQuarticRing
open FactorAssignmentProgram FactorAssignmentBoundary QueryTupleState
open HighQueryAdapter TruncatedRingProgram

noncomputable section
attribute [local simp] Fin.coe_ofNat_eq_mod

/-- Each component is a measured cost of a polynomial local invocation. -/
def budget {r Q n d : ℕ} (q : Factor.Spec r Q n d) (P S Z : ℕ) : ℕ :=
  70*P+70 + FactorAssignmentCorrect.assignmentBudget q P S Z +
    TruncatedRingProgram.additionBudget n (baseWidth 3 q.p.t) d q.u q.J + 14*(896*P)+22

end
end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HeadAcceptedCorrect
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

/-- The fixed loader's label count is named so callers do not repeatedly
normalize the full structured command merely to compare program types. -/
def programFromLabels (src : Fin 896) : ℕ := size (commandFrom src) + 1

def smallProgramFrom (src : Fin 896) : Program 16 896 (programFromLabels src) := by
  unfold programFromLabels
  exact compiled (commandFrom src) src 847

def programFrom (src : Fin 896) : Program 40 896 (programFromLabels src) :=
  ProgramLinking.liftProgram (smallProgramFrom src) leafRegs id

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

/-- Load the head at the reverse traversal's paid unary address. The suspended
DFS address on845 and its representative frames remain caller data. -/
def loadHead : Code := .call (SignatureHeadLoader.programFrom 843)

/-- Install each representative into the ambient tuple before evaluating any
head. This pass also handles zero-width heads by consuming their real frame. -/
def baselineHead : Code :=
  .seq (.call (SignatureHeadLoader.programFrom 843))
    QueryTupleVisitor.installRepresentative

/-- The full key and factor-record stream are staged once per head. All raw
head assignments then pass through the concrete key/correction gate, factor
evaluator, and addition/reset path before multiplication into the tuple. -/
def evaluateLoadedHead : Code :=
  .seq SignatureHeadPrepare.command
    (.seq (HeadSumAssembly.head HeadSumAssembly.accepted)
      QueryAssembler.TupleMultiply.command)

def evaluateHead : Code := .seq loadHead evaluateLoadedHead

/-- One fixed visitor reconstructs representatives, evaluates all head sums,
and adds the completed product to the current finite-difference pair. The
unit construction and empty passes retain the empty-tuple contribution. -/
def visitor : Code :=
  .seq QueryTupleInit.command
    (.seq (QueryExecution.replay baselineHead)
      (.seq (QueryExecution.replay evaluateHead) QueryExecution.TupleEnd.command))

end
end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryVisitorProgram
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_SignatureTupleLoadCommand
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! The fixed loader call shared by the tuple syntax and its proof. -/
namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SignatureTupleLoader
open BitProgram StructuredCalls

/-- The DFS always requests its current physical head. -/
def loadHead : Cmd 40 896 := .call (SignatureHeadLoader.programFrom headAddress)

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SignatureTupleLoader
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_SignatureTupleCommand
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! The fixed actual attained-signature tuple command. -/
namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SignatureTupleComplete
open BitProgram StructuredCalls SignatureTupleProgram SignatureTupleNative
noncomputable section

/-- The concrete DFS table has no algorithm-service arguments. -/
def routines : Routines 40 896 :=
  assembleRoutines SignatureTupleLoader.loadHead candidateCall QueryVisitorProgram.visitor

abbrev command : Cmd 40 896 := SignatureTupleProgram.command controllerPorts routines

end
end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SignatureTupleComplete
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

/-- Each emitted pair is expanded immediately to ambient Boolean masks. All
attained tuples contribute to851 before its signed value is added to850. -/
def pairCallback : Code :=
  .seq QueryExecution.PairStart.command
    (.seq SignatureTupleComplete.command QueryAssembler.commitPair)

def pairs : Code := DifferencePairsProgram.command pairPorts pairCallback

/-- One actual framed interpolation node is consumed. The selected node value
and canonical metadata feed every pair; readout is performed after the full
signed node accumulation and appended in increasing node order. -/
abbrev nodeBody : Code :=
  .seq QueryAssembler.Nodes.beginNode
    (.seq NativeLayoutLoad.command
      (.seq bootstrapNode
        (.seq PairNativeSetup.setupCaller
          (.seq pairs QueryNodeFinish.command))))

abbrev nodeLoop : Code := .while 37 nodeBody

/-- The node cursor is copied from the produced table once. A physical peek
initializes the guard; every completed node refreshes it after its callbacks. -/
abbrev nodes : Code :=
  .seq QueryAssembler.Nodes.initializeNodes
    (.seq QueryNodeFinish.guardCursor nodeLoop)

end
end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryStreamProgram
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

def sumBudget {r Q n d : ℕ} (q : Factor.Spec r Q n d) (P S Z B h : ℕ) : ℕ :=
  (2*(HeadEvaluationProgram.StagedGate.bodyPolynomial P+
    HeadAcceptedCorrect.budget q P S Z)+126*B+54*h+286)*2^h

/-- Only this fixed polynomial coefficient is shared across heads. The
exponent remains the attained maximum head size supplied by the proved layout. -/
def timeCoefficient {r Q n d : ℕ} (q : Factor.Spec r Q n d) (B₀ P S Z B : ℕ) : ℕ :=
  QueryVisitorLoad.runEnvelope B₀ P+100*P+200+
    (2*(HeadEvaluationProgram.StagedGate.bodyPolynomial P+HeadAcceptedCorrect.budget q P S Z)+
      126*B+54*n+286)+multiplyBudget q P

end
end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryVisitorHead
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_QueryVisitorSemantics
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! Concrete execution of the two representative passes. The saved frame
stack is traversed in place, and every semantic dictionary is the one written
by the actual arithmetic command. -/
noncomputable section
namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryVisitorSemantics
open OAI BitProgram StructuredCalls OAI.Algorithms.SubexponentialSAT.SqrtLog
open SubexpSetupStorage LeafHeadSetupProgram
open SubexpLiftRing SubexpQuarticRing MomentsProgram TruncatedRingProgram
open QueryTupleState QueryTupleVisitor SignatureTupleProgram SignatureTupleSource


open scoped BigOperators

def evaluationCost (s : ProducedSource) {d : ℕ}
    (q : LeafProgram.Factor.Spec s.input.r s.input.Q s.input.n d)
    (P S Z B height : ℕ) : ℕ :=
  QueryVisitorHead.timeCoefficient q s.bound P S Z B*2^height


def visitorCost (s : ProducedSource) {d : ℕ}
    (q : LeafProgram.Factor.Spec s.input.r s.input.Q s.input.n d)
    (P S Z B height : ℕ) : ℕ :=
  QueryTupleSum.budget s.input.n (baseWidth 3 q.p.t) d q.p.t q.J P+1600*(P+1)+
    (baselineCost s P+evaluationCost s q P S Z B height+20)*s.input.r


def visitorCoefficient (s : ProducedSource) {d : ℕ}
    (q : LeafProgram.Factor.Spec s.input.r s.input.Q s.input.n d)
    (P S Z B : ℕ) : ℕ :=
  QueryTupleSum.budget s.input.n (baseWidth 3 q.p.t) d q.p.t q.J P+1600*(P+1)+
    baselineCost s P+QueryVisitorHead.timeCoefficient q s.bound P S Z B+20

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryVisitorSemantics
end
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_SignatureTupleRun
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! Complete runs of the fixed attained-signature controller. The retained
boundary cap is separate from transient prefix storage and measured time. -/
noncomputable section
namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SignatureTupleRun

open Classical
open OAI SubexpLiftRing BitProgram StructuredCalls OAI.Algorithms.SubexponentialSAT.SqrtLog
open LeafHeadSetupProgram OAI.Algorithms.SubexponentialSAT.SubexpSetupStorage
open SignatureTupleDFS SignatureTupleTraversal SignatureTupleProgram
open SignatureTupleNative SignatureTupleRefinement SignatureTupleLoader SignatureTupleSource
open SignatureTupleComplete

def leafCost (s : ProducedSource) {d : ℕ}
    (q : LeafProgram.Factor.Spec s.input.r s.input.Q s.input.n d) (F S Z B height : ℕ) : ℕ :=
  QueryVisitorSemantics.visitorCost s q F S Z B height+eventPolynomial s F

def runTime (s : ProducedSource) {d : ℕ}
    (q : LeafProgram.Factor.Spec s.input.r s.input.Q s.input.n d) (F S Z B height : ℕ) : ℕ :=
  eventPolynomial s F+(2*eventPolynomial s F)*s.input.r*tupleCount s.key s.input.r*4^height+
    tupleCount s.key s.input.r*leafCost s q F S Z B height+2

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SignatureTupleRun
end
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_QueryPairEvaluation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! The actual finite-difference callback uses the physical pair masks and
one semantic node accumulator. The reference support decoding below is used
only in the proof; the executed controller retains its four finite words. -/
namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryPairEvaluation

open OAI BitProgram StructuredCalls SqrtLog SubexpLiftRing SubexpQuarticRing
open LeafProgram QueryTupleState QueryPairCommit QueryReadyConstruction
open SignatureTupleSource
open scoped BigOperators
open SqrtLog.ProgramTapeReplay

noncomputable def callbackBudget (s : ProducedSource) {d : ℕ}
    (q : Factor.Spec s.input.r s.input.Q s.input.n d)
    (N F S Z B height : ℕ) : ℕ :=
  startBudget s.input.n F+SignatureTupleRun.runTime s q F S Z B height+commitBudget q N F

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryPairEvaluation
end


