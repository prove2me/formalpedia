-- Prove2me | Definitions.Def_OAIQ081S193
-- name    : OAIQ081S193
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-29T23:51:27.553978+00:00
-- url     : https://prove2.me/theorems/69e8e5be-fe3b-490c-8f1e-e28be171e119
-- title:
--   Definitions bundle OAIQ081S193 of the split of OpenAI, The Exponential Time Hypothesis is False
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.exact_count_and_sat`, carved from OpenAI's openai/math development (OpenAI, *The Exponential Time Hypothesis is False*, OpenAI Math Release, October 25, 2026, result family 378, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 14 declarations of OpenAI's Lean: 13 definitions and 1 inductive type or structure. The definitions and types are `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighQueryProgram.accepted`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighQueryProgram.branch`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighQueryProgram.conditioned`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighQueryProgram.guardedCount`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighQueryProgram.highLoop`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighQueryProgram.marked`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighQueryProgram.preparedCount`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeLeafProgram.command`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeLeafProgram.localCommand`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeLeafProgram.localProgram`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryStreamProgram.command`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryStreamProgram.program`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryVisitorHead.HeadBounds`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SignatureTupleComplete.program`.
--
--   **Sources.** They come from these modules of lean/OAI/Algorithms, in whole or in part: [`SubexponentialSAT_SqrtLogSpace_HighQueryProgram`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLogSpace/HighQueryProgram.lean), [`SubexponentialSAT_SqrtLogSpace_NativeLeafProgram`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLogSpace/NativeLeafProgram.lean), [`SubexponentialSAT_SqrtLogSpace_QueryStreamProgram`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLogSpace/QueryStreamProgram.lean), [`SubexponentialSAT_SqrtLogSpace_QueryVisitorHead`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLogSpace/QueryVisitorHead.lean), [`SubexponentialSAT_SqrtLogSpace_SignatureTupleCommand`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLogSpace/SignatureTupleCommand.lean).
--
--   **Imports.** It imports the published bundle `Def_SubexponentialSAT`; the bundle `OAIQ081S191` of this split.
--
--   **Imported by** (directly, in this split): the statements `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighQueryCorrect.accepted`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighQueryCorrect.marked`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighQueryCount.branch_kept_of_stream`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighQueryCount.branch_prepared_of_stream`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighQueryCount.run`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighQueryLoop.branch_step_resources`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighQueryProgram.conditioned_resources`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighQueryReturnReplay.accepted`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighQueryReturnReplay.marked`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighQueryTraversal.high_loop_run`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeHashQueries.accepted`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeHashQueries.accepted_replay`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeHashQueries.marked`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeHashQueries.marked_replay`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeLargeEntry.run`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeLeafContract.local_execution`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeLeafContract.local_from_runs`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeLeafContract.uniform_contract`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryHeadBudgets.headBounds`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryKeptFrame.kept_frame`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryKeptFrame.trace_interval`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryNodeEvaluation.nodeSource_run`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryNodeSourceBounds.headBounds`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryPairEvaluation.callback_cursor_run`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryPairEvaluation.callback_run`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryPairEvaluation.run`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QuerySelectorFrames.five_word_command_avoids`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryStreamCorrect.run`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryTopFrame.eval_top`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryVisitorHead.evaluateHead_run`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryVisitorSemantics.evaluation_pass`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryVisitorSemantics.visitor_run`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SignatureTupleRun.positive_run_resources`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SignatureTupleRun.run_resources` and `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SignatureTupleRun.zero_run`; the proofs of `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighQueryCorrect.accepted`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighQueryCorrect.marked`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighQueryCount.branch_kept_of_stream`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighQueryCount.branch_prepared_of_stream`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighQueryCount.run`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighQueryLoop.branch_step_resources`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighQueryProgram.conditioned_resources`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighQueryReturnReplay.accepted`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighQueryReturnReplay.marked`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighQueryTraversal.high_loop_run`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeHashQueries.accepted`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeHashQueries.accepted_replay`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeHashQueries.marked`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeHashQueries.marked_replay`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeLargeEntry.run`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeLeafContract.local_execution`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeLeafContract.local_from_runs`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeLeafContract.uniform_contract`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryHeadBudgets.headBounds`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryKeptFrame.kept_frame`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryKeptFrame.trace_interval`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryNodeEvaluation.nodeSource_run`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryNodeSourceBounds.headBounds`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryPairEvaluation.callback_cursor_run`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryPairEvaluation.callback_run`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryPairEvaluation.run`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QuerySelectorFrames.five_word_command_avoids`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryStreamCorrect.node_run`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryStreamCorrect.run`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryTopFrame.eval_top`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryVisitorHead.evaluateHead_run`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryVisitorSemantics.evaluation_pass`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryVisitorSemantics.visitor_run`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SignatureTupleRun.positive_run_resources`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SignatureTupleRun.run_resources`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SignatureTupleRun.zero_run` and `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.exact_count_and_sat`.
-- source:
--   OpenAI, The Exponential Time Hypothesis is False, OpenAI Math Release, October 25, 2026, https://github.com/openai/math (result family 378; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/The-Exponential-Time-Hypothesis-is-False-October-25-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Algorithms at commit 7ef5c0c

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_SubexponentialSAT
import Definitions.Def_OAIQ081S191

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

def program := compiled command 837 851

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

/-- Count one conditioned query. The current high assignment is decoded from
its actual counter word before node evaluation. The final word on323 is read
from the canonical reconstruction, rather than from a count bit. -/
abbrev command : Code :=
  .seq HighQueryAdapter.prepareHigh (.seq nodes QueryReconstruction.command)

def program := compiled command 330 323

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

/-- The stream already decodes the high context. Only the durable-counter copy
precedes it; the actual guard reset follows it even if the stream clobbers21. -/
def conditioned : Code := .seq copyHighCounter
  (.seq QueryStreamProgram.command restoreHighGuard)

/-- The real binary adder consumes each canonical residual count323 into788.
Neither a successful branch list nor a Boolean early exit is materialized. -/
def branch : Code := SqrtLog.LeafBranchProgram.body highPorts conditioned

def highLoop : Code := ExecCNFTupleEnumeration.enumerate highPorts.counter branch

def preparedCount : Code := .seq prepare (.seq seed highLoop)

def guardedCount : Code := .ite 8 preparedCount reject

/-- The marked frontend stages the actual current reference321 exactly once.
The complete canonical count is returned on323 for natural-number accumulation. -/
def marked (k : ℕ) : Code := .seq (HighMarkedFrontend.command k)
  (.seq guardedCount HighQueryExecution.markedReturn)

/-- The accepted frontend stages no mark. History-only source assembly is
performed by AcceptedQueryStage before this call, and788 is the full output. -/
def accepted (k : ℕ) : Code := .seq (HighMarkedFrontend.acceptedCommand k)
  (.seq guardedCount HighQueryExecution.acceptedReturn)

open HashGreedyProgram.NativeRound

end
end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighQueryProgram
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_NativeLeafProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! One fixed counting leaf, parameterized only by the fixed clause width.
The actual candidate queries and the separate history-only final query are
installed in the native greedy run. Terminal outer formulas use the checked
zero/power-of-two dispatcher. Semantic and resource composition is proved
separately; this file introduces no callback or evaluator parameter. -/
namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeLeafProgram

open BitProgram StructuredCalls
noncomputable section

/-- Physical preparation, all staged marked-query rounds, then the distinct
history-only accepted count. The full canonical result is written on788. -/
def localCommand (k : ℕ) : Cmd 40 896 :=
  NativeLeafRun.command (HighQueryProgram.marked k) (HighQueryProgram.accepted k)

def localProgram (k : ℕ) := compiled (localCommand k) 784 788

/-- Outer terminal classification retains ambient n. A nonterminal call
loads the disjoint leaf bank, executes the fixed local program, copies its
whole count to263, and physically clears the leaf bank before returning. -/
def command (k : ℕ) : Cmd 80 1220 :=
  NativeLeafDispatch.command (NativeLeafExecution.command (localCommand k))

end
end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeLeafProgram
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_QueryVisitorHead
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FiniteFallback.literalFintype
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

/-- Fixed numerical envelopes used at every head boundary. These fields are
inequalities in actual source sizes, with no execution or output services. -/
structure HeadBounds (s : LeafHeadSetupProgram.Native.Inputs) {d : ℕ}
    (q : Factor.Spec s.r s.Q s.n d) (M P S Z B L width : ℕ) : Prop where
  load : SignatureHeadLoader.retainedOutputBound s.n s.N s.D s.columnLength L ≤ P
  matrix : QueryVisitorLoadBounds.matrixEnvelope s L ≤ P
  key : QueryVisitorLoadBounds.keyEnvelope s L ≤ P
  select : 11*s.n+6 ≤ P
  count : s.n+1 ≤ P
  rows : q.ps.length ≤ P
  cache : 4*M+6 ≤ P
  capacity : FactorAssignmentLoop.byteBound s.n (baseWidth 3 q.p.t) d q.u q.J ≤ P
  multiply : FactorProductSpace.byteBound s.n (baseWidth 3 q.p.t) d q.p.t q.J ≤ P
  size : 1029*P+99+s.n+s.n*FactorTableProgram.literalRecordBound s.n
    (FactorTableNative.specializedPayloadBound s.n q.u q.J (baseWidth 3 q.p.t) d)+1 ≤ S
  radius : q.p.R+1 ≤ s.Q
  clause_width : ∀ f (hf : f < q.rows.length),
    ∀ w ∈ HashInputProgram.Expansion.weightedRow q.p.t d q.source q.rows[f],
      w.literals.length ≤ width
  positive : 1 ≤ Z
  compact : P ≤ Z
  bit : q.bitWidth ≤ Z
  degree : d*baseWidth 3 q.p.t ≤ Z
  hash : ∀ f (hf : f < q.rows.length),
    FactorEvaluationSpace.inputScale (baseWidth 3 q.p.t) d s.n q.u q.J
      width q.rows[f].length q.digits.length ≤ Z
  marked : FactorEvaluationSpace.inputScale (baseWidth 3 q.p.t) d s.n q.u q.J
    q.markedClause.length 0 0 ≤ Z
  head_local : 896*P+HeadEvaluationProgram.StagedGate.bodyPolynomial P+
    HeadAcceptedCorrect.budget q P S Z ≤ B
  counter : 9*(s.n+1)+8 ≤ B

end
end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryVisitorHead
end


