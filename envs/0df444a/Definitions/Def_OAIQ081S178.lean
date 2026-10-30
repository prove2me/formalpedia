-- Prove2me | Definitions.Def_OAIQ081S178
-- name    : OAIQ081S178
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-29T23:24:21.980807+00:00
-- url     : https://prove2.me/theorems/78028f11-8a4d-4b51-a6be-03e70db416b6
-- title:
--   Definitions bundle OAIQ081S178 of the split of OpenAI, The Exponential Time Hypothesis is False
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.exact_count_and_sat`, carved from OpenAI's openai/math development (OpenAI, *The Exponential Time Hypothesis is False*, OpenAI Math Release, October 25, 2026, result family 378, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 138 declarations of OpenAI's Lean: 107 definitions, 19 inductive types or structures and 12 theorems. The definitions and types are `OAI.Algorithms.SubexponentialSAT.SqrtLog.ProducedQueryResources.ScanBounds`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.ProducedQueryResources.SmallInputs`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.ProducedQueryResources.headSize`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.ProducedQueryResources.make`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.ProducedQueryResources.matrixHeight`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.ProducedQueryResources.ofPacking`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.ProducedQueryResources.problem`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.ProducedQueryResources.rank`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FactorAssignmentBoundary.Entry`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FactorAssignmentBoundary.Ready`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FactorAssignmentCallback.Input`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FactorTableNative.PayloadMeaning`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HeadSumNative.Accumulator`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighQueryEntryShadow.Data`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighQueryEntryShadow.erase`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighQueryProgram.Data`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighQueryReturnReplay.Data`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighQueryReturnReplay.restore`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighQuerySetup.preparedModel`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighQuerySetup.preparedProblem`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeCodeAssembly.command`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeHashQuerySetup.Data`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeHashQuerySetup.hiddenCap`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeLeafPreparation.afterCanonical`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeLeafPreparation.command`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeLeafRun.command`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeQueryPreparation.FrontArithmeticData`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeQueryPreparation.FrontArithmeticData.arithmeticSteps`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeQueryPreparation.FrontArithmeticData.cache`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeQueryPreparation.FrontArithmeticData.half`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeQueryPreparation.FrontArithmeticData.modulus`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeQueryPreparation.FrontArithmeticData.output`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeQueryPreparation.FrontArithmeticData.ringState`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeQueryPreparation.FrontData`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeQueryPreparation.FrontData.arithmetic`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeQueryPreparation.FrontData.arithmeticSteps`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeQueryPreparation.FrontData.cache`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeQueryPreparation.FrontData.first`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeQueryPreparation.FrontData.half`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeQueryPreparation.FrontData.modulus` and 86 more.
--
--   **Sources.** They come from these modules of lean/OAI/Algorithms, in whole or in part: `SubexponentialSAT_SqrtLogSpace_FactorAssignmentBoundary`, `SubexponentialSAT_SqrtLogSpace_FactorAssignmentCallbackNative`, `SubexponentialSAT_SqrtLogSpace_FactorTablePayloadMeaning`, `SubexponentialSAT_SqrtLogSpace_HeadSumNative`, `SubexponentialSAT_SqrtLogSpace_HighQueryEntryShadow`, `SubexponentialSAT_SqrtLogSpace_HighQueryProgram`, `SubexponentialSAT_SqrtLogSpace_HighQueryReturnReplay`, `SubexponentialSAT_SqrtLogSpace_HighQuerySetup`, `SubexponentialSAT_SqrtLogSpace_NativeCodeAssembly`, `SubexponentialSAT_SqrtLogSpace_NativeHashQuerySetup`, `SubexponentialSAT_SqrtLogSpace_NativeLeafPreparation`, `SubexponentialSAT_SqrtLogSpace_NativeLeafRun`, `SubexponentialSAT_SqrtLogSpace_NativeQueryPreparation`, `SubexponentialSAT_SqrtLogSpace_NodeAppendSpace`, `SubexponentialSAT_SqrtLogSpace_NodeReadoutSpace`, `SubexponentialSAT_SqrtLogSpace_QueryAssembler`, `SubexponentialSAT_SqrtLogSpace_QueryExecution`, `SubexponentialSAT_SqrtLogSpace_QueryModelBudgets`, `SubexponentialSAT_SqrtLogSpace_QueryNodeFinish`, `SubexponentialSAT_SqrtLogSpace_QueryNodeLoopSpace`, `SubexponentialSAT_SqrtLogSpace_QueryNodeReadout`, `SubexponentialSAT_SqrtLogSpace_QueryPairCommit`, `SubexponentialSAT_SqrtLogSpace_QueryPairEvaluation`, `SubexponentialSAT_SqrtLogSpace_QueryProgram`, `SubexponentialSAT_SqrtLogSpace_QueryReconstruction`, `SubexponentialSAT_SqrtLogSpace_QuerySourceSnapshot`, `SubexponentialSAT_SqrtLogSpace_QueryStreamCorrect`, `SubexponentialSAT_SqrtLogSpace_QueryTupleInit`, `SubexponentialSAT_SqrtLogSpace_QueryTupleState`, `SubexponentialSAT_SqrtLogSpace_QueryTupleVisitor`, `SubexponentialSAT_SqrtLogSpace_QueryVisitorHead`, `SubexponentialSAT_SqrtLogSpace_QueryVisitorSemantics`, `SubexponentialSAT_SqrtLogSpace_SignatureHeadLoader`, `SubexponentialSAT_SqrtLogSpace_SignatureTupleComplete`, `SubexponentialSAT_SqrtLogSpace_SignatureTupleRun`, `SubexponentialSAT_SqrtLogSpace_SignatureTupleSource`, `SubexponentialSAT_SqrtLog_ProducedQueryResourcesConstructor`, `SubexponentialSAT_SqrtLog_ProducedQueryResourcesOrigin`, `SubexponentialSAT_SqrtLog_ProducedQueryResourcesPacking`, `SubexponentialSAT_SqrtLog_ProducedQueryResourcesScalars`.
--
--   **Imports.** It imports the published bundle `Def_SubexponentialSAT`; the bundles `OAIQ081S168`, `OAIQ081S169`, `OAIQ081S171` and `OAIQ081S172` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ081S183` and `OAIQ081S185`; the statements `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FactorAssignmentBoundary.Entry.prepare`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FactorAssignmentCallback.Input.payload_correct`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FactorAssignmentCallback.Input.staged_factorJet`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HashQueryParameterBounds.accepted_envelope`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HashQueryParameterBounds.accepted_numeric_caps`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HashQueryParameterBounds.trial_envelope`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HashQueryParameterBounds.trial_numeric_caps`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HeadSumNative.Accumulator.advance`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HeadSumNative.Accumulator.initial`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeLeafContract.prepared_loaded`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeLeafPreparation.afterCanonical_eval`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeLeafRun.prepare_raw`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryAssembler.commitPair_eval`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryEnvelopeBudgets.chosen_ofPacking_cutoff`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryEnvelopeBudgets.eventually_ofPacking_bounds_of_scan`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryExecution.TupleEnd.command_run`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryExecution.replay_resources`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryNodeFinish.command_eval`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryProgram.signedScale_run_space`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryReconstruction.run_space_with_full_frame`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryStreamCorrect.NodeBoundary.sourceBank`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SignatureTupleComplete.scan_kernel`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.chosen_query_scalars_cutoff_of_scope_resources`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.eventually_scan_bounds_of_scope_resources` and `OAI.Algorithms.SubexponentialSAT.SqrtLog.ProducedQueryResources.rank_budget`; the proofs of `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FactorAssignmentBoundary.Entry.prepare`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FactorAssignmentCallback.Input.staged_factorJet`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HashQueryParameterBounds.accepted_envelope`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HashQueryParameterBounds.accepted_numeric_caps`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HashQueryParameterBounds.trial_envelope`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HashQueryParameterBounds.trial_numeric_caps`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HeadSumNative.Accumulator.advance`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HeadSumNative.Accumulator.initial`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighQueryCorrect.accepted`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighQueryCorrect.marked`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighQueryCount.run`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeHashQueries.accepted_replay`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeHashQueries.marked_replay`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeLeafContract.chosen_loaded_local_space`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeLeafContract.prepared_loaded`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeLeafContract.staged_rounds_time_hashCalls`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeLeafPreparation.afterCanonical_eval`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeLeafRun.prepare_raw`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryAssembler.commitPair_eval`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryEnvelopeBudgets.chosen_ofPacking_cutoff`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryEnvelopeBudgets.eventually_ofPacking_bounds_of_scan`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryExecution.TupleEnd.command_run`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryNodeFinish.command_eval`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryProgram.signedScale_run_space`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryReconstruction.run_space_with_full_frame`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryStreamCorrect.NodeBoundary.sourceBank`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SignatureTupleComplete.scan_kernel`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.chosen_query_scalars_cutoff_of_scope_resources`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.chosen_scalar_input_cap_of_scope_resources`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.eventually_scan_bounds_of_scope_resources` and `OAI.Algorithms.SubexponentialSAT.SqrtLog.ProducedQueryResources.rank_budget`.
-- source:
--   OpenAI, The Exponential Time Hypothesis is False, OpenAI Math Release, October 25, 2026, https://github.com/openai/math (result family 378; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/The-Exponential-Time-Hypothesis-is-False-October-25-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Algorithms at commit 7ef5c0c

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_SubexponentialSAT
import Definitions.Def_OAIQ081S168
import Definitions.Def_OAIQ081S169
import Definitions.Def_OAIQ081S171
import Definitions.Def_OAIQ081S172

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_FactorTablePayloadMeaning
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.Packing.nonemptyUniversal
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! The unchanged actual specialized payload and its source witness predicate.
Execution and resource theorems remain in FactorTableNative. -/
namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FactorTableNative
open OAI BitProgram StructuredCalls SubexpLiftRing SubexpQuarticRing
open OAI.Algorithms.SubexponentialSAT.SqrtLog OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgram
open PerturbationAssembly LayoutProgram DensePolynomialProgram
open OAI.Algorithms.SubexponentialSAT.Subexp OAI.Algorithms.SubexponentialSAT.Subexp.ConstructivePacking OAI.Algorithms.SubexponentialSAT.MulticolorTypes

/-- Meaning of a stored incidence payload. The low branch retains the actual
native source row witness; both branches expose a canonical scalar dictionary. -/
structure PayloadMeaning {r Q d : ℕ} (p : SourceBank.Parameters r Q d)
    (ps : List (ℕ × ℕ)) (P : PackingData (Fin ps.length) (UniversalType r Q 1))
    (u J n f : ℕ) (theta : Coeff (baseWidth 3 p.t) d)
    (s : FactorTableProgram.OuterStore) (j : ℕ) (payload : List Bool) : Prop where
  good : ∃ entries : List (MomentsProgram.Product.Entry n (baseWidth 3 p.t) d),
    TruncatedRingProgram.Good ∅ u J entries ∧ payload = MomentsProgram.Product.bytes entries
  source : if (s 574).getD j false then
    payload = Encoding.frame (originKey n) ++
      Encoding.frame (if (s 575).getD j false then s 548 else s 547)
    else ∃ xs : List (DensePolynomialProgram.Fixed.Array (baseWidth 3 p.t) d (p.R+1)),
      xs.length = n ∧
      LayoutSourceRowsProgram.RowProperty DensePolynomialProgram.Fixed.encode
        (fun z out => PolynomialExecutorProgram.meaning p.ops out.val =
          LayoutSourceRowsProgram.sourceRowFamily ps n f j
            (LayoutSourceRowsProgram.totalPackedSource p P) z)
        ((p.R+1)*(d*baseWidth 3 p.t)) 0 xs ∧
      payload = specializedRowPayload p.t p.model p.modulus p.cache J (p.R+1)
        theta (pairChoice xs (s 546)) (s 857)

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FactorTableNative
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_FactorAssignmentCallbackNative
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! Concrete physical inputs for the streamed factor callback. The source
context is the actual q.ctx, and the dispatcher determines every selected row
and clause. These predicates contain stored words and finite size bounds only.
Their construction from the actual loader/cache run remains an integration step. -/
namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FactorAssignmentCallback
open OAI BitProgram StructuredCalls SubexpLiftRing SubexpQuarticRing
open SqrtLog SqrtLog.LeafProgram HashCircuitProgram HashCircuitProgram.Native
open IdempotentApplyProgram.Steps MomentsProgram NativeSemantics
open FactorAssignmentProgram
open Subexp.ConstructivePacking MulticolorTypes LayoutProgram DensePolynomialProgram

noncomputable section

/-- Physical callback boundary, specialized to the source's actual arithmetic
context. In particular no incidence family or evaluator execution is a field. -/
structure Input {r Q n d : ℕ} (q : Factor.Spec r Q n d) (A S : ℕ)
    (one seed : FactorAssignmentLoop.Raw n (baseWidth 3 q.p.t) d)
    (a : FactorAssignmentProgram.Data) (f : ℕ) : Prop where
  scalar : FactorTableNative.ScalarMasters q.p.t q.p.model q.p.modulus q.p.cache q.J q.p.R
    q.theta (projectState localRegister FactorTableProgram.basePort a) n
  masters : FactorTableNative.SourceMasters q.p q.ps q.packing
    (projectState localRegister FactorTableProgram.basePort a)
  incoming : ∀ i, (a.stacks i).length ≤ A
  size : 1029*A+99+n+n*FactorTableProgram.literalRecordBound n
    (FactorTableNative.specializedPayloadBound n q.u q.J (baseWidth 3 q.p.t) d)+1 ≤ S
  radius : q.p.R+1 ≤ Q
  rows : a.stacks 701 = Encoding.encodeList id q.rawRows
  clauses : a.stacks 700 = Encoding.encodeList id q.clauses
  count : a.stacks 704 = List.replicate q.rawRows.length true
  mark : a.stacks 705 = Encoding.encodeNat q.mark
  flag : a.stacks 706 = [q.marked]
  factor : a.stacks 149 = (Encoding.encodeNat f).reverse
  seedBytes : a.stacks 151 = Product.bytes seed
  blank : ∀ i ∈ callbackScratch, a.stacks (lowStack i) = []
  tableBlank : ∀ i ∈ FactorTableSpace.writtenPorts, i ≠ 62 → i ≠ 556 → a.stacks i = []
  correction : (a.stacks 857).length = n
  hashWidth : (a.stacks 708).length = q.bitWidth
  hashModulus : BinaryArithmetic.toNat (a.stacks 707) = q.clauses.length
  ringShape : (a.stacks 280).length = d * baseWidth 3 q.p.t
  low : ∀ i : Fin 56, a.stacks (lowStack (Factor.nativeStacks (Memory.lowPort i))) =
    low q.ctx i
  oneBytes : a.stacks 69 = Product.bytes one
  minusBytes : a.stacks 76 = RingProgram.flat q.minus
  tape : a.stacks 143 = IdempotentApplyProgram.triplesTape q.digits
  shape : (a.stacks 88).length = n
  clauseOutput : a.stacks 63 = []
  clauseWork : ∀ i ∈ FactorServices.clauseScratch,
    a.stacks (lowStack (Clause.callerStacks i)) = []

end
end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FactorAssignmentCallback
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

def command : Code := .seq (clearMany clearPorts)
  (.call (ProgramLinking.liftProgram MomentsReadoutProgram.program registers ports))

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

/-- Actual cache staging, original native readout, and order-preserving append. -/
def command : Code := .seq prepare (.seq NodeReadoutSpace.command append)

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NodeAppendSpace
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

section SignedArray

attribute [local simp] Fin.coe_ofNat_eq_mod

open OAI.Algorithms.SubexponentialSAT.SqrtLog OAI.Algorithms.SubexponentialSAT.SubexpLiftRing OAI.Algorithms.SubexponentialSAT.SubexpQuarticRing
open MomentsProgram TruncatedRingProgram

def signedState (regs : Fin 8 → Bool) (s : Squarefree.ScaleProgram.Store)
    (sign : Bool) : State 8 41 :=
  ⟨regs, fun i => if h : i.val < 40 then Squarefree.ScaleProgram.tapes s ⟨i.val, h⟩
    else [sign]⟩

/-- Concrete port readiness for the signed scaler. This is a physical input
condition for this local instruction sequence, not an evaluation service. -/
structure ScaleReady (d : State 40 896) (e : Squarefree.ScaleProgram.Environment)
    (source : List Bool) (sign : Bool) : Prop where
  «stacks» : ∀ i, d.stacks (leafScalePorts i) =
    (signedState (fun j => d.regs (leafArithmeticRegs j))
      (Squarefree.ScaleProgram.idle e source []) sign).stacks i

/-- Only the normalizer's peripheral scratch must be empty. Its parameters
are shared with the actual scalar machine. -/
structure NormalizeScratchReady (d : State 40 896) : Prop where
  empty : ∀ i : Fin 28, i ≠ 5 → i ≠ 12 → i ≠ 24 → i ≠ 15 → i ≠ 27 →
    d.stacks (leafNormalizePorts i) = []

noncomputable def scaleLeafResult (d : State 40 896) (e : Squarefree.ScaleProgram.Environment)
    (rr : Fin 8 → Bool) (source : List Bool) (sign : Bool) : State 40 896 :=
  embedState leafArithmeticRegs leafScalePorts d
    (signedState rr {Squarefree.ScaleProgram.idle e [] [] with output := source} sign)

noncomputable def accumulateLeafResult (d : State 40 896) (e : Squarefree.ScaleProgram.Environment)
    (rr ss : Fin 8 → Bool) (source result : List Bool) (sign : Bool) : State 40 896 :=
  embedState leafArithmeticRegs leafNormalizePorts (scaleLeafResult d e rr source sign)
    (Normalize.state ss e.modulus e.width e.count result [])

noncomputable def pairUpdateResult (d : State 40 896) : State 40 896 :=
  ⟨readRegs d.regs 0 1 (d.stacks 848).head?, Function.update d.stacks 848 []⟩

end SignedArray

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryProgram
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

abbrev Data := State 40 896

noncomputable def headState (a : Data) (word tail address : List Bool) : Data :=
  let b := popWordState 840 838 (by decide) a word tail
  ⟨readRegs b.regs 0 1 (some true), Function.update b.stacks 843 address⟩

noncomputable def overwriteState (src dst : Fin 896) (a : Data) : Data :=
  copyState src dst ⟨readRegs a.regs 0 1 none, StackRoutines.clearStacks dst a.stacks⟩

def tested (a : Data) : Data := ⟨readRegs a.regs 0 1 (a.stacks 840).head?,a.stacks⟩

def finished (a : Data) : Data :=
  tested ⟨readRegs a.regs 0 1 none,StackRoutines.clearStacks 838 a.stacks⟩

/-- The source loop records only the remaining escaped frames and one unary
address. This is a proof predicate, not an executable list of visits. -/
structure FrameCursor (base : ℕ) (words : List (List Bool)) (a : Data) : Prop where
  frames : a.stacks 840 = suspendedFrames words
  current : a.stacks 838 = []
  address : a.stacks 843 = List.replicate (base + words.length) true
  guard : a.regs 1 = !words.isEmpty

noncomputable def restartState (a : Data) : Data :=
  overwriteState 845 843 (overwriteState 837 840 a)

noncomputable def stagedRepresentative (a : Data) : Data := overwriteState 838 859 a

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryTupleVisitor
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

abbrev Data := State 40 896

noncomputable def clearPairState (a : Data) : Data :=
  embedState FactorEnvironment.registerMap id a
    (SubexpSetupStorage.clearManyState pairScratch
      (projectState FactorEnvironment.registerMap id a))

def clearPairCost (a : Data) : ℕ :=
  SubexpSetupStorage.clearManyCost pairScratch (projectState FactorEnvironment.registerMap id a)+1

/-- The signed-update environment is read from persistent actual cache words;
no coefficient table or arithmetic scratch is supplied by an oracle. -/
def pairEnvironment (a : Data) : Squarefree.ScaleProgram.Environment :=
  ⟨a.stacks 194,a.stacks 202,a.stacks 203,a.stacks 201,a.stacks 211,a.stacks 204⟩

noncomputable def preparedPair (a : Data) : Data :=
  overwriteState 211 34 (FactorEnvironment.bootstrapResult (clearPairState a))

noncomputable def preparePairCost (a : Data) : ℕ := clearPairCost a+
  (FactorEnvironment.bootstrapCost (clearPairState a)+
    (2*((FactorEnvironment.bootstrapResult (clearPairState a)).stacks 34).length+
      7*((FactorEnvironment.bootstrapResult (clearPairState a)).stacks 211).length+8))

open SubexpLiftRing SubexpQuarticRing
open OAI.Algorithms.SubexponentialSAT.SqrtLog.MomentsProgram
open TruncatedRingProgram


/-! The interpolation-node cursor is the actual framed table emitted by the
ring producer. Its low-bank loader is embedded into the common leaf bank;
all high pair/tuple state is preserved by the injective port map. -/
namespace Nodes

abbrev LowData := State 40 768

def low (a : Data) : LowData := projectState id lowPort a

noncomputable def installed (a : Data) (b : LowData) : Data :=
  embedState id lowPort a b

theorem installed_low (a : Data) (b : LowData) (i : Fin 768) :
    (installed a b).stacks (lowPort i)=b.stacks i :=
  embedState_stack id lowPort a b (Fin.castAdd_injective 768 128) i

theorem installed_high (a : Data) (b : LowData) (i : Fin 896) (hi : 768 ≤ i.val) :
    (installed a b).stacks i=a.stacks i := by
  apply embedState_stack_frame
  rintro ⟨j,hj⟩
  have hv := congrArg Fin.val hj
  change j.val=i.val at hv
  omega

def initializedLow (a : Data) : LowData :=
  let s := RingNodeSetup.storeOf (low a)
  OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafNodeSamplesProgram.state (readRegs a.regs 0 1 none)
    (RingNodeSetup.initialized s)

noncomputable def initialized (a : Data) : Data :=
  NodeReadoutSpace.clearedMany [850,851,863] (installed a (initializedLow a))

noncomputable def initializeCost (a : Data) : ℕ :=
  RingNodeSetup.initializeCost (RingNodeSetup.storeOf (low a))+1+
    NodeReadoutSpace.clearCost [850,851,863] (installed a (initializedLow a))

def clearedNode (a : Data) : Data := NodeReadoutSpace.clearedMany nodeResetPorts a

def readLow (a : Data) (bits : List Bool) (tail : List (List Bool)) : LowData :=
  let c := low (clearedNode a)
  OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafNodeSamplesProgram.state (RingNodeSetup.nodeRegs c.regs)
    (RingNodeSetup.nodeRead (RingNodeSetup.storeOf c) bits tail)

noncomputable def begunNode (a : Data) (bits : List Bool) (tail : List (List Bool)) : Data :=
  installed (clearedNode a) (readLow a bits tail)

def beginNodeCost (a : Data) (bits : List Bool) : ℕ :=
  NodeReadoutSpace.clearCost nodeResetPorts a+9*bits.length+9

theorem readLow_frame (a : Data) (bits : List Bool) (tail : List (List Bool))
    (i : Fin 768) (h301 : i≠301) (h302 : i≠302) (h78 : i≠78) :
    (readLow a bits tail).stacks i=(low (clearedNode a)).stacks i := by
  have hs := congrArg (fun x : LowData => x.stacks i)
    (RingNodeSetup.state_storeOf (low (clearedNode a)))
  change OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafNodeSamplesProgram.tapes
    (RingNodeSetup.nodeRead (RingNodeSetup.storeOf (low (clearedNode a))) bits tail) i = _
  rw [RingNodeSetup.nodeRead_frame _ _ _ i h301 h302 h78]
  exact hs

theorem begunNode_frame (a : Data) (bits : List Bool) (tail : List (List Bool))
    (i : Fin 896) (hi : i∉301::nodeResetPorts) :
    (begunNode a bits tail).stacks i=a.stacks i := by
  have hc : i∉nodeResetPorts := by simp_all
  have hread : (begunNode a bits tail).stacks i=(clearedNode a).stacks i := by
    by_cases hlo : i.val<768
    · let j : Fin 768 := ⟨i.val,hlo⟩
      have hj : lowPort j=i := Fin.ext rfl
      change (installed (clearedNode a) (readLow a bits tail)).stacks i=_
      rw [←hj,installed_low,readLow_frame]
      · rfl
      all_goals intro h; have hh := congrArg lowPort h; rw [hj] at hh
      all_goals exact hi (by simp [hh,lowPort,nodeResetPorts])
    · exact installed_high _ _ i (by omega)
  rw [hread,clearedNode,NodeReadoutSpace.clearedMany_stack,ite_eq_right hc]



end Nodes


/-! Native multiplication of one completed head sum into the tuple product.
The original accumulator is relocated only at its two persistent operands. -/
namespace TupleMultiply

open OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgram

def raw (a : Data) : Data := NodeReadoutSpace.clearedMany [61,70] a

noncomputable def prepared (a : Data) : Data :=
  FactorEnvironment.bootstrapResult (clearPairState (raw a))

def environment (a : Data) : Product.Store :=
  Product.idle (a.stacks 194) (a.stacks 202) (a.stacks 203) (a.stacks 201)
    (a.stacks 204) (a.stacks 212) (a.stacks 243)

noncomputable def prepareCost (a : Data) : ℕ :=
  NodeReadoutSpace.clearCost [61,70] a+(clearPairCost (raw a)+
    FactorEnvironment.bootstrapCost (clearPairState (raw a)))

noncomputable def productState (a : Data) (b : Factor.Data) : Data := embedState id ports a b

end TupleMultiply

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryAssembler
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

abbrev Data := State 40 896

noncomputable def cleared (ports : List (Fin 896)) (a : Data) : Data :=
  embedState FactorAssignmentProgram.localRegister id a
    (clearManyState ports (projectState FactorAssignmentProgram.localRegister id a))

def clearCost (ports : List (Fin 896)) (a : Data) : ℕ :=
  clearManyCost ports (projectState FactorAssignmentProgram.localRegister id a) + 1

noncomputable def copied (a : Data) : Data :=
  QueryTupleVisitor.overwriteState 703 869 (QueryTupleVisitor.overwriteState 69 852 a)

noncomputable def finished (a : Data) : Data := cleared lowPorts (copied a)

noncomputable def finishCost (a : Data) : ℕ :=
  2 * (a.stacks 852).length + 7 * (a.stacks 69).length + 8 +
    (2 * (a.stacks 869).length + 7 * (a.stacks 703).length + 8 +
      clearCost lowPorts (copied a))


structure Initialized (a b : Data) {n width d : ℕ}
    (one : RingProgram.Code (SubexpQuarticRing.Word width) d) (u J : ℕ) : Prop where
  unit : b.stacks 852 = MomentsProgram.Product.bytes (FactorAssignmentProgram.oneEntries (n:=n) one)
  unit_good : NativeSemantics.Good (∅ : Finset (Fin n)) u J (FactorAssignmentProgram.oneEntries one)
  baseline : b.stacks 869 = a.stacks 703
  low : ∀ i : Fin 56, b.stacks (i.castAdd 840) = []
  scratch : b.stacks 841 = []
  frame : ∀ i, i ∉ changed → b.stacks i = a.stacks i


open CommandRegisterFrames

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryTupleInit
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

abbrev Data := State 40 896

/-- A source-prefix assertion for the actual compiled command table. -/
structure PrefixBound (command : Code) (steps : ℕ) (a : Data) (bound : ℕ) : Prop where
  bound : ∀ q z, q ≤ steps → Trace (compiled command 838 838) q
    (a.withPC (some (compiled command 838 838).entry)) z →
    ∀ i, (z.stacks i).length ≤ bound

namespace TupleEnd

open OAI.Algorithms.SubexponentialSAT.SqrtLog SubexpLiftRing SubexpQuarticRing MomentsProgram TruncatedRingProgram

noncomputable def cleaned (a : Data) : Data := QueryTupleInit.cleared currentHeadPorts a

noncomputable def result (a : Data) (rr : Fin 8 → Bool)
    (modulus width degree output : List Bool) : Data :=
  cleaned (QueryTupleSum.result a rr modulus width degree output)

end TupleEnd

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryExecution
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_QueryTupleState
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! The attained-tuple traversal retains the actual query inputs and the
meaning of its current pair accumulator. These predicates contain word
identities and algebraic facts, with no execution or algorithm-service fields. -/
namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryTupleState

open OAI BitProgram StructuredCalls OAI.Algorithms.SubexponentialSAT.SqrtLog SubexpLiftRing SubexpQuarticRing
open LeafProgram MomentsProgram LayoutProgram Subexp.ConstructivePacking MulticolorTypes
open TruncatedRingProgram SubexpSetupStorage

abbrev Data := State 40 896

structure QueryMasterFrame (before after : Data) : Prop where
  word : ∀ i∈masterPorts, after.stacks i=before.stacks i

/-- Inner head and tuple products retain the full dense value. Only the
outer pair accumulator uses the additive marker readout. -/
structure DenseWord {r Q n d : ℕ} (q : Factor.Spec r Q n d) (port : Fin 896)
    (value : Dense (q.p.model.O q.p.t) q.p.t q.J) (a : Data) : Prop where
  entries : ∃ entries : List (Product.Entry n (baseWidth 3 q.p.t) d),
    a.stacks port=Product.bytes entries ∧ Good ∅ q.p.t q.J entries ∧
      rawValue q.p.t q.J q.p.ops.decode entries=value

/-- The same actual dictionary supplies the bytes, empty-support storage
bound, and additive readout meaning. No stronger equality of unobserved
lifting-marker coefficients is required. -/
structure PairAccumulatorMeaning {r Q n d : ℕ} (q : Factor.Spec r Q n d)
    (value : Truncated (q.p.model.O q.p.t) q.J) (a : Data) : Prop where
  entries : ∃ entries : List (Product.Entry n (baseWidth 3 q.p.t) d),
    a.stacks 851=Product.bytes entries ∧ Good ∅ q.p.t q.J entries ∧
      Dense.readout (rawValue q.p.t q.J q.p.ops.decode entries)=value

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryTupleState
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
open IdempotentApplyProgram.Steps MomentsProgram NativeSemantics
open OAI.Algorithms.SubexponentialSAT.SubexpLiftRing OAI.Algorithms.SubexponentialSAT.SubexpQuarticRing
open FactorAssignmentProgram

noncomputable section
attribute [local simp] Fin.coe_ofNat_eq_mod

/-- Physical entry facts produced by the actual addressed loader, ring
producer, accepted-head overlay, and the previous accumulator's reset. -/
structure Entry {r Q n d : ℕ} (q : Factor.Spec r Q n d) (P M S : ℕ)
    (a : FactorAssignmentProgram.Data) : Prop where
  scalar : FactorTableNative.ScalarMasters q.p.t q.p.model q.p.modulus q.p.cache q.J q.p.R
    q.theta (projectState localRegister FactorTableProgram.basePort a) n
  masters : FactorTableNative.SourceMasters q.p q.ps q.packing
    (projectState localRegister FactorTableProgram.basePort a)
  incoming : WordBound P a
  copies : ∀ pair ∈ LeafNodeCacheProgram.directCopies,
    (a.stacks (lowStack pair.1)).length ≤ M
  ambientCap : (a.stacks 128).length ≤ M
  oneCap : (a.stacks 207).length ≤ M
  cacheFits : 4*M+6 ≤ P
  seedFits : FactorAssignmentLoop.byteBound n (baseWidth 3 q.p.t) d q.u q.J ≤ P
  lowBlank : ∀ i : Fin 56, a.stacks (i.castAdd 840) = []
  width : a.stacks 202 = q.width
  degree : a.stacks 204 = List.replicate d true
  precision : a.stacks 212 = List.replicate q.u true
  minus : q.minus = q.p.minusOne
  digits : a.stacks 281 = IdempotentApplyProgram.triplesTape q.digits
  rows : a.stacks 701 = Encoding.encodeList id q.rawRows
  clauses : a.stacks 700 = Encoding.encodeList id q.clauses
  count : a.stacks 704 = List.replicate q.rawRows.length true
  mark : a.stacks 705 = Encoding.encodeNat q.mark
  flag : a.stacks 706 = [q.marked]
  correction : (a.stacks 857).length = n
  hashWidth : (a.stacks 708).length = q.bitWidth
  hashModulus : BinaryArithmetic.toNat (a.stacks 707) = q.clauses.length
  size : 1029*P+99+n+n*FactorTableProgram.literalRecordBound n
    (FactorTableNative.specializedPayloadBound n q.u q.J (baseWidth 3 q.p.t) d)+1 ≤ S
  radius : q.p.R+1 ≤ Q

/-- Physical prepared-store facts, with no evaluator, layout service, or
query result among the fields. The mutable149/150/151 fields are supplied by
the concrete record reader and current Good-empty-support accumulator. -/
structure Ready {r Q n d : ℕ} (q : Factor.Spec r Q n d) (P S : ℕ)
    (one : FactorAssignmentLoop.Raw n (baseWidth 3 q.p.t) d)
    (a : FactorAssignmentProgram.Data) : Prop where
  scalar : FactorTableNative.ScalarMasters q.p.t q.p.model q.p.modulus q.p.cache q.J q.p.R
    q.theta (projectState localRegister FactorTableProgram.basePort a) n
  masters : FactorTableNative.SourceMasters q.p q.ps q.packing
    (projectState localRegister FactorTableProgram.basePort a)
  incoming : ∀ i, (a.stacks i).length ≤ P
  size : 1029*P+99+n+n*FactorTableProgram.literalRecordBound n
    (FactorTableNative.specializedPayloadBound n q.u q.J (baseWidth 3 q.p.t) d)+1 ≤ S
  radius : q.p.R+1 ≤ Q
  rows : a.stacks 701 = Encoding.encodeList id q.rawRows
  clauses : a.stacks 700 = Encoding.encodeList id q.clauses
  count : a.stacks 704 = List.replicate q.rawRows.length true
  mark : a.stacks 705 = Encoding.encodeNat q.mark
  flag : a.stacks 706 = [q.marked]
  blank : ∀ i ∈ callbackScratch, a.stacks (lowStack i) = []
  tableBlank : ∀ i ∈ FactorTableSpace.writtenPorts, i ≠ 62 → i ≠ 556 → a.stacks i = []
  correction : (a.stacks 857).length = n
  hashWidth : (a.stacks 708).length = q.bitWidth
  hashModulus : BinaryArithmetic.toNat (a.stacks 707) = q.clauses.length
  ringShape : (a.stacks 280).length = d * baseWidth 3 q.p.t
  low : ∀ i : Fin 56, a.stacks (lowStack (Factor.nativeStacks (Memory.lowPort i))) =
    low q.ctx i
  oneBytes : a.stacks 69 = Product.bytes one
  minusBytes : a.stacks 76 = RingProgram.flat q.minus
  tape : a.stacks 143 = IdempotentApplyProgram.triplesTape q.digits
  shape : (a.stacks 88).length = n
  clauseOutput : a.stacks 63 = []
  clauseWork : ∀ i ∈ FactorServices.clauseScratch,
    a.stacks (lowStack (Clause.callerStacks i)) = []
  seedFits : FactorAssignmentLoop.byteBound n (baseWidth 3 q.p.t) d q.u q.J ≤ P

end
end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FactorAssignmentBoundary
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_HeadSumNative
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! Correctness of the fixed head rescan. The invariant retains the current
normalized dictionary and the actual immutable source words. Its compact
boundary is reused after every candidate; no execution service is assumed. -/
namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HeadSumNative
open OAI BitProgram StructuredCalls SqrtLog SqrtLog.LeafProgram SqrtLog.MomentsProgram
open SubexpLiftRing SubexpQuarticRing TruncatedRingProgram HeadSumProgram
open HeadIdentifierProgram BucketTupleProgram.Concrete
open QueryTupleState (masterPorts QueryMasterFrame )
open scoped BigOperators

noncomputable section

structure Accumulator {r Q n d : ℕ} (q : Factor.Spec r Q n d)
    (origin : HeadSumProgram.Data) (contribution : ℕ → Dense (q.p.model.O q.p.t) q.u q.J)
    (P i : ℕ) (a : HeadSumProgram.Data) : Prop where
  compact : ∀ j, (a.stacks j).length ≤ P
  retained : ∀ j ∈ retainedPorts, a.stacks j = origin.stacks j
  low : ∀ j : Fin 56, a.stacks (j.castAdd 840) = []
  scratch0 : a.stacks 883 = []
  scratch1 : a.stacks 884 = []
  partialSum : ∃ entries : List (Product.Entry n (baseWidth 3 q.p.t) d),
    Good ∅ q.u q.J entries ∧ a.stacks 853 = Product.bytes entries ∧
      rawValue q.u q.J q.p.ops.decode entries = ∑ j ∈ Finset.range i, contribution j

end
end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HeadSumNative
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_QueryModelBudgets
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryModelBudgets
open SqrtLog SqrtLog.LeafParametersProgram Circuit

/-- The serializer changes only two previously empty numeric ports. -/
theorem serialized_model_values_le (x : Input) (padding : Fin 8 → ℕ) (S : ℕ)
    (h : ∀ j, (result Serialization.code (Execute.guardedModel x padding)).val j ≤ S) :
    ∀ j, (Execute.guardedModel x padding).val j ≤ S := by
  intro j
  by_cases h44 : j = 44
  · subst j
    simp [Execute.guardedModel, Fin.coe_ofNat_eq_mod]
  by_cases h45 : j = 45
  · subst j
    simp [Execute.guardedModel, Fin.coe_ofNat_eq_mod]
  exact (Serialization.frame _ j h44 h45) ▸ h j

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryModelBudgets
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_NativeQueryPreparation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! Concrete query packing and arithmetic preparation. Numeric and physical
input caps are kept separate from the subsequent exponential node traversal.
Every arithmetic object is returned by its actual native producer. -/
namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeQueryPreparation

open OAI BitProgram StructuredCalls SqrtLog LeafParametersProgram
open LeafProgram.Query CostAssembly.Polynomial

/-- The literal packing input includes every initial stack, physical padded
parameter word, and the numerically bounded complete type alphabet. -/
theorem packing_size_le (a : Data) (p : PackingCallerProgram.Problem) (S : ℕ)
    (hsources : PackingCallerProgram.Sources a p)
    (hwords : ∀ i, (a.stacks i).length ≤ S)
    (hn : p.n ≤ S) (hf : p.factors ≤ S) (hD : p.incidences ≤ S)
    (hr : p.r ≤ S) (hQ : p.Q ≤ S) (heps : p.s ≤ S)
    (htypes : p.r ^ (2 * p.Q) ≤ S) :
    PackingCallerProgram.globalSize a p ≤ 790 * (S + 1) := by
  have halphabet : p.r ^ p.Q ≤ S := by
    calc
      _ ≤ (p.r ^ p.Q) ^ 2 := Nat.le_self_pow (by decide) _
      _ = p.r ^ (2 * p.Q) := by rw [← pow_mul, Nat.mul_comm p.Q 2]
      _ ≤ S := htypes
  have hscopes := hwords 718
  rw [hsources.scopes] at hscopes
  have hmask := hwords 719
  rw [hsources.mask] at hmask
  have hmass : PackingCallerProgram.inputMass a ≤ 768 * S := by
    unfold PackingCallerProgram.inputMass
    calc
      _ ≤ ∑ _i : Fin 768, S := Finset.sum_le_sum (fun i _ => hwords i)
      _ = _ := by simp
  have h709 := hwords 709
  have h720 := hwords 720
  have h721 := hwords 721
  have h722 := hwords 722
  have h723 := hwords 723
  change PackingCallerProgram.inputMass a +
    (p.n + p.factors + p.incidences + p.r + p.Q + p.s + p.r ^ p.Q + p.r ^ (2 * p.Q) +
      (PackingIncidenceInput.Scan.scopeBits p.scopes).length + p.mask.length +
      (a.stacks 720).length + (a.stacks 709).length + (a.stacks 722).length +
      (a.stacks 723).length + (a.stacks 721).length + 1) + 1 ≤ _
  omega

theorem shadow_empty (a : Data) (h : PackingCallerProgram.Empty a) :
    PackingCallerProgram.Empty (shadow a) := by
  constructor
  · intro i
    change (shadow a).stacks (PackingCallerProgram.Wide.ports i) = []
    rw [shadow_visible a _ (Or.inr (by change 332 < 417+i.val; omega))]
    exact h.bank i
  · exact (shadow_visible a 684 (by decide)).trans h.temporary
  · exact (shadow_visible a 133 (by decide)).trans h.words
  · exact (shadow_visible a 135 (by decide)).trans h.metadata
  · exact (shadow_visible a 136 (by decide)).trans h.plans
  · intro i
    exact (shadow_visible a _ (Or.inr (by change 332 < 730+i.val; omega))).trans (h.parked i)

/-- The actual incidence scan retains one neutral factor for each uncovered
low coordinate. This is the original native factor-count identity. -/
theorem packing_factors_eq (q : LeafQueryFrontend.Query) (k : ℕ) (hg : Guard (q.input k)) :
    (packingProblem q k hg).factors = (q.input k).factors := by
  unfold PackingCallerProgram.Problem.factors packingProblem
  rw [PackingIncidenceInput.Stats.native_factor_count]
  rfl

/-- Concrete packing data returned by the guarded frontend preparation. -/
structure FrontPackingData (q : LeafQueryFrontend.Query) (k : ℕ)
    (hg : Guard (q.input k)) where
  first : MulticolorTypes.Word (packingProblem q k hg).r (packingProblem q k hg).Q
  rest : List (MulticolorTypes.Word (packingProblem q k hg).r (packingProblem q k hg).Q)
  packed : Data
  packingSteps : ℕ

/-- Concrete arithmetic data returned after packing. A standard product keeps
elaboration of the dependent ring objects shallow. -/
def FrontArithmeticData (q : LeafQueryFrontend.Query) (k : ℕ)
    (l : Fin 8 → ℕ) : Type :=
  ℕ × LeafRingSetupProgram.Data ×
    SubexpPreparedQuartic.Modulus 3 ((Execute.guardedModel (q.input k) l).val 33) ×
    RingProgram.ScalarCache 3 ((Execute.guardedModel (q.input k) l).val 33) ×
    RingProgram.ScalarCode 3 ((Execute.guardedModel (q.input k) l).val 33) × Data

namespace FrontArithmeticData

variable {q : LeafQueryFrontend.Query} {k : ℕ} {l : Fin 8 → ℕ}

abbrev arithmeticSteps (data : FrontArithmeticData q k l) := data.1
abbrev ringState (data : FrontArithmeticData q k l) := data.2.1
abbrev modulus (data : FrontArithmeticData q k l) := data.2.2.1
abbrev cache (data : FrontArithmeticData q k l) := data.2.2.2.1
abbrev half (data : FrontArithmeticData q k l) := data.2.2.2.2.1
abbrev output (data : FrontArithmeticData q k l) := data.2.2.2.2.2

end FrontArithmeticData

/-- All concrete data produced by native query preparation. -/
def FrontData (q : LeafQueryFrontend.Query) (k : ℕ) (hg : Guard (q.input k))
    (l : Fin 8 → ℕ) : Type :=
  FrontPackingData q k hg × FrontArithmeticData q k l

namespace FrontData

variable {q : LeafQueryFrontend.Query} {k : ℕ} {hg : Guard (q.input k)}
  {l : Fin 8 → ℕ}

abbrev packing (data : FrontData q k hg l) := data.1
abbrev arithmetic (data : FrontData q k hg l) := data.2
abbrev first (data : FrontData q k hg l) := data.packing.first
abbrev rest (data : FrontData q k hg l) := data.packing.rest
abbrev packed (data : FrontData q k hg l) := data.packing.packed
abbrev packingSteps (data : FrontData q k hg l) := data.packing.packingSteps
abbrev arithmeticSteps (data : FrontData q k hg l) := data.arithmetic.arithmeticSteps
abbrev ringState (data : FrontData q k hg l) := data.arithmetic.ringState
abbrev modulus (data : FrontData q k hg l) := data.arithmetic.modulus
abbrev cache (data : FrontData q k hg l) := data.arithmetic.cache
abbrev half (data : FrontData q k hg l) := data.arithmetic.half
abbrev output (data : FrontData q k hg l) := data.arithmetic.output

end FrontData

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeQueryPreparation
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

def command : Code := .seq NodeAppendSpace.command finishNode

def program := compiled command 850 863

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryNodeFinish
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

def command : Cmd 40 896 :=
  .seq NodeAppendSpace.handoff
    (liftCommand coreCommand 256 323 id (Fin.castAdd 128))

def program := compiled command 863 323

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryReconstruction
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

def bootstrapResult (s : Native.Inputs) (a : Data)
    (ra : Fin 3 → Bool) (rd rc : Fin 8 → Bool) (words : List (List Bool)) : Data :=
  retainedState (bootState a ra rd rc s.r s.node.val s.records s.height (unary s.R) s.width words)

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SignatureHeadLoader
end
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

abbrev Data := State 40 896

open HashGreedyProgram.NativeRound

end
end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighQueryProgram
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_HighQueryEntryShadow
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! The proof shadow erases exactly the five suspended caller words. Actual
query sources, reusable workspace, reference and temporary bytes are retained.
No length premise is imposed on any erased word; this module constructs no
execution and changes no instruction table. -/
namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighQueryEntryShadow

open BitProgram StructuredCalls SqrtLog ProgramTapeReplay

abbrev Data := State 40 896

/-- This is exactly the shadow used by the actual query's replay theorem. -/
def erase (a : Data) : Data :=
  rebaseState (fun i => i ∈ HighQueryProgram.Carried.words) (fun _ => []) a

@[simp] theorem erase_regs (a : Data) : (erase a).regs = a.regs := rfl

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighQueryEntryShadow
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_HighQueryReturnReplay
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! The complete fixed query has an actual same-step replay after erasing its
five suspended caller words. These lemmas transport the exact output contracts
and every prefix of that execution. They do not construct a query evaluator;
the actual marked or accepted execution is supplied by the count proof. -/
namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighQueryReturnReplay

open BitProgram StructuredCalls SqrtLog.ProgramTapeReplay
open HashGreedyProgram.NativeRound HighQueryEntryShadow

abbrev Data := State 40 896

local notation "H" => (fun i : Fin 896 => i ∈ HighQueryProgram.Carried.words)

/-- Proof-side restoration of exactly the bytes ignored by the fixed query. -/
def restore (input output : Data) : Data := rebaseState H input.stacks output

@[simp] theorem restore_regs (input output : Data) :
    (restore input output).regs = output.regs := rfl

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighQueryReturnReplay
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_HighQuerySetup
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! Concrete preparation and fresh high-counter initialization for the fixed
marked and accepted queries. The witness below is produced by the actual
programs; no implementation or evaluator is supplied as a hypothesis. -/
namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighQuerySetup

open OAI BitProgram StructuredCalls SqrtLog LeafParametersProgram
open LeafProgram.Query HashGreedyProgram.NativeRound
open HighMarkedFrontend

def preparedModel (q : LeafQueryFrontend.Query) (k : ℕ) (padding : Fin 8 → ℕ) :=
  Execute.guardedModel (q.input k) padding

noncomputable def preparedProblem (q : LeafQueryFrontend.Query) (k : ℕ)
    (hg : Guard (q.input k)) :=
  packingProblem q k hg

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighQuerySetup
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

/-- Native code construction uses the metadata producer and both streamed
searches before physically serializing their retained matrices. -/
def command : Cmd 40 896 := .seq parameters (.seq NativeCode.searches serialize)

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

/-- Actual code searches and row serialization followed by paid selector
initialization. The code matrices are produced by the searches themselves. -/
def afterCanonical : Cmd 40 896 := .seq NativeCodeAssembly.command afterCode

/-- The executable preparation is fixed before its input. Numeric parameters
occur only in the correctness and resource statements. -/
def command : Cmd 40 896 := .seq NativeLeafSetup.canonicalStart afterCanonical

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeLeafPreparation
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_ProducedQueryResourcesOrigin
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Actual selector provenance for a query.  This package includes every
trial (successful or not), the final selected rows, and an optional mark.
It carries no resource inequality about the resulting query. -/
namespace SubexponentialSAT.SqrtLog.ProducedQueryResources
open Filter
open scoped Topology
open Asymptotic HashSelectProgram LeafQueryFrontend LeafScopeResourceBounds HighIncidenceProgram

noncomputable section

/-- Numerical output from the actual neutral-completed scan and high mask. -/
structure ScanBounds (q : Query) (k exponent : ℕ) : Prop where
  guard : LeafParametersProgram.Guard (q.input k)
  residual : (q.input k).freeCount ≤ ambient q ∧ ambient q ≤ 2*(q.input k).freeCount
  factors : (q.input k).factors ≤ 4*ambient q+HashSelect.loopCap (ambient q) q.clauses.length+2
  occurrence : (q.input k).occurrence ≤ L (q.input k).freeCount^exponent
  arity : (q.input k).arity ≤ L (q.input k).freeCount^exponent
  branch : (Branches.trueCount (highMask q.scopeRows (ambient q)) : ℝ) ≤
    (ambient q : ℝ)/Real.sqrt (L (ambient q) : ℝ)

end
end SubexponentialSAT.SqrtLog.ProducedQueryResources

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_ProducedQueryResourcesScalars
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Polynomial numerical dimensions of every actual large-input query.
These bounds do not include serialized bucket or sparse-dictionary buffers. -/
namespace SubexponentialSAT.SqrtLog.ProducedQueryResources
open Filter Asymptotic LeafQueryFrontend
open scoped Topology

/-- This cap applies to scalar counts only. The free/incidence counts are
read from the native scan; no independent statistics are supplied. -/
structure SmallInputs (q : Query) (k n : ℕ) : Prop where
  free : (q.input k).freeCount ≤ n
  clauses : (q.input k).clauses ≤ n^2
  occurrence : (q.input k).occurrence ≤ n
  arity : (q.input k).arity ≤ n
  factors : (q.input k).factors ≤ n^2
  incidences : (q.input k).incidences ≤ n^2
  width : k ≤ n
  magnitude : LeafParametersProgram.magnitude (q.input k) ≤ n^4

end SubexponentialSAT.SqrtLog.ProducedQueryResources

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_ProducedQueryResourcesConstructor
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Numerical constructor for an actual query. Rank and maximum head size
are its two geometry arguments; ProducedQueryRank and LayoutProducedHeads
supply them from the actual packing. This module does not assert that an
arbitrary pair of natural numbers has those geometric bounds. -/
namespace SubexponentialSAT.SqrtLog.ProducedQueryResources
open Filter Asymptotic LeafQueryFrontend CostAssembly
open scoped Topology

noncomputable section

/-- Uniform absolute coefficient-height envelope for the literal pulled
matrix. The ambient dimension is kept distinct from the free schedule. -/
def matrixHeight (q : Query) (k : ℕ) : ℕ :=
  2*(q.input k).occurrence*(8*layoutQ (q.input k).freeCount)^(
    2*layoutCutoff (q.input k).freeCount (q.input k).occurrence)

def make (q : Query) (k B labelRows headSize C d qi e : ℕ) : Resources where
  residual := (q.input k).freeCount
  clauses := q.clauses.length
  initialOccurrence := B
  localOccurrence := (q.input k).occurrence
  factors := (q.input k).factors
  branchVars := HighIncidenceProgram.Branches.trueCount (highMask q.scopeRows (ambient q))
  labelBase := 2*ambient q*matrixHeight q k+1
  labelRows := labelRows
  heads := layoutR (q.input k).freeCount
  headSize := headSize
  setup := CodeSetupOuterCost.setupMajorant C d qi (ambient q)
  bits := (ambient q+1)^e
  ordinary := (ambient q+1)^e

end
end SubexponentialSAT.SqrtLog.ProducedQueryResources

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_ProducedQueryResourcesPacking
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! The resource geometry is read from the actual searched packing and its
emitted original-variable word rows. No rank or head-size number is supplied
as a machine input. -/
namespace SubexponentialSAT.SqrtLog.ProducedQueryResources
open scoped BigOperators
open SubexponentialSAT.MulticolorTypes
open LeafQueryFrontend
noncomputable section

abbrev problem (q : Query) (k : ℕ) (hg : LeafParametersProgram.Guard (q.input k)) :=
  LeafProgram.Query.packingProblem q k hg

def rank (q : Query) (k : ℕ) (hg : LeafParametersProgram.Guard (q.input k))
    (a : Word (problem q k hg).r (problem q k hg).Q)
    (tail : List (Word (problem q k hg).r (problem q k hg).Q)) : ℕ :=
  let p := problem q k hg
  let R := (LeafParametersProgram.produce (q.input k)).R
  CostAssembly.maxTotalRank Finset.univ
    (BucketProgram.ProducedRank.actualRank (ProducedQueryRank.packing p a tail)
      (ProducedQueryRank.owner p) (SubexponentialSAT.Subexp.TailInterval.intervalStart p.r p.Q R) R
      (ProducedQueryRank.rows p a tail) (lowBytes q))

def headSize (q : Query) (k : ℕ) (hg : LeafParametersProgram.Guard (q.input k))
    (a : Word (problem q k hg).r (problem q k hg).Q)
    (tail : List (Word (problem q k hg).r (problem q k hg).Q)) : ℕ :=
  let p := problem q k hg
  LayoutProducedHeads.maxSelected p.n p.Q p.r (ProducedQueryRank.rows p a tail) (lowBytes q)

def ofPacking (q : Query) (k B C d qi e : ℕ)
    (hg : LeafParametersProgram.Guard (q.input k))
    (a : Word (problem q k hg).r (problem q k hg).Q)
    (tail : List (Word (problem q k hg).r (problem q k hg).Q)) : CostAssembly.Resources :=
  make q k B (rank q k hg a tail) (headSize q k hg a tail) C d qi e

end
end SubexponentialSAT.SqrtLog.ProducedQueryResources

end OAI.Algorithms
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

/-- No formula, successful code, or input-dependent table occurs in the code. -/
def command (markedQuery acceptedQuery : Cmd 40 896) : Cmd 40 896 :=
  .seq NativeLeafPreparation.command (afterPreparation markedQuery acceptedQuery)

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeLeafRun
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_NativeHashQuerySetup
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! The actual prepared selector boundary supplies the literal marked and
history-only frontend, packing, arithmetic and high-counter initialization.
The common bound is unchanged. Suspended caller words have a separate bound
which never occurs in the measured setup time. -/
namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeHashQuerySetup

open BitProgram StructuredCalls SqrtLog DisjointReuse LeafParametersProgram
open HashGreedyCode HashQueryEntry HighFrontendSources NativeQueryInputBounds
open HighMarkedFrontend HighQuerySetup ProducedQueryResources
open HashGreedyProgram.NativeRound

abbrev Data := State 40 896

/-- Every actual callback has such a finite hidden cap. Choosing it imposes
no restriction on the collector tail, mass or remaining-round word. -/
def hiddenCap (a : Data) : ℕ :=
  HighQueryProgram.Carried.words.sup (fun i => (a.stacks i).length)

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeHashQuerySetup
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_QueryNodeLoopSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! The fixed node loop consumes the producer's framed cursor. Each actual
node execution supplies its own emitted coefficient word; no uniform choice
of byte representatives across register states is required. The indexed
invariant carries the complete retained query context between nodes. -/

namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryNodeLoopSpace

open BitProgram StructuredCalls

abbrev Data := State 40 896

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryNodeLoopSpace
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_QueryPairCommit
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! The signed finite-difference term is committed to the actual node word.
The pair product and the node sum use the same stored dictionaries as their
validity and readout witnesses. Marker readout remains additive. -/
namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryPairCommit

open OAI BitProgram StructuredCalls OAI.Algorithms.SubexponentialSAT.SqrtLog SubexpLiftRing SubexpQuarticRing
open LeafProgram MomentsProgram LayoutProgram
open TruncatedRingProgram QueryProgram QueryTupleState

abbrev Data := State 40 896

/-- The actual node dictionary, after additive shared-marker readout. -/
structure NodeAccumulatorMeaning {r Q n d : ℕ} (q : Factor.Spec r Q n d)
    (value : Truncated (q.p.model.O q.p.t) q.J) (a : Data) : Prop where
  entries : ∃ entries : List (Product.Entry n (baseWidth 3 q.p.t) d),
    a.stacks 850=Product.bytes entries ∧ Good ∅ q.p.t q.J entries ∧
      Dense.readout (rawValue q.p.t q.J q.p.ops.decode entries)=value

open CommandRegisterFrames

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryPairCommit
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_SignatureTupleSource
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! Shared actual produced input data for the tuple controller and visitor.
The record contains source words, native readiness and paid cache semantics;
it contains no evaluator, resource contract, or successful execution premise. -/
noncomputable section
namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SignatureTupleSource
open OAI BitProgram StructuredCalls OAI.Algorithms.SubexponentialSAT.SqrtLog
open SignatureTupleProgram SignatureTupleNative SignatureTupleRefinement SignatureTupleLoader
open LeafHeadSetupProgram OAI.Algorithms.SubexponentialSAT.SubexpSetupStorage

/-- Native source data and the actual cache words produced by node bootstrap.
This record contains no evaluator, query service, or execution assumption. -/
structure ProducedSource where
  input : Native.Inputs
  source : Data
  ready : Native.Ready input source
  bound : ℕ
  bounded : WordBound bound source
  rows : input.rows.length=input.n+input.N
  owner : Fin input.D → Fin input.n
  plans : Fin input.D → ℕ × ℕ
  plans_eq : input.plans=List.ofFn plans
  owners_eq : ∀ i,(plans i).1=(owner i).val
  addressRegisters : Fin 3 → Bool
  dimensionRegisters : Fin 8 → Bool
  cacheRegisters : Fin 8 → Bool
  cacheWords : List (List Bool)
  cache : CacheCorrect input.height (unary input.R) input.width cacheWords

namespace ProducedSource

def base (s : ProducedSource) : ℕ := s.input.node.val*s.input.r

def headSize (s : ProducedSource) (depth : ℕ) : ℕ :=
  (selectedHeads s.input.n s.input.rows s.input.low (s.base+depth)).length

def key (s : ProducedSource) (depth : ℕ) : Fin (2^s.headSize depth) → Fin s.input.D → ℤ :=
  AttainedSignatures.integerKey (integerMatrix s.input s.owner (s.base+depth))

def masters (s : ProducedSource) : Data :=
  Native.start s.input s.source s.addressRegisters s.dimensionRegisters s.cacheRegisters s.cacheWords

end ProducedSource


end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SignatureTupleSource
end
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_QueryNodeReadout
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! The actual node dictionary is read into increasing Taylor coefficients,
appended to the interpolation stream, and reclaimed before the next node.
The dictionary witness, encoded result and resource trace are shared. -/
namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryNodeReadout

open OAI BitProgram StructuredCalls OAI.Algorithms.SubexponentialSAT.SqrtLog SubexpLiftRing SubexpQuarticRing
open LeafProgram MomentsProgram LayoutProgram TruncatedRingProgram QueryTupleState
open QueryPairCommit QueryReadyConstruction

abbrev Data := State 40 896

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryNodeReadout
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

/-- Actual multiplication time after one normalized head sum. -/
def multiplyBudget {r Q n d : ℕ} (q : Factor.Spec r Q n d) (P : ℕ) : ℕ :=
  51000*(P+1)+FactorProductSpace.budget n (baseWidth 3 q.p.t) d q.p.t q.J

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
abbrev Data := State 40 896

def baselineCost (s : ProducedSource) (B : ℕ) : ℕ :=
  QueryVisitorLoad.runEnvelope s.bound B+90*B+89


open scoped BigOperators

def evaluationSpace (s : ProducedSource) {d : ℕ}
    (q : LeafProgram.Factor.Spec s.input.r s.input.Q s.input.n d) (P B : ℕ) : ℕ :=
  max (QueryVisitorLoad.runEnvelope s.bound P)
    (max (996*P+200) (max B (896*P+QueryVisitorHead.multiplyBudget q P)))

def visitorSpace (s : ProducedSource) {d : ℕ}
    (q : LeafProgram.Factor.Spec s.input.r s.input.Q s.input.n d) (P B : ℕ) : ℕ :=
  max (2400*(P+1)+baselineCost s P+
    QueryTupleSum.budget s.input.n (baseWidth 3 q.p.t) d q.p.t q.J P)
    (evaluationSpace s q P B)

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryVisitorSemantics
end
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_SignatureTupleComplete
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! Concrete cursor invariants for the fixed attained-signature controller.
The integer head matrices come from native source words.  Each boundary uses
one retained cap; reload and predecessor-scan prefix bounds remain transient.
-/

noncomputable section
namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SignatureTupleComplete

open Classical
open OAI.Algorithms.SubexponentialSAT.SubexpLiftRing
open OAI BitProgram StructuredCalls OAI.Algorithms.SubexponentialSAT.SqrtLog
open LeafHeadSetupProgram OAI.Algorithms.SubexponentialSAT.SubexpSetupStorage
open SignatureTupleDFS SignatureTupleTraversal SignatureTupleProgram
open SignatureTupleNative SignatureTupleRefinement SignatureTupleLoader SignatureTupleSource

/-- Fixed time and prefix caps for one controller event. Candidate numbers
occur only as a multiplicative running-time charge. -/
def eventPolynomial (s : ProducedSource) (F : ℕ) : ℕ :=
  scannerEnvelope s.bound+runEnvelope s.bound F+200*F+200

def prefixEnvelope (s : ProducedSource) (F : ℕ) : ℕ :=
  4000*(F+1)+runEnvelope s.bound F

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SignatureTupleComplete
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

def runSpace (s : ProducedSource) {d : ℕ}
    (q : LeafProgram.Factor.Spec s.input.r s.input.Q s.input.n d) (F B : ℕ) : ℕ :=
  max (prefixEnvelope s F) (QueryVisitorSemantics.visitorSpace s q F B)

/-- The empty-head path uses its actual unit-addition prefix bound. Both
branches retain the same F and have a single polynomial transient cap. -/
def completeSpace (s : ProducedSource) {d : ℕ}
    (q : LeafProgram.Factor.Spec s.input.r s.input.Q s.input.n d) (F B : ℕ) : ℕ :=
  max (runSpace s q F B)
    (896*F+QueryTupleSum.budget s.input.n (baseWidth 3 q.p.t) d q.p.t q.J F+1600*(F+1))

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

def commitBudget {r Q n d : ℕ} (q : Factor.Spec r Q n d) (N F : ℕ) : ℕ :=
  51000*(F+1)+QueryProgram.pairUpdateBudget n (baseWidth 3 q.p.t) d q.p.t q.J N N

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryPairEvaluation
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_QuerySourceSnapshot
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! A proof-only native source snapshot retains the actual readiness words.
It does not clear the running machine. The loader starts from the same native
input and generated cache, so all of its eighteen masters remain identical.
Unrelated scratch from earlier nodes is excluded from the source-local cap. -/
noncomputable section
namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QuerySourceSnapshot
open OAI BitProgram StructuredCalls SqrtLog SubexpSetupStorage
open LeafHeadSetupProgram LeafParametersProgram LeafProgram LeafProgram.PreparedSource

/-- A proof snapshot, with every retained byte copied from the actual source. -/
def snapshot (a : LeafHeadSetupProgram.Data) : LeafHeadSetupProgram.Data :=
  ⟨a.regs,fun i => if i ∈ retainedPorts then a.stacks i else []⟩

theorem snapshot_retained (a : LeafHeadSetupProgram.Data) (i : Fin 768)
    (hi : i ∈ retainedPorts) : (snapshot a).stacks i=a.stacks i := ite_eq_left hi

/-- Only the sixteen actual source words enter this bound. -/
theorem snapshot_bound (a : LeafHeadSetupProgram.Data) (A : ℕ)
    (ha : ∀ i ∈ retainedPorts,(a.stacks i).length ≤ A) : WordBound A (snapshot a) := by
  intro i
  change (if i ∈ retainedPorts then a.stacks i else []).length ≤ A
  split_ifs with hi
  · exact ha i hi
  · exact Nat.zero_le _

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QuerySourceSnapshot
end
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_QueryStreamCorrect
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! Physical boundaries of the fixed conditioned query. The node invariant
retains the actual prepared words and the exact length of the emitted stream;
it contains no execution or evaluator fields. -/
namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryStreamCorrect

open OAI BitProgram StructuredCalls SqrtLog SubexpLiftRing SubexpQuarticRing
open SubexpSetupStorage

abbrev Data := State 40 896

/-- These are the immutable prepared inputs between interpolation nodes.
The node index and the growing coefficient stream have separate exact fields. -/
structure NodeBoundary (initial : Data) (t d Q J B index : ℕ) (a : Data) : Prop where
  cursor : a.stacks 301=Encoding.encodeList id ((RingNodeMetadata.nodeBits t d Q).drop index)
  node : a.stacks 307=List.replicate index true
  guard : a.regs 37= !((RingNodeMetadata.nodeBits t d Q).drop index).isEmpty
  retained : ∀ i∈retainedPorts,a.stacks i=initial.stacks i
  stream_length : (a.stacks 863).length=index*(J*(d*baseWidth 3 t))
  readout_scratch : (0 : ℕ) < index → a.stacks 89=[]
  bounded : WordBound B a

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryStreamCorrect
end


