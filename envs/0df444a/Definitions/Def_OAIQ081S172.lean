-- Prove2me | Definitions.Def_OAIQ081S172
-- name    : OAIQ081S172
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-29T23:16:07.128152+00:00
-- url     : https://prove2.me/theorems/24ef0c67-b644-4995-aa52-6267658b651f
-- title:
--   Definitions bundle OAIQ081S172 of the split of OpenAI, The Exponential Time Hypothesis is False
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.exact_count_and_sat`, carved from OpenAI's openai/math development (OpenAI, *The Exponential Time Hypothesis is False*, OpenAI Math Release, October 25, 2026, result family 378, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 26 declarations of OpenAI's Lean: 18 definitions, 4 inductive types or structures and 4 theorems. The definitions and types are `OAI.Algorithms.SubexponentialSAT.SqrtLog.ProducedQueryResources.lowBytes`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FactorAssignmentCallback.dispatched`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FactorEvaluationSpace.hashArithmetic`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FactorTableNative.Ready`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FactorTableNative.SourceMasters`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HashQueryEntry.AcceptedEntry`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HashQueryEntry.MarkedEntry`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HashQueryEntry.acceptedQuery`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HashQueryEntry.trialQuery`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HeadSourceLocality.freeLabel`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeLeafPreparation.continuationSpace`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeLeafPreparation.continuationTime`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeLeafPreparation.retainedBound`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeLeafSetup.parameterTime`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NodeAppendSpace.result`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NodeReadoutSpace.localState`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NodeReadoutSpace.result`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryNodeEvaluation.prepareNode`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryNodeFinish.result`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryStreamProgram.bootstrapNode`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryTupleVisitor.installRepresentative`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SignatureHeadLoader.bootstrapProgram`.
--
--   **Sources.** They come from these modules of lean/OAI/Algorithms, in whole or in part: `SubexponentialSAT_SqrtLogSpace_FactorArithmeticProgram`, `SubexponentialSAT_SqrtLogSpace_FactorAssignmentCallback`, `SubexponentialSAT_SqrtLogSpace_FactorTableNative`, `SubexponentialSAT_SqrtLogSpace_HashQueryEntry`, `SubexponentialSAT_SqrtLogSpace_HeadSignatureLocality`, `SubexponentialSAT_SqrtLogSpace_NativeLeafPreparation`, `SubexponentialSAT_SqrtLogSpace_NativeLeafSetup`, `SubexponentialSAT_SqrtLogSpace_NativeQueryPreparation`, `SubexponentialSAT_SqrtLogSpace_NodeAppendSpace`, `SubexponentialSAT_SqrtLogSpace_NodeReadoutSpace`, `SubexponentialSAT_SqrtLogSpace_QueryModelBudgets`, `SubexponentialSAT_SqrtLogSpace_QueryNodeEvaluation`, `SubexponentialSAT_SqrtLogSpace_QueryNodeFinish`, `SubexponentialSAT_SqrtLogSpace_QueryStreamProgram`, `SubexponentialSAT_SqrtLogSpace_QueryTupleVisitor`, `SubexponentialSAT_SqrtLogSpace_SignatureHeadLoader`, `SubexponentialSAT_SqrtLog_PackingCallerProgramState`, `SubexponentialSAT_SqrtLog_PackingLoaderProgramReady`, `SubexponentialSAT_SqrtLog_ProducedQueryResourcesPacking`.
--
--   **Imports.** It imports the published bundle `Def_SubexponentialSAT`; the bundles `OAIQ081S153`, `OAIQ081S157`, `OAIQ081S158`, `OAIQ081S159`, `OAIQ081S160`, `OAIQ081S161`, `OAIQ081S162`, `OAIQ081S164` and `OAIQ081S165` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ081S177` and `OAIQ081S178`; the statements `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FactorAssignmentCallback.dispatch_eval`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FactorTableNative.Ready.staged_common`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FactorTableNative.source_of_masters`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HashQueryEntry.accepted_entry`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HashQueryEntry.prepared_accepted_entry`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HashQueryEntry.prepared_trial_entry`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HashQueryEntry.trial_entry`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HeadSumCorrect.gate_source_iff`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.LeafPreparationBudgets.chosen_preparation_time_envelope`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.LeafPreparationBudgets.continuationTime_le_envelope`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.LeafPreparationBudgets.prepared_common_bound_polynomial`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeLeafContract.chosen_loaded_local_space`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeLeafSetup.canonicalParameterTime_polynomial` and `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeLeafSetup.parameters_trace_space`; the proofs of `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FactorAssignmentCallback.dispatch_eval`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FactorTableNative.Ready.staged_common`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FactorTableNative.source_of_masters`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HashQueryEntry.accepted_entry`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HashQueryEntry.prepared_accepted_entry`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HashQueryEntry.prepared_trial_entry`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HashQueryEntry.trial_entry`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HeadSumCorrect.gate_source_iff`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighQueryCorrect.accepted`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighQueryCorrect.marked`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighQueryCount.run`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.LeafPreparationBudgets.chosen_preparation_time_envelope`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.LeafPreparationBudgets.continuationTime_le_envelope`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.LeafPreparationBudgets.prepared_common_bound_polynomial`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeHashQueries.accepted_replay`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeHashQueries.marked_replay`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeLeafSetup.canonicalParameterTime_polynomial` and `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeLeafSetup.parameters_trace_space`.
-- source:
--   OpenAI, The Exponential Time Hypothesis is False, OpenAI Math Release, October 25, 2026, https://github.com/openai/math (result family 378; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/The-Exponential-Time-Hypothesis-is-False-October-25-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Algorithms at commit 7ef5c0c

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_SubexponentialSAT
import Definitions.Def_OAIQ081S153
import Definitions.Def_OAIQ081S157
import Definitions.Def_OAIQ081S158
import Definitions.Def_OAIQ081S159
import Definitions.Def_OAIQ081S160
import Definitions.Def_OAIQ081S161
import Definitions.Def_OAIQ081S162
import Definitions.Def_OAIQ081S164
import Definitions.Def_OAIQ081S165

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

def hashArithmetic : Cmd 40 768 :=
  .seq Factor.indicator (.seq (Factor.clear 68) (.seq (Factor.clear 62) Factor.accumulate))

end
end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FactorEvaluationSpace
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_FactorAssignmentCallback
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! The actual specialized callback dispatches one stored original factor ID.
The general dispatch theorem fixes its physical payload, flags and exact frame;
hash and marked branch correctness is supplied by their concrete native proofs. -/
namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FactorAssignmentCallback

open OAI BitProgram StructuredCalls
open SqrtLog SqrtLog.LeafProgram MomentsProgram FactorAssignmentProgram

noncomputable section
attribute [local simp] Fin.coe_ofNat_eq_mod

def dispatched (a : FactorAssignmentProgram.Data) (rf : Fin 8 → Bool)
    (rows clauses : List (List Bool)) (marked : Bool) (mark factor : ℕ) : FactorAssignmentProgram.Data :=
  embedState id lowStack (callbackInitial a)
    (FactorDispatch.finished (dispatchInput a) rf rows clauses marked mark factor)

end
end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FactorAssignmentCallback
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_FactorTableNative
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.Packing.nonemptyUniversal
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

structure SourceMasters {r Q d : ℕ} (p : SourceBank.Parameters r Q d)
    (ps : List (ℕ × ℕ)) (P : PackingData (Fin ps.length) (UniversalType r Q 1))
    (a : SourceReady.Data) : Prop where
  colors : a.stacks 130=List.replicate r true
  nodes : a.stacks 131=List.replicate Q true
  typeWidth : a.stacks 132=List.replicate (Q*r) true
  positive : a.stacks 710=p.saved.hp
  negative : a.stacks 711=p.saved.hn
  scalarWidth : a.stacks 140=p.width
  power : a.stacks 712=p.power.1
  powerNegative : p.power.2=[]
  radius : a.stacks 138=List.replicate p.R true
  offset : a.stacks 139=p.aWord
  metadata : a.stacks 135=SelectorProgram.rawRecords
    (PackingMetadata.records P (fun v=>List.replicate v.val true) CollisionProgram.encodeType)
  plans : a.stacks 136=LayoutOwnerFiberProgram.stream ps
  inverses : a.stacks 713=(List.ofFn (fun i=>RingProgram.flat (p.inverse i))).flatten
  negatives : a.stacks 714=(List.ofFn (fun i=>RingProgram.flat (p.negative i))).flatten
  differences : a.stacks 715=(List.ofFn (fun i=>
    (List.ofFn (fun j=>RingProgram.flat (p.difference i j))).flatten)).flatten
  ringWidth : a.stacks 717=p.ringWidth
  rowWidth : a.stacks 716=p.rowWidth
  zero : a.stacks 280=RingProgram.flat p.ops.zeroRun.1
  one : a.stacks 207=RingProgram.flat p.ops.oneRun.1
  minusOne : a.stacks 211=RingProgram.flat p.minusOne
  inverseDenominator : a.stacks 728=RingProgram.flat p.invDenom


variable {r Q d n J S f : ℕ} {p : SourceBank.Parameters r Q d}
    {ps : List (ℕ × ℕ)} {P : PackingData (Fin ps.length) (UniversalType r Q 1)}
    {a : SourceReady.Data} {theta : DensePolynomialProgram.Coeff (baseWidth 3 p.t) d}

/-- Only concrete retained words and numeric size bounds occur in the table
entry contract. Private scratch is cleared and rebuilt by the command itself. -/
structure Ready {r Q d : ℕ} (p : SourceBank.Parameters r Q d)
    (ps : List (ℕ × ℕ)) (P : PackingData (Fin ps.length) (UniversalType r Q 1))
    (u J n f B S : ℕ) (theta : Coeff (baseWidth 3 p.t) d)
    (a : FactorTableProgram.OuterData) : Prop where
  positiveU : 0 < u
  positiveJ : 0 < J
  scalar : ScalarMasters p.t p.model p.modulus p.cache J p.R theta
    (projectState id FactorTableProgram.basePort a) n
  masters : SourceMasters p ps P (projectState id FactorTableProgram.basePort a)
  selected : a.stacks 556 = List.replicate f true
  mask : (a.stacks 857).length = n
  incoming : ∀ i, (a.stacks i).length ≤ B
  size : 1029*B+99+n+n*FactorTableProgram.literalRecordBound n
    (specializedPayloadBound n u J (baseWidth 3 p.t) d)+1 ≤ S
  arraySize : (p.R+1)*(d*baseWidth 3 p.t) ≤ S
  countSize : p.R+1 ≤ S
  metadataSize : ∀ x,SourceBank.MetadataBound (PackingMetadata.value P CollisionProgram.encodeType x) S
  incidenceSize : ps.length ≤ S
  ambientSize : n ≤ S
  factorSize : f ≤ S
  plansSize : (LayoutOwnerFiberProgram.stream ps).length ≤ S

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FactorTableNative
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_NativeLeafSetup
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! Actual sparse-code metadata production, with paid polynomial time and every-prefix word bounds. -/

namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeLeafSetup

open BitProgram StructuredCalls SqrtLog SqrtLog.LeafOuterProgram

/-- This is precisely the paid outer metadata-stage budget: input copies,
arithmetic, seven unary outputs, output copies and complete worker cleanup. -/
def parameterTime (m B W ml Bl : ℕ) : ℕ :=
  10000 * (W + CodeParametersProgram.fullBudget m B ml Bl + 2)

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeLeafSetup
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

def continuationTime (m B L : ℕ) (a prepared : Data) : ℕ :=
  let P := NativeLeafSetup.parameterTime m B L (a.stacks 782).length (a.stacks 786).length
  let A := L + P
  let R := NativeCodeAssembly.afterBoundary A m B
    (prepared.stacks 801) (a.stacks 782) (a.stacks 768)
  P + NativeCodeAssembly.afterTime A m B (prepared.stacks 800).length
    (prepared.stacks 801) (a.stacks 782) (a.stacks 768) +
      finishTime (SparseCode.distanceDenom m B) R

def continuationSpace (m B L : ℕ) (a prepared : Data) : ℕ :=
  let P := NativeLeafSetup.parameterTime m B L (a.stacks 782).length (a.stacks 786).length
  let A := L + P
  let R := NativeCodeAssembly.afterBoundary A m B
    (prepared.stacks 801) (a.stacks 782) (a.stacks 768)
  max (max (A + 1) (NativeCodeAssembly.afterSpace A m B (prepared.stacks 800).length
    (prepared.stacks 801) (a.stacks 782) (a.stacks 768)))
      (R + finishTime (SparseCode.distanceDenom m B) R)

def retainedBound (m B L : ℕ) (a prepared : Data) : ℕ :=
  let P := NativeLeafSetup.parameterTime m B L (a.stacks 782).length (a.stacks 786).length
  let A := L + P
  let R := NativeCodeAssembly.afterBoundary A m B
    (prepared.stacks 801) (a.stacks 782) (a.stacks 768)
  max R (2 * (SparseCode.distanceDenom m B * HashCandidates.digitWidth m) + 3)

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeLeafPreparation
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

noncomputable def trialQuery {n B : ℕ} (F : DisjointReuse.RawCNF n) (hm : 0 < F.length)
    (shifts : SparseCode.SuppliedShifts F.length B) (Q : SparseCode.SuppliedLocal F.length B)
    (rounds : ℕ) (word : List Bool) (e : Fin F.length) (d : Data) : LeafQueryFrontend.Query :=
  rawQueryFromRows F (trialRows F hm shifts Q rounds word) (some e)
    (Encoding.encodeNat e.val) (d.stacks 783) (d.stacks 782) (d.stacks 785)

/-- All source-side obligations at the actual marked callback entry. The
frontend itself owns the single paid marker operation. -/
structure MarkedEntry (q : LeafQueryFrontend.Query) (staged a : Data) : Prop where
  valid : q.Valid
  sources : LeafProgram.Query.Sources q (HighMarkedFrontend.project a)
  clean : LeafProgram.Query.CleanWork (HighMarkedFrontend.project a)
  marked : q.mark.isSome = true
  index : a.stacks 321 = q.index.reverse
  index_empty : a.stacks 705 = []
  flag_empty : a.stacks 706 = []
  scratch : a.stacks 767 = []
  collector : HashMassAdapter.Ready (fun ws => ws = HashMassAdapter.workspace staged) a
  frontend : q.Ready (LeafProgram.Query.markedInput (HighMarkedFrontend.project a))

/-- The final query receives precisely the attained history, with no trial
candidate and no marked clause. Its false index is written by `noMarkInput`. -/
noncomputable def acceptedQuery {n B : ℕ} (F : DisjointReuse.RawCNF n) (hm : 0 < F.length)
    (shifts : SparseCode.SuppliedShifts F.length B) (Q : SparseCode.SuppliedLocal F.length B)
    (rounds : ℕ) (d : Data) : LeafQueryFrontend.Query :=
  rawQueryFromRows F
    ((HashGreedyCNF.history (NativeLeafSemantics.indexed F)
      (SparseCode.distanceDenom F.length B) (initial shifts Q) rounds).map (raw F.length hm))
    none [false] (d.stacks 783) (d.stacks 782) (d.stacks 785)

structure AcceptedEntry (q : LeafQueryFrontend.Query) (a : Data) : Prop where
  valid : q.Valid
  sources : LeafProgram.Query.Sources q (HighMarkedFrontend.project a)
  clean : LeafProgram.Query.CleanWork (HighMarkedFrontend.project a)
  unmarked : q.mark = none
  index : q.index = [false]
  index_empty : a.stacks 705 = []
  flag_empty : a.stacks 706 = []
  scratch : a.stacks 767 = []
  frontend : q.Ready (LeafProgram.Query.unmarkedInput (HighMarkedFrontend.project a))

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HashQueryEntry
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_HeadSignatureLocality
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.Packing.nonemptyUniversal
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! Exact full-integer head labels and fixed-high cancellation, extracted
unchanged from HeadSourceLocality. All raw rows and original coordinate IDs
are retained; source-product locality remains in the importing module. -/
noncomputable section
namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HeadSourceLocality
open scoped BigOperators
open OAI.Algorithms.SubexponentialSAT.SqrtLog


open OAI.Algorithms.SubexponentialSAT.MulticolorTypes OAI.Algorithms.SubexponentialSAT.Subexp.ConstructivePacking
open LayoutProgram

variable {r Q d n : ℕ}

/-- Actual full integer keys use every emitted raw row, restricted only to
this head's free original coordinates. -/
def freeLabel (p : SourceBank.Parameters r Q d) (ps : List (ℕ × ℕ))
    (P : PackingData (Fin ps.length) (UniversalType r Q 1))
    (owner : Fin ps.length → Fin n) (head : Fin Q → Fin n → Fin r)
    (H : Finset (Fin n)) (node : Fin Q) (g : Fin r)
    (a : Moments.Head (fun v : ResidualEmbedding.Free H => head node v.val) g → Bool) :
    Fin ps.length → ℤ :=
  LayoutSignatureBound.boolSignature
    (fun j v => LayoutProducedMatrix.literalNat P owner p.aWord.length p.R node j.val v.val.val.val) a

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HeadSourceLocality
end
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

/-- Physical serialized length caps also bound every pre-serialization word;
no numeric value is used as a replacement for a padded word length. -/
theorem serialized_model_lengths_le (x : Input) (padding : Fin 8 → ℕ) (S : ℕ)
    (h : ∀ j, (result Serialization.code (Execute.guardedModel x padding)).len j ≤ S) :
    ∀ j, (Execute.guardedModel x padding).len j ≤ S := by
  intro j
  by_cases h44 : j = 44
  · subst j
    simp [Execute.guardedModel, Fin.coe_ofNat_eq_mod]
  by_cases h45 : j = 45
  · subst j
    simp [Execute.guardedModel, Fin.coe_ofNat_eq_mod]
  have hj := h j
  simpa [Serialization.code, result, next, output, lengthBound, h44, h45] using hj

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryModelBudgets
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_PackingLoaderProgramReady
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Exact selector memory and environment from the physically generated
alphabet, retaining all ambient head addresses before factor addresses. -/
namespace SubexponentialSAT.SqrtLog.PackingLoaderProgram
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.Subexp SubexponentialSAT.MulticolorTypes
attribute [local simp] Fin.coe_ofNat_eq_mod

theorem ready_memory (regs : Fin 16 → Bool) {r Q : ℕ}
    (a : Word r Q) (tail : List (Word r Q))
    (hrows : (a::tail).map ReadPlan.encodeWord=AssignmentAlphabetSemantics.wordBytes r Q)
    (n f : ℕ) (pairs nb sb mb rb : List Bool) :
    SequentialProgram.Memory ReadPlan.encodeWord a tail (n+f) []
      (readyLocal regs r Q n f pairs nb sb mb rb).stacks := by
  have hm := AssignmentInitProgram.output_memory ReadPlan.encodeWord a tail
    (context r Q n f pairs)
    (by simp [context,AssignmentInputProgram.context,←hrows])
    (by simp [context,AssignmentInputProgram.context,←hrows])
    (by simp [context,AssignmentInputProgram.context,AssignmentInputProgram.unary,
      ReadPlan.encodeWord_length,ReadPlan.wordWidth])
  have hc : (context r Q n f pairs).seedCount=n+f := by
    simp [context,AssignmentInputProgram.context,AssignmentInputProgram.seedCount,Nat.add_comm]
  rw [hc] at hm
  constructor
  · simpa [readyLocal] using hm.assignment
  · simpa [readyLocal] using hm.alphabet
  · simpa [readyLocal] using hm.width
  · simpa [readyLocal] using hm.processed
  · intro i hi
    rw [readyLocal_low regs r Q n f pairs nb sb mb rb i
      ((by decide : ∀ i : Fin 48, i∈SequentialProgram.scratchPorts → i.val < 20) i hi)]
    exact hm.scratch i hi

end SubexponentialSAT.SqrtLog.PackingLoaderProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_PackingCallerProgramState
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.PackingCallerProgram
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.Subexp SubexponentialSAT.MulticolorTypes
open PackingLoaderProgram PackingIncidenceInput
attribute [local simp] Fin.coe_ofNat_eq_mod

theorem parameters_workspace (a : Wide.Data) : Workspace (Wide.parameterStore (Wide.project a)) := by
  constructor <;> simp [Wide.parameterStore]

end SubexponentialSAT.SqrtLog.PackingCallerProgram

end OAI.Algorithms
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

theorem shadow_sources (a : Data) (p : PackingCallerProgram.Problem)
    (h : PackingCallerProgram.Sources a p) : PackingCallerProgram.Sources (shadow a) p := by
  constructor
  · exact (shadow_visible a 718 (by decide)).trans h.scopes
  · exact (shadow_visible a 128 (by decide)).trans h.ambientUnary
  · exact (shadow_visible a 719 (by decide)).trans h.mask
  · simpa only [shadow_visible a 709 (by decide)] using h.ambient
  · simpa only [shadow_visible a 720 (by decide)] using h.coordinate
  · simpa only [shadow_visible a 721 (by decide)] using h.radius
  · simpa only [shadow_visible a 722 (by decide)] using h.epsilon
  · simpa only [shadow_visible a 723 (by decide)] using h.incidence

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeQueryPreparation
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

def localState (rr : Fin 8 → Bool)
    (modulus width degree dictionary zero marker taylor shape output : List Bool) : State 8 40 :=
  MomentsReadoutProgram.wideState rr
    {modulus := modulus, width := width, count := degree, dict := dictionary, out := output}
    (MomentsReadoutProgram.inputHigh zero marker taylor shape)

noncomputable def result (a : Data) (rr : Fin 8 → Bool)
    (modulus width degree dictionary zero marker taylor shape bits : List Bool) : Data :=
  embedState registers ports (clearedMany clearPorts a)
    (localState rr modulus width degree dictionary zero marker taylor shape bits)

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

noncomputable def result (a : Data) (rr : Fin 8 → Bool)
    (modulus width degree dictionary zero marker taylor shape bits : List Bool) : Data :=
  appendResult (NodeReadoutSpace.result (prepared a) rr modulus width degree dictionary zero
    marker taylor shape bits)

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NodeAppendSpace
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

/-- The first tuple pass installs the current representative into the full
ambient baseline. The second pass can then retain every foreign head. -/
def installRepresentative : Code :=
  .seq (overwrite 838 859)
    (.seq (.call HighQueryAdapter.NativeOverlay.prepareProgram)
      (.seq (overwrite 145 869) (.call (StackRoutines.clearProgram 859 0 1))))

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryTupleVisitor
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

/-- The actual cache bootstrap is a fixed finite program. -/
def bootstrapProgram := compiled (.seq boot retainCache) 307 647

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SignatureHeadLoader
end
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

noncomputable def result (a : Data) (rr : Fin 8 → Bool)
    (modulus width degree dictionary zero marker taylor shape bits : List Bool) : Data :=
  finished (NodeAppendSpace.result a rr modulus width degree dictionary zero
    marker taylor shape bits)

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryNodeFinish
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

/-- The native integer-cache bootstrap is reused, without the old tuple
initializer or the old materialized support evaluator. -/
abbrev bootstrapNode : Code := .call (ProgramLinking.liftProgram
  SignatureHeadLoader.bootstrapProgram SignatureHeadLoader.leafRegs QueryAssembler.Nodes.lowPort)

end
end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryStreamProgram
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_QueryNodeEvaluation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! Concrete initialization of a node evaluation. The paid node read, layout
load, native cache bootstrap and pair setup are the fixed commands used by the
streaming query; no evaluator is supplied to these constructions. -/
namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryNodeEvaluation

open OAI BitProgram StructuredCalls SqrtLog SubexpSetupStorage
open LeafHeadSetupProgram QueryTupleState

/-- This is the exact prefix of the fixed node body, before its pair loop. -/
def prepareNode : Code :=
  .seq QueryAssembler.Nodes.beginNode
    (.seq NativeLayoutLoad.command
      (.seq QueryStreamProgram.bootstrapNode PairNativeSetup.setupCaller))

open LeafParametersProgram LeafProgram LeafProgram.PreparedSource

open SubexpLiftRing SubexpQuarticRing
open scoped BigOperators


end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryNodeEvaluation
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

/-- Exactly the forward low mask consumed by the head identifier program. -/
def lowBytes (q : Query) : List Bool := q.forward.map Bool.not

end
end SubexponentialSAT.SqrtLog.ProducedQueryResources

end OAI.Algorithms
end


