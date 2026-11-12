-- Prove2me | Definitions.Def_Q238L026
-- name    : Q238L026
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-11T11:25:25.886891+00:00
-- url     : https://prove2.me/theorems/e283f1d7-3475-4dfd-9f97-39d5b175d64f
-- title:
--   Definitions bundle Q238L026 of the split of OpenAI, Single-Exponential Recovery and Bounded-Price Strictness for Metric k-Median
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.MetricKMedianRecovery.global_application`, carved from OpenAI's openai/math development (OpenAI, *Single-Exponential Recovery and Bounded-Price Strictness for Metric k-Median*, OpenAI Math Release, September 24, 2026, result family 125, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 65 declarations of OpenAI's Lean: 57 definitions, 4 inductive types or structures and 4 theorems. The definitions and types are `OAI.MetricKMedianRecovery.BitMachine.BinaryGlobalCall.pack`, `OAI.MetricKMedianRecovery.BitMachine.BinaryIntegralRecovery.stateAt`, `OAI.MetricKMedianRecovery.BitMachine.BinaryJump.jumpBits`, `OAI.MetricKMedianRecovery.BitMachine.BinaryLength.planBits`, `OAI.MetricKMedianRecovery.BitMachine.BinaryLocalCost.connection`, `OAI.MetricKMedianRecovery.BitMachine.BinaryLocalCost.cost`, `OAI.MetricKMedianRecovery.BitMachine.BinaryMatch.contextBits`, `OAI.MetricKMedianRecovery.BitMachine.BinaryMenu.optBits`, `OAI.MetricKMedianRecovery.BitMachine.BinaryMenu.radii`, `OAI.MetricKMedianRecovery.BitMachine.BinaryPhaseFuel.pack`, `OAI.MetricKMedianRecovery.BitMachine.BinaryPopulation.pack`, `OAI.MetricKMedianRecovery.BitMachine.BinaryRandomizedZeroBranch.Seed`, `OAI.MetricKMedianRecovery.BitMachine.BinaryRandomizedZeroBranch.count`, `OAI.MetricKMedianRecovery.BitMachine.BinaryRandomizedZeroBranch.embed`, `OAI.MetricKMedianRecovery.BitMachine.BinaryRandomizedZeroBranch.layout`, `OAI.MetricKMedianRecovery.BitMachine.BinaryRandomizedZeroBranch.raw`, `OAI.MetricKMedianRecovery.BitMachine.BinaryRationalPower.pack`, `OAI.MetricKMedianRecovery.BitMachine.BinaryRationalSort.entryBits`, `OAI.MetricKMedianRecovery.BitMachine.BinaryRegular.pack`, `OAI.MetricKMedianRecovery.BitMachine.BinaryRegularChain.pack`, `OAI.MetricKMedianRecovery.BitMachine.BinaryRoundingMatrix.colIndex_computes`, `OAI.MetricKMedianRecovery.BitMachine.BinaryZeroBranch.output`, `OAI.MetricKMedianRecovery.CanonicalCoupledMerge.Certified`, `OAI.MetricKMedianRecovery.CanonicalCoupledMerge.Certified.coupled`, `OAI.MetricKMedianRecovery.CanonicalCoupledMerge.Correction.error`, `OAI.MetricKMedianRecovery.CanonicalCoupledMerge.Outcome.Correct`, `OAI.MetricKMedianRecovery.CanonicalCoupledMerge.Outcome.Keys`, `OAI.MetricKMedianRecovery.CanonicalCoupledMerge.Outcome.Resources`, `OAI.MetricKMedianRecovery.CanonicalCoupledMerge.Outcome.Rooted`, `OAI.MetricKMedianRecovery.CanonicalCoupledMerge.Output.Correct`, `OAI.MetricKMedianRecovery.CanonicalCoupledMerge.Output.Resources`, `OAI.MetricKMedianRecovery.CanonicalCoupledMerge.Output.project`, `OAI.MetricKMedianRecovery.CanonicalCoupledMerge.StartOutput`, `OAI.MetricKMedianRecovery.CanonicalCoupledMerge.StartOutput.Correct`, `OAI.MetricKMedianRecovery.CanonicalCoupledMerge.StartOutput.Rooted`, `OAI.MetricKMedianRecovery.CanonicalCoupledMerge.StartOutput.project`, `OAI.MetricKMedianRecovery.CanonicalCoupledMerge.State.Resources`, `OAI.MetricKMedianRecovery.CanonicalCoupledMerge.State.a`, `OAI.MetricKMedianRecovery.CanonicalCoupledMerge.State.b`, `OAI.MetricKMedianRecovery.CanonicalCoupledMerge.advanceState` and 21 more.
--
--   **Sources.** They come from these modules of lean/OAI/Combinatorics, in whole or in part: `KMedianRecovery_Algorithms_GlobalCall`, `KMedianRecovery_Algorithms_IntegralRecoverySemantics`, `KMedianRecovery_Branching_CopyAge`, `KMedianRecovery_Branching_ObservableCapacity`, `KMedianRecovery_Branching_PopulationMachine`, `KMedianRecovery_Branching_RandomizedZeroBranch`, `KMedianRecovery_Encoding_ColorLabelMachine`, `KMedianRecovery_Encoding_LengthEncode`, `KMedianRecovery_Encoding_RationalLeaves`, `KMedianRecovery_Encoding_RationalSort`, `KMedianRecovery_Encoding_WordExtras`, `KMedianRecovery_Geometry_LocalCandidates`, `KMedianRecovery_Geometry_RoundingMatrix`, `KMedianRecovery_Machines_CorrectionSize`, `KMedianRecovery_Machines_CoupledLoop`, `KMedianRecovery_Machines_MatchFold`, `KMedianRecovery_Machines_MatchSize`, `KMedianRecovery_Machines_MenuMachine`, `KMedianRecovery_Machines_MergeResources`, `KMedianRecovery_Recovery_CanonicalParents`, `KMedianRecovery_Recovery_CoupledFinish`, `KMedianRecovery_Recovery_CoupledInitial`, `KMedianRecovery_Recovery_CoupledLeaf`, `KMedianRecovery_Recovery_CoupledResolve`, `KMedianRecovery_Recovery_Guide`, `KMedianRecovery_Recovery_InitialCorrect`, `KMedianRecovery_Recovery_InitialProject`, `KMedianRecovery_Recovery_LeafOrder`, `KMedianRecovery_Recovery_LengthPolynomial`, `KMedianRecovery_Recovery_LengthSearch`, `KMedianRecovery_Recovery_NearEligible`, `KMedianRecovery_Recovery_RegularChain`, `KMedianRecovery_Recovery_Step2`, `KMedianRecovery_Recovery_Values`.
--
--   **Imports.** It imports the published bundle `Def_KMedianRecovery`; the bundles `Q238L014`, `Q238L015`, `Q238L017`, `Q238L018`, `Q238L019` and `Q238L020` of this split.
--
--   **Imported by** (directly, in this split): the bundles `Q238L030` and `Q238L031`; the statements `OAI.MetricKMedianRecovery.BitMachine.BinaryCoupledStep.a_pack_s238r`, `OAI.MetricKMedianRecovery.BitMachine.BinaryCoupledStep.banks_pack_s238r`, `OAI.MetricKMedianRecovery.BitMachine.BinaryRationalSort.ranked_pack_s238r`, `OAI.MetricKMedianRecovery.BitMachine.BinaryZeroBranch.fair_zero_completion_s238r`, `OAI.MetricKMedianRecovery.BitMachine.BinaryZeroBranch.successful_completion_s238r`, `OAI.MetricKMedianRecovery.CanonicalCoupledMerge.initialHistory_spec_s238r`, `OAI.MetricKMedianRecovery.CanonicalCoupledMerge.leaf_certified_s238r`, `OAI.MetricKMedianRecovery.CanonicalCoupledMerge.resolve_correct_s238r`, `OAI.MetricKMedianRecovery.CanonicalCoupledMerge.start_certificate_s238r`, `OAI.MetricKMedianRecovery.CanonicalCoupledMerge.start_correct_s238r`, `OAI.MetricKMedianRecovery.CanonicalCoupledMerge.start_small_certificate_s238r`, `OAI.MetricKMedianRecovery.CanonicalCoupledMerge.step_correct_s238r`, `OAI.MetricKMedianRecovery.CanonicalSensitiveEndpoint.endpoints_s238r`, `OAI.MetricKMedianRecovery.Sampling.Comparison.guideLoss_domination_s238r` and `OAI.MetricKMedianRecovery.Sampling.Comparison.history_menu_budget_s238r`; the proofs of `OAI.MetricKMedianRecovery.BitMachine.BinaryAssignmentWeight.identities_pack_s238r`, `OAI.MetricKMedianRecovery.BitMachine.BinaryBlueBlocks.at_pack_s238r`, `OAI.MetricKMedianRecovery.BitMachine.BinaryBlueCell.op_pack_s238r`, `OAI.MetricKMedianRecovery.BitMachine.BinaryBlueLoop.run_pack_s238r`, `OAI.MetricKMedianRecovery.BitMachine.BinaryBlueSize.tableRun_best_bound_s238r`, `OAI.MetricKMedianRecovery.BitMachine.BinaryBlueSize.table_length_s238r`, `OAI.MetricKMedianRecovery.BitMachine.BinaryBlueTable.next_pack_s238r`, `OAI.MetricKMedianRecovery.BitMachine.BinaryBranchCheck.badBalls_nil_s238r`, `OAI.MetricKMedianRecovery.BitMachine.BinaryBranchCheck.run_pack_s238r`, `OAI.MetricKMedianRecovery.BitMachine.BinaryBranchContext.copyData_pack_s238r`, `OAI.MetricKMedianRecovery.BitMachine.BinaryBranchContext.origins_pack_s238r`, `OAI.MetricKMedianRecovery.BitMachine.BinaryBranchContext.parts_pack_s238r`, `OAI.MetricKMedianRecovery.BitMachine.BinaryBranchProgram.bluePack_pack_s238r`, `OAI.MetricKMedianRecovery.BitMachine.BinaryBranchProgram.completion_pack_s238r`, `OAI.MetricKMedianRecovery.BitMachine.BinaryBranchProgram.plan_pack_s238r`, `OAI.MetricKMedianRecovery.BitMachine.BinaryBranchProgram.rowInput_pack_s238r`, `OAI.MetricKMedianRecovery.BitMachine.BinaryBranchRandomize.context_pack_s238r`, `OAI.MetricKMedianRecovery.BitMachine.BinaryBranchRandomize.labels_pack_s238r`, `OAI.MetricKMedianRecovery.BitMachine.BinaryBranchRows.capRow_one_s238r`, `OAI.MetricKMedianRecovery.BitMachine.BinaryBranchRows.capRow_zero_s238r`, `OAI.MetricKMedianRecovery.BitMachine.BinaryBranchTape.Count.cut_pack_s238r`, `OAI.MetricKMedianRecovery.BitMachine.BinaryCategorical.Prepare.left_pack_s238r`, `OAI.MetricKMedianRecovery.BitMachine.BinaryCategorical.Prepare.run_pack_s238r`, `OAI.MetricKMedianRecovery.BitMachine.BinaryCategorical.bagWords_pack_s238r`, `OAI.MetricKMedianRecovery.BitMachine.BinaryCategorical.choose_pack_s238r`, `OAI.MetricKMedianRecovery.BitMachine.BinaryCategorical.draw_pack_s238r`, `OAI.MetricKMedianRecovery.BitMachine.BinaryCategorical.marginal_pack_s238r`, `OAI.MetricKMedianRecovery.BitMachine.BinaryCompletionRealize.added_pack_s238r`, `OAI.MetricKMedianRecovery.BitMachine.BinaryCompletionRealize.redIndices_pack_s238r`, `OAI.MetricKMedianRecovery.BitMachine.BinaryCompletionRealize.run_pack_s238r`, `OAI.MetricKMedianRecovery.BitMachine.BinaryCompletion.saving_pack_s238r`, `OAI.MetricKMedianRecovery.BitMachine.BinaryCopyTables.locations_pack_s238r`, `OAI.MetricKMedianRecovery.BitMachine.BinaryCoupledStep.Q_pack_s238r`, `OAI.MetricKMedianRecovery.BitMachine.BinaryCoupledStep.a_pack_s238r`, `OAI.MetricKMedianRecovery.BitMachine.BinaryCoupledStep.banks_pack_s238r`, `OAI.MetricKMedianRecovery.BitMachine.BinaryCoupledStep.mapped_pack_s238r`, `OAI.MetricKMedianRecovery.BitMachine.BinaryCross.finalCount_pack_s238r`, `OAI.MetricKMedianRecovery.BitMachine.BinaryDyadic.lookup_draw_s238r`, `OAI.MetricKMedianRecovery.BitMachine.BinaryEllipsoidAdvance.found_pack_s238r`, `OAI.MetricKMedianRecovery.BitMachine.BinaryEllipsoidCut.inflateWords_pack_s238r`, `OAI.MetricKMedianRecovery.BitMachine.BinaryEllipsoidCut.shapeWords_pack_s238r`, `OAI.MetricKMedianRecovery.BitMachine.BinaryEllipsoidInitial.indices_replicate_s238r`, `OAI.MetricKMedianRecovery.BitMachine.BinaryEllipsoidIteration.iterate_length_bound_s238r`, `OAI.MetricKMedianRecovery.BitMachine.BinaryEllipsoidIteration.run_pack_s238r`, `OAI.MetricKMedianRecovery.BitMachine.BinaryFinSet.diff_pack_s238r`, `OAI.MetricKMedianRecovery.BitMachine.BinaryFinSet.pad_pack_s238r`, `OAI.MetricKMedianRecovery.BitMachine.BinaryFiniteContext.alphabet_pack_s238r`, `OAI.MetricKMedianRecovery.BitMachine.BinaryFiniteContext.countInter_pack_s238r`, `OAI.MetricKMedianRecovery.BitMachine.BinaryFiniteContext.selected_pack_s238r`, `OAI.MetricKMedianRecovery.BitMachine.BinaryFiniteContext.union_list_pack_s238r`, `OAI.MetricKMedianRecovery.BitMachine.BinaryInitialAuto.context_pack_s238r`, `OAI.MetricKMedianRecovery.BitMachine.BinaryInputParser.Stream.run_code_s238r`, `OAI.MetricKMedianRecovery.BitMachine.BinaryInverseCDF.find_pack_s238r`, `OAI.MetricKMedianRecovery.BitMachine.BinaryLocalCandidates.run_pack_s238r`, `OAI.MetricKMedianRecovery.BitMachine.BinaryProjection.run_setBits_s238r`, `OAI.MetricKMedianRecovery.BitMachine.BinaryRationalSort.ranked_pack_s238r`, `OAI.MetricKMedianRecovery.BitMachine.BinaryRationalSort.sumBottom_pack_s238r`, `OAI.MetricKMedianRecovery.BitMachine.BinarySamplingOracle.total_pack_s238r`, `OAI.MetricKMedianRecovery.BitMachine.BinarySeed.nest_tensor_s238r`, `OAI.MetricKMedianRecovery.BitMachine.BinaryZeroBranch.fair_zero_completion_s238r`, `OAI.MetricKMedianRecovery.BitMachine.BinaryZeroBranch.successful_completion_s238r`, `OAI.MetricKMedianRecovery.BitMachine.RationalMatrix.determinantWords_encode_s238r`, `OAI.MetricKMedianRecovery.BitMachine.RationalMatrix.fold_steps_s238r`, `OAI.MetricKMedianRecovery.BitMachine.RationalMatrix.mulWords_encode_s238r`, `OAI.MetricKMedianRecovery.BitMachine.RationalMatrix.solveWords_bird_s238r`, `OAI.MetricKMedianRecovery.BitMachine.WordList.Slices.run_items_s238r`, `OAI.MetricKMedianRecovery.BitMachine.WordList.flatMapWith_typed_s238r`, `OAI.MetricKMedianRecovery.CanonicalCoupledMerge.initialHistory_spec_s238r`, `OAI.MetricKMedianRecovery.CanonicalCoupledMerge.leaf_certified_s238r`, `OAI.MetricKMedianRecovery.CanonicalCoupledMerge.resolve_correct_s238r`, `OAI.MetricKMedianRecovery.CanonicalCoupledMerge.start_certificate_s238r`, `OAI.MetricKMedianRecovery.CanonicalCoupledMerge.start_correct_s238r`, `OAI.MetricKMedianRecovery.CanonicalCoupledMerge.start_small_certificate_s238r`, `OAI.MetricKMedianRecovery.CanonicalCoupledMerge.step_correct_s238r`, `OAI.MetricKMedianRecovery.CanonicalSensitiveEndpoint.endpoints_s238r`, `OAI.MetricKMedianRecovery.Sampling.Comparison.guideLoss_domination_s238r`, `OAI.MetricKMedianRecovery.Sampling.Comparison.history_menu_budget_s238r` and `OAI.MetricKMedianRecovery.Sampling.Comparison.integral_records_success_s238r`.
-- source:
--   OpenAI, Single-Exponential Recovery and Bounded-Price Strictness for Metric k-Median, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 125; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Single-Exponential-Recovery-and-Bounded-Price-Strictness-for-Metric-k-Median-September-24-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Combinatorics at commit adc7f12

import Mathlib
import Definitions.Def_KMedianRecovery
import Definitions.Def_Q238L014
import Definitions.Def_Q238L015
import Definitions.Def_Q238L017
import Definitions.Def_Q238L018
import Definitions.Def_Q238L019
import Definitions.Def_Q238L020

section
-- module Solutions.Q238_KM.KMedianRecovery_Recovery_LengthPolynomial
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine
open WordOperations UnaryTake

namespace WordList

lemma length_encode (ws : List (List Bool)) :
    (encode ws).length=2*(ws.map List.length).sum+2*ws.length := by
  induction ws with
  | nil => rfl
  | cons w ws ih => simp only [encode,length_cons,List.map_cons,List.sum_cons,List.length_cons,ih]; omega
lemma length_le_encode (ws : List (List Bool)) : ws.length ≤ (encode ws).length := by
  rw [length_encode]; omega

end WordList
end MetricKMedianRecovery.BitMachine

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Recovery_Step2
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine

section
open WordOperations BinaryArithmetic
namespace WordList.Lookup

lemma run_encode (i : ℕ) (ws : List (List Bool)) :
    run (pairBits (i.bits,encode ws))=ws[i]?.getD [] := by
  apply head_iterate
  have h := length_le_encode ws
  rw [pairBits_length]
  dsimp only
  omega
end WordList.Lookup
end
open WordOperations
end MetricKMedianRecovery.BitMachine

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Recovery_Values
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine
open WordOperations BinaryArithmetic
namespace BinaryOpeningPayment
open WordList RationalLinearFeasibility

lemma field_encode (k : ℕ) (ws : List (List Bool)) : field k (encode ws)=ws[k]?.getD [] :=
  Lookup.run_encode k ws

end BinaryOpeningPayment
end MetricKMedianRecovery.BitMachine

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Encoding_RationalLeaves
attribute [-instance] _root_.OAI.MetricKMedianRecovery.RationalLeaves.labelLinearOrder
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.RationalLeaves
variable {V : Type*} [PseudoMetricSpace V]

attribute [local instance] metric

variable [DecidableEq V]

def copy (key : ℕ) : Label V → Label V :=
  Sum.elim (fun i=>leaf key i 0) Sum.inr

end MetricKMedianRecovery.RationalLeaves

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Recovery_LengthSearch
attribute [-instance] _root_.OAI.MetricKMedianRecovery.Categorical.binaryOracleIndexDecidableEq _root_.OAI.MetricKMedianRecovery.Categorical.binaryOracleIndexFintype _root_.OAI.MetricKMedianRecovery.RationalLeaves.labelLinearOrder
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.CanonicalSensitiveEndpoint
open PhaseSequence PhaseHistoryTransfer PhaseMergeCompletion PhaseMergeRefinement PhaseCountCrossing
  CanonicalMergeCrossing CanonicalLengthView RationalLeaves
variable {V : Type*} [PseudoMetricSpace V] [DecidableEq V] {d : ℕ}
attribute [local instance] RationalLeaves.metric

def EndpointSpec (loc : Fin d → V) (F : Finset V) (B Q : Finset (Label V))
    (v lam eta : ℝ) (q n k key : ℕ) (b : ℚ) (H : List (Label V))
    (T U : List (List (Label V))) (J : Plan (Label V)) : Prop :=
  let C := J.common H
  let i := parent J.root
  Good (fun j=>original (loc j)) (F.image original) B Q v ((1+v^2)^q) lam eta C ∧
  Runs (fun j=>original (loc j)) (F.image original) (insert (leaf key i 0) B)
    (insert (leaf key i 0) (Q∪C.toFinset)) v lam (q+1) n (J.small T U) ∧
  Runs (fun j=>original (loc j)) (F.image original) (insert (leaf key i b) B)
    (insert (leaf key i b) (Q∪C.toFinset)) v lam (q+1) n (J.large T U) ∧
  let a := ((after (insert (leaf key i 0) (Q∪C.toFinset)) (J.small T U))∩F.image original).card
  let c := ((after (insert (leaf key i b) (Q∪C.toFinset)) (J.large T U))∩F.image original).card
  a=k ∨ Sandwich k a c

end MetricKMedianRecovery.CanonicalSensitiveEndpoint

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Recovery_LeafOrder
attribute [-instance] _root_.OAI.MetricKMedianRecovery.Categorical.binaryOracleIndexDecidableEq _root_.OAI.MetricKMedianRecovery.Categorical.binaryOracleIndexFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.CanonicalSensitiveEndpoint
open PhaseSequence PhaseHistoryTransfer PhaseMergeCompletion PhaseMergeRefinement PhaseCountCrossing
  CanonicalMergeCrossing CanonicalLengthView RationalLeaves
variable {V : Type*} [LinearOrder V] {d : ℕ}

def run (loc : Fin d → V) (distance : V → Fin d → ℚ) (F : Finset V)
    (Q : Finset (Label V)) (v lam b : ℚ) (q n k key precision : ℕ)
    (H : List (Label V)) (T U : List (List (Label V))) (J : Plan (Label V)) :
    CanonicalLengthSearch.Result (Label V) :=
  let C := J.common H
  let i := parent J.root
  let A := J.small T U
  let Z := J.large T U
  let R := Q∪C.toFinset
  if ((after (insert (leaf key i 0) R) A)∩F.image original).card=k then
    .success 0 A
  else
    CanonicalLengthSearch.run (F.image original) R (leaf key i)
      (fun s=>FiniteLabelContinuation.continuation (fun j=>original (loc j)) (rows distance)
        (F.image original) v lam (q+1) n (insert (leaf key i s) R)) A Z b k precision

attribute [local instance] RationalLeaves.metric

end MetricKMedianRecovery.CanonicalSensitiveEndpoint

namespace MetricKMedianRecovery.CanonicalCoupledMerge
open PhaseSequence PhaseHistoryTransfer PhaseMergeCompletion PhaseMergeRefinement PhaseCountCrossing
  CanonicalMergeCrossing RationalLeaves PhaseMergeInvariant PhaseCoupledMerge
variable {V : Type*} [DecidableEq V] {d : ℕ}

def Correction.error : Correction V → ℚ
  | .identity => 0
  | .shorten _ _ l u => u-l

def State.a (F : Finset V) (s : State V) :=
  ((after (after ∅ s.mapPrefix) s.T)∩F.image original).card

def State.b (F : Finset V) (s : State V) :=
  ((after (after ∅ s.P) s.U)∩F.image original).card

variable [PseudoMetricSpace V]
attribute [local instance] RationalLeaves.metric

structure Certified (loc : Fin d → V) (F : Finset V) (v eta lo hi : ℝ)
    (q n k : ℕ) (s : State V) : Prop where
  before : Before (3*q) s.B
  before_map : Before (3*q) s.mapFree
  disjoint : Disjoint (F.image original) s.B
  low : lo≤(s.lam:ℝ)
  high : (s.lam':ℝ)≤hi
  price : (s.lam:ℝ)≤(s.lam':ℝ)
  eps_nonneg : (0:ℝ)≤ s.correction.error
  error : (s.lam':ℝ)-s.lam+(d:ℝ)*((1-3*v)*(s.correction.error:ℝ))≤(d:ℝ)*eta
  inj : Function.Injective s.correction.apply
  fixed : ∀ i∈F.image original,s.correction.apply i=i
  shrink : ∀ j,∀ x∈F.image original∪s.B,
    dist (original (loc j)) (s.correction.apply x)≤dist (original (loc j)) x
  loss : ∀ j,∀ x∈F.image original∪s.B,
    dist (original (loc j)) x≤dist (original (loc j)) (s.correction.apply x)+s.correction.error
  old_prefix : PrefixData (fun j=>original (loc j)) (F.image original) s.B v s.lam eta q s.P
  new_prefix : PrefixData (fun j=>original (loc j)) (F.image original) s.mapFree v s.lam' eta q s.mapPrefix
  sandwich : Sandwich k (s.a F) (s.b F)
  new_tail : Runs (fun j=>original (loc j)) (F.image original) s.mapFree (after ∅ s.mapPrefix) v s.lam' q n s.T
  old_tail : Runs (fun j=>original (loc j)) (F.image original) s.B (after ∅ s.P) v s.lam q n s.U

noncomputable def Certified.coupled {loc : Fin d → V} {F : Finset V} {v eta lo hi : ℝ}
    {q n k : ℕ} {s : State V} (h : Certified loc F v eta lo hi q n k s) :
    Coupled (fun j=>original (loc j)) (F.image original) v eta lo hi q n k where
  B := s.B
  P := s.P
  r := s.correction.apply
  lam := s.lam
  lam' := s.lam'
  eps := s.correction.error
  a := s.a F
  b := s.b F
  disjoint := h.disjoint
  low := h.low
  high := h.high
  price := h.price
  eps_nonneg := h.eps_nonneg
  error := by simpa only [Fintype.card_fin] using h.error
  inj := h.inj
  fixed := h.fixed
  shrink := h.shrink
  loss := h.loss
  old_prefix := h.old_prefix
  new_prefix := h.new_prefix
  sandwich := h.sandwich
  new_tail := h.new_tail.attains
  old_tail := h.old_tail.attains

def Output.Correct (loc : Fin d → V) (F : Finset V) (v eta lo hi : ℝ)
    (total k : ℕ) (o : Output V) : Prop :=
  Disjoint (F.image original) o.B ∧ lo≤(o.lam:ℝ) ∧ (o.lam:ℝ)≤hi ∧
  PrefixData (fun j=>original (loc j)) (F.image original) o.B v o.lam eta total o.P ∧
    ((after ∅ o.P)∩F.image original).card=k

end MetricKMedianRecovery.CanonicalCoupledMerge

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Machines_MergeResources
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.CanonicalCoupledMerge
open RationalLeaves RationalHeight
variable {V : Type*} [DecidableEq V]

structure State.Resources (F : Finset V) (q h p : ℕ) (s : State V) : Prop where
  bank : BankBound F h (3*q) (q*(2*F.card+1)) s.B
  correction : s.correction.Bounded h
  oldPrice : Height s.lam p
  newPrice : Height s.lam' p

end MetricKMedianRecovery.CanonicalCoupledMerge

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Recovery_CoupledFinish
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.CanonicalCoupledMerge
open PhaseSequence PhaseHistoryTransfer PhaseMergeCompletion PhaseMergeRefinement PhaseCountCrossing
  CanonicalMergeCrossing RationalLeaves PhaseMergeInvariant PhaseCoupledMerge
variable {V : Type*} [PseudoMetricSpace V] [DecidableEq V] {d : ℕ}
attribute [local instance] RationalLeaves.metric

def finish (B : Finset (Label V)) (lam : ℚ) (P T : List (List (Label V))) : Output V :=
  ⟨B,lam,P++T⟩

def sameState (B : Finset (Label V)) (lam : ℚ) (P T U : List (List (Label V))) : State V :=
  ⟨B,P,.identity,lam,lam,T,U⟩

end MetricKMedianRecovery.CanonicalCoupledMerge

namespace MetricKMedianRecovery.CanonicalCoupledMerge
open PhaseSequence PhaseHistoryTransfer PhaseMergeCompletion PhaseMergeRefinement PhaseCountCrossing
  CanonicalMergeCrossing RationalLeaves PhaseMergeInvariant PhaseCoupledMerge
variable {V : Type*} [PseudoMetricSpace V] [DecidableEq V] {d : ℕ}
attribute [local instance] RationalLeaves.metric

def advanceState (s : State V) (G : List (Label V)) (T U : List (List (Label V))) : State V :=
  { s with P := s.P++[G],T := T,U := U }

end MetricKMedianRecovery.CanonicalCoupledMerge

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Recovery_CoupledLeaf
attribute [-instance] _root_.OAI.MetricKMedianRecovery.Categorical.binaryOracleIndexDecidableEq
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.CanonicalCoupledMerge
open PhaseSequence PhaseHistoryTransfer PhaseMergeCompletion PhaseMergeRefinement PhaseCountCrossing
  CanonicalMergeCrossing RationalLeaves PhaseMergeInvariant PhaseCoupledMerge
variable {V : Type*} [PseudoMetricSpace V] [DecidableEq V] {d : ℕ}
attribute [local instance] RationalLeaves.metric

def leafState (B : Finset (Label V)) (P : List (List (Label V))) (lam : ℚ)
    (key : ℕ) (i : V) (H : List (Label V)) (l u : ℚ) (T U : List (List (Label V))) : State V :=
  ⟨insert (leaf key i u) B,P++[H++[leaf key i u]],.shorten key i l u,lam,lam,T,U⟩

end MetricKMedianRecovery.CanonicalCoupledMerge

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Recovery_CoupledResolve
attribute [-instance] _root_.OAI.MetricKMedianRecovery.Categorical.binaryOracleIndexDecidableEq
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.CanonicalCoupledMerge

section
open PhaseSequence PhaseHistoryTransfer PhaseMergeCompletion PhaseMergeRefinement PhaseCountCrossing
  CanonicalMergeCrossing RationalLeaves PhaseMergeInvariant PhaseCoupledMerge CanonicalLengthView
variable {V : Type*} [LinearOrder V] {d : ℕ}

def resolve (loc : Fin d → V) (distance : V → Fin d → ℚ) (F : Finset V)
    (v M : ℚ) (N precision q n k key : ℕ) (B : Finset (Label V)) (lam : ℚ)
    (P : List (List (Label V))) : CanonicalMergeCrossing.Result (Label V) → Outcome V
  | .success H T => .inl (finish B lam (P++[H]) T)
  | .common H T U => .inr (sameState B lam (P++[H]) T U)
  | .sensitive H G T U =>
    match view (rows distance) (F.image original) ((F.sort (·≤·)).map original) H G with
    | none => .inl (finish B lam P [])
    | some J =>
      let i := parent J.root
      let C := J.common H
      match CanonicalSensitiveEndpoint.run loc distance F (after ∅ P) v lam (20*N*M) q n k key precision H T U J with
      | .success s W => .inl (finish (insert (leaf key i s) B) lam (P++[C++[leaf key i s]]) W)
      | .bracket l u A Z => .inr (leafState B P lam key i C l u A Z)

variable [PseudoMetricSpace V]
attribute [local instance] RationalLeaves.metric

def Outcome.Correct (loc : Fin d → V) (F : Finset V) (v eta lo hi : ℝ) (q n k : ℕ) : Outcome V → Prop
  | .inl o => o.Correct loc F v eta lo hi (q+(n+1)) k
  | .inr s => Certified loc F v eta lo hi (q+1) n k s

end

open PhaseSequence PhaseHistoryTransfer PhaseMergeCompletion PhaseMergeRefinement PhaseCountCrossing
  CanonicalMergeCrossing RationalLeaves PhaseMergeInvariant PhaseCoupledMerge
variable {V : Type*} [LinearOrder V] {d : ℕ}

def banks (F : Finset V) (B : Finset (Label V)) (q : ℕ) : Finset (Label V) :=
  PhaseMergePath.pool (F.image original) (PhaseMergePath.pool (F.image original) B (copy (3*q))) (copy (3*q+1))

def step (loc : Fin d → V) (distance : V → Fin d → ℚ) (F : Finset V)
    (v M : ℚ) (N precision q n k : ℕ) (s : State V) : Outcome V :=
  match s.T,s.U with
  | H::T,G::U =>
    let W := FiniteLabelContinuation.continuation (fun j=>original (loc j)) (rows distance)
      (F.image original) v s.lam' (q+1) n (after ∅ s.mapPrefix∪G.toFinset)
    let c := finalCount (F.image original) (after ∅ s.mapPrefix) G W
    if c=k then .inl (finish s.mapFree s.lam' (s.mapPrefix++[G]) W)
    else if Sandwich k (s.a F) c then
      resolve loc distance F v M N precision q n k (3*q+2) (banks F s.mapFree q)
        s.lam' s.mapPrefix
        (FiniteLabelCrossing.run (fun j=>original (loc j)) (rows distance) (F.image original)
          (after ∅ s.mapPrefix) v s.lam' q n k (copy (3*q)) (copy (3*q+1)) H G T W)
    else .inr (advanceState s G W U)
  | _,_ => .inl (finish s.B s.lam s.P [])

attribute [local instance] RationalLeaves.metric

end MetricKMedianRecovery.CanonicalCoupledMerge

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Branching_CopyAge
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.CanonicalCoupledMerge
open RationalLeaves RationalHeight
variable {V : Type*} [DecidableEq V]

structure Output.Resources (F : Finset V) (q h p : ℕ) (o : Output V) : Prop where
  bank : BankBound F h (3*q) (q*(2*F.card+1)) o.B
  price : Height o.lam p

def Outcome.Resources (F : Finset V) (q h p : ℕ) : Outcome V → Prop
  | .inl o => o.Resources F (q+1) h p
  | .inr s => s.Resources F (q+1) h p

end MetricKMedianRecovery.CanonicalCoupledMerge

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Encoding_WordExtras
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryJump
open WordOperations WordList RationalLeaves CanonicalMergeRefinement BinaryArithmetic
open BinaryFiniteContext (labels )
open BinaryOpeningPayment (field field_encode)
def jumpBits {m : ℕ} : Jump (Label (Fin m)) → List Bool
  | .add i=>encode [(0:ℕ).bits,[],[],[],BinaryLabel.encode i]
  | .remove C T A i=>encode [(1:ℕ).bits,labels C,labels T,labels A,BinaryLabel.encode i]
  | .replace C T i=>encode [(2:ℕ).bits,labels C,labels T,[],BinaryLabel.encode i]

end MetricKMedianRecovery.BitMachine.BinaryJump

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Encoding_RationalSort
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryRationalSort
open WordOperations WordList BinaryArithmetic

def entryBits (p : ℚ ×ₗ ℕ) : List Bool := pairBits (BinaryRational.encode (ofLex p).1,(ofLex p).2.bits)
end MetricKMedianRecovery.BitMachine.BinaryRationalSort

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Branching_PopulationMachine
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryPopulation
open WordOperations WordList BinaryArithmetic
open BinaryOpeningPayment (field field_encode)
attribute [local irreducible] WordList.mapWith
def pack (P : ℚ) (m : ℕ) (ds : List ℚ) : List Bool :=
  encode [BinaryRational.encode P,m.bits,RationalArray.encode ds]
end MetricKMedianRecovery.BitMachine.BinaryPopulation

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Encoding_ColorLabelMachine
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryRationalPower
open WordOperations WordList RationalHeight
def pack (q : ℚ) (n : ℕ) : List Bool := pairBits (List.replicate n true,BinaryRational.encode q)
end MetricKMedianRecovery.BitMachine.BinaryRationalPower

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Machines_MenuMachine
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryMenu
open WordOperations WordList BinaryArithmetic
open BinaryOpeningPayment (field field_encode)
def optBits (o : Option ℚ) : List Bool := encode (o.toList.map BinaryRational.encode)
def radii (κ pop : ℚ) (near : Option ℚ) : List Bool := encode [BinaryRational.encode κ,BinaryRational.encode pop,optBits near]
attribute [local irreducible] mapWith
end MetricKMedianRecovery.BitMachine.BinaryMenu

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Recovery_NearEligible
attribute [-instance] _root_.OAI.MetricKMedianRecovery.RationalLeaves.labelLinearOrder
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.Sampling
variable {V : Type*} [LinearOrder V] [PseudoMetricSpace V]
namespace Comparison
variable {D S O : Finset V}
open RadiusMenus

open scoped Classical

noncomputable def prescribedEntry (C : Comparison D S O) (hD : D.Nonempty)
    (hP : 0 < comparisonCost D C.assign) (hm : 0 < C.bad.card)
    (s : State V) (w : D) : MainEntry C.bad.card :=
  if hs : C.Correct hD mainKappa s then
    (C.correct_entry_exists hD mainKappa mainKappa_pos s hs hP hm w w.property).choose
  else .inl ⟨0,by unfold firstSize; omega⟩

noncomputable def activeGuide (C : Comparison D S O) (hD : D.Nonempty)
    (Δ : ℝ) (hΔ : 0 ≤ Δ) (hP : 0 < comparisonCost D C.assign) (hm : 0 < C.bad.card)
    (s : State V) (hs : C.Correct hD mainKappa s) (ht : ¬C.Terminal mainKappa Δ s) :
    Guided.Kernel Unit (MainAction D C.bad.card) :=
  if hball : mainKappa*comparisonCost D C.assign < C.nearTotal Δ s then
    Guided.routed
      (conditionalClients D S Δ s (C.nearEligible s) (Finset.filter_subset _ _)
        (C.nearTotal Δ s) ((mul_pos mainKappa_pos hP).trans hball)
        (C.eligible_near_weight hD Δ hΔ s hs))
      (fun _ w => .inr (.inr (w,C.prescribedEntry hD hP hm s w)))
  else Guided.routed
      (conditionalClients D S Δ s (C.removalEligible Δ s) (Finset.filter_subset _ _)
        (C.removalTotal Δ s)
        (by have hh : mainKappa*comparisonCost D C.assign < C.removalTotal Δ s := by
              by_contra hc
              exact ht ⟨le_of_not_gt hball,le_of_not_gt hc⟩
            exact (mul_pos mainKappa_pos hP).trans hh)
        (C.eligible_removal_weight hD Δ hΔ s hs))
      (fun _ w => .inr (.inl w))

end Comparison
end MetricKMedianRecovery.Sampling

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Recovery_Guide
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.Sampling
variable {V : Type*} [LinearOrder V] [PseudoMetricSpace V]
namespace Comparison
variable {D S O : Finset V}
open RadiusMenus
open scoped Classical

noncomputable def guideAt (C : Comparison D S O) (hD : D.Nonempty)
    (Δ : ℝ) (hΔ : 0 ≤ Δ) (hP : 0 < comparisonCost D C.assign) (hm : 0 < C.bad.card)
    (s : Option (State V)) : Guided.Kernel Unit (MainAction D C.bad.card) :=
  match s with
  | none => Guided.pure (.inl ())
  | some s => if hs : C.Correct hD mainKappa s then
      if ht : C.Terminal mainKappa Δ s then Guided.pure (.inl ())
      else C.activeGuide hD Δ hΔ hP hm s hs ht
    else ⟨fun _ a => (mainActual D S Δ C.bad.card).weight (some s) a,
      fun _ a => (mainActual D S Δ C.bad.card).nonneg (some s) a,
      fun _ => (mainActual D S Δ C.bad.card).total (some s)⟩

noncomputable def guideKernel (C : Comparison D S O) (hD : D.Nonempty)
    (Δ : ℝ) (hΔ : 0 ≤ Δ) (hP : 0 < comparisonCost D C.assign) (hm : 0 < C.bad.card) :
    Guided.Kernel (Option (State V)) (MainAction D C.bad.card) :=
  ⟨fun s a => (C.guideAt hD Δ hΔ hP hm s).weight () a,
    fun s a => (C.guideAt hD Δ hΔ hP hm s).nonneg () a,
    fun s => (C.guideAt hD Δ hΔ hP hm s).total ()⟩

def Valid (C : Comparison D S O) (hD : D.Nonempty) : Option (State V) → Prop
  | none => False
  | some s => C.Correct hD mainKappa s

noncomputable def remaining (C : Comparison D S O) : Option (State V) → ℕ
  | none => 0
  | some s => C.counter s

noncomputable def guideLoss (C : Comparison D S O) (hD : D.Nonempty) (Δ : ℝ)
    (s : Option (State V)) (a : MainAction D C.bad.card) : ℝ :=
  if C.Valid hD s ∧ ¬C.stop hD Δ s then
    NearClients.progressConstant mainKappa * actionMenuWeight C.bad.card a else 1

end Comparison
end MetricKMedianRecovery.Sampling

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Branching_ObservableCapacity
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryZeroBranch
open WordOperations WordList BinaryBranchContext BinaryBranchProgram BinaryArithmetic
attribute [local instance] Classical.propDecidable
open BinaryOpeningPayment (field field_encode)
variable {n : ℕ}
noncomputable def output (δ : Fin n→Fin n→ℚ) (D F S : Finset (Fin n)) (Δ : ℚ) (s : RationalSampling.State n)
    (colors : Fin n→Fin 3) (q : ℕ)
    (bits : Categorical.BinaryOracleIndex (Fin (s.leaves.length*n)) s.leaves.length (Categorical.Explicit.exponent s.leaves.length)
      (Categorical.Explicit.samples (s.leaves.length*n) s.leaves.length)→Bool) : Finset (Fin n) := by
  classical
  exact if hr : BinaryBranchCheck.Ready δ F S s colors q 0 0 then
    result δ D F S Δ s colors hr.2.1 (Fin.elim0 : Fin 0→Fin n) Fin.elim0 q bits
  else S
end MetricKMedianRecovery.BitMachine.BinaryZeroBranch

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Branching_RandomizedZeroBranch
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryRandomizedZeroBranch
open WordOperations WordList BinaryBranchContext
variable {n : ℕ}
abbrev Seed (n p : ℕ) := (Fin n→Fin 4)×BinaryObservableBranch.Bits n p
def embed {n p : ℕ} (seed : Seed n p) : BinaryBranchTape.Seed n 1 p := ((seed.1,fun _=>⟨0,by unfold ColorLabel.labelRange; positivity⟩),seed.2)
def raw {n p : ℕ} (seed : Seed n p) : List Bool := BinaryBranchTape.raw (embed seed)
abbrev count (n p : ℕ) := BinaryBranchTape.colorCount n+BinaryBranchTape.completionCount n p
def layout (n p : ℕ) : (Fin (count n p)→Bool)≃Seed n p :=
  (BinaryBranchTape.split _ _).trans (Equiv.prodCongr (BinaryBranchTape.colors n)
    (BinaryCategorical.Tape.layout (p*n) p (Categorical.Explicit.exponent p) (Categorical.Explicit.samples (p*n) p)))
end MetricKMedianRecovery.BitMachine.BinaryRandomizedZeroBranch

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Algorithms_IntegralRecoverySemantics
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryIntegralRecovery
open WordOperations WordList Sampling.Comparison
variable {n : ℕ}
noncomputable def stateAt (δ : Fin n→Fin n→ℚ) (D F S : Finset (Fin n)) (Δ : ℕ) (P : ℚ) (m : ℕ)
    (seed : Fin (2*m)→Fin (integralPrecision D (Δ:ℝ) m)→Bool) (i : Fin (2*m+1)) :
    Option (RationalSampling.State n) :=
  ((List.ofFn seed).take i.val).foldl
    (RationalSampling.next δ D F S Δ P (1/1000000) m BinarySampler.Parameters.M BinarySampler.Parameters.E
      (RadiusMenus.thirdSize mainKappa m) (integralPrecision D (Δ:ℝ) m)) (some RationalSampling.State.initial)
end MetricKMedianRecovery.BitMachine.BinaryIntegralRecovery

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Encoding_LengthEncode
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryLength
open WordOperations WordList RationalLeaves CanonicalLengthView BinaryArithmetic
open BinaryFiniteContext (labels )
open BinaryOpeningPayment (field field_encode)
def planBits {m : ℕ} : Plan (Label (Fin m)) → List Bool
  | .free i f=>encode [(0:ℕ).bits,BinaryLabel.encode i,BinaryLabel.encode f,[],[]]
  | .paid C T i=>encode [(1:ℕ).bits,BinaryLabel.encode i,[],labels C,labels T]
end MetricKMedianRecovery.BitMachine.BinaryLength

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Geometry_LocalCandidates
attribute [-instance] _root_.OAI.MetricKMedianRecovery.Categorical.binaryOracleIndexFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryLocalCost
open WordOperations WordList BinaryArithmetic RationalLeaves
open BinaryFiniteContext (labels )
open BinaryOpeningPayment (field field_encode)
def connection {m d : ℕ} (distance : Fin m→Fin d→ℚ) (S : Finset (Label (Fin m))) (j : Fin d) : ℚ :=
  RationalMin.minimum ((BinaryLabel.orderedSort S).map (fun a=>rows distance a j))
def cost {m d : ℕ} (distance : Fin m→Fin d→ℚ) (S : Finset (Label (Fin m))) : ℚ := ∑ j,connection distance S j
end MetricKMedianRecovery.BitMachine.BinaryLocalCost

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Machines_CoupledLoop
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.CanonicalCoupledMerge
open PhaseSequence PhaseHistoryTransfer PhaseMergeCompletion PhaseMergeRefinement PhaseCountCrossing
  CanonicalMergeCrossing RationalLeaves PhaseMergeInvariant PhaseCoupledMerge
variable {V : Type*} [LinearOrder V] {d : ℕ}

def run (loc : Fin d → V) (distance : V → Fin d → ℚ) (F : Finset V)
    (v M : ℚ) (N precision k : ℕ) : ℕ → ℕ → State V → Output V
  | _q,0,s => finish s.B s.lam s.P []
  | q,n+1,s => match step loc distance F v M N precision q n k s with
    | .inl o => o
    | .inr t => run loc distance F v M N precision k (q+1) n t

attribute [local instance] RationalLeaves.metric

end MetricKMedianRecovery.CanonicalCoupledMerge

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Recovery_CoupledInitial
attribute [-instance] _root_.OAI.MetricKMedianRecovery.Categorical.binaryOracleIndexDecidableEq _root_.OAI.MetricKMedianRecovery.Categorical.binaryOracleIndexFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.CanonicalCoupledMerge
open PhaseSequence PhaseHistoryTransfer PhaseMergeCompletion PhaseMergeRefinement PhaseCountCrossing
  CanonicalMergeCrossing RationalLeaves PhaseMergeInvariant PhaseCoupledMerge
variable {V : Type*} [LinearOrder V] {d : ℕ}

def initial (l u : ℚ) (T U : List (List (Label V))) : State V :=
  ⟨∅,[],.identity,l,u,T,U⟩

attribute [local instance] RationalLeaves.metric

end MetricKMedianRecovery.CanonicalCoupledMerge

namespace MetricKMedianRecovery.CanonicalCoupledMerge
open PhaseSequence PhaseHistoryTransfer PhaseMergeCompletion PhaseMergeRefinement PhaseCountCrossing
  CanonicalMergeCrossing RationalLeaves PhaseMergeInvariant PhaseCoupledMerge
variable {V : Type*} [LinearOrder V] {d : ℕ}

inductive StartOutput (V : Type*) where
  | small (o : Output V)
  | normal (o : Output V)

def initialHistory (loc : Fin d → V) (distance : V → Fin d → ℚ) (F : Finset V)
    (v lam : ℚ) (total : ℕ) : List (List (Label V)) :=
  FiniteLabelContinuation.continuation (fun j=>original (loc j)) (rows distance)
    (F.image original) v lam 0 total ∅

def initialCount (loc : Fin d → V) (distance : V → Fin d → ℚ) (F : Finset V)
    (v lam : ℚ) (total : ℕ) : ℕ :=
  ((after ∅ (initialHistory loc distance F v lam total))∩F.image original).card

def start (loc : Fin d → V) (distance : V → Fin d → ℚ) (F : Finset V)
    (v lo M : ℚ) (N precision total k : ℕ) : StartOutput V :=
  let count := fun lam => initialCount loc distance F v lam total
  if count lo≤k then .small (finish ∅ lo [] (initialHistory loc distance F v lo total))
  else
    let high := 8*(d:ℚ)*M
    let I := PriceBisection.search count k (PriceBisection.iterations lo high precision) (lo,high)
    let U := initialHistory loc distance F v I.1 total
    let T := initialHistory loc distance F v I.2 total
    if count I.1=k then .normal (finish ∅ I.1 [] U)
    else if count I.2=k then .normal (finish ∅ I.2 [] T)
    else .normal (run loc distance F v M N precision k 0 total (initial I.1 I.2 T U))

variable [PseudoMetricSpace V]
attribute [local instance] RationalLeaves.metric

def StartOutput.Correct (loc : Fin d → V) (F : Finset V) (v eta : ℝ) (lo M : ℚ)
    (total k : ℕ) : StartOutput V → Prop
  | .small o => o.B=∅ ∧ o.lam=lo ∧
      PrefixData (fun j=>original (loc j)) (F.image original) ∅ v lo eta total o.P ∧
      ((after ∅ o.P)∩F.image original).card≤k
  | .normal o => o.Correct loc F v eta lo (8*(d:ℝ)*(M:ℝ)) total k

end MetricKMedianRecovery.CanonicalCoupledMerge

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Recovery_CanonicalParents
attribute [-instance] _root_.OAI.MetricKMedianRecovery.Categorical.binaryOracleIndexDecidableEq
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.CanonicalCoupledMerge
open RationalLeaves CanonicalLengthView
variable {V : Type*} [LinearOrder V] {d : ℕ}

def Outcome.Rooted (F : Finset V) : Outcome V→Prop
  | .inl o => CanonicalCoupledMerge.Rooted F o.B
  | .inr s => CanonicalCoupledMerge.Rooted F s.B

def StartOutput.Rooted (F : Finset V) : StartOutput V→Prop
  | .small o => CanonicalCoupledMerge.Rooted F o.B
  | .normal o => CanonicalCoupledMerge.Rooted F o.B
end MetricKMedianRecovery.CanonicalCoupledMerge

namespace MetricKMedianRecovery.CanonicalCoupledMerge
open RationalLeaves PhaseSequence PhaseHistoryTransfer PhaseMergeInvariant PhaseMergeCertificate HistoryPhaseBound
variable {V : Type*} [LinearOrder V] [PseudoMetricSpace V] {d : ℕ}
attribute [local instance] RationalLeaves.metric

def Output.project (o : Output V) : Finset V := RationalLeaves.project (after ∅ o.P)

end MetricKMedianRecovery.CanonicalCoupledMerge

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Machines_CorrectionSize
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.CanonicalCoupledMerge
open RationalLeaves
variable {V : Type*} [LinearOrder V] {d : ℕ}
def Outcome.Keys (q : ℕ) : Outcome V→Prop
  | .inl _=>True
  | .inr s=>s.correction.Keys (q+1)
end MetricKMedianRecovery.CanonicalCoupledMerge

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Machines_MatchFold
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryMatch
open WordOperations WordList RationalLeaves CanonicalMatch
open BinaryFiniteContext (labels )
open BinaryOpeningPayment (field field_encode)

def contextBits (base : List Bool) (key : ℕ) {m : ℕ} (F : Finset (Label (Fin m))) :=
  encode [base,key.bits,labels ((BinaryLabel.orderedSort F).map (copy key))]
end MetricKMedianRecovery.BitMachine.BinaryMatch

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Machines_MatchSize
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryRegular
open WordOperations WordList RationalLeaves CanonicalMergePath PhaseSequence
open BinaryFiniteContext (labels )
open BinaryOpeningPayment (field field_encode)

def pack {m : ℕ} (base : List Bool) (key : ℕ) (H J : List (Label (Fin m))) : List Bool :=
  encode [base,key.bits,labels H,labels J]
end MetricKMedianRecovery.BitMachine.BinaryRegular

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Recovery_RegularChain
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryRegularChain
open WordOperations WordList RationalLeaves CanonicalMergePath PhaseSequence
open BinaryFiniteContext (labels )
open BinaryOpeningPayment (field field_encode)
def pack {m : ℕ} (base : List Bool) (key spare : ℕ) (R H G : List (Label (Fin m))) : List Bool :=
  encode [base,key.bits,spare.bits,labels R,labels H,labels G]
end MetricKMedianRecovery.BitMachine.BinaryRegularChain

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Recovery_InitialCorrect
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryPhaseFuel
open WordOperations BinaryArithmetic RationalPhaseFuel RationalHeight

def pack (Z w : ℚ) (q : ℕ) : List Bool :=
  pairBits (BinaryRational.encode Z,pairBits (BinaryRational.encode w,List.replicate q true))

end MetricKMedianRecovery.BitMachine.BinaryPhaseFuel

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Recovery_InitialProject
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.CanonicalCoupledMerge
variable {V : Type*} [LinearOrder V]
def StartOutput.project : StartOutput V→Finset V
  | .small o => o.project
  | .normal o => o.project
end MetricKMedianRecovery.CanonicalCoupledMerge

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Geometry_RoundingMatrix
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryRoundingMatrix
open WordOperations WordList BinaryArithmetic
open BinaryOpeningPayment (field field_encode)
variable {n : ℕ}
noncomputable def colIndex_computes : PolyComputes colIndex := discardPrefix_computes
end MetricKMedianRecovery.BitMachine.BinaryRoundingMatrix

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Algorithms_GlobalCall
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryGlobalCall
open WordOperations WordList BinaryArithmetic
open BinaryOpeningPayment (field field_encode)
def pack (I : RationalMetricInput) (M : ℚ) (raw : List Bool) : List Bool :=
  encode [I.bits,BinaryRational.encode M,raw]
end MetricKMedianRecovery.BitMachine.BinaryGlobalCall

end OAI
end


