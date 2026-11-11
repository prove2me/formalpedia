-- Prove2me | Definitions.Def_Q238K022
-- name    : Q238K022
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-10T23:16:30.234448+00:00
-- url     : https://prove2.me/theorems/d484940c-9f61-4fb7-950c-33a41028c89b
-- title:
--   Definitions bundle Q238K022 of the split of OpenAI, Single-Exponential Recovery and Bounded-Price Strictness for Metric k-Median
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.MetricKMedianRecovery.global_application`, carved from OpenAI's openai/math development (OpenAI, *Single-Exponential Recovery and Bounded-Price Strictness for Metric k-Median*, OpenAI Math Release, September 24, 2026, result family 125, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 99 declarations of OpenAI's Lean: 73 definitions, 2 inductive types or structures, 2 instances and 22 theorems. The definitions and types are `OAI.MetricKMedianRecovery.BitMachine.BinaryOpeningOracle.resultBits`, `OAI.MetricKMedianRecovery.BitMachine.BinaryPhaseFuel.pack`, `OAI.MetricKMedianRecovery.BitMachine.BinaryPopulation.pack`, `OAI.MetricKMedianRecovery.BitMachine.BinaryRationalPower.pack`, `OAI.MetricKMedianRecovery.BitMachine.BinaryRationalSort.entryBits`, `OAI.MetricKMedianRecovery.BitMachine.BinaryRegular.pack`, `OAI.MetricKMedianRecovery.BitMachine.BinaryRegularChain.pack`, `OAI.MetricKMedianRecovery.BitMachine.BinaryRoundingMatrix.pack`, `OAI.MetricKMedianRecovery.BitMachine.BinarySampler.Draw.pack`, `OAI.MetricKMedianRecovery.BitMachine.BinarySampler.config`, `OAI.MetricKMedianRecovery.BitMachine.BinarySamplingReference.pack`, `OAI.MetricKMedianRecovery.BitMachine.BinarySamplingState.optionBits`, `OAI.MetricKMedianRecovery.BitMachine.BinarySanitizedBest.pack`, `OAI.MetricKMedianRecovery.BitMachine.BinaryWeakSolve.pack`, `OAI.MetricKMedianRecovery.BlueDP.nextTable`, `OAI.MetricKMedianRecovery.BlueDP.tableBest`, `OAI.MetricKMedianRecovery.BlueDP.tableRun`, `OAI.MetricKMedianRecovery.BlueDP.tableStep`, `OAI.MetricKMedianRecovery.BlueDP.tables`, `OAI.MetricKMedianRecovery.CanonicalCoupledMerge.Rooted`, `OAI.MetricKMedianRecovery.CanonicalLengthView.Plan.large`, `OAI.MetricKMedianRecovery.CanonicalLengthView.Plan.small`, `OAI.MetricKMedianRecovery.CanonicalLengthView.accepts`, `OAI.MetricKMedianRecovery.CanonicalLengthView.view`, `OAI.MetricKMedianRecovery.CanonicalMergeCrossing.continuation`, `OAI.MetricKMedianRecovery.EffectiveOpenability.storedOpening`, `OAI.MetricKMedianRecovery.Ellipsoid.Stored.exactSolve`, `OAI.MetricKMedianRecovery.Ellipsoid.Stored.facePoint`, `OAI.MetricKMedianRecovery.Ellipsoid.Stored.point`, `OAI.MetricKMedianRecovery.Ellipsoid.exactSolve`, `OAI.MetricKMedianRecovery.Ellipsoid.facePoint`, `OAI.MetricKMedianRecovery.FiniteLabelContinuation.complete`, `OAI.MetricKMedianRecovery.FiniteLabelContinuation.continuation`, `OAI.MetricKMedianRecovery.FiniteLabelCrossing.run`, `OAI.MetricKMedianRecovery.FreshCopyEndpoints.familyMetric`, `OAI.MetricKMedianRecovery.Guided.Realized.canonical`, `OAI.MetricKMedianRecovery.IntegralAssembly.countBound`, `OAI.MetricKMedianRecovery.PhaseFreshAllocation.enlargedMetric`, `OAI.MetricKMedianRecovery.PhaseMergePath.Walk`, `OAI.MetricKMedianRecovery.PhaseMergeRefinement.Chain` and 35 more.
--
--   **Sources.** They come from these modules of lean/OAI/Combinatorics, in whole or in part: `KMedianRecovery_Algorithms_CandidateSanitize`, `KMedianRecovery_Branching_BlueTable`, `KMedianRecovery_Branching_PopulationMachine`, `KMedianRecovery_Branching_SuccessfulFavorableProbability`, `KMedianRecovery_Encoding_ColorLabelMachine`, `KMedianRecovery_Encoding_Matrix`, `KMedianRecovery_Encoding_RationalSort`, `KMedianRecovery_Geometry_FamilyMetric`, `KMedianRecovery_Geometry_LeafDistances`, `KMedianRecovery_Geometry_RoundingMatrix`, `KMedianRecovery_Machines_MatchSize`, `KMedianRecovery_Machines_MergeResources`, `KMedianRecovery_Recovery_BlindUpdate`, `KMedianRecovery_Recovery_CanonicalParents`, `KMedianRecovery_Recovery_Cluster`, `KMedianRecovery_Recovery_CommonL`, `KMedianRecovery_Recovery_DestinationFacility`, `KMedianRecovery_Recovery_Destinations`, `KMedianRecovery_Recovery_Entry`, `KMedianRecovery_Recovery_FacePoint`, `KMedianRecovery_Recovery_FiniteContinuation`, `KMedianRecovery_Recovery_FiniteCross`, `KMedianRecovery_Recovery_Guide`, `KMedianRecovery_Recovery_InitialCorrect`, `KMedianRecovery_Recovery_LeafOutcome`, `KMedianRecovery_Recovery_LengthPolynomial`, `KMedianRecovery_Recovery_MergeCross`, `KMedianRecovery_Recovery_MergePath`, `KMedianRecovery_Recovery_MergeRefine`, `KMedianRecovery_Recovery_NearEligible`, `KMedianRecovery_Recovery_Pack10`, `KMedianRecovery_Recovery_Pack8`, `KMedianRecovery_Recovery_Pool`, `KMedianRecovery_Recovery_RegularChain`, `KMedianRecovery_Recovery_Row`, `KMedianRecovery_Recovery_SingleRadiusRatio`, `KMedianRecovery_Recovery_State2`, `KMedianRecovery_Recovery_Step2`, `KMedianRecovery_Recovery_StoredForms`, `KMedianRecovery_Recovery_Values`, `KMedianRecovery_Sampling_RealizedKernel`, `KMedianRecovery_Sampling_SamplerContext`, `KMedianRecovery_Sampling_SamplerDraw`, `KMedianRecovery_Sampling_SamplingReference`, `KMedianRecovery_Sampling_SamplingStateMachine`, `KMedianRecovery_Strictness_Clipped`.
--
--   **Imports.** It imports the published bundle `Def_KMedianRefinedRecovery`; the bundles `Q238K006`, `Q238K008`, `Q238K010`, `Q238K011`, `Q238K013`, `Q238K014`, `Q238K015` and `Q238K016` of this split.
--
--   **Imported by** (directly, in this split): the bundle `Q238K027`; the statements `OAI.MetricKMedianRecovery.BitMachine.BinaryBlueSize.tableRun_best_bound_s238`, `OAI.MetricKMedianRecovery.BitMachine.BinaryBlueSize.table_length_s238`, `OAI.MetricKMedianRecovery.BitMachine.BinaryBlueTable.next_pack_s238`, `OAI.MetricKMedianRecovery.BitMachine.BinaryBranchProgram.objective_eq_source_s238`, `OAI.MetricKMedianRecovery.BitMachine.BinaryDecision.prepared_pack_s238`, `OAI.MetricKMedianRecovery.BitMachine.BinaryDelete.step_pack_s238`, `OAI.MetricKMedianRecovery.BitMachine.BinaryExactSolve.point_pack_s238`, `OAI.MetricKMedianRecovery.BitMachine.BinaryFiniteMachine.completed_pack_s238`, `OAI.MetricKMedianRecovery.BitMachine.BinaryIntegralRecovery.sampleContext_pack_s238`, `OAI.MetricKMedianRecovery.BitMachine.BinaryLength.view_pack_s238`, `OAI.MetricKMedianRecovery.BitMachine.BinaryPhaseFinish.answer_pack_s238`, `OAI.MetricKMedianRecovery.BitMachine.BinaryPhaseFinish.finish_length_s238`, `OAI.MetricKMedianRecovery.BitMachine.BinaryPhaseFirst.bids_context_s238`, `OAI.MetricKMedianRecovery.BitMachine.BinaryPhaseFirst.eligible_context_s238`, `OAI.MetricKMedianRecovery.BitMachine.BinaryPhaseTrace.iterate_pack_s238`, `OAI.MetricKMedianRecovery.BitMachine.BinaryProjection.run_setBits_s238`, `OAI.MetricKMedianRecovery.BitMachine.BinaryRationalSort.ranked_pack_s238`, `OAI.MetricKMedianRecovery.BitMachine.BinaryRecovery.result_success_s238`, `OAI.MetricKMedianRecovery.BitMachine.BinarySampler.Loop.fold_length_cap_s238`, `OAI.MetricKMedianRecovery.BitMachine.BinarySampler.Weights.weight_pair_s238`, `OAI.MetricKMedianRecovery.BitMachine.BinarySamplingReference.entries_pack_s238`, `OAI.MetricKMedianRecovery.CanonicalMergeCrossing.continuation_spec_s238`, `OAI.MetricKMedianRecovery.EffectiveOpenability.storedOpening_complete_s238`, `OAI.MetricKMedianRecovery.Ellipsoid.Stored.exactSolve_eq_s238`, `OAI.MetricKMedianRecovery.FiniteLabelCrossing.run_spec_s238`, `OAI.MetricKMedianRecovery.RationalLinearFeasibility.storedForms_sound_s238`, `OAI.MetricKMedianRecovery.RationalPhase.complete_spec_s238`, `OAI.MetricKMedianRecovery.RationalPhase.completion_spec_s238`, `OAI.MetricKMedianRecovery.RationalPhase.first_none_maximal_s238`, `OAI.MetricKMedianRecovery.RationalSampling.trace_probability_s238`, `OAI.MetricKMedianRecovery.Sampling.Comparison.covered_completion_sum_s238`, `OAI.MetricKMedianRecovery.Sampling.Comparison.covered_cost_aggregate_s238`, `OAI.MetricKMedianRecovery.Sampling.Comparison.integralPrecision_spec_s238`, `OAI.MetricKMedianRecovery.Sampling.Comparison.successful_completion_charge_s238` and `OAI.MetricKMedianRecovery.Sampling.Comparison.surrogate_success_s238`; the proofs of `OAI.MetricKMedianRecovery.BitMachine.BinaryAssignmentWeight.identities_pack_s238`, `OAI.MetricKMedianRecovery.BitMachine.BinaryBlueBlocks.at_pack_s238`, `OAI.MetricKMedianRecovery.BitMachine.BinaryBlueCell.op_pack_s238`, `OAI.MetricKMedianRecovery.BitMachine.BinaryBlueLoop.run_pack_s238`, `OAI.MetricKMedianRecovery.BitMachine.BinaryBlueSize.tableRun_best_bound_s238`, `OAI.MetricKMedianRecovery.BitMachine.BinaryBlueSize.table_length_s238`, `OAI.MetricKMedianRecovery.BitMachine.BinaryBlueTable.next_pack_s238`, `OAI.MetricKMedianRecovery.BitMachine.BinaryBoundedDecision.run_pack_s238`, `OAI.MetricKMedianRecovery.BitMachine.BinaryBranchCheck.badBalls_nil_s238`, `OAI.MetricKMedianRecovery.BitMachine.BinaryBranchCheck.run_pack_s238`, `OAI.MetricKMedianRecovery.BitMachine.BinaryBranchContext.copyData_pack_s238`, `OAI.MetricKMedianRecovery.BitMachine.BinaryBranchContext.origins_pack_s238`, `OAI.MetricKMedianRecovery.BitMachine.BinaryBranchContext.parts_pack_s238`, `OAI.MetricKMedianRecovery.BitMachine.BinaryBranchProgram.bluePack_pack_s238`, `OAI.MetricKMedianRecovery.BitMachine.BinaryBranchProgram.completion_pack_s238`, `OAI.MetricKMedianRecovery.BitMachine.BinaryBranchProgram.objective_eq_source_s238`, `OAI.MetricKMedianRecovery.BitMachine.BinaryBranchProgram.plan_pack_s238`, `OAI.MetricKMedianRecovery.BitMachine.BinaryBranchProgram.result_guarantee_s238`, `OAI.MetricKMedianRecovery.BitMachine.BinaryBranchProgram.rowInput_pack_s238`, `OAI.MetricKMedianRecovery.BitMachine.BinaryBranchProgram.run_pack_s238`, `OAI.MetricKMedianRecovery.BitMachine.BinaryBranchRandomize.context_pack_s238`, `OAI.MetricKMedianRecovery.BitMachine.BinaryBranchRandomize.labels_pack_s238`, `OAI.MetricKMedianRecovery.BitMachine.BinaryBranchRows.capRow_one_s238`, `OAI.MetricKMedianRecovery.BitMachine.BinaryBranchRows.capRow_zero_s238`, `OAI.MetricKMedianRecovery.BitMachine.BinaryBranchTape.Count.cut_pack_s238`, `OAI.MetricKMedianRecovery.BitMachine.BinaryCategorical.Prepare.left_pack_s238`, `OAI.MetricKMedianRecovery.BitMachine.BinaryCategorical.Prepare.run_pack_s238`, `OAI.MetricKMedianRecovery.BitMachine.BinaryCategorical.bagWords_pack_s238`, `OAI.MetricKMedianRecovery.BitMachine.BinaryCategorical.choose_pack_s238`, `OAI.MetricKMedianRecovery.BitMachine.BinaryCategorical.draw_pack_s238`, `OAI.MetricKMedianRecovery.BitMachine.BinaryCategorical.marginal_pack_s238`, `OAI.MetricKMedianRecovery.BitMachine.BinaryCategorical.nextTable_pack_s238`, `OAI.MetricKMedianRecovery.BitMachine.BinaryCategorical.output_pack_s238`, `OAI.MetricKMedianRecovery.BitMachine.BinaryCompletionRealize.added_pack_s238`, `OAI.MetricKMedianRecovery.BitMachine.BinaryCompletionRealize.redIndices_pack_s238`, `OAI.MetricKMedianRecovery.BitMachine.BinaryCompletionRealize.run_pack_s238`, `OAI.MetricKMedianRecovery.BitMachine.BinaryCompletion.saving_pack_s238`, `OAI.MetricKMedianRecovery.BitMachine.BinaryCopyTables.locations_pack_s238`, `OAI.MetricKMedianRecovery.BitMachine.BinaryCoupledStep.Q_pack_s238`, `OAI.MetricKMedianRecovery.BitMachine.BinaryCoupledStep.mapped_pack_s238`, `OAI.MetricKMedianRecovery.BitMachine.BinaryCross.edge_pack_s238`, `OAI.MetricKMedianRecovery.BitMachine.BinaryCross.finalCount_pack_s238`, `OAI.MetricKMedianRecovery.BitMachine.BinaryDecision.prepared_pack_s238`, `OAI.MetricKMedianRecovery.BitMachine.BinaryDelete.step_pack_s238`, `OAI.MetricKMedianRecovery.BitMachine.BinaryDyadic.lookup_draw_s238`, `OAI.MetricKMedianRecovery.BitMachine.BinaryEllipsoidAdvance.found_pack_s238`, `OAI.MetricKMedianRecovery.BitMachine.BinaryEllipsoidCut.inflateWords_pack_s238`, `OAI.MetricKMedianRecovery.BitMachine.BinaryEllipsoidCut.shapeWords_pack_s238`, `OAI.MetricKMedianRecovery.BitMachine.BinaryEllipsoidInitial.indices_replicate_s238`, `OAI.MetricKMedianRecovery.BitMachine.BinaryEllipsoidIteration.iterate_length_bound_s238`, `OAI.MetricKMedianRecovery.BitMachine.BinaryEllipsoidIteration.run_pack_s238`, `OAI.MetricKMedianRecovery.BitMachine.BinaryExactSolve.gram_pack_s238`, `OAI.MetricKMedianRecovery.BitMachine.BinaryExactSolve.point_pack_s238`, `OAI.MetricKMedianRecovery.BitMachine.BinaryExactSolve.rhs_pack_s238`, `OAI.MetricKMedianRecovery.BitMachine.BinaryExactSolve.transposed_pack_s238`, `OAI.MetricKMedianRecovery.BitMachine.BinaryFinSet.diff_pack_s238`, `OAI.MetricKMedianRecovery.BitMachine.BinaryFinSet.pad_pack_s238`, `OAI.MetricKMedianRecovery.BitMachine.BinaryFinalFace.run_pack_s238`, `OAI.MetricKMedianRecovery.BitMachine.BinaryFiniteContext.alphabet_pack_s238`, `OAI.MetricKMedianRecovery.BitMachine.BinaryFiniteContext.countInter_pack_s238`, `OAI.MetricKMedianRecovery.BitMachine.BinaryFiniteContext.selected_pack_s238`, `OAI.MetricKMedianRecovery.BitMachine.BinaryFiniteContext.union_list_pack_s238`, `OAI.MetricKMedianRecovery.BitMachine.BinaryFiniteMachine.completed_pack_s238`, `OAI.MetricKMedianRecovery.BitMachine.BinaryInitialAuto.context_pack_s238`, `OAI.MetricKMedianRecovery.BitMachine.BinaryInputParser.Stream.run_code_s238`, `OAI.MetricKMedianRecovery.BitMachine.BinaryIntegralRecovery.Fair.demandWord_pack_s238`, `OAI.MetricKMedianRecovery.BitMachine.BinaryIntegralRecovery.Fair.repack_pack_s238`, `OAI.MetricKMedianRecovery.BitMachine.BinaryIntegralRecovery.Guesses.ranges_pack_s238`, `OAI.MetricKMedianRecovery.BitMachine.BinaryIntegralRecovery.sampleContext_pack_s238`, `OAI.MetricKMedianRecovery.BitMachine.BinaryInverseCDF.find_pack_s238`, `OAI.MetricKMedianRecovery.BitMachine.BinaryJump.view_pack_s238`, `OAI.MetricKMedianRecovery.BitMachine.BinaryLength.view_pack_s238`, `OAI.MetricKMedianRecovery.BitMachine.BinaryLocalAnchor.run_pack_s238`, `OAI.MetricKMedianRecovery.BitMachine.BinaryLocalAnchor.state_pack_s238`, `OAI.MetricKMedianRecovery.BitMachine.BinaryLocalCandidates.run_pack_s238`, `OAI.MetricKMedianRecovery.BitMachine.BinaryLocalRefine.integral_spec_s238`, `OAI.MetricKMedianRecovery.BitMachine.BinaryLocalRefine.run_pack_s238`, `OAI.MetricKMedianRecovery.BitMachine.BinaryLocalSearch.iterate_pack_s238`, `OAI.MetricKMedianRecovery.BitMachine.BinaryMetricAnchor.anchorInput_pack_s238`, `OAI.MetricKMedianRecovery.BitMachine.BinaryMetricAnchor.produce_s238`, `OAI.MetricKMedianRecovery.BitMachine.BinaryMetricBest.run_pack_s238`, `OAI.MetricKMedianRecovery.BitMachine.BinaryNodeScan.markers_pack_s238`, `OAI.MetricKMedianRecovery.BitMachine.BinaryObservableBranch.run_pack_s238`, `OAI.MetricKMedianRecovery.BitMachine.BinaryOpeningNearest.run_source_s238`, `OAI.MetricKMedianRecovery.BitMachine.BinaryPhaseFinish.answer_pack_s238`, `OAI.MetricKMedianRecovery.BitMachine.BinaryPhaseFinish.finish_length_s238`, `OAI.MetricKMedianRecovery.BitMachine.BinaryPhaseTrace.iterate_length_s238`, `OAI.MetricKMedianRecovery.BitMachine.BinaryPhaseTrace.iterate_pack_s238`, `OAI.MetricKMedianRecovery.BitMachine.BinaryProjection.run_setBits_s238`, `OAI.MetricKMedianRecovery.BitMachine.BinaryRandomizedBranch.source_run_s238`, `OAI.MetricKMedianRecovery.BitMachine.BinaryRationalSort.ranked_pack_s238`, `OAI.MetricKMedianRecovery.BitMachine.BinaryRationalSort.sumBottom_pack_s238`, `OAI.MetricKMedianRecovery.BitMachine.BinarySampler.Loop.fold_length_cap_s238`, `OAI.MetricKMedianRecovery.BitMachine.BinarySampler.Weights.weight_pair_s238`, `OAI.MetricKMedianRecovery.BitMachine.BinarySamplingOracle.reference_pair_s238`, `OAI.MetricKMedianRecovery.BitMachine.BinarySamplingOracle.total_pack_s238`, `OAI.MetricKMedianRecovery.BitMachine.BinarySamplingReference.entries_pack_s238`, `OAI.MetricKMedianRecovery.BitMachine.BinarySeed.nest_tensor_s238`, `OAI.MetricKMedianRecovery.BitMachine.RationalMatrix.determinantWords_encode_s238`, `OAI.MetricKMedianRecovery.BitMachine.RationalMatrix.fold_steps_s238`, `OAI.MetricKMedianRecovery.BitMachine.RationalMatrix.mulWords_encode_s238`, `OAI.MetricKMedianRecovery.BitMachine.RationalMatrix.solveWords_bird_s238`, `OAI.MetricKMedianRecovery.BitMachine.WordList.Slices.run_items_s238`, `OAI.MetricKMedianRecovery.BitMachine.WordList.flatMapWith_typed_s238`, `OAI.MetricKMedianRecovery.CanonicalMergeCrossing.continuation_spec_s238`, `OAI.MetricKMedianRecovery.CanonicalMergePath.advancePrefix_spec_s238`, `OAI.MetricKMedianRecovery.CanonicalMergeRefinement.refinePath_spec_s238`, `OAI.MetricKMedianRecovery.EffectiveOpenability.storedOpening_complete_s238`, `OAI.MetricKMedianRecovery.Ellipsoid.Stored.exactSolve_eq_s238`, `OAI.MetricKMedianRecovery.Ellipsoid.boundedRationalDecide_correct_s238`, `OAI.MetricKMedianRecovery.Ellipsoid.weakSolve_complete_diameters_s238`, `OAI.MetricKMedianRecovery.FiniteLabelCrossing.run_spec_s238`, `OAI.MetricKMedianRecovery.RationalLinearFeasibility.storedForms_sound_s238`, `OAI.MetricKMedianRecovery.RationalPhase.complete_spec_s238`, `OAI.MetricKMedianRecovery.RationalPhase.completion_spec_s238`, `OAI.MetricKMedianRecovery.RationalPhase.first_none_maximal_s238`, `OAI.MetricKMedianRecovery.RationalSampling.trace_probability_s238`, `OAI.MetricKMedianRecovery.Sampling.Comparison.covered_completion_sum_s238`, `OAI.MetricKMedianRecovery.Sampling.Comparison.covered_cost_aggregate_s238` and `OAI.MetricKMedianRecovery.Sampling.Comparison.successful_completion_charge_s238`.
-- source:
--   OpenAI, Single-Exponential Recovery and Bounded-Price Strictness for Metric k-Median, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 125; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Single-Exponential-Recovery-and-Bounded-Price-Strictness-for-Metric-k-Median-September-24-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Combinatorics at commit adc7f12

import Mathlib
import Definitions.Def_KMedianRefinedRecovery
import Definitions.Def_Q238K006
import Definitions.Def_Q238K008
import Definitions.Def_Q238K010
import Definitions.Def_Q238K011
import Definitions.Def_Q238K013
import Definitions.Def_Q238K014
import Definitions.Def_Q238K015
import Definitions.Def_Q238K016

section
-- module Solutions.Q238_KM.KMedianRecovery_Recovery_Row
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.RationalLinearFeasibility

def Row.Holds {n : ℕ} (r : Row n) (x : Fin n → ℚ) : Prop := r.value x ≤ r.bound
instance instDecidableHolds {n : ℕ} (r : Row n) (x : Fin n → ℚ) : Decidable (r.Holds x) := inferInstanceAs (Decidable (_ ≤ _))

end MetricKMedianRecovery.RationalLinearFeasibility

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Recovery_FacePoint
attribute [-instance] _root_.OAI.MetricKMedianRecovery.Categorical.binaryOracleIndexDecidableEq _root_.OAI.MetricKMedianRecovery.Categorical.binaryOracleIndexFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.Ellipsoid
open Matrix RationalLinearFeasibility PolytopeCertificate
open scoped BigOperators

def facePoint {n : ℕ} (rows : List (Row n)) (B : ℕ) : Fin n → ℚ :=
  let picked := finalFace rows B
  let C := rowMatrix picked
  let G := PositiveSolve.freezeMat (Cᵀ*C)
  let d := PositiveSolve.freezeVec (Cᵀ *ᵥ rowBounds picked)
  PositiveSolve.solve n G d

def exactSolve {n : ℕ} (rows : List (Row n)) (B : ℕ) : Option (Fin n → ℚ) :=
  if boundedRationalDecide rows B then some (facePoint rows B) else none

end MetricKMedianRecovery.Ellipsoid

end OAI
end

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
-- module Solutions.Q238_KM.KMedianRecovery_Recovery_Pack8
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine
open WordOperations BinaryArithmetic RationalLinearFeasibility Ellipsoid
open UnaryResources
namespace BinaryWeakSolve
open RationalMatrix

def pack (n p s R : ℕ) (rs : List (Row n)) : List Bool :=
  pairBits (List.replicate n true,pairBits (List.replicate p true,
    pairBits (List.replicate s true,pairBits (R.bits,BinaryRow.rowsEncode rs))))
end BinaryWeakSolve
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
-- module Solutions.Q238_KM.KMedianRecovery_Encoding_Matrix
attribute [-instance] _root_.OAI.MetricKMedianRecovery.Categorical.binaryOracleIndexDecidableEq _root_.OAI.MetricKMedianRecovery.Categorical.binaryOracleIndexFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.Ellipsoid.Stored
open Matrix RationalLinearFeasibility
open scoped BigOperators

def point {n : ℕ} (picked : List (Row n)) : Fin n → ℚ :=
  let C := matrix (rowMatrix picked)
  let G := matrix (Cᵀ*C)
  let d := vector (Cᵀ *ᵥ rowBounds picked)
  BirdRational.solve G d

def facePoint {n : ℕ} (rows : List (Row n)) (B : ℕ) : Fin n → ℚ :=
  point (finalFace rows B)

def exactSolve {n : ℕ} (rows : List (Row n)) (B : ℕ) : Option (Fin n → ℚ) :=
  if boundedRationalDecide rows B then some (facePoint rows B) else none

end MetricKMedianRecovery.Ellipsoid.Stored

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Recovery_StoredForms
attribute [-instance] _root_.OAI.MetricKMedianRecovery.Categorical.binaryOracleIndexDecidableEq _root_.OAI.MetricKMedianRecovery.Categorical.binaryOracleIndexFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.RationalLinearFeasibility
open scoped BigOperators
variable {V R : Type*} [Fintype V] {n : ℕ}

def storedForms (e : Fin n ≃ V) (rows : List R) (f : R → Form V) (B : ℕ) :
    Option (V → ℚ) :=
  (Ellipsoid.Stored.exactSolve (rows.map (fun r => (f r).enumeratedRow e)) B).map
    (fun y v => y (e.symm v))

end MetricKMedianRecovery.RationalLinearFeasibility

namespace MetricKMedianRecovery.EffectiveOpenability
open RationalLinearFeasibility RationalOpenability OpenabilityLinearization

def storedOpening {m d : ℕ} (distance : Fin m → Fin d → ℚ) (F W : Finset (Fin m))
    (v z lam eta : ℚ) (i : Fin m) : Option (Variables (Fin d) F → ℚ) :=
  storedForms (variableEnum d F)
    (kindRows (List.ofFn (fun j : Fin d => j)) (subtypeList W) (subtypeList F))
    (forms distance F W v z lam eta i) ⌈(1+v^2)*z⌉₊

end MetricKMedianRecovery.EffectiveOpenability

namespace MetricKMedianRecovery.RationalPhase
open EffectiveOpenability OrdinaryProducer OpenabilityLinearization

def first {m d : ℕ} (distance : Fin m → Fin d → ℚ) (F W : Finset (Fin m))
    (v z lam : ℚ) : List (Fin m) → Option (Event m d)
  | [] => none
  | i::todo =>
    if i∈F ∧ i∉W then
      match storedOpening distance F W v z lam 0 i with
      | none => first distance F W v z lam todo
      | some x => some ⟨i,Vector.ofFn (fun j => x (.inl j))⟩
    else first distance F W v z lam todo

def finish {m d : ℕ} (distance : Fin m → Fin d → ℚ) (F : Finset (Fin m))
    (v lam : ℚ) : ℕ → State m d → State m d × List (Event m d)
  | 0,s => (s,[])
  | fuel+1,s =>
    match first distance F s.opened v s.phase lam (List.ofFn (fun i : Fin m => i)) with
    | none => (s,[])
    | some e =>
      let r := finish distance F v lam fuel (update distance v s e)
      (r.1,e::r.2)

end MetricKMedianRecovery.RationalPhase

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Recovery_Pack10
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryOpeningOracle
open WordOperations BinaryArithmetic RationalLinearFeasibility RationalOpenability
open EffectiveOpenability BinaryExactSolve

def resultBits {m d : ℕ} (F : Finset (Fin m)) :
    Option (Variables (Fin d) F → ℚ) → List Bool
  | none=>[]
  | some x=>true::RationalMatrix.rowEncode (fun j=>x (variableEnum d F j))

end MetricKMedianRecovery.BitMachine.BinaryOpeningOracle

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Strictness_Clipped
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.RationalPhase
open EffectiveOpenability OrdinaryProducer

def run {m d : ℕ} (distance : Fin m → Fin d → ℚ) (F : Finset (Fin m))
    (v lam : ℚ) : ℕ → State m d → State m d × List (Instruction m d)
  | 0,s => (s,[])
  | q+1,s =>
      let r := finish distance F v lam F.card s
      let u := advance distance v r.1
      let t := run distance F v lam q u
      (t.1,r.2.map Instruction.opening ++ Instruction.advance::t.2)

end MetricKMedianRecovery.RationalPhase

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Recovery_Entry
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.RationalPhase
open EffectiveOpenability PhaseSequence PhaseHistoryTransfer PhaseMergeCompletion OrdinaryProducer

def historyRun {m d : ℕ} (distance : Fin m → Fin d → ℚ) (F : Finset (Fin m))
    (v lam : ℚ) : ℕ → State m d → State m d × List (List (Fin m))
  | 0,s => (s,[])
  | n+1,s =>
    let r := finish distance F v lam F.card s
    let u := advance distance v r.1
    let t := historyRun distance F v lam n u
    (t.1,(r.2.map Event.facility)::t.2)

end MetricKMedianRecovery.RationalPhase

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Recovery_Pool
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.PhaseMergePath
open PhaseSequence
variable {D X : Type*} [Fintype D] [PseudoMetricSpace X] [DecidableEq X]

inductive Walk (loc : D → X) (F B Q : Finset X) (copy : X → X) (v z lam eta : ℝ) :
    ℕ → List X → List X → Prop
  | nil {H} (hgood : Good loc F B Q copy v z lam eta H) :
      Walk loc F B Q copy v z lam eta 0 H H
  | cons {n H G J} (hgood : Good loc F B Q copy v z lam eta H)
      (hstep : Step loc F B Q copy v z lam H G)
      (tail : Walk loc F B Q copy v z lam eta n G J) :
      Walk loc F B Q copy v z lam eta (n+1) H J

end MetricKMedianRecovery.PhaseMergePath

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Recovery_MergePath
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.RationalPhase
open PhaseSequence PhaseHistoryTransfer PhaseMergeCompletion OrdinaryProducer

def completion {m d : ℕ} (distance : Fin m → Fin d → ℚ) (F : Finset (Fin m))
    (v z lam : ℚ) (Q : Finset (Fin m)) : List (Fin m) :=
  (finish distance F v lam F.card ⟨Q,z,Vector.replicate d 0⟩).2.map Event.facility

end MetricKMedianRecovery.RationalPhase

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Recovery_MergeRefine
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.PhaseMergeRefinement

section
open PhaseSequence PhaseMergePath
variable {D X : Type*} [Fintype D] [PseudoMetricSpace X] [DecidableEq X]

inductive Chain (loc : D → X) (F B Q : Finset X) (v z lam eta : ℝ) :
    ℕ → List X → List X → Prop
  | nil {H} (hgood : Good loc F B Q v z lam eta H) : Chain loc F B Q v z lam eta 0 H H
  | cons {n H G J} (hgood : Good loc F B Q v z lam eta H)
      (hstep : Adjacent loc F B Q H G) (tail : Chain loc F B Q v z lam eta n G J) :
      Chain loc F B Q v z lam eta (n+1) H J

end

open PhaseSequence PhaseMergePath

end MetricKMedianRecovery.PhaseMergeRefinement

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Recovery_MergeCross
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.CanonicalMergeCrossing
open PhaseSequence PhaseHistoryTransfer PhaseMergeCompletion PhaseMergeRefinement PhaseCountCrossing
variable {D X : Type*} [Fintype D] [PseudoMetricSpace X] [DecidableEq X]

def continuation {m d : ℕ} (distance : Fin m → Fin d → ℚ) (F : Finset (Fin m))
    (v lam : ℚ) (q n : ℕ) (Q : Finset (Fin m)) : List (List (Fin m)) :=
  (RationalPhase.historyRun distance F v lam n ⟨Q,(1+v^2)^q,Vector.replicate d 0⟩).2

end MetricKMedianRecovery.CanonicalMergeCrossing

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Geometry_FamilyMetric
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.FreshCopyEndpoints
open PhaseHistoryTransfer
variable {D X : Type*} [Fintype D] [PseudoMetricSpace X] [DecidableEq X]

@[instance_reducible]
noncomputable def familyMetric (i : X) : PseudoMetricSpace (X ⊕ ℝ) :=
  LeafMetric.attachedMetric (fun _ : ℝ => i) (fun s => max s 0) (fun _ => le_max_right _ _)

end MetricKMedianRecovery.FreshCopyEndpoints

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Recovery_FiniteContinuation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.FiniteLabelContinuation
open PhaseSequence PhaseHistoryTransfer PhaseMergeCompletion CanonicalMergeCrossing
variable {X : Type*} [LinearOrder X] {d : ℕ}

def complete (loc : Fin d → X) (distance : X → Fin d → ℚ) (F : Finset X) (v z lam : ℚ)
    (Q : Finset X) : List X :=
  (RationalPhase.completion (rows loc F Q distance) (select loc F Q F) v z lam
    (select loc F Q Q)).map (embed loc F Q)

def continuation (loc : Fin d → X) (distance : X → Fin d → ℚ) (F : Finset X) (v lam : ℚ)
    (q n : ℕ) (Q : Finset X) : List (List X) :=
  (CanonicalMergeCrossing.continuation (rows loc F Q distance) (select loc F Q F) v lam q n
    (select loc F Q Q)).map (List.map (embed loc F Q))

end MetricKMedianRecovery.FiniteLabelContinuation

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Recovery_FiniteCross
attribute [-instance] _root_.OAI.MetricKMedianRecovery.Categorical.binaryOracleIndexDecidableEq
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.FiniteLabelCrossing
open PhaseSequence PhaseHistoryTransfer PhaseMergeCompletion CanonicalMergeCrossing PhaseCountCrossing
variable {X : Type*} [LinearOrder X] {d : ℕ}

def run (loc : Fin d → X) (distance : X → Fin d → ℚ) (F Q : Finset X)
    (v lam : ℚ) (q n k : ℕ) (copy spare : X → X) (H G : List X)
    (T U : List (List X)) : Result X :=
  let complete := FiniteLabelContinuation.complete loc distance F v ((1+v^2)^q) lam
  let S := CanonicalMergeRefinement.regularChain F (F.sort (·≤·)) complete Q copy spare H G
  scan F Q k (FiniteLabelContinuation.continuation loc distance F v lam (q+1) n) U H T S

end MetricKMedianRecovery.FiniteLabelCrossing

namespace MetricKMedianRecovery.CanonicalLengthView
open PhaseSequence PhaseMergeRefinement CanonicalMergeRefinement PhaseCountCrossing
variable {X : Type*} [DecidableEq X] {d : ℕ}

def Plan.small (T U : List (List X)) : Plan X → List (List X)
  | .free _ _ => U
  | .paid _ _ _ => T

def Plan.large (T U : List (List X)) : Plan X → List (List X)
  | .free _ _ => T
  | .paid _ _ _ => U

def accepts (distance : X → Fin d → ℚ) (F : Finset X) (H G : List X) : Plan X → Prop
  | .free i f => i∈F ∧ f∉F ∧ G=H++[f] ∧ ∀ j,distance i j=distance f j
  | .paid C T i => i∈F ∧ H=C++i::T ∧ G=C++T

instance instDecidableAccepts (distance : X → Fin d → ℚ) (F : Finset X) (H G : List X) (J : Plan X) :
    Decidable (accepts distance F H G J) := by cases J <;> dsimp only [accepts] <;> infer_instance

def view (distance : X → Fin d → ℚ) (F : Finset X) (R H G : List X) : Option (Plan X) :=
  (candidates R H G).find? (fun J=>decide (accepts distance F H G J))

end MetricKMedianRecovery.CanonicalLengthView

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Machines_MergeResources
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.RationalLeaves
open RationalHeight
variable {V : Type*} [DecidableEq V]

def HeightBound (h : ℕ) : Label V → Prop
  | .inl _ => True
  | .inr c => Height c.2.2 h

end MetricKMedianRecovery.RationalLeaves

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
-- module Solutions.Q238_KM.KMedianRecovery_Recovery_State2
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.Sampling

variable {V : Type*} [LinearOrder V] [PseudoMetricSpace V]

noncomputable def reference (S : Finset V) (Δ : ℝ) (s : State V) (x : V) : ℝ :=
  tagDistance Δ s x (chosen S Δ s x)

lemma reference_nonneg (S : Finset V) (Δ : ℝ) (s : State V) (x : V)
    (hΔ : 0 ≤ Δ) (hr : ∀ z ∈ s.leaves, 0 ≤ z.2) : 0 ≤ reference S Δ s x := by
  unfold reference
  generalize chosen S Δ s x = t
  cases ht : ofLex t with
  | inl v => simpa only [tagDistance, ht] using (dist_nonneg (x := x) (y := v))
  | inr j =>
    cases j with
    | zero => simpa only [tagDistance, ht] using hΔ
    | succ j =>
      cases hz : s.leaves[j]? with
      | none => simpa only [tagDistance, ht, hz] using hΔ
      | some z =>
        simp only [tagDistance, ht, hz]
        exact add_nonneg dist_nonneg (hr z (List.mem_of_getElem? hz))

end MetricKMedianRecovery.Sampling

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Geometry_LeafDistances
attribute [-instance] _root_.OAI.MetricKMedianRecovery.Categorical.binaryOracleIndexDecidableEq _root_.OAI.MetricKMedianRecovery.Categorical.binaryOracleIndexFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.Sampling
open RadiusMenus
variable {V : Type*} [LinearOrder V] [PseudoMetricSpace V]

noncomputable def clientWeight (S : Finset V) (Δ : ℝ) (s : State V) (w : V) : ℝ :=
  max 0 (reference S Δ s w)

noncomputable def totalWeight (D S : Finset V) (Δ : ℝ) (s : State V) : ℝ :=
  ∑ w ∈ D, clientWeight S Δ s w

lemma clientWeight_nonneg (S : Finset V) (Δ : ℝ) (s : State V) (w : V) :
    0 ≤ clientWeight S Δ s w := le_max_left _ _

lemma clientWeight_eq (S : Finset V) (Δ : ℝ) (s : State V) (w : V)
    (hΔ : 0 ≤ Δ) (hr : ∀ z ∈ s.leaves, 0 ≤ z.2) :
    clientWeight S Δ s w = reference S Δ s w :=
  max_eq_right (reference_nonneg S Δ s w hΔ hr)

noncomputable def transitionWeight (D S : Finset V) (Δ : ℝ) (M E J : ℕ)
    (s : Option (State V)) (a : Action D M E J) : ℝ :=
  match s with
  | none => if a = Sum.inl () then 1 else 0
  | some s => if 0 < totalWeight D S Δ s then
      match a with
      | .inl _ => 0
      | .inr (.inl w) => clientWeight S Δ s w/(2*totalWeight D S Δ s)
      | .inr (.inr (w,e)) => clientWeight S Δ s w/(2*totalWeight D S Δ s)*menuWeight M E J e
    else if a = Sum.inl () then 1 else 0

lemma transitionWeight_nonneg (D S : Finset V) (Δ : ℝ) (M E J : ℕ)
    (s : Option (State V)) (a : Action D M E J) : 0 ≤ transitionWeight D S Δ M E J s a := by
  classical
  cases s with
  | none => simp only [transitionWeight]; split_ifs <;> norm_num
  | some s =>
    simp only [transitionWeight]
    split_ifs with h
    · rcases a with u | (w | ⟨w,e⟩)
      · exact le_rfl
      · exact div_nonneg (clientWeight_nonneg S Δ s w) (by positivity)
      · exact mul_nonneg (div_nonneg (clientWeight_nonneg S Δ s w) (by positivity))
          (menuWeight_nonneg M E J e)
    · norm_num
    · norm_num

lemma transitionWeight_total (D S : Finset V) (Δ : ℝ) (M E J : ℕ)
    (hM : 0 < M) (hJ : 0 < J) (s : Option (State V)) :
    ∑ a : Action D M E J, transitionWeight D S Δ M E J s a = 1 := by
  classical
  cases s with
  | none => simp [transitionWeight]
  | some s =>
    by_cases h : 0 < totalWeight D S Δ s
    · simp only [transitionWeight, ite_eq_left h, Fintype.sum_sum_type, Fintype.sum_prod_type,
        Finset.sum_const_zero, zero_add, ← Finset.mul_sum, menuWeight_total M E J hM hJ, mul_one]
      rw [← Finset.sum_div, Finset.sum_coe_sort]
      change totalWeight D S Δ s/(2*totalWeight D S Δ s) +
        totalWeight D S Δ s/(2*totalWeight D S Δ s) = 1
      field_simp
      ring
    · simp [transitionWeight, h]

noncomputable def actualKernel (D S : Finset V) (Δ : ℝ) (M E J : ℕ)
    (hM : 0 < M) (hJ : 0 < J) : Guided.Kernel (Option (State V)) (Action D M E J) :=
  ⟨transitionWeight D S Δ M E J, transitionWeight_nonneg D S Δ M E J,
    transitionWeight_total D S Δ M E J hM hJ⟩

noncomputable def menuRadius (D : Finset V) (hD : D.Nonempty) (P kappa : ℝ)
    (m M E J : ℕ) (s : State V) (w : V) : Entry M E J → Option ℝ
  | .inl j => some ((j.val+1)*kappa*Population.radius D hD P m w)
  | .inr (.inl e) => (nearestLeaf s w).map (fun r => r/(1+kappa)^e.val)
  | .inr (.inr j) => some ((j.val+1)*kappa*Population.radius D hD P m w)

noncomputable def update (D F S : Finset V) (hD : D.Nonempty) (Δ P kappa : ℝ)
    (m M E J : ℕ) (s : Option (State V)) (a : Action D M E J) : Option (State V) :=
  match s with
  | none => none
  | some s => if 0 < totalWeight D S Δ s then
      match a with
      | .inl _ => none
      | .inr (.inl w) =>
        match ofLex (chosen S Δ s w) with
        | .inl v => retain m (s.remove v)
        | .inr _ => none
      | .inr (.inr (w,e)) =>
        match menuRadius D hD P kappa m M E J s w e with
        | none => none
        | some R => if (F.filter (fun v => dist w.val v ≤ R)).Nonempty then
            retain m (s.add w R) else none
    else none

end MetricKMedianRecovery.Sampling

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
-- module Solutions.Q238_KM.KMedianRecovery_Sampling_SamplingReference
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinarySamplingReference
open WordOperations WordList BinaryArithmetic
open BinaryOpeningPayment (field field_encode)
open BinaryRationalSort (entryBits)
attribute [local irreducible] WordList.mapWith
variable {n l : ℕ}
def pack (Δ : ℚ) (A : Finset (Fin n)) (v : Fin l→Fin n) (r : Fin l→ℚ) (row : Fin n→ℚ) : List Bool :=
  encode [n.bits,BinaryRational.encode Δ,BinaryFinSet.encode A,
    encode (List.ofFn (fun j=>leafBits (v j) (r j))),RationalMatrix.rowEncode row]
end MetricKMedianRecovery.BitMachine.BinarySamplingReference

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Sampling_SamplingStateMachine
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinarySamplingState
open WordOperations WordList BinaryArithmetic RationalSampling
open BinaryOpeningPayment (field field_encode)
variable {n : ℕ}
def optionBits (s : Option (RationalSampling.State n)) : List Bool := WordList.encode (s.toList.map encode)
end MetricKMedianRecovery.BitMachine.BinarySamplingState

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Sampling_SamplerContext
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinarySampler
open WordOperations WordList BinaryArithmetic
open BinaryOpeningPayment (field field_encode)
variable {n : ℕ}
def config (δ : Fin n→Fin n→ℚ) (D F S : Finset (Fin n)) (Δ P κ : ℚ) (m M E J : ℕ) : List Bool :=
  encode [n.bits,RationalMatrix.encode δ,BinaryFinSet.encode D,BinaryFinSet.encode F,BinaryFinSet.encode S,
    BinaryRational.encode Δ,BinaryRational.encode P,BinaryRational.encode κ,m.bits,BinaryMenu.weights M E J]
end MetricKMedianRecovery.BitMachine.BinarySampler

namespace MetricKMedianRecovery.Dyadic.Canonical
open FiniteSampling
variable {A : Type*}
variable [Fintype A] [DecidableEq A]
lemma draw_average (p : A→ℝ) (hp : ∀ a,0≤p a) (ht : ∑ a,p a=1)
    (b : ℕ) (d : A) (as : List A) (ha : as.Perm (Finset.univ.toList)) (f : A→ℝ) :
    average (fun bits=>f (draw p b d as bits))=∑ a,weight p b d a*f a := by
  classical
  rw [average,Fintype.expect_eq_sum_div_card]
  have he := Fintype.sum_equiv (Categorical.uniformBits b)
    (fun bits=>f (draw p b d as bits)) (fun v=>f (select d (list p b as) v.val)) (fun _=>rfl)
  rw [he,Fintype.card_fun,Fintype.card_bool,Fintype.card_fin,Nat.cast_pow,Nat.cast_ofNat]
  rw [←Finset.sum_range (fun v=>f (select d (list p b as) v))]
  have hle : ((list p b as).map Prod.snd).sum≤2^b := by
    rw [list_sum _ _ _ ha]; exact rawCount_sum_le p hp ht b
  rw [select_sum d (list p b as) (2^b) hle f,list_sum _ _ _ ha]
  have hs : ((list p b as).map (fun aw=>(aw.2:ℝ)*f aw.1)).sum=∑ a,(rawCount p b a:ℝ)*f a := by
    simp only [list,List.map_map,Function.comp_def]
    rw [(ha.map (fun a=>(rawCount p b a:ℝ)*f a)).sum_eq]
    exact Finset.sum_map_toList _ _
  rw [hs]
  simp only [weight,count,Nat.cast_add,add_div,add_mul,Finset.sum_add_distrib]
  rw [Finset.sum_div]
  congr 1
  · apply Finset.sum_congr rfl
    intro a _
    ring
  · simp only [Nat.cast_ite,Nat.cast_zero,ite_div,zero_div,ite_mul,zero_mul,Finset.sum_ite_eq',Finset.mem_univ,ite_true, if_true]
    rw [Nat.cast_sub (rawCount_sum_le p hp ht b),Nat.cast_pow,Nat.cast_ofNat]
    ring
end MetricKMedianRecovery.Dyadic.Canonical

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Recovery_Cluster
attribute [-instance] _root_.OAI.MetricKMedianRecovery.Categorical.binaryOracleIndexDecidableEq
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.Sampling
variable {V : Type*} [LinearOrder V] [PseudoMetricSpace V]

namespace Comparison
variable {D S O : Finset V}
noncomputable def nearTotal (C : Comparison D S O) (Δ : ℝ) (s : State V) : ℝ :=
  ∑ o ∈ C.bad \ C.covered s, ∑ p ∈ C.near o, reference S Δ s p
noncomputable def removalTotal (C : Comparison D S O) (Δ : ℝ) (s : State V) : ℝ :=
  ∑ p ∈ D.filter (fun p => ∃ o ∈ C.nonproxy \ s.deleted, chosen S Δ s p = realTag o),
    reference S Δ s p

def Correct (C : Comparison D S O) (hD : D.Nonempty) (kappa : ℝ) (s : State V) : Prop :=
  s.deleted ⊆ C.nonproxy ∧
  (s.leaves.map (fun z => C.assign z.1)).Nodup ∧
  ∀ z ∈ s.leaves,
    z.1 ∈ D ∧ C.assign z.1 ∈ C.bad ∧
    dist z.1 (C.assign z.1) ≤ (6/5 : ℝ)*clusterMean D C.assign (C.assign z.1) ∧
    0 < z.2 ∧ dist z.1 (C.assign z.1) ≤ z.2 ∧
    z.2 ≤ (1+kappa)*dist z.1 (C.assign z.1) +
      kappa*Population.radius D hD (comparisonCost D C.assign) C.bad.card z.1

lemma correct_radii_nonneg (C : Comparison D S O) (hD : D.Nonempty)
    (kappa : ℝ) (s : State V) (hs : C.Correct hD kappa s) : ∀ z ∈ s.leaves, 0 ≤ z.2 := by
  intro z hz
  exact (hs.2.2 z hz).2.2.2.1.le

lemma correct_leaf_dominates (C : Comparison D S O) (hD : D.Nonempty)
    (kappa : ℝ) (s : State V) (hs : C.Correct hD kappa s)
    (w : V) (hw : w ∈ D) (z : V × ℝ) (hz : z ∈ s.leaves) :
    dist w (C.assign w) ≤ dist w z.1+z.2 := by
  have hh := C.comparison_triangle w z.1 hw (hs.2.2 z hz).1
  have hr := (hs.2.2 z hz).2.2.2.2.1
  linarith

lemma correct_nearestLeaf_lower (C : Comparison D S O) (hD : D.Nonempty)
    (kappa : ℝ) (s : State V) (hs : C.Correct hD kappa s)
    (w : V) (hw : w ∈ D) (r : ℝ) (hr : nearestLeaf s w = some r) :
    dist w (C.assign w) ≤ r :=
  nearestLeaf_lower s w r _ hr (fun z hz => C.correct_leaf_dominates hD kappa s hs w hw z hz)

end Comparison
end MetricKMedianRecovery.Sampling

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Recovery_SingleRadiusRatio
attribute [-instance] _root_.OAI.MetricKMedianRecovery.Categorical.binaryOracleIndexDecidableEq
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.Sampling
variable {V : Type*} [LinearOrder V] [PseudoMetricSpace V]
namespace Comparison
variable {D S O : Finset V}

lemma single_radius_ratio (C : Comparison D S O) (hD : D.Nonempty)
    (hP : 0 < comparisonCost D C.assign) (hm : 0 < C.bad.card)
    (w : V) (hw : w ∈ D)
    (hr : 10*Population.radius D hD (comparisonCost D C.assign) C.bad.card w < dist w (C.assign w)) :
    dist w (C.assign w)/Population.radius D hD (comparisonCost D C.assign) C.bad.card w ≤
      (10/9 : ℝ)*C.bad.card := by
  let q := Population.radius D hD (comparisonCost D C.assign) C.bad.card w
  have hq : 0 < q := Population.radius_pos D hD _ _ w hP hm
  have hcharge : ∀ p ∈ Population.ball D w q, (9/10 : ℝ)*dist w (C.assign w) ≤ dist p (C.assign p) := by
    intro p hp
    have hp' := Finset.mem_filter.mp hp
    have hh := C.comparison_triangle w p hw hp'.1
    linarith [hp'.2]
  have hh := Population.disjoint_population_budget D ({()} : Finset Unit)
    (fun _ => Population.ball D w q) (fun _ => q) (fun _ => dist w (C.assign w))
    (fun p => dist p (C.assign p)) (comparisonCost D C.assign) C.bad.card hP hm
    (fun _ _ => dist_nonneg) rfl (fun _ _ => Finset.filter_subset _ _) (by simp)
    (fun _ _ => hq) (fun _ _ => dist_nonneg)
    (fun _ _ => Population.radius_feasible D hD _ _ w hP hm) (fun _ _ => hcharge)
  simpa only [Finset.sum_singleton] using hh

end Comparison
end MetricKMedianRecovery.Sampling

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Recovery_Destinations
attribute [-instance] _root_.OAI.MetricKMedianRecovery.Categorical.binaryOracleIndexDecidableEq _root_.OAI.MetricKMedianRecovery.Categorical.binaryOracleIndexFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.Sampling.Comparison
open Completion
variable {V : Type*} [LinearOrder V] [PseudoMetricSpace V] {D S O : Finset V}

noncomputable def destinations (C : Comparison D S O) (s : State V) :
    Finset (Destination V s.leaves.length) :=
  C.good.image (fun o => Destination.proxy (C.proxy o)) ∪
    Finset.univ.image Destination.covered ∪
    (C.bad \ C.covered s).image Destination.uncovered

lemma ownDestination_mem (C : Comparison D S O) (s : State V) (p : V) (hp : p ∈ D) :
    C.ownDestination s p ∈ C.destinations s := by
  classical
  unfold ownDestination destinations
  split_ifs with hg hc
  · exact Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_image.mpr ⟨_, hg, rfl⟩))
  · exact Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_image.mpr
      ⟨_, Finset.mem_univ _, rfl⟩))
  · exact Finset.mem_union_right _ (Finset.mem_image.mpr
      ⟨_, Finset.mem_sdiff.mpr ⟨Finset.mem_sdiff.mpr ⟨C.assigned p hp, hg⟩, hc⟩, rfl⟩)

lemma destinations_nonempty (C : Comparison D S O) (hD : D.Nonempty) (s : State V) :
    (C.destinations s).Nonempty := by
  obtain ⟨p, hp⟩ := hD
  exact ⟨_, C.ownDestination_mem s p hp⟩

end MetricKMedianRecovery.Sampling.Comparison

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Recovery_DestinationFacility
attribute [-instance] _root_.OAI.MetricKMedianRecovery.Categorical.binaryOracleIndexDecidableEq
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.Sampling.Comparison
open Completion
variable {V : Type*} [LinearOrder V] [PseudoMetricSpace V] {D S O : Finset V}

@[simp] lemma destinations_proxy (C : Comparison D S O) (s : State V) (v : V) :
    Destination.proxy v ∈ C.destinations s ↔ v ∈ C.good.image C.proxy := by
  simp [destinations]

@[simp] lemma destinations_uncovered (C : Comparison D S O) (s : State V) (v : V) :
    Destination.uncovered v ∈ C.destinations s ↔ v ∈ C.bad \ C.covered s := by
  simp [destinations]

end MetricKMedianRecovery.Sampling.Comparison

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Branching_SuccessfulFavorableProbability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.Sampling
open Completion Categorical FiniteSampling Comparison
variable {V : Type*} [LinearOrder V] [PseudoMetricSpace V]

noncomputable def branchScore (D S : Finset V) (Δ : ℝ) (s : State V) (u v : V) : ℝ :=
  assignmentWeight D (completionAssignment S Δ s) u * dist u v

end MetricKMedianRecovery.Sampling

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Recovery_NearEligible
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

lemma correct_entry_exists (C : Comparison D S O) (hD : D.Nonempty)
    (kappa : ℝ) (hk : 0 < kappa) (s : State V) (hs : C.Correct hD kappa s)
    (hP : 0 < comparisonCost D C.assign) (hm : 0 < C.bad.card)
    (w : V) (hw : w ∈ D) :
    ∃ e : Entry (firstSize kappa) (geometricCap kappa hk) (thirdSize kappa C.bad.card),
    ∃ R : ℝ,
      menuRadius D hD (comparisonCost D C.assign) kappa C.bad.card
        (firstSize kappa) (geometricCap kappa hk) (thirdSize kappa C.bad.card) s w e = some R ∧
      0 < R ∧ dist w (C.assign w) ≤ R ∧
      R ≤ (1+kappa)*dist w (C.assign w)+
        kappa*Population.radius D hD (comparisonCost D C.assign) C.bad.card w ∧
      (∀ j, e = .inr (.inr j) →
        10*Population.radius D hD (comparisonCost D C.assign) C.bad.card w < dist w (C.assign w) ∧
        (∀ z ∈ s.leaves, 10*dist w (C.assign w) < dist w z.1+z.2) ∧
        j.val+1 = Nat.ceil (dist w (C.assign w)/
          (kappa*Population.radius D hD (comparisonCost D C.assign) C.bad.card w))) := by
  let q := Population.radius D hD (comparisonCost D C.assign) C.bad.card w
  let r := dist w (C.assign w)
  have hq : 0 < q := Population.radius_pos D hD _ _ w hP hm
  by_cases hsmall : r ≤ 10*q
  · have ha := first_menu_available kappa q r hk hq dist_nonneg hsmall
    let j : Fin (firstSize kappa) := ⟨upwardIndex kappa q r-1, by omega⟩
    have hj : j.val+1 = upwardIndex kappa q r := by dsimp [j]; omega
    refine ⟨.inl j, additiveRadius kappa q (upwardIndex kappa q r), ?_,
      additiveRadius_pos kappa q _ hk hq (by omega), ha.2.2.1, ha.2.2.2, ?_⟩
    · simp only [menuRadius, additiveRadius, ← Nat.cast_add_one, hj, q]
    · intro j' he
      contradiction
  · have hr : 0 < r := lt_trans (mul_pos (by norm_num) hq) (lt_of_not_ge hsmall)
    by_cases hleaf : ∃ d, nearestLeaf s w = some d ∧ d ≤ 10*r
    · obtain ⟨d,hd,hdub⟩ := hleaf
      obtain ⟨e,he,hlo,hhi⟩ := geometric_menu_available kappa d r hk hr
        (C.correct_nearestLeaf_lower hD kappa s hs w hw d hd) hdub
      refine ⟨.inr (.inl ⟨e,by omega⟩),d/(1+kappa)^e,?_,hr.trans_le hlo,hlo,?_,?_⟩
      · simp only [menuRadius, hd, Option.map_some]
      · have h0 : 0 ≤ kappa*q := mul_nonneg hk.le hq.le
        linarith
      · intro j heq
        cases Sum.inr.inj heq
    · have hb := C.single_radius_ratio hD hP hm w hw (lt_of_not_ge hsmall)
      have ha := third_menu_available kappa q r C.bad.card hk hq hr hb
      let j : Fin (thirdSize kappa C.bad.card) := ⟨Nat.ceil (r/(kappa*q))-1,by omega⟩
      have hj : j.val+1 = Nat.ceil (r/(kappa*q)) := by dsimp [j]; omega
      refine ⟨.inr (.inr j),additiveRadius kappa q (Nat.ceil (r/(kappa*q))),?_,
        additiveRadius_pos kappa q _ hk hq (by omega),ha.2.2.1,ha.2.2.2,?_⟩
      · simp only [menuRadius, additiveRadius, ← Nat.cast_add_one, hj, q, r]
      · intro j' heq
        have he : j = j' := Sum.inr.inj (Sum.inr.inj heq)
        subst j'
        refine ⟨lt_of_not_ge hsmall,?_,hj⟩
        intro z hz
        obtain ⟨d,hd,hle⟩ := nearestLeaf_of_mem s w z hz
        have hdgt : 10*r < d := lt_of_not_ge (fun h => hleaf ⟨d,hd,h⟩)
        exact hdgt.trans_le hle

noncomputable def nearEligible (C : Comparison D S O) (s : State V) : Finset V :=
  D.filter (fun p => C.assign p ∈ C.bad \ C.covered s ∧
    dist p (C.assign p) ≤ (6/5 : ℝ)*clusterMean D C.assign (C.assign p))

noncomputable def removalEligible (C : Comparison D S O) (Δ : ℝ) (s : State V) : Finset V :=
  D.filter (fun p => ∃ o ∈ C.nonproxy \ s.deleted, chosen S Δ s p = realTag o)

lemma nearTotal_eq (C : Comparison D S O) (Δ : ℝ) (s : State V) :
    C.nearTotal Δ s = ∑ p ∈ C.nearEligible s, reference S Δ s p := by
  classical
  simp only [nearTotal, near, cluster, Finset.filter_filter, nearEligible, Finset.sum_filter]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro p hp
  have he : ∀ o, (if C.assign p = o ∧ dist p o ≤ (6/5 : ℝ)*clusterMean D C.assign o
      then reference S Δ s p else 0) =
      (if o = C.assign p then
        (if dist p (C.assign p) ≤ (6/5 : ℝ)*clusterMean D C.assign (C.assign p)
        then reference S Δ s p else 0) else 0) := by
    intro o
    by_cases h : o = C.assign p
    · subst o
      simp
    · simp [h, Ne.symm h]
  simp_rw [he]
  simp only [Finset.sum_ite_eq']
  split_ifs <;> simp_all

def Terminal (C : Comparison D S O) (kappa Δ : ℝ) (s : State V) : Prop :=
  C.nearTotal Δ s ≤ kappa*comparisonCost D C.assign ∧
    C.removalTotal Δ s ≤ kappa*comparisonCost D C.assign

noncomputable def counter (C : Comparison D S O) (s : State V) : ℕ :=
  2*C.bad.card-(s.leaves.length+s.deleted.card)

open scoped Classical

noncomputable def conditionalClients (D S : Finset V) (Δ : ℝ) (s : State V)
    (E : Finset V) (hE : E ⊆ D) (T : ℝ) (hT : 0 < T)
    (he : ∑ p ∈ E, clientWeight S Δ s p = T) : Guided.Kernel Unit D := by
  classical
  refine ⟨fun _ w => if w.val ∈ E then clientWeight S Δ s w/T else 0, ?_, ?_⟩
  · intro u w
    split_ifs
    · exact div_nonneg (clientWeight_nonneg S Δ s w) hT.le
    · exact le_rfl
  · intro u
    have hh : (∑ w : D, if w.val ∈ E then clientWeight S Δ s w/T else 0) =
        (∑ w : D, if w.val ∈ E then clientWeight S Δ s w else 0)/T := by
      rw [Finset.sum_div]
      apply Finset.sum_congr rfl
      intro w _
      split_ifs <;> simp
    rw [hh,Finset.sum_coe_sort D (fun p => if p ∈ E then clientWeight S Δ s p else 0),
      ← Finset.sum_filter,Finset.filter_mem_eq_of_subset hE,he]
    exact div_self (ne_of_gt hT)

noncomputable def prescribedEntry (C : Comparison D S O) (hD : D.Nonempty)
    (hP : 0 < comparisonCost D C.assign) (hm : 0 < C.bad.card)
    (s : State V) (w : D) : MainEntry C.bad.card :=
  if hs : C.Correct hD mainKappa s then
    (C.correct_entry_exists hD mainKappa mainKappa_pos s hs hP hm w w.property).choose
  else .inl ⟨0,by unfold firstSize; omega⟩

lemma eligible_near_weight (C : Comparison D S O) (hD : D.Nonempty) (Δ : ℝ) (hΔ : 0 ≤ Δ)
    (s : State V) (hs : C.Correct hD mainKappa s) :
    (∑ p ∈ C.nearEligible s, clientWeight S Δ s p) = C.nearTotal Δ s := by
  rw [C.nearTotal_eq]
  exact Finset.sum_congr rfl (fun p _ => clientWeight_eq S Δ s p hΔ
    (C.correct_radii_nonneg hD mainKappa s hs))

lemma eligible_removal_weight (C : Comparison D S O) (hD : D.Nonempty) (Δ : ℝ) (hΔ : 0 ≤ Δ)
    (s : State V) (hs : C.Correct hD mainKappa s) :
    (∑ p ∈ C.removalEligible Δ s, clientWeight S Δ s p) = C.removalTotal Δ s :=
  Finset.sum_congr rfl (fun p _ => clientWeight_eq S Δ s p hΔ
    (C.correct_radii_nonneg hD mainKappa s hs))

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

noncomputable abbrev mainActual (D S : Finset V) (Δ : ℝ) (m : ℕ) :=
  actualKernel D S Δ (firstSize mainKappa) (geometricCap mainKappa mainKappa_pos)
    (thirdSize mainKappa m) (by unfold firstSize; omega) (by unfold thirdSize; omega)

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

def Valid (C : Comparison D S O) (hD : D.Nonempty) : Option (State V) → Prop
  | none => False
  | some s => C.Correct hD mainKappa s

noncomputable def remaining (C : Comparison D S O) : Option (State V) → ℕ
  | none => 0
  | some s => C.counter s

end Comparison
end MetricKMedianRecovery.Sampling

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Sampling_RealizedKernel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.Guided.Realized
open FiniteSampling
variable {S A Ω : Type*} [Fintype A] [Fintype Ω]

noncomputable def canonical [DecidableEq A] (p : Kernel S A) (b : ℕ) (d : A)
    (as : List A) (h : as.Perm Finset.univ.toList) : Draw (Ω:=Fin b→Bool) (FixedDyadic.kernel p b d) where
  run s := Dyadic.Canonical.draw (p.weight s) b d as
  law s g := Dyadic.Canonical.draw_average (p.weight s) (p.nonneg s) (p.total s) b d as h g
end MetricKMedianRecovery.Guided.Realized

namespace MetricKMedianRecovery.RationalSampling
open Sampling BitMachine
variable {n : ℕ}
def entryCode (M E J : ℕ) : Entry M E J→List Bool
  | .inl i=>BinaryMenu.code 0 i.val
  | .inr (.inl i)=>BinaryMenu.code 1 i.val
  | .inr (.inr i)=>BinaryMenu.code 2 i.val
def actionCode (D : Finset (Fin n)) (M E J : ℕ) : Action D M E J→List Bool
  | .inl _=>WordList.encode [(0:ℕ).bits,[],[]]
  | .inr (.inl w)=>WordList.encode [(1:ℕ).bits,w.val.val.bits,[]]
  | .inr (.inr (w,e))=>WordList.encode [(2:ℕ).bits,w.val.val.bits,entryCode M E J e]
end MetricKMedianRecovery.RationalSampling

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Algorithms_CandidateSanitize
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinarySanitizedBest
open WordOperations WordList
open BinaryOpeningPayment (field field_encode)
variable {n : ℕ}
def pack (δ : Fin n→Fin n→ℚ) (D F S : Finset (Fin n)) (k : ℕ) (xs : List (List Bool)) : List Bool :=
  encode [RationalMatrix.encode δ,BinaryFinSet.encode D,BinaryFinSet.encode F,BinaryFinSet.encode S,k.bits,encode xs]
end MetricKMedianRecovery.BitMachine.BinarySanitizedBest

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Branching_BlueTable
attribute [-instance] _root_.OAI.MetricKMedianRecovery.Categorical.binaryOracleIndexDecidableEq
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BlueDP
variable {L A : Type*} [LinearOrder L]
def nextTable (C : Finset L→Candidate (List A)) (U : Finset L) (T : Table L A) : Table L A :=
  (states U).map (fun W=>(W,select ((enumBlocks W).map (fun V=>merge (C V) (lookup (W\V) T)))))
def tables (C : Finset L→Candidate (List A)) (U : Finset L) : ℕ→Table L A
  | 0=>initialTable U
  | t+1=>nextTable C U (tables C U t)
def tableStep (C : Finset L→Candidate (List A)) (U : Finset L) (s : Table L A×Candidate (List A)) :
    Table L A×Candidate (List A) :=
  let T:=nextTable C U s.1
  (T,choose s.2 (lookup U T))
def tableRun (C : Finset L→Candidate (List A)) (U : Finset L) (c : ℕ) : Table L A×Candidate (List A) :=
  (tableStep C U)^[c] (initialTable U,none)
def tableBest (C : Finset L→Candidate (List A)) (U : Finset L) (c : ℕ) : Candidate (List A) :=
  if U=∅ then some (0,[]) else (tableRun C U c).2
end MetricKMedianRecovery.BlueDP

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
def pack (δ : Fin n→Fin n→ℚ) (u : ℚ) (cap : ℕ) : List Bool :=
  encode [RationalMatrix.encode δ,List.replicate n true,BinaryRational.encode u,cap.bits]
end MetricKMedianRecovery.BitMachine.BinaryRoundingMatrix

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
-- module Solutions.Q238_KM.KMedianRecovery_Recovery_BlindUpdate
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.Sampling.Comparison
open MetricKMedianRecovery RadiusMenus Guided FixedDyadic FiniteSampling
variable {V : Type*} [LinearOrder V] [PseudoMetricSpace V]

noncomputable local instance instDecidableEqAction_1_r713957_1 (D : Finset V) (M E J : ℕ) : DecidableEq (Action D M E J) := Classical.decEq _
noncomputable abbrev blindUpdate (D F S : Finset V) (hD : D.Nonempty)
    (Δ P : ℝ) (m : ℕ) :=
  update D F S hD Δ P mainKappa m (firstSize mainKappa)
    (geometricCap mainKappa mainKappa_pos) (thirdSize mainKappa m)

end MetricKMedianRecovery.Sampling.Comparison

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Recovery_LeafOutcome
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.PhaseFreshAllocation
open PhaseSequence PhaseMergePath PhaseMergeCompletion PhaseCountCrossing
variable {D X : Type*} [Fintype D] [PseudoMetricSpace X] [DecidableEq X]

@[instance_reducible]
noncomputable def enlargedMetric : PseudoMetricSpace (X ⊕ (X × Bool)) :=
  LeafMetric.attachedMetric Prod.fst (fun _ => 0) (fun _ => le_rfl)

end MetricKMedianRecovery.PhaseFreshAllocation

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Recovery_CanonicalParents
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.CanonicalCoupledMerge
open RationalLeaves CanonicalLengthView
variable {V : Type*} [LinearOrder V] {d : ℕ}
def Rooted (F : Finset V) (B : Finset (Label V)) : Prop := ∀ x∈B,parent x∈F
end MetricKMedianRecovery.CanonicalCoupledMerge

namespace MetricKMedianRecovery.RationalLeaves
open PhaseSequence
variable {V : Type*} [PseudoMetricSpace V] [DecidableEq V]
attribute [local instance] RationalLeaves.metric

def project (Q : Finset (Label V)) : Finset V := Q.image parent
end MetricKMedianRecovery.RationalLeaves

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Recovery_CommonL
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.IntegralAssembly
open LocalSearch Anchoring Completion Sampling Surplus FiniteSampling IntegralCandidates

noncomputable def countBound (L : ℕ) : ℕ :=
  max (2*L) ⌈4*countConstant (1/100)*(L:ℝ)/(gamma/16)⌉₊

end MetricKMedianRecovery.IntegralAssembly

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
-- module Solutions.Q238_KM.KMedianRecovery_Sampling_SamplerDraw
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinarySampler.Draw
open WordOperations WordList BinaryArithmetic
open BinaryOpeningPayment (field field_encode)
variable {n : ℕ}
def pack (cfg : List Bool) (s : Option (RationalSampling.State n)) (b : ℕ) (tape : List Bool) : List Bool :=
  encode [cfg,BinarySamplingState.optionBits s,List.replicate b true,tape]
end MetricKMedianRecovery.BitMachine.BinarySampler.Draw

end OAI
end


