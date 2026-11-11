-- Prove2me | Definitions.Def_OAIQ253P005
-- name    : OAIQ253P005
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-11T05:51:57.335034+00:00
-- url     : https://prove2.me/theorems/f637f34b-ed7c-48a8-b79c-e2c540702c4a
-- title:
--   Definitions bundle OAIQ253P005 of the split of OpenAI, The Partition Principle does not imply Choice
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.PartitionPilot.Forcing.TransitiveGround.exists_model_partitionPrinciple_without_choice`, carved from OpenAI's openai/math development (OpenAI, *The Partition Principle does not imply Choice*, OpenAI Math Release, September 24, 2026, result family 244, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 549 declarations of OpenAI's Lean: 260 definitions, 5 inductive types or structures and 284 theorems. The definitions and types are `OAI.PartitionPilot.Forcing.BoundedFormula.eventSupportGraphFormula`, `OAI.PartitionPilot.Forcing.BoundedFormula.eventSupportSetFormula`, `OAI.PartitionPilot.Forcing.GroundMainFinalGeometry.decodedAction`, `OAI.PartitionPilot.Forcing.GroundMainStage.compressionFilters`, `OAI.PartitionPilot.Forcing.GroundMainStage.compressionInitial`, `OAI.PartitionPilot.Forcing.GroundMainStage.compressionSeparators`, `OAI.PartitionPilot.Forcing.GroundMainStage.compressionSources`, `OAI.PartitionPilot.Forcing.GroundMainStage.compressionTargets`, `OAI.PartitionPilot.Forcing.GroundMainStage.compressionTaskAction`, `OAI.PartitionPilot.Forcing.GroundMainStage.compressionTasks`, `OAI.PartitionPilot.Forcing.GroundMainStage.ofCodes`, `OAI.PartitionPilot.Forcing.GroundMainStage.ofValidity`, `OAI.PartitionPilot.Forcing.GrowthLayerWitnessCode.toLayer`, `OAI.PartitionPilot.Forcing.IdealEmbeddingCode.toIdealEmbedding`, `OAI.PartitionPilot.Forcing.InitialMainAlgebra.action`, `OAI.PartitionPilot.Forcing.InitialMainAlgebra.identity`, `OAI.PartitionPilot.Forcing.InitialMainAlgebra.inverse`, `OAI.PartitionPilot.Forcing.InitialMainAlgebra.meetGraph`, `OAI.PartitionPilot.Forcing.InitialMainAlgebra.multiplication`, `OAI.PartitionPilot.Forcing.InitialMainAlgebra.order`, `OAI.PartitionPilot.Forcing.MainPrefixGraphCode.decodedTransitionIndex`, `OAI.PartitionPilot.Forcing.MainSuccessorOutputCode`, `OAI.PartitionPilot.Forcing.Name.inputEvaluationName`, `OAI.PartitionPilot.Forcing.Name.refinementConditionNames`, `OAI.PartitionPilot.Forcing.Name.refinementPairClassGraph`, `OAI.PartitionPilot.Forcing.Name.renamedFamily`, `OAI.PartitionPilot.Forcing.Name.sharedConditionName`, `OAI.PartitionPilot.Forcing.Name.unionEntryParams`, `OAI.PartitionPilot.Forcing.NiceNameSystem`, `OAI.PartitionPilot.Forcing.NiceRefinementIndexSystem`, `OAI.PartitionPilot.Forcing.PosetAction.PrincipalSupported`, `OAI.PartitionPilot.Forcing.PosetAction.principalSupportFamily`, `OAI.PartitionPilot.Forcing.PosetAction.rowCoordinates`, `OAI.PartitionPilot.Forcing.PosetActionCode.presentedAct`, `OAI.PartitionPilot.Forcing.PosetActionCode.toPosetAction`, `OAI.PartitionPilot.Forcing.PosetActionCode.toPresentedPosetAction`, `OAI.PartitionPilot.Forcing.PreparationForcingCode`, `OAI.PartitionPilot.Forcing.RectangleFulfillmentCode`, `OAI.PartitionPilot.Forcing.RecursiveStateData.successorCodeFromEnvironment`, `OAI.PartitionPilot.Forcing.RefinementDataHistory` and 225 more.
--
--   **Sources.** They come from these modules of lean/OAI/SetTheory, in whole or in part: `PartitionPrinciple_Definability_AssignmentQueryFormulas`, `PartitionPrinciple_Definability_BatchGraphSetFormulas`, `PartitionPrinciple_Definability_BoundedAtomicEquality`, `PartitionPrinciple_Definability_CodedLayerRestrictions`, `PartitionPrinciple_Definability_CrossStageMembershipFormulas`, `PartitionPrinciple_Definability_DepthSlotCodes`, `PartitionPrinciple_Definability_EqualityStepSyntax`, `PartitionPrinciple_Definability_FlatLimitConditionFormulas`, `PartitionPrinciple_Definability_ForcingHistoryConditionFormulas`, `PartitionPrinciple_Definability_ForcingHistoryOutputFormulas`, `PartitionPrinciple_Definability_ForcingWitnessFormulas`, `PartitionPrinciple_Definability_GroundAssignmentClassGraphs`, `PartitionPrinciple_Definability_GroundBelowFunctionGraphs`, `PartitionPrinciple_Definability_GroundCompositionFamilyFormulas`, `PartitionPrinciple_Definability_GroundDefinableRelationProducts`, `PartitionPrinciple_Definability_GroundEligibleTaskSetRecognition`, `PartitionPrinciple_Definability_GroundFlatCarrierSequences`, `PartitionPrinciple_Definability_GroundFlatCopyGraphs`, `PartitionPrinciple_Definability_GroundFunctionRangeFamilies`, `PartitionPrinciple_Definability_GroundLiftedCompressionFormulas`, `PartitionPrinciple_Definability_GroundLiftedRowTupleProvenance`, `PartitionPrinciple_Definability_GroundPackedRefinementFormulaData`, `PartitionPrinciple_Definability_GroundPairedCompositionRows`, `PartitionPrinciple_Definability_GroundPartialFunctionSpaces`, `PartitionPrinciple_Definability_GroundPreparationEventSupportGraphs`, `PartitionPrinciple_Definability_GroundPushFilterFamilyFormulas`, `PartitionPrinciple_Definability_GroundRationalCodes`, `PartitionPrinciple_Definability_GroundRecursiveActionFormulas`, `PartitionPrinciple_Definability_GroundRefinementPairClassGraphs`, `PartitionPrinciple_Definability_GroundRegularFormulas`, `PartitionPrinciple_Definability_GroundSelectedSupportTupleFamilies`, `PartitionPrinciple_Definability_GroundSeparatorFamilyFormulas`, `PartitionPrinciple_Definability_GroundStageOneFormulaData`, `PartitionPrinciple_Definability_InitialMainAlgebraCodes`, `PartitionPrinciple_Definability_LeastSlotOwnerCodes`, `PartitionPrinciple_Definability_LinkedMainInvariantCodes`, `PartitionPrinciple_Definability_LinkedMainTransitionRawCodes`, `PartitionPrinciple_Definability_LinkedProfileTransitionRawCodes`, `PartitionPrinciple_Definability_MainPrefixTraceStepFormulas`, `PartitionPrinciple_Definability_MainPrefixValidityFormulas`, `PartitionPrinciple_Definability_NameSupportFormulas`, `PartitionPrinciple_Definability_NatUnionCodes`, `PartitionPrinciple_Definability_NaturalStepFormulas`, `PartitionPrinciple_Definability_NonemptyTupleFields`, `PartitionPrinciple_Definability_ParentSupportCodes`, `PartitionPrinciple_Definability_PreparedCertificateCodes`, `PartitionPrinciple_Definability_PreservedMainPrefixHistoryFormulas`, `PartitionPrinciple_Definability_RecursivePrimitiveFormulas`, `PartitionPrinciple_Definability_RefinementDataHistoryEntryFormulas`, `PartitionPrinciple_Definability_RefinementHistoryOrderOutputFormulas`, `PartitionPrinciple_Definability_SeparationEntryFormulas`, `PartitionPrinciple_Definability_SerializedChronologyFormulas`, `PartitionPrinciple_Definability_SupportedCertificateFamilyFormulas`, `PartitionPrinciple_Definability_TaggedGrowthLayerFormulas`, `PartitionPrinciple_Definability_TaggedSumPresentations`, `PartitionPrinciple_Definability_TaskRepresentativeCodes`, `PartitionPrinciple_Definability_VisibilityProfileFormulas`, `PartitionPrinciple_Forcing_ActionPostcompositionCodes`, `PartitionPrinciple_Forcing_ActiveNameImageSymmetry`, `PartitionPrinciple_Forcing_ConditionQuantifiers`, `PartitionPrinciple_Forcing_EligibleBatchEquivariance`, `PartitionPrinciple_Forcing_FinitePrincipalNameSupports`, `PartitionPrinciple_Forcing_ForcingHistoryTestDecomposition`, `PartitionPrinciple_Forcing_GroundBatchEarlierLayerWitnesses`, `PartitionPrinciple_Forcing_GroundCountableFunctionForcing`, `PartitionPrinciple_Forcing_GroundDefinableRefinementNameGraphs`, `PartitionPrinciple_Forcing_GroundFixedIndexAssignmentSlices`, `PartitionPrinciple_Forcing_GroundFlatSuccessorFullActionGraph`, `PartitionPrinciple_Forcing_GroundForcingHistorySuccessors`, `PartitionPrinciple_Forcing_GroundMainFinalStructuralCommonSupportInduction`, `PartitionPrinciple_Forcing_GroundNiceRefinementIndexActionLaws`, `PartitionPrinciple_Forcing_GroundNiceSupportEvaluation`, `PartitionPrinciple_Forcing_GroundOrdinaryEqualityDecisionFusion`, `PartitionPrinciple_Forcing_GroundOutsideRowNames`, `PartitionPrinciple_Forcing_GroundPairNameFamilies`, `PartitionPrinciple_Forcing_GroundPrincipalSupportZF`, `PartitionPrinciple_Forcing_GroundProductActions`, `PartitionPrinciple_Forcing_GroundRawRefinementStageWitnesses`, `PartitionPrinciple_Forcing_GroundRecursiveActions`, `PartitionPrinciple_Forcing_GroundRefinementAssignmentActionFamilies`, `PartitionPrinciple_Forcing_GroundRefinementValidityForcing`, `PartitionPrinciple_Forcing_GroundRenamedNameFamilyBounds`, `PartitionPrinciple_Forcing_GroundRepresentedDomainConditions`, `PartitionPrinciple_Forcing_GroundRowAssignmentActions`, `PartitionPrinciple_Forcing_GroundSelectedOrbitNameFamilies`, `PartitionPrinciple_Forcing_GroundSharedConditionalNames`, `PartitionPrinciple_Forcing_GroundSizeWitnesses`, `PartitionPrinciple_Forcing_GroundSmallFunctionPermutations`, `PartitionPrinciple_Forcing_GroundStageOneRawNames`, `PartitionPrinciple_Forcing_GroundSymmetricPowerSet`, `PartitionPrinciple_Forcing_GroundTestedMeetFilters`, `PartitionPrinciple_Forcing_GroundVaryingFamilyEvaluation`, `PartitionPrinciple_Forcing_IdealInsertionProfileTransport`, `PartitionPrinciple_Forcing_IndexedTupleNames`, `PartitionPrinciple_Forcing_NameRenameSteps`, `PartitionPrinciple_Forcing_PreparedWitnessCertificateGraphs`, `PartitionPrinciple_Forcing_RenamedPairNameFamilies`, `PartitionPrinciple_Forcing_StructuralForcingStageWitnessStep`, `PartitionPrinciple_Forcing_SymmetricGroundForcing`, `PartitionPrinciple_Forcing_UniformGroundSizeWitnesses`, `PartitionPrinciple_Geometry_AssignmentIndexLevels`, `PartitionPrinciple_Geometry_DecodedMeetMaps`, `PartitionPrinciple_Geometry_GroundAssignmentIndexLevels`, `PartitionPrinciple_Geometry_GroundBatchEmbeddingRecognition`, `PartitionPrinciple_Geometry_GroundCertificateProfileImageFamilies`, `PartitionPrinciple_Geometry_GroundCodedBinaryHeights`, `PartitionPrinciple_Geometry_GroundCompressionHeightSteps`, `PartitionPrinciple_Geometry_GroundCompressionStarIncidence`, `PartitionPrinciple_Geometry_GroundContainmentOrders`, `PartitionPrinciple_Geometry_GroundDefinableIndexBounds`, `PartitionPrinciple_Geometry_GroundDefinableSelections`, `PartitionPrinciple_Geometry_GroundEligibleCaps`, `PartitionPrinciple_Geometry_GroundExternalLocalHeightSelection`, `PartitionPrinciple_Geometry_GroundExternalTileSlotSupports`, `PartitionPrinciple_Geometry_GroundFamilyValueUnions`, `PartitionPrinciple_Geometry_GroundFiniteSeedBounds`, `PartitionPrinciple_Geometry_GroundFiniteWordLaws`, `PartitionPrinciple_Geometry_GroundGrowthLayerRecognition`, `PartitionPrinciple_Geometry_GroundHartogs`, `PartitionPrinciple_Geometry_GroundIdentityInsertionTasks`, `PartitionPrinciple_Geometry_GroundIndexedImageCovers`, `PartitionPrinciple_Geometry_GroundIndexedMixedOperationLifts`, `PartitionPrinciple_Geometry_GroundIndexedOperationLifts`, `PartitionPrinciple_Geometry_GroundIndexedValueLifts`, `PartitionPrinciple_Geometry_GroundInitialMainAlgebra`, `PartitionPrinciple_Geometry_GroundLinkedProfileTransitionRecognition`, `PartitionPrinciple_Geometry_GroundLinkedTransitionRetarget`, `PartitionPrinciple_Geometry_GroundMainFinalSeparatedActors`, `PartitionPrinciple_Geometry_GroundMainFinalStructuralCompression`, `PartitionPrinciple_Geometry_GroundMixtureDensityRecovery`, `PartitionPrinciple_Geometry_GroundNaturalFamilyShift`, `PartitionPrinciple_Geometry_GroundNiceAssignmentClassFamilies`, `PartitionPrinciple_Geometry_GroundNiceRefinementVisibility`, `PartitionPrinciple_Geometry_GroundPreparationFamilyImages`, `PartitionPrinciple_Geometry_GroundRawLayerPushforward`, `PartitionPrinciple_Geometry_GroundRawRefinementDataIdentification`, `PartitionPrinciple_Geometry_GroundRefinementAssignmentImages`, `PartitionPrinciple_Geometry_GroundRowAssignmentProjections`, `PartitionPrinciple_Geometry_GroundRowDistinguishing`, `PartitionPrinciple_Geometry_GroundTaskBearingInsertionFulfillment`, `PartitionPrinciple_Geometry_GroundTaskRepresentativeRecognition`, `PartitionPrinciple_Geometry_GroundTemplateIntervalFamilies`, `PartitionPrinciple_Geometry_GroundTileStarIncidence`, `PartitionPrinciple_Geometry_GroundTwoPointHeights`, `PartitionPrinciple_Geometry_InitialCompressionAccounting`, `PartitionPrinciple_Geometry_IntervalEmbeddingFamilyCodes`, `PartitionPrinciple_Geometry_RectangleFulfillmentAtBound`, `PartitionPrinciple_Geometry_RepresentativeIndexSteps`, `PartitionPrinciple_Geometry_TileStarIncomingCodes`, `PartitionPrinciple_Geometry_UniformAtomicEquality`, `PartitionPrinciple_Transfinite_ExternalChronologyStageLaws`, `PartitionPrinciple_Transfinite_GroundChronologyLayerRelation`, `PartitionPrinciple_Transfinite_GroundChronologyPairs`, `PartitionPrinciple_Transfinite_GroundCompressionPrefixGraphs`, `PartitionPrinciple_Transfinite_GroundCountableFunctionClosure`, `PartitionPrinciple_Transfinite_GroundCountableRelationSelections`, `PartitionPrinciple_Transfinite_GroundDefinableRefinementHistories`, `PartitionPrinciple_Transfinite_GroundFlatLimitAdequacy`, `PartitionPrinciple_Transfinite_GroundInitialCompressionHistory`, `PartitionPrinciple_Transfinite_GroundInitialMainStage`, `PartitionPrinciple_Transfinite_GroundInitialPreservedMainPrefix`, `PartitionPrinciple_Transfinite_GroundLinkedMainStageCodeLaws`, `PartitionPrinciple_Transfinite_GroundLinkedMainStageLevels`, `PartitionPrinciple_Transfinite_GroundMainPrefixDecoding`, `PartitionPrinciple_Transfinite_GroundMainPrefixSelectedStepTotality`, `PartitionPrinciple_Transfinite_GroundMainStageCandidates`, `PartitionPrinciple_Transfinite_GroundMainStageFromCodes`, `PartitionPrinciple_Transfinite_GroundNaturalRecursion`, `PartitionPrinciple_Transfinite_GroundOmegaOneTaskBearingSuccessorFunction`, `PartitionPrinciple_Transfinite_GroundOrdinalOrderCodes`, `PartitionPrinciple_Transfinite_GroundSmallFunctionSpaces`, `PartitionPrinciple_Transfinite_GroundStageOneAssignmentUnions`, `PartitionPrinciple_Transfinite_GroundStageOneOrder`, `PartitionPrinciple_Transfinite_GroundStandardInaccessible`, `PartitionPrinciple_Transfinite_GroundStructuralHistoryTestUnions`, `PartitionPrinciple_Transfinite_GroundTaskBearingSuccessorDecoding`, `PartitionPrinciple_Transfinite_MainPrefixHistoryUnionRecognition`, `PartitionPrinciple_Transfinite_MainPrefixSelectedTraceLaws`, `PartitionPrinciple_Transfinite_MainStageTaskCodes`, `PartitionPrinciple_Transfinite_NonzeroLimitOrdinalCodes`, `PartitionPrinciple_Transfinite_OrdinalRecursionTraces`, `PartitionPrinciple_Transfinite_OwnerBirthLayers`, `PartitionPrinciple_Transfinite_RecursiveStateFieldEnvironments`, `PartitionPrinciple_Transfinite_RefinementBirthEnumerationFairness`, `PartitionPrinciple_Transfinite_RefinementHistoryPrefixLevels`, `PartitionPrinciple_Transfinite_StageOneDataBoundLaws`.
--
--   **Imports.** It imports the published bundle `Def_PartitionPrinciple`; the bundles `OAIQ253P002` and `OAIQ253P003` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ253P006`, `OAIQ253P007` and `OAIQ253P008`; the statement `OAI.PartitionPilot.Forcing.TransitiveGround.exists_groundInitialExternalBoundedGeometry`.
-- source:
--   OpenAI, The Partition Principle does not imply Choice, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 244; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/The-Partition-Principle-does-not-imply-Choice-September-24-2026/partition-principle-without-choice.pdf; Apache License 2.0); definitions carved from lean/OAI/SetTheory at commit 7ef5c0c

import Lean.Elab.Tactic.Omega
import Mathlib
import Mathlib.Algebra.Group.Subgroup.Map
import Mathlib.Data.List.Chain
import Mathlib.Data.Prod.Lex
import Mathlib.GroupTheory.CoprodI
import Mathlib.GroupTheory.FreeGroup.Reduce
import Mathlib.Logic.Equiv.Option
import Mathlib.Logic.Relation
import Mathlib.SetTheory.Cardinal.Arithmetic
import Mathlib.SetTheory.Cardinal.Regular
import Mathlib.SetTheory.ZFC.Rank
import Definitions.Def_PartitionPrinciple
import Definitions.Def_OAIQ253P002
import Definitions.Def_OAIQ253P003

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Definability_NatUnionCodes
attribute [-instance] _root_.OAI.PartitionPilot.Forcing.GroundMainPrefix.withTopSmall
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI



namespace PartitionPilot.Forcing

open scoped ZFSet

universe u

theorem graphRestriction_restrict {A B f : ZFSet.{u}} (subset : B ⊆ A) :
    graphRestriction B (graphRestriction A f) = graphRestriction B f := by
  apply ZFSet.ext
  intro z
  constructor
  · intro hz
    obtain ⟨x, hx, y, rfl, entry⟩ := mem_graphRestriction.1 hz
    exact pair_mem_graphRestriction.2 ⟨(pair_mem_graphRestriction.1 entry).1, hx⟩
  · intro hz
    obtain ⟨x, hx, y, rfl, entry⟩ := mem_graphRestriction.1 hz
    exact pair_mem_graphRestriction.2
      ⟨pair_mem_graphRestriction.2 ⟨entry, subset hx⟩, hx⟩

end PartitionPilot.Forcing



end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Transfinite_OrdinalRecursionTraces
attribute [-instance] _root_.OAI.PartitionPilot.Forcing.GroundMainPrefix.withTopSmall
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI



namespace PartitionPilot.Forcing

open scoped ZFSet
universe u

namespace OrdinalRecursionTrace

variable {R : ZFSet.{u} → ZFSet.{u} → ZFSet.{u} → Prop}

theorem restrict {A B f : ZFSet.{u}} (trace : OrdinalRecursionTrace R A f)
    (ordinalB : ordinalSetProperty B) (subset : B ⊆ A) :
    OrdinalRecursionTrace R B (graphRestriction B f) := by
  refine ⟨trace.1.restrict subset, ?_⟩
  intro β hβ y hy
  have earlier : β ⊆ B := fun x hx => ordinalB.1 β hβ x hx
  rw [graphRestriction_restrict earlier]
  exact trace.2 β (subset hβ) y (pair_mem_graphRestriction.1 hy).1

end OrdinalRecursionTrace

end PartitionPilot.Forcing

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Definability_GroundPartialFunctionSpaces
attribute [-instance] _root_.OAI.PartitionPilot.Forcing.GroundMainPrefix.withTopSmall
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI



namespace PartitionPilot.Forcing.TransitiveGround
open SetFormula
universe u
variable (M : TransitiveGround.{u})

noncomputable def definable_groundPower (powers : Realize M.sets powerSet Fin.elim0) :
    GroundDefinableFunction M (fun env : Fin 1 → ZFSet.{u} => M.groundPower (env 0)) where
  formula := exactSetFormula 0 (BoundedFormula.allMem 0 (.mem 0 3)).toFormula
  closed := fun _ members => M.groundPower_mem powers (members 0)
  correct := by
    intro env members z hz
    apply M.realize_exactSetFormula 0 _ (extend z env) hz
      (fun w h => ((M.mem_groundPower (env 0) w).1 h).1)
    intro w hw
    rw [M.mem_groundPower, and_iff_right hw]
    rw [BoundedFormula.realize_toFormula M _ _ (Fin.cases hw (Fin.cases hz members))]
    rfl

end PartitionPilot.Forcing.TransitiveGround



namespace PartitionPilot.Forcing
open SetRealization SetFormula
universe u

namespace TransitiveGround
variable (M : TransitiveGround.{u})

def definable_familySetCode
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets) :
    GroundDefinableFunction M (fun env : Fin 2 → ZFSet.{u} => ZFSet.prod (env 0) {env 1}) where
  formula := familySetCodeFormula
  closed := fun _ members => M.prod_mem pairing unions powers separation (members 0)
    (by simpa only [ZFSet.pair_eq_singleton] using M.unorderedPair_mem pairing (members 1) (members 1))
  correct := by
    intro env members z hz
    have ground := M.prod_mem pairing unions powers separation (members 0)
      (by simpa only [ZFSet.pair_eq_singleton] using M.unorderedPair_mem pairing (members 1) (members 1))
    apply M.realize_exactSetFormula 0 _ (extend z env) hz (fun _ h => M.transitive ground h)
    intro w hw
    exact (BoundedFormula.realize_toFormula M _ _ (Fin.cases hw (Fin.cases hz members))).trans
      (BoundedFormula.truth_familySetEntryFormula 0 2 3 _)

end TransitiveGround
end PartitionPilot.Forcing



namespace PartitionPilot.Forcing.TransitiveGround

open SetFormula
universe u
variable (M : TransitiveGround.{u})

theorem partialFunctions_mem
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    {X Y : ZFSet.{u}} (hX : X ∈ M.sets) (hY : Y ∈ M.sets) : M.partialFunctions X Y ∈ M.sets := by
  have space := M.groundRelations_mem pairing unions powers separation hX hY
  let params := extend X (extend Y Fin.elim0)
  have selected := M.separation_mem separation (BoundedFormula.partialFunctionFormula 1 2 0).toFormula
    params (Fin.cases hX (Fin.cases hY (fun j => Fin.elim0 j))) space
  have correct (p : ZFSet.{u}) (hp : p ∈ M.sets) :
      Realize M.sets (BoundedFormula.partialFunctionFormula 1 2 0).toFormula (extend p params) ↔
        PartialFunctionCode X Y p :=
    (BoundedFormula.realize_toFormula M _ _
      (Fin.cases hp (Fin.cases hX (Fin.cases hY (fun j => Fin.elim0 j))))).trans
        (BoundedFormula.truth_partialFunctionFormula 1 2 0 _)
  have eq : ZFSet.sep (fun p => Realize M.sets
      (BoundedFormula.partialFunctionFormula 1 2 0).toFormula (extend p params)) (M.groundRelations X Y) =
        M.partialFunctions X Y := by
    apply ZFSet.ext
    intro p
    rw [ZFSet.mem_sep, M.mem_partialFunctions]
    constructor
    · rintro ⟨hp, rel⟩
      have ground := M.transitive space hp
      exact ⟨ground, (correct p ground).1 rel⟩
    · rintro ⟨ground, code⟩
      exact ⟨(M.mem_groundRelations X Y p).2 ⟨ground, code.shape⟩, (correct p ground).2 code⟩
  exact eq ▸ selected

end PartitionPilot.Forcing.TransitiveGround

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Forcing_GroundSizeWitnesses
attribute [-instance] _root_.OAI.PartitionPilot.Forcing.GroundMainPrefix.withTopSmall
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PartitionPilot.Forcing

universe u

namespace TransitiveGround

open SetRealization SetFormula
variable (M : TransitiveGround.{u})

theorem realize_hasInjectionFormula {n} (d c : Fin n) (env : Fin n → ZFSet.{u})
    (members : ∀ j, env j ∈ M.sets) :
    Realize M.sets (hasInjectionFormula d c) env ↔ M.groundEmbeddable (env d) (env c) := by
  rw [hasInjectionFormula, realize_ex]
  constructor
  · rintro ⟨f, hf, rel⟩
    exact ⟨f, hf, (BoundedFormula.truth_injectionFormula d.succ c.succ 0 _).1
      ((BoundedFormula.realize_toFormula M _ _ (Fin.cases hf members)).1 rel)⟩
  · rintro ⟨f, hf, code⟩
    exact ⟨f, hf, (BoundedFormula.realize_toFormula M _ _ (Fin.cases hf members)).2
      ((BoundedFormula.truth_injectionFormula d.succ c.succ 0 _).2 code)⟩

end TransitiveGround

end PartitionPilot.Forcing

end

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Transfinite_GroundSmallFunctionSpaces
attribute [-instance] _root_.OAI.PartitionPilot.Forcing.GroundMainPrefix.withTopSmall
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PartitionPilot.Forcing.TransitiveGround

open SetRealization SetFormula
universe u
variable (M : TransitiveGround.{u})

theorem smallPartialFunctions_mem
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    {X Y N : ZFSet.{u}} (hX : X ∈ M.sets) (hY : Y ∈ M.sets) (hN : N ∈ M.sets) :
    M.smallPartialFunctions X Y N ∈ M.sets := by
  have space := M.partialFunctions_mem pairing unions powers separation hX hY
  let params := extend N Fin.elim0
  have selected := M.separation_mem separation (hasInjectionFormula 0 1)
    params (Fin.cases hN (fun j => Fin.elim0 j)) space
  have eq : ZFSet.sep (fun p => Realize M.sets (hasInjectionFormula 0 1) (extend p params))
      (M.partialFunctions X Y) = M.smallPartialFunctions X Y N := by
    apply ZFSet.ext
    intro p
    rw [ZFSet.mem_sep, smallPartialFunctions, ZFSet.mem_sep]
    constructor
    · rintro ⟨hp, rel⟩
      exact ⟨hp, (M.realize_hasInjectionFormula 0 1 (extend p params)
        (Fin.cases (M.transitive space hp) (Fin.cases hN (fun j => Fin.elim0 j)))).1 rel⟩
    · rintro ⟨hp, small⟩
      exact ⟨hp, (M.realize_hasInjectionFormula 0 1 (extend p params)
        (Fin.cases (M.transitive space hp) (Fin.cases hN (fun j => Fin.elim0 j)))).2 small⟩
  exact eq ▸ selected

end PartitionPilot.Forcing.TransitiveGround

end

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Definability_NonemptyTupleFields
attribute [-instance] _root_.OAI.PartitionPilot.Forcing.GroundMainPrefix.withTopSmall
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI



namespace PartitionPilot.Forcing
universe u

theorem refinementIndexCode_eq_iff (level C E U Rf Rc level' C' E' U' Rf' Rc' : ZFSet.{u}) :
    refinementIndexCode level C E U Rf Rc = refinementIndexCode level' C' E' U' Rf' Rc' ↔
      level = level' ∧ C = C' ∧ E = E' ∧ U = U' ∧ Rf = Rf' ∧ Rc = Rc' := by
  simp only [refinementIndexCode, nonemptyTupleCode, Matrix.cons_val_zero,
    Matrix.cons_val_succ, ZFSet.pair_inj]

theorem mem_refinementIndexBound (L P V W z : ZFSet.{u}) :
    z ∈ refinementIndexBound L P V W ↔
      ∃ level ∈ L, ∃ C ∈ P, ∃ E ∈ P, ∃ U ∈ V, ∃ Rf ∈ W, ∃ Rc ∈ W,
        z = refinementIndexCode level C E U Rf Rc := by
  simp only [refinementIndexBound, ZFSet.mem_prod]
  constructor
  · rintro ⟨level, hlevel, rest, ⟨C, hC, rest', ⟨E, hE, rest'', ⟨U, hU,
      rest''', ⟨Rf, hRf, Rc, hRc, rfl⟩, rfl⟩, rfl⟩, rfl⟩, rfl⟩
    exact ⟨level, hlevel, C, hC, E, hE, U, hU, Rf, hRf, Rc, hRc, rfl⟩
  · rintro ⟨level, hlevel, C, hC, E, hE, U, hU, Rf, hRf, Rc, hRc, rfl⟩
    exact ⟨level, hlevel, _, ⟨C, hC, _, ⟨E, hE, _, ⟨U, hU, _,
      ⟨Rf, hRf, Rc, hRc, rfl⟩, rfl⟩, rfl⟩, rfl⟩, rfl⟩

theorem refinementIndexCode_mem_bound (L P V W level C E U Rf Rc : ZFSet.{u}) :
    refinementIndexCode level C E U Rf Rc ∈ refinementIndexBound L P V W ↔
      level ∈ L ∧ C ∈ P ∧ E ∈ P ∧ U ∈ V ∧ Rf ∈ W ∧ Rc ∈ W := by
  rw [mem_refinementIndexBound]
  constructor
  · rintro ⟨l, hl, c, hc, e, he, a, ha, r, hr, t, ht, equal⟩
    obtain ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩ := (refinementIndexCode_eq_iff _ _ _ _ _ _ _ _ _ _ _ _).1 equal
    exact ⟨hl, hc, he, ha, hr, ht⟩
  · rintro ⟨hl, hc, he, hu, hf, hr⟩
    exact ⟨level, hl, C, hc, E, he, U, hu, Rf, hf, Rc, hr, rfl⟩

end PartitionPilot.Forcing



namespace PartitionPilot.Forcing.TransitiveGround
open SetFormula
universe u
variable (M : TransitiveGround.{u})

theorem refinementIndexCode_fields_mem {level C E U Rf Rc : ZFSet.{u}}
    (ground : refinementIndexCode level C E U Rf Rc ∈ M.sets) :
    level ∈ M.sets ∧ C ∈ M.sets ∧ E ∈ M.sets ∧ U ∈ M.sets ∧
      Rf ∈ M.sets ∧ Rc ∈ M.sets := by
  have fields := M.nonemptyTupleCode_field_mem 5 ![level, C, E, U, Rf, Rc] ground
  exact ⟨fields 0, fields 1, fields 2, fields 3, fields 4, fields 5⟩

end PartitionPilot.Forcing.TransitiveGround



namespace PartitionPilot.Forcing
open SetFormula
universe u

namespace TransitiveGround
variable (M : TransitiveGround.{u})

theorem realize_refinementIndexFieldFormula {n} (z I : Fin n) (j : Fin 6)
    (env : Fin n → ZFSet.{u}) (members : ∀ k, env k ∈ M.sets) :
    Realize M.sets (refinementIndexFieldFormula z I j) env ↔
      ∃ fields : Fin 6 → ZFSet.{u}, nonemptyTupleCode 5 fields ∈ env I ∧
        env z = ZFSet.pair (nonemptyTupleCode 5 fields) (fields j) := by
  rw [refinementIndexFieldFormula, realize_exBlock]
  have actual (w : Fin 7 → ZFSet.{u}) (ground : ∀ k, w k ∈ M.sets) :
      Realize M.sets (.conj (.mem (prefixIndex n 7 0) (suffixIndex n 7 I))
        (.conj (BoundedFormula.nonemptyTupleFormula 5 (prefixIndex n 7 0)
          (fun k => prefixIndex n 7 k.succ)).toFormula
          (BoundedFormula.orderedPairFormula (suffixIndex n 7 z) (prefixIndex n 7 0)
            (prefixIndex n 7 j.succ)).toFormula)) (extendMany 7 w env) ↔
      w 0 ∈ env I ∧ w 0 = nonemptyTupleCode 5 (fun k => w k.succ) ∧
        env z = ZFSet.pair (w 0) (w j.succ) := by
    simp only [Realize, BoundedFormula.realize_toFormula M _ _
      (extendMany_members 7 w env ground members), BoundedFormula.truth_nonemptyTupleFormula,
      BoundedFormula.truth_orderedPairFormula, extendMany_prefix, extendMany_suffix]
  constructor
  · rintro ⟨w, ground, holds⟩
    obtain ⟨hi, eq, pair⟩ := (actual w ground).1 holds
    exact ⟨fun k => w k.succ, eq ▸ hi, eq ▸ pair⟩
  · rintro ⟨fields, hi, pair⟩
    have hcode := M.transitive (members I) hi
    have hf := M.nonemptyTupleCode_field_mem 5 fields hcode
    let w := extend (nonemptyTupleCode 5 fields) fields
    have ground : ∀ k, w k ∈ M.sets := Fin.cases hcode hf
    exact ⟨w, ground, (actual w ground).2 ⟨hi, rfl, pair⟩⟩

theorem refinementIndexFieldGraph_mem
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    {I B : ZFSet.{u}} (hI : I ∈ M.sets) (hB : B ∈ M.sets) (j : Fin 6) :
    refinementIndexFieldGraph I B j ∈ M.sets := by
  have hp := M.prod_mem pairing unions powers separation hI hB
  let params := extend I Fin.elim0
  have ground := M.separation_mem separation (refinementIndexFieldFormula 0 1 j)
    params (Fin.cases hI (fun k => Fin.elim0 k)) hp
  have equal : ZFSet.sep (fun z => Realize M.sets (refinementIndexFieldFormula 0 1 j)
      (extend z params)) (ZFSet.prod I B) = refinementIndexFieldGraph I B j := by
    apply ZFSet.ext
    intro z
    rw [ZFSet.mem_sep, refinementIndexFieldGraph, ZFSet.mem_sep]
    apply and_congr_right
    intro hz
    exact M.realize_refinementIndexFieldFormula 0 1 j _
      (Fin.cases (M.transitive hp hz) (Fin.cases hI (fun k => Fin.elim0 k)))
  exact equal ▸ ground

end TransitiveGround

end PartitionPilot.Forcing



end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Definability_GroundFlatCopyGraphs
attribute [-instance] _root_.OAI.PartitionPilot.Forcing.GroundMainPrefix.withTopSmall
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI



namespace PartitionPilot.Forcing
open SetFormula
universe u

namespace TransitiveGround
variable (M : TransitiveGround.{u})
variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
variable (unions : Realize M.sets SetFormula.union Fin.elim0)
variable (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
include pairing unions powers separation

theorem realize_relationCompositionCodeFormula (env : Fin 5 → ZFSet.{u})
    (members : ∀ j, env j ∈ M.sets) (z : ZFSet.{u}) (hz : z ∈ M.sets) :
    Realize M.sets relationCompositionCodeFormula (extend z env) ↔
      z = relationCompose (env 0) (env 1) (env 2) (env 3) (env 4) := by
  apply M.realize_exactSetFormula 0 _ _ hz
    (fun _ member => M.transitive (M.relationCompose_mem pairing unions powers separation
      (members 0) (members 1) (members 2) (members 3) (members 4)) member)
  intro w hw
  rw [BoundedFormula.realize_toFormula M _ _ (Fin.cases hw (Fin.cases hz members)),
    BoundedFormula.truth_composeEntryFormula, mem_relationCompose]
  rfl

noncomputable def definable_relationCompose : GroundDefinableFunction M
    (fun env : Fin 5 → ZFSet.{u} => relationCompose (env 0) (env 1) (env 2) (env 3) (env 4)) where
  formula := relationCompositionCodeFormula
  closed := fun _ members => M.relationCompose_mem pairing unions powers separation
    (members 0) (members 1) (members 2) (members 3) (members 4)
  correct := M.realize_relationCompositionCodeFormula pairing unions powers separation

end TransitiveGround
end PartitionPilot.Forcing



namespace PartitionPilot.Forcing
open SetFormula
open scoped ZFSet
universe u

theorem functionGraphRange_function {A f : ZFSet.{u}} (function : FunctionGraphOn A f) :
    ZFSet.IsFunc A (functionGraphRange A f) f := by
  refine ⟨?_, function.to_isFunc.2⟩
  intro z hz
  obtain ⟨x, hx, y, rfl⟩ := function.shape z hz
  exact ZFSet.pair_mem_prod.2 ⟨hx, (mem_functionGraphRange A f y).2 ⟨x, hx, hz⟩⟩

end PartitionPilot.Forcing



end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Definability_ParentSupportCodes
attribute [-instance] _root_.OAI.PartitionPilot.Forcing.GroundMainPrefix.withTopSmall
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI



namespace PartitionPilot.Forcing
open SetFormula
universe u

namespace TransitiveGround
variable (M : TransitiveGround.{u})

variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
variable (unions : Realize M.sets SetFormula.union Fin.elim0)
variable (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
variable {I B R : ZFSet.{u}} (hI : I ∈ M.sets) (hB : B ∈ M.sets) (hR : R ∈ M.sets)

include pairing unions powers separation hI hB hR in
theorem relationFiberFamily_mem : M.relationFiberFamily I B R ∈ M.sets := by
  have hW := M.groundPower_mem powers hB
  let params := extend I (extend (M.groundPower B) (extend B (extend R Fin.elim0)))
  have selected := M.bounded_separation_mem separation
    (BoundedFormula.relationFiberFamilyEntryFormula 0 1 2 3 4) params
    (Fin.cases hI (Fin.cases hW (Fin.cases hB (Fin.cases hR (fun j => Fin.elim0 j)))))
    (M.prod_mem pairing unions powers separation hI hW)
  have equal : ZFSet.sep (fun z => BoundedFormula.Truth
      (BoundedFormula.relationFiberFamilyEntryFormula 0 1 2 3 4) (extend z params))
      (ZFSet.prod I (M.groundPower B)) = M.relationFiberFamily I B R := by
    apply ZFSet.ext
    intro z
    rw [ZFSet.mem_sep, relationFiberFamily, ZFSet.mem_sep]
    exact and_congr Iff.rfl (BoundedFormula.truth_relationFiberFamilyEntryFormula 0 1 2 3 4 _)
  exact equal ▸ selected

include separation hI hB hR in
theorem relationFiberFamily_function :
    ZFSet.IsFunc I (M.groundPower B) (M.relationFiberFamily I B R) := by
  refine ⟨fun _ hz => (ZFSet.mem_sep.1 hz).1, ?_⟩
  intro i hi
  have bound := (M.mem_groundPower B (relationFiber B R i)).2
    ⟨M.relationFiber_mem separation hB hR (M.transitive hI hi),
      fun _ hz => (mem_relationFiber _ _ _ _).1 hz |>.1⟩
  exact ⟨relationFiber B R i,
    (M.pair_mem_relationFiberFamily I B R i _).2 ⟨hi, bound, rfl⟩,
    fun f entry => ((M.pair_mem_relationFiberFamily I B R i f).1 entry).2.2⟩

include separation hI hB hR in
theorem relationFiberFamily_entries (i f : ZFSet.{u}) :
    ZFSet.pair i f ∈ M.relationFiberFamily I B R ↔ i ∈ I ∧ f = relationFiber B R i := by
  constructor
  · intro entry
    have parts := (M.pair_mem_relationFiberFamily I B R i f).1 entry
    exact ⟨parts.1, parts.2.2⟩
  · rintro ⟨hi, rfl⟩
    obtain ⟨f, entry, _⟩ := (M.relationFiberFamily_function separation hI hB hR).2 i hi
    have equal := ((M.pair_mem_relationFiberFamily I B R i f).1 entry).2.2
    exact equal ▸ entry

end TransitiveGround





namespace TransitiveGround
variable (M : TransitiveGround.{u})
theorem externalStarSupportGraph_mem
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    {V Q E U C Requests classifier copies localPoints action zero first : ZFSet.{u}}
    (hV : V ∈ M.sets) (hQ : Q ∈ M.sets) (hE : E ∈ M.sets) (hU : U ∈ M.sets)
    (hC : C ∈ M.sets) (hRequests : Requests ∈ M.sets) (hClassifier : classifier ∈ M.sets)
    (hCopies : copies ∈ M.sets) (hLocal : localPoints ∈ M.sets) (hAction : action ∈ M.sets)
    (hZero : zero ∈ M.sets) (hFirst : first ∈ M.sets) :
    externalStarSupportGraph V Q E U C Requests classifier copies localPoints action zero first ∈ M.sets := by
  let params := extend V (extend Q (extend E (extend U (extend C (extend Requests (extend classifier (extend copies (extend localPoints (extend action (extend zero (extend first (Fin.elim0))))))))))))
  have members : ∀ i, params i ∈ M.sets := Fin.cases hV (Fin.cases hQ (Fin.cases hE (Fin.cases hU (Fin.cases hC (Fin.cases hRequests (Fin.cases hClassifier (Fin.cases hCopies (Fin.cases hLocal (Fin.cases hAction (Fin.cases hZero (Fin.cases hFirst ((fun i => Fin.elim0 i)))))))))))))
  have selected := M.bounded_separation_mem separation
    (BoundedFormula.externalStarSupportEntryFormula 0 1 2 3 4 5 6 7 8 9 10 11 12) params members
    (M.prod_mem pairing unions powers separation hV hQ)
  have equal : ZFSet.sep (fun z => BoundedFormula.Truth
      (BoundedFormula.externalStarSupportEntryFormula 0 1 2 3 4 5 6 7 8 9 10 11 12) (extend z params))
      (ZFSet.prod V Q) = externalStarSupportGraph V Q E U C Requests classifier copies localPoints action zero first := by
    apply ZFSet.ext
    intro z
    rw [ZFSet.mem_sep, BoundedFormula.truth_externalStarSupportEntryFormula]
    change (z ∈ ZFSet.prod V Q ∧ z ∈ externalStarSupportGraph V Q E U C Requests classifier copies localPoints action zero first) ↔ _
    exact ⟨And.right, fun hz => ⟨(ZFSet.mem_sep.1 hz).1, hz⟩⟩
  exact equal ▸ selected

end TransitiveGround





end PartitionPilot.Forcing

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Forcing_ConditionQuantifiers
attribute [-instance] _root_.OAI.PartitionPilot.Forcing.GroundMainPrefix.withTopSmall
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PartitionPilot.Forcing.Name

open SetRealization SetFormula
universe u
variable {P : Type u} [Preorder P] {s : Presentation P}

noncomputable def unionEntryParams (τ : Name s) : Fin 3 → ZFSet.{u} :=
  extend τ.val (extend s.carrier (extend s.conditionOrder Fin.elim0))

end PartitionPilot.Forcing.Name

end


end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Geometry_GroundContainmentOrders
attribute [-instance] _root_.OAI.PartitionPilot.Forcing.GroundMainPrefix.withTopSmall
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PartitionPilot.Forcing.PartialOrderCode

open SetRealization
universe u
variable {Q R : ZFSet.{u}} (h : PartialOrderCode Q R)

theorem conditionOrder_eq :
    letI _decodedOrder := h.toPartialOrder
    (SetMembers.presentation Q).conditionOrder = R := by
  let decodedOrder := h.toPartialOrder
  apply ZFSet.ext
  intro z
  rw [Presentation.conditionOrder, Presentation.mem_subset]
  constructor
  · rintro ⟨⟨x, y⟩, le, eq⟩
    change ZFSet.pair (SetMembers.raw x) (SetMembers.raw y) = z at eq
    exact eq ▸ le
  · intro hz
    obtain ⟨x, hx, y, hy, eq⟩ := ZFSet.mem_prod.1 (h.relation hz)
    refine ⟨(SetMembers.ofMem x hx, SetMembers.ofMem y hy), ?_, ?_⟩
    · change ZFSet.pair (SetMembers.raw (SetMembers.ofMem x hx))
        (SetMembers.raw (SetMembers.ofMem y hy)) ∈ R
      rw [SetMembers.raw_ofMem, SetMembers.raw_ofMem, ← eq]
      exact hz
    · change ZFSet.pair (SetMembers.raw (SetMembers.ofMem x hx))
        (SetMembers.raw (SetMembers.ofMem y hy)) = z
      rw [SetMembers.raw_ofMem, SetMembers.raw_ofMem]
      exact eq.symm

end PartitionPilot.Forcing.PartialOrderCode



namespace PartitionPilot.Forcing

universe u

namespace TransitiveGround

open SetFormula
variable (M : TransitiveGround.{u})

theorem reverseInclusionCode_mem
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    {Q : ZFSet.{u}} (hQ : Q ∈ M.sets) : reverseInclusionCode Q ∈ M.sets := by
  have pairs := M.prod_mem pairing unions powers separation hQ hQ
  let params := extend Q Fin.elim0
  have selected := M.separation_mem separation (BoundedFormula.reverseInclusionEntryFormula 0 1).toFormula
    params (Fin.cases hQ (fun j => Fin.elim0 j)) pairs
  have correct (z : ZFSet.{u}) (hz : z ∈ M.sets) :
      Realize M.sets (BoundedFormula.reverseInclusionEntryFormula 0 1).toFormula (extend z params) ↔
        z ∈ reverseInclusionCode Q :=
    (BoundedFormula.realize_toFormula M _ _ (Fin.cases hz (Fin.cases hQ (fun j => Fin.elim0 j)))).trans
      (BoundedFormula.truth_reverseInclusionEntryFormula 0 1 _)
  have eq : ZFSet.sep (fun z => Realize M.sets
      (BoundedFormula.reverseInclusionEntryFormula 0 1).toFormula (extend z params)) (ZFSet.prod Q Q) =
        reverseInclusionCode Q := by
    apply ZFSet.ext
    intro z
    rw [ZFSet.mem_sep]
    constructor
    · rintro ⟨hz, rel⟩
      exact (correct z (M.transitive pairs hz)).1 rel
    · intro hz
      have hzP := (reverseInclusion_partialOrder Q).relation hz
      exact ⟨hzP, (correct z (M.transitive pairs hzP)).2 hz⟩
  exact eq ▸ selected

end TransitiveGround

end PartitionPilot.Forcing

end

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Forcing_GroundSmallFunctionPermutations
attribute [-instance] _root_.OAI.PartitionPilot.Forcing.GroundMainPrefix.withTopSmall
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace PartitionPilot.Forcing.TransitiveGround

open SetRealization SetFormula
universe u
variable (M : TransitiveGround.{u})

theorem smallFunctionOrder_mem
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    {X Y N : ZFSet.{u}} (hX : X ∈ M.sets) (hY : Y ∈ M.sets) (hN : N ∈ M.sets) :
    letI _smallOrder := M.smallFunctionOrder X Y N
    (SetMembers.presentation (M.smallPartialFunctions X Y N)).conditionOrder ∈ M.sets := by
  let smallOrder := M.smallFunctionOrder X Y N
  rw [(reverseInclusion_partialOrder (M.smallPartialFunctions X Y N)).conditionOrder_eq]
  exact M.reverseInclusionCode_mem pairing unions powers separation
    (M.smallPartialFunctions_mem pairing unions powers separation hX hY hN)

end PartitionPilot.Forcing.TransitiveGround


section

namespace PartitionPilot.Forcing

open SetRealization
universe u
variable {X Y : Type u} (s : Presentation X) (t : Presentation Y)

theorem entryPermutation_injection (e : X ≃ X) :
    InjectionCode (ZFSet.prod s.carrier t.carrier) (ZFSet.prod s.carrier t.carrier)
      (entryPermutationGraph s t e) := by
  apply (s.product t).graph_injection (s.product t)
  intro a b eq
  apply Prod.ext
  · exact e.injective (congrArg (fun z : X × Y => z.1) eq)
  · have same := congrArg (fun z : X × Y => z.2) eq
    exact same

theorem graphRename_eq_image (e : X ≃ X) (p : ZFSet.{u}) :
    graphRename s t e p = relationImage p (ZFSet.prod s.carrier t.carrier) (entryPermutationGraph s t e) := by
  apply s.relation_ext t (graphRename_shape s t _ _) (fun _ hz => (ZFSet.mem_sep.1 hz).1)
  intro x y
  rw [pair_mem_graphRename, ZFSet.mem_sep]
  constructor
  · intro rel
    refine ⟨ZFSet.pair_mem_prod.2 ⟨s.encode_mem x, t.encode_mem y⟩,
      ZFSet.pair (s.encode (e.symm x)) (t.encode y), rel, ?_⟩
    apply ((s.product t).pair_mem_graph (s.product t) _ (e.symm x, y) (x, y)).2
    exact Prod.ext (e.apply_symm_apply x) rfl
  · rintro ⟨_, z, hz, rel⟩
    have hzC := (ZFSet.pair_mem_prod.1 ((entryPermutation_injection s t e).function.1 rel)).1
    obtain ⟨⟨a, b⟩, rfl⟩ := ((s.product t).mem_carrier z).1 hzC
    have eq := ((s.product t).pair_mem_graph (s.product t) _ (a, b) (x, y)).1 rel
    have ax : a = e.symm x := (e.symm_apply_apply a).symm.trans (congrArg e.symm (congrArg Prod.fst eq))
    have by' : b = y := congrArg Prod.snd eq
    change ZFSet.pair (s.encode a) (t.encode b) ∈ p at hz
    simpa only [ax, by'] using hz

end PartitionPilot.Forcing



namespace PartitionPilot.Forcing.TransitiveGround

open SetRealization SetFormula
universe u
variable (M : TransitiveGround.{u}) {X Y : Type u} (s : Presentation X) (t : Presentation Y)

theorem inverse_function_graph_mem
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (e : X ≃ Y) (hX : s.carrier ∈ M.sets) (hY : t.carrier ∈ M.sets)
    (graph : s.graph t e ∈ M.sets) : t.graph s e.symm ∈ M.sets := by
  rw [← s.converse_graph t e]
  exact M.relationConverse_mem pairing unions powers separation hX hY graph

theorem entryPermutationGraph_mem
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (e : X ≃ X) (hX : s.carrier ∈ M.sets) (hY : t.carrier ∈ M.sets)
    (graph : s.graph s e ∈ M.sets) : entryPermutationGraph s t e ∈ M.sets := by
  have product := M.prod_mem pairing unions powers separation hX hY
  have bound := M.prod_mem pairing unions powers separation product product
  let params := extend (s.graph s e) (extend s.carrier (extend t.carrier
    (extend (ZFSet.prod s.carrier t.carrier) Fin.elim0)))
  have selected := M.bounded_separation_mem separation (BoundedFormula.entryPermutationFormula 0 1 2 3 4)
    params (Fin.cases graph (Fin.cases hX (Fin.cases hY (Fin.cases product (fun i => Fin.elim0 i))))) bound
  have eq : ZFSet.sep (fun z => BoundedFormula.Truth (BoundedFormula.entryPermutationFormula 0 1 2 3 4)
      (extend z params)) (ZFSet.prod (ZFSet.prod s.carrier t.carrier) (ZFSet.prod s.carrier t.carrier)) =
        entryPermutationGraph s t e := by
    apply ZFSet.ext
    intro z
    rw [ZFSet.mem_sep]
    exact ⟨fun h => (BoundedFormula.entryPermutation_correct s t e z).1 h.2,
      fun hz => ⟨(entryPermutation_injection s t e).function.1 hz,
        (BoundedFormula.entryPermutation_correct s t e z).2 hz⟩⟩
  exact eq ▸ selected

theorem graphRename_mem
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (e : X ≃ X) (hX : s.carrier ∈ M.sets) (hY : t.carrier ∈ M.sets)
    (graph : s.graph s e ∈ M.sets) {p : ZFSet.{u}} (hp : p ∈ M.sets) : graphRename s t e p ∈ M.sets := by
  rw [graphRename_eq_image]
  exact M.relationImage_mem separation hp (M.prod_mem pairing unions powers separation hX hY)
    (M.entryPermutationGraph_mem s t pairing unions powers separation e hX hY graph)

theorem smallPartialFunctions_rename
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (e : X ≃ X) (hX : s.carrier ∈ M.sets) (hY : t.carrier ∈ M.sets)
    (graph : s.graph s e ∈ M.sets) {N p : ZFSet.{u}} (hN : N ∈ M.sets)
    (hp : p ∈ M.smallPartialFunctions s.carrier t.carrier N) :
    graphRename s t e p ∈ M.smallPartialFunctions s.carrier t.carrier N := by
  obtain ⟨hpM, code, small⟩ := (M.mem_smallPartialFunctions s.carrier t.carrier N p).1 hp
  refine (M.mem_smallPartialFunctions s.carrier t.carrier N _).2
    ⟨M.graphRename_mem s t pairing unions powers separation e hX hY graph hpM,
      graphRename_partial s t e code, ?_⟩
  rw [graphRename_eq_image]
  exact M.groundEmbeddable_image pairing unions powers separation hpM
    (M.prod_mem pairing unions powers separation hX hY) hN
    (M.entryPermutationGraph_mem s t pairing unions powers separation e hX hY graph)
    (entryPermutation_injection s t e) code.shape small

end PartitionPilot.Forcing.TransitiveGround

end


namespace PartitionPilot.Forcing.TransitiveGround

open SetRealization SetFormula
universe u
variable (M : TransitiveGround.{u}) {X Y : Type u} (s : Presentation X) (t : Presentation Y)
variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
variable (unions : Realize M.sets SetFormula.union Fin.elim0)
variable (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
variable {N : ZFSet.{u}} (hX : s.carrier ∈ M.sets) (hY : t.carrier ∈ M.sets) (hN : N ∈ M.sets)

noncomputable def renameSmallCondition (e : X ≃ X) (graph : s.graph s e ∈ M.sets)
    (p : SetMembers (M.smallPartialFunctions s.carrier t.carrier N)) :
    SetMembers (M.smallPartialFunctions s.carrier t.carrier N) :=
  SetMembers.ofMem (graphRename s t e (SetMembers.raw p))
    (M.smallPartialFunctions_rename s t pairing unions powers separation e hX hY graph hN (SetMembers.raw_mem p))

theorem raw_renameSmallCondition (e : X ≃ X) (graph : s.graph s e ∈ M.sets)
    (p : SetMembers (M.smallPartialFunctions s.carrier t.carrier N)) :
    SetMembers.raw (M.renameSmallCondition s t pairing unions powers separation hX hY hN e graph p) =
      graphRename s t e (SetMembers.raw p) := SetMembers.raw_ofMem _ _

theorem renameSmallCondition_inverse (e : X ≃ X)
    (graph : s.graph s e ∈ M.sets) (inverse : s.graph s e.symm ∈ M.sets)
    (p : SetMembers (M.smallPartialFunctions s.carrier t.carrier N)) :
    M.renameSmallCondition s t pairing unions powers separation hX hY hN e.symm inverse
      (M.renameSmallCondition s t pairing unions powers separation hX hY hN e graph p) = p := by
  apply SetMembers.raw_injective
  rw [raw_renameSmallCondition, raw_renameSmallCondition]
  exact graphRename_inverse s t e
    (M.smallFunction_raw_properties s.carrier t.carrier N p).2.1.shape

theorem renameSmallCondition_le_iff (e : X ≃ X) (graph : s.graph s e ∈ M.sets)
    (p q : SetMembers (M.smallPartialFunctions s.carrier t.carrier N)) :
    letI _smallOrder := M.smallFunctionOrder s.carrier t.carrier N
    M.renameSmallCondition s t pairing unions powers separation hX hY hN e graph p ≤
      M.renameSmallCondition s t pairing unions powers separation hX hY hN e graph q ↔ p ≤ q := by
  let smallOrder := M.smallFunctionOrder s.carrier t.carrier N
  rw [M.smallFunction_le_iff, M.smallFunction_le_iff, raw_renameSmallCondition, raw_renameSmallCondition]
  constructor
  · intro subset
    have back := graphRename_mono s t e.symm subset
    rw [graphRename_inverse s t e (M.smallFunction_raw_properties s.carrier t.carrier N q).2.1.shape,
      graphRename_inverse s t e (M.smallFunction_raw_properties s.carrier t.carrier N p).2.1.shape] at back
    exact back
  · exact graphRename_mono s t e

noncomputable def renameSmallOrderIso (e : X ≃ X) (graph : s.graph s e ∈ M.sets) :
    letI _smallOrder := M.smallFunctionOrder s.carrier t.carrier N
    SetMembers (M.smallPartialFunctions s.carrier t.carrier N) ≃o
      SetMembers (M.smallPartialFunctions s.carrier t.carrier N) := by
  letI smallOrder := M.smallFunctionOrder s.carrier t.carrier N
  have inverse := M.inverse_function_graph_mem s s pairing unions powers separation e hX hX graph
  exact {
    toFun := M.renameSmallCondition s t pairing unions powers separation hX hY hN e graph
    invFun := M.renameSmallCondition s t pairing unions powers separation hX hY hN e.symm inverse
    left_inv := M.renameSmallCondition_inverse s t pairing unions powers separation hX hY hN e graph inverse
    right_inv := M.renameSmallCondition_inverse s t pairing unions powers separation hX hY hN e.symm inverse graph
    map_rel_iff' := fun {p q} => M.renameSmallCondition_le_iff s t pairing unions powers separation hX hY hN e graph p q }

theorem raw_renameSmallOrderIso (e : X ≃ X) (graph : s.graph s e ∈ M.sets)
    (p : SetMembers (M.smallPartialFunctions s.carrier t.carrier N)) :
    letI _smallOrder := M.smallFunctionOrder s.carrier t.carrier N
    SetMembers.raw (M.renameSmallOrderIso s t pairing unions powers separation hX hY hN e graph p) =
      graphRename s t e (SetMembers.raw p) := SetMembers.raw_ofMem _ _

end PartitionPilot.Forcing.TransitiveGround

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Transfinite_GroundChronologyPairs
attribute [-instance] _root_.OAI.PartitionPilot.Forcing.GroundMainPrefix.withTopSmall
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PartitionPilot.Forcing
open SetFormula SetRealization
universe u

namespace TransitiveGround
variable (M : TransitiveGround.{u})

theorem chronologyPairs_mem
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    {T : ZFSet.{u}} (hT : T ∈ M.sets) : chronologyPairs T ∈ M.sets := by
  let params := extend T Fin.elim0
  have ground := M.bounded_separation_mem separation (BoundedFormula.chronologyPairFormula 0 1)
    params (Fin.cases hT (fun i => Fin.elim0 i)) (M.prod_mem pairing unions powers separation hT hT)
  have equal : ZFSet.sep (fun z => BoundedFormula.Truth (BoundedFormula.chronologyPairFormula 0 1)
      (extend z params)) (ZFSet.prod T T) = chronologyPairs T := by
    apply ZFSet.ext
    intro z
    rw [ZFSet.mem_sep, BoundedFormula.truth_chronologyPairFormula]
    exact ⟨And.right, fun hz => ⟨chronologyPairs_subset T hz, hz⟩⟩
  exact equal ▸ ground

end TransitiveGround

end PartitionPilot.Forcing

end

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Definability_EqualityStepSyntax
attribute [-instance] _root_.OAI.PartitionPilot.Forcing.GroundMainPrefix.withTopSmall
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PartitionPilot.Forcing.TransitiveGround

open SetRealization SetFormula
universe u
variable (M : TransitiveGround.{u}) {P : Type u} [Preorder P] (s : Presentation P)

theorem realize_conditionLE (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (carrier : s.carrier ∈ M.sets) (order : s.conditionOrder ∈ M.sets)
    {m : Nat} (i j o : Fin m) (env : Fin m → ZFSet.{u}) (p q : P)
    (hi : env i = s.encode p) (hj : env j = s.encode q) (ho : env o = s.conditionOrder) :
    Realize M.sets (pairMembershipFormula i j o) env ↔ p ≤ q := by
  have hp : env i ∈ M.sets := hi ▸ M.transitive carrier (s.encode_mem p)
  have hq : env j ∈ M.sets := hj ▸ M.transitive carrier (s.encode_mem q)
  have horder : env o ∈ M.sets := ho ▸ order
  rw [M.realize_pairMembershipFormula pairing i j o env hp hq horder, hi, hj, ho,
    s.pair_mem_conditionOrder]

end PartitionPilot.Forcing.TransitiveGround



end

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Definability_BoundedAtomicEquality
attribute [-instance] _root_.OAI.PartitionPilot.Forcing.GroundMainPrefix.withTopSmall
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PartitionPilot.Forcing.TransitiveGround

open SetRealization SetFormula
universe u
variable (M : TransitiveGround.{u})

variable {P : Type u} [Preorder P] (s : Presentation P)

noncomputable def equalityParameters : Fin 2 → ZFSet.{u} :=
  extend s.carrier (extend s.conditionOrder Fin.elim0)

theorem rawRelationMeaning_coded
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (carrier : s.carrier ∈ M.sets) (S : ZFSet.{u}) (hS : S ∈ M.sets) :
    M.RawRelationMeaning s (RawCodedRelation s S) codedRelationFormula
      (extend S (equalityParameters s)) := by
  intro p x hx y hy
  exact M.realize_tripleMembershipFormula pairing 0 1 2 3 _
    (M.transitive carrier (s.encode_mem p)) hx hy hS

end PartitionPilot.Forcing.TransitiveGround



end

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Geometry_UniformAtomicEquality
attribute [-instance] _root_.OAI.PartitionPilot.Forcing.GroundMainPrefix.withTopSmall
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI



section

namespace PartitionPilot.Forcing.TransitiveGround

open SetRealization SetFormula
universe u
variable (M : TransitiveGround.{u}) {P : Type u} [Preorder P] (s : Presentation P)

theorem fixedPoint_equalityCertificate {B S : ZFSet.{u}} (hS : S ∈ M.sets) (bound : S ⊆ B)
    (fixed : definableOperator M.sets equalityStateFormula (equalityParameters s) B S = S) :
    Realize M.sets equalityCertificateFormula (extend S (equalityParameters s)) := by
  apply (M.realize_postfixedFormula equalityStateFormula (equalityParameters s) hS bound).2
  rw [fixed]

end PartitionPilot.Forcing.TransitiveGround

end


end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Forcing_NameRenameSteps
attribute [-instance] _root_.OAI.PartitionPilot.Forcing.GroundMainPrefix.withTopSmall
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section




namespace PartitionPilot.Forcing.SetFormula

def candidateForcingFormula {n : Nat} (phi : SetFormula (n + 1)) : SetFormula (n + 4) :=
  ex (.conj (.mem 0 2)
    (forcingTranslation (ordinaryGroundPrimitives (0 : Fin 2) 1) phi
      (extend 3 (extend 4 Fin.elim0)) 1
      (extend 0 (fun i => i.succ.succ.succ.succ.succ))))

end PartitionPilot.Forcing.SetFormula

end



namespace PartitionPilot.Forcing
open SetRealization SetFormula
universe u

namespace SetFormula

def ordinaryEqualityDecisionFormula {n : Nat}
    (carrier order condition sigma tau : Fin n) : SetFormula n :=
  disj
    (forcingTranslation (ordinaryGroundPrimitives (0 : Fin 2) 1) (.equal 0 1)
      (extend carrier (extend order Fin.elim0)) condition (extend sigma (extend tau Fin.elim0)))
    (forcingTranslation (ordinaryGroundPrimitives (0 : Fin 2) 1) (.neg (.equal 0 1))
      (extend carrier (extend order Fin.elim0)) condition (extend sigma (extend tau Fin.elim0)))

end SetFormula

namespace TransitiveGround
variable (M : TransitiveGround.{u})

noncomputable def ordinaryEqualityDecisions (Q order sigma tau : ZFSet.{u}) : ZFSet.{u} :=
  ZFSet.sep (fun p => Realize M.sets (ordinaryEqualityDecisionFormula 1 2 0 3 4)
    (extend p ![Q, order, sigma, tau])) Q

end TransitiveGround




namespace SetFormula

def ordinaryMembershipDecisionFormula {n : Nat}
    (carrier order condition sigma tau : Fin n) : SetFormula n :=
  disj
    (forcingTranslation (ordinaryGroundPrimitives (0 : Fin 2) 1) (.mem 0 1)
      (extend carrier (extend order Fin.elim0)) condition (extend sigma (extend tau Fin.elim0)))
    (forcingTranslation (ordinaryGroundPrimitives (0 : Fin 2) 1) (.neg (.mem 0 1))
      (extend carrier (extend order Fin.elim0)) condition (extend sigma (extend tau Fin.elim0)))

end SetFormula

namespace TransitiveGround
variable (M : TransitiveGround.{u})

noncomputable def ordinaryMembershipDecisions (Q order sigma tau : ZFSet.{u}) : ZFSet.{u} :=
  ZFSet.sep (fun p => Realize M.sets (ordinaryMembershipDecisionFormula 1 2 0 3 4)
    (extend p ![Q, order, sigma, tau])) Q

end TransitiveGround
end PartitionPilot.Forcing

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Forcing_GroundProductActions
attribute [-instance] _root_.OAI.PartitionPilot.Forcing.GroundMainPrefix.withTopSmall
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


section

namespace PartitionPilot.Forcing.SetFormula

universe u

def uniformRenameFormula : SetFormula 4 :=
  ex (.conj (atomicApplication renameCertificateFormula Fin.elim0 0 3 4)
    (pairMembershipFormula 1 2 0))

end PartitionPilot.Forcing.SetFormula

namespace PartitionPilot.Forcing.PosetActionCode

open SetRealization
universe u
variable {G P m i e R A : ZFSet.{u}} (h : PosetActionCode G P m e R A)

noncomputable def toPosetAction (group : GroupCode G m i e) (order : PartialOrderCode P R) :
    letI _decodedGroup := group.toGroup
    letI _decodedOrder := order.toPartialOrder
    PosetAction (SetMembers G) (SetMembers P) := by
  letI decodedGroup := group.toGroup
  letI decodedOrder := order.toPartialOrder
  exact {
    iso := fun g => {
      toFun := h.act g
      invFun := h.act g⁻¹
      left_inv := h.act_inv_left group g
      right_inv := h.act_inv_right group g
      map_rel_iff' := h.act_le_iff group order g _ _ }
    one := h.act_one group
    mul := h.act_mul group }

theorem actionGraph_eq (group : GroupCode G m i e) (order : PartialOrderCode P R) :
    letI _decodedGroup := group.toGroup
    letI _decodedOrder := order.toPartialOrder
    (h.toPosetAction group order).actionGraph (SetMembers.presentation P) (SetMembers.presentation G) = A := by
  let decodedGroup := group.toGroup
  let decodedOrder := order.toPartialOrder
  exact ((SetMembers.presentation G).product (SetMembers.presentation P)).graph_decodeFunction
    (SetMembers.presentation P) A h.function

end PartitionPilot.Forcing.PosetActionCode

end


section

namespace PartitionPilot.Forcing.PosetAction

open SetRealization SetFormula
universe u
variable {G I : Type u} [Group G] [PartialOrder I] [OrderBot I]

theorem nonbottom_actionGraph_eq_sep (a : PosetAction G I) (s : Presentation I)
    (t : Presentation G) :
    a.nonbottom.actionGraph s.nonbottom t = ZFSet.sep
      (fun z => BoundedFormula.Truth (BoundedFormula.actionRestrictionEntryFormula 0 1 2)
        (extend z (extend t.carrier (extend s.nonbottom.carrier Fin.elim0))))
      (a.actionGraph s t) := by
  apply ZFSet.ext
  intro z
  constructor
  · intro hz
    obtain ⟨⟨g, x⟩, rfl⟩ := ((t.product s.nonbottom).mem_graph s.nonbottom
      (fun gx => a.nonbottom.iso gx.1 gx.2) z).1 hz
    apply ZFSet.mem_sep.2
    refine ⟨(a.triple_mem_actionGraph s t g x.val (a.iso g x.val)).2 rfl, ?_⟩
    exact (BoundedFormula.truth_actionRestrictionEntryFormula 0 1 2 _).2
      ⟨t.encode g, t.encode_mem g, s.nonbottom.encode x, s.nonbottom.encode_mem x,
        s.nonbottom.encode (a.nonbottom.iso g x), s.nonbottom.encode_mem _, rfl⟩
  · intro hz
    obtain ⟨original, shape⟩ := ZFSet.mem_sep.1 hz
    obtain ⟨g, hg, x, hx, y, hy, eq⟩ :=
      (BoundedFormula.truth_actionRestrictionEntryFormula 0 1 2 _).1 shape
    obtain ⟨g, rfl⟩ := (t.mem_carrier g).1 hg
    obtain ⟨x, rfl⟩ := (s.nonbottom.mem_carrier x).1 hx
    obtain ⟨y, rfl⟩ := (s.nonbottom.mem_carrier y).1 hy
    change z = ZFSet.pair (ZFSet.pair (t.encode g) (s.nonbottom.encode x))
      (s.nonbottom.encode y) at eq
    rw [eq]
    apply (a.nonbottom.triple_mem_actionGraph s.nonbottom t g x y).2
    apply Subtype.ext
    exact (a.triple_mem_actionGraph s t g x.val y.val).1 (eq ▸ original)

end PartitionPilot.Forcing.PosetAction

namespace PartitionPilot.Forcing.TransitiveGround

open SetRealization SetFormula
universe u
variable (M : TransitiveGround.{u})

theorem nonbottom_actionGraph_mem {G I : Type u} [Group G] [PartialOrder I] [OrderBot I]
    (a : PosetAction G I) (s : Presentation I) (t : Presentation G)
    (separation : SeparationSchema M.sets) (carrier : s.carrier ∈ M.sets)
    (group : t.carrier ∈ M.sets) (graph : a.actionGraph s t ∈ M.sets) :
    a.nonbottom.actionGraph s.nonbottom t ∈ M.sets := by
  rw [a.nonbottom_actionGraph_eq_sep s t]
  exact M.bounded_separation_mem separation (BoundedFormula.actionRestrictionEntryFormula 0 1 2)
    (extend t.carrier (extend s.nonbottom.carrier Fin.elim0))
    (Fin.cases group (Fin.cases (M.nonbottom_carrier_mem s separation carrier)
      (fun j => Fin.elim0 j))) graph

end PartitionPilot.Forcing.TransitiveGround

end


namespace PartitionPilot.Forcing.TransitiveGround

open SetFormula SetRealization
universe u
variable (M : TransitiveGround.{u}) {G I C : Type u} [Group G] [PartialOrder I] [PartialOrder C]

theorem productColumns_actionGraph_mem
    (a : PosetAction G I) (s : Presentation I) (c : Presentation C) (t : Presentation G)
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (rows : s.carrier ∈ M.sets) (columns : c.carrier ∈ M.sets) (group : t.carrier ∈ M.sets)
    (graph : a.actionGraph s t ∈ M.sets) :
    (a.productColumns C).actionGraph (s.product c) t ∈ M.sets := by
  have coordinates : (s.product c).carrier ∈ M.sets :=
    M.prod_mem pairing unions powers separation rows columns
  have bound := M.prod_mem pairing unions powers separation
    (M.prod_mem pairing unions powers separation group coordinates) coordinates
  let params := extend t.carrier (extend s.carrier (extend c.carrier
    (extend (s.product c).carrier (extend (a.actionGraph s t) Fin.elim0))))
  have members : ∀ k, params k ∈ M.sets :=
    Fin.cases group (Fin.cases rows (Fin.cases columns (Fin.cases coordinates
      (Fin.cases graph (fun k => Fin.elim0 k)))))
  have selected := M.bounded_separation_mem separation
    (BoundedFormula.productColumnsEntryFormula 0 1 2 3 4 5) params members bound
  have eq : ZFSet.sep (fun z => BoundedFormula.Truth
      (BoundedFormula.productColumnsEntryFormula 0 1 2 3 4 5) (extend z params))
      (ZFSet.prod (ZFSet.prod t.carrier (s.product c).carrier) (s.product c).carrier) =
        (a.productColumns C).actionGraph (s.product c) t := by
    apply ZFSet.ext
    intro z
    rw [ZFSet.mem_sep, BoundedFormula.productColumnsEntry_correct]
    exact ⟨And.right, fun hz => ⟨((t.product (s.product c)).graph_isFunc (s.product c)
      (fun x => (a.productColumns C).iso x.1 x.2)).1 hz, hz⟩⟩
  exact eq ▸ selected

end PartitionPilot.Forcing.TransitiveGround

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Definability_NameSupportFormulas
attribute [-instance] _root_.OAI.PartitionPilot.Forcing.GroundMainPrefix.withTopSmall
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace PartitionPilot.Forcing

open SetRealization Compression.RecursiveMaps
universe u
variable {I G : Type u} [Group G]

theorem pair_mem_supportBasisCode (b : Presentation I) (t : Presentation G)
    (K : I → Subgroup G) (i : I) (g : G) :
    ZFSet.pair (b.encode i) (t.encode g) ∈ supportBasisCode b t K ↔ g ∈ K i :=
  (b.product t).encode_mem_subset (fun z => z.2 ∈ K z.1) (i, g)

end PartitionPilot.Forcing



end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Forcing_SymmetricGroundForcing
attribute [-instance] _root_.OAI.PartitionPilot.Forcing.GroundMainPrefix.withTopSmall
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PartitionPilot.Forcing.TransitiveGround

open SetRealization SetFormula Compression.RecursiveMaps
universe u
variable (M : TransitiveGround.{u}) {I G P : Type u} [Group G] [PartialOrder P]
variable (a : PosetAction G P) (s : Presentation P) (t : Presentation G) (b : Presentation I)

noncomputable def symmetryParameters (K : I → Subgroup G) : Fin 5 → ZFSet.{u} :=
  extend s.carrier (extend t.carrier (extend b.carrier
    (extend (supportBasisCode b t K) (extend (a.conditionMapFamily s t) Fin.elim0))))

end PartitionPilot.Forcing.TransitiveGround



end


end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Definability_SeparationEntryFormulas
attribute [-instance] _root_.OAI.PartitionPilot.Forcing.GroundMainPrefix.withTopSmall
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace PartitionPilot.Forcing.SetFormula

def separationEntryFormula {k n m : Nat} (A : ForcingPrimitives k) (φ : SetFormula (n + 1))
    (params : Fin k → Fin m) (names : Fin n → Fin m) (z τ : Fin m) : SetFormula m :=
  ex (exConditions (params A.carrier).succ (exConditions (params A.carrier).succ.succ
    (.conj (orderedPairFormula z.succ.succ.succ 2 1)
      (.conj (pairMembershipFormula 2 0 τ.succ.succ.succ)
        (.conj (pairMembershipFormula 1 0 (params A.order).succ.succ.succ)
          (forcingTranslation A φ (fun j => (params j).succ.succ.succ) 1
            (extend 2 (fun i => (names i).succ.succ.succ))))))))

end PartitionPilot.Forcing.SetFormula

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Definability_CrossStageMembershipFormulas
attribute [-instance] _root_.OAI.PartitionPilot.Forcing.GroundMainPrefix.withTopSmall
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PartitionPilot.Forcing
open SetRealization SetFormula
universe u
namespace SetFormula

def crossStageMembershipEntryFormula {n : Nat}
    (entry terms lowerCarrier upperCarrier upperOrder tau : Fin n) : SetFormula n :=
  exConditions terms (exConditions lowerCarrier.succ
    (.conj (orderedPairFormula entry.succ.succ 1 0)
      (forcingTranslation (ordinaryGroundPrimitives (0 : Fin 2) 1) (.mem 0 1)
        (extend upperCarrier.succ.succ (extend upperOrder.succ.succ Fin.elim0)) 0
        (extend 1 (extend tau.succ.succ Fin.elim0)))))

end SetFormula

end PartitionPilot.Forcing

end

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Forcing_FinitePrincipalNameSupports
attribute [-instance] _root_.OAI.PartitionPilot.Forcing.GroundMainPrefix.withTopSmall
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI



namespace PartitionPilot.Forcing.PosetAction

open Compression.RecursiveMaps Compression.RecursiveMaps.CosetGeometry.OrderAction
universe u
variable {G I : Type u} [Group G] [PartialOrder I] (a : PosetAction G I)

theorem principalFix_antitone {C D : I} (lower : C ≤ D) : a.principalFix D ≤ a.principalFix C :=
  fun _ fixed x hx => fixed x (le_trans hx lower)

theorem principalFix_conjugation (g h : G) (C : I) :
    conjugateHom g h ∈ a.principalFix (a.iso g C) ↔ h ∈ a.principalFix C := by
  constructor
  · intro fixed x lower
    apply (a.iso g).injective
    have eq := fixed (a.iso g x) ((a.iso g).monotone lower)
    change a.iso (g * h * g⁻¹) (a.iso g x) = a.iso g x at eq
    rw [a.mul, a.mul, a.point_inv_left] at eq
    exact eq
  · intro fixed x lower
    have old : a.iso g⁻¹ x ≤ C := by
      have back := (a.iso g⁻¹).monotone lower
      simpa only [a.point_inv_left] using back
    change a.iso (g * h * g⁻¹) x = x
    rw [a.mul, a.mul, fixed _ old, a.point_inv_right]

def PrincipalSupported (K : Subgroup G) : Prop := ∃ C, a.principalFix C ≤ K

theorem principalSupported_top (C : I) : a.PrincipalSupported ⊤ := ⟨C, le_top⟩

theorem principalSupported_upward {K H : Subgroup G}
    (supported : a.PrincipalSupported K) (lower : K ≤ H) : a.PrincipalSupported H := by
  obtain ⟨C, hc⟩ := supported
  exact ⟨C, le_trans hc lower⟩

theorem principalSupported_inf (directed : ∀ C D : I, ∃ E, C ≤ E ∧ D ≤ E)
    {K H : Subgroup G} (left : a.PrincipalSupported K) (right : a.PrincipalSupported H) :
    a.PrincipalSupported (K ⊓ H) := by
  obtain ⟨C, hc⟩ := left
  obtain ⟨D, hd⟩ := right
  obtain ⟨E, ce, de⟩ := directed C D
  exact ⟨E, le_inf (le_trans (a.principalFix_antitone ce) hc)
    (le_trans (a.principalFix_antitone de) hd)⟩

theorem principalSupported_conjugate (g : G) {K : Subgroup G} (supported : a.PrincipalSupported K) :
    a.PrincipalSupported (K.map (conjugateHom g)) := by
  obtain ⟨C, hc⟩ := supported
  refine ⟨a.iso g C, ?_⟩
  intro h fixed
  let k := g⁻¹ * h * g
  have eq : conjugateHom g k = h := by simp [conjugateHom, k, mul_assoc]
  have old : k ∈ a.principalFix C := (a.principalFix_conjugation g k C).1 (eq.symm ▸ fixed)
  exact Subgroup.mem_map.2 ⟨k, hc old, eq⟩

def principalSupportFamily (C : I) (directed : ∀ C D : I, ∃ E, C ≤ E ∧ D ≤ E) :
    NormalSubgroupFamily G where
  mem := a.PrincipalSupported
  top := a.principalSupported_top C
  upward := a.principalSupported_upward
  inf := a.principalSupported_inf directed
  conjugate := a.principalSupported_conjugate

end PartitionPilot.Forcing.PosetAction



namespace PartitionPilot.Forcing
open SetRealization Compression.RecursiveMaps Compression.RecursiveMaps.CosetGeometry.OrderAction
universe u v
variable {P : Type u} [PartialOrder P] {G : Type v} [Group G]

variable (a : PosetAction G P) (s : Presentation P)

variable {L : Type v} [PartialOrder L]

theorem principalFix_map_conjugate (d : PosetAction G L) (g : G) (v : L) :
    (d.principalFix v).map (conjugateHom g) = d.principalFix (d.iso g v) := by
  apply Subgroup.ext
  intro h
  constructor
  · intro member
    obtain ⟨k, hk, rfl⟩ := Subgroup.mem_map.1 member
    exact (d.principalFix_conjugation g k v).2 hk
  · intro fixed
    let k := g⁻¹ * h * g
    have equal : conjugateHom g k = h := by simp [conjugateHom, k, mul_assoc]
    exact Subgroup.mem_map.2
      ⟨k, (d.principalFix_conjugation g k v).1 (equal.symm ▸ fixed), equal⟩

theorem niceNameCode_principal_hs (d : PosetAction G L) (base v : L)
    (directed : ∀ x y : L, ∃ z, x ≤ z ∧ y ≤ z) {T : ZFSet.{u}}
    (children : ∀ σ : Name s, σ.val ∈ T →
      HereditarilySymmetric a s (d.principalSupportFamily base directed) σ)
    {τ : Name s} (code : NiceNameCode a s T (d.principalFix v) τ.val) :
    HereditarilySymmetric a s (d.principalSupportFamily base directed) τ :=
  niceNameCode_hs a s (d.principalSupportFamily base directed) ⟨v, le_refl _⟩ children code

end PartitionPilot.Forcing



end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Forcing_GroundSymmetricPowerSet
attribute [-instance] _root_.OAI.PartitionPilot.Forcing.GroundMainPrefix.withTopSmall
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PartitionPilot.Forcing.SetFormula

def codedPowerEntryFormula {k m : Nat} (N : SetFormula (k + 1))
    (params : Fin k → Fin m) (z W top : Fin m) : SetFormula m :=
  ex (.conj (.mem 0 W.succ) (.conj (domainApplication N (fun j => (params j).succ) 0)
    (orderedPairFormula z.succ 0 top.succ)))

end PartitionPilot.Forcing.SetFormula

end


end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Forcing_IndexedTupleNames
attribute [-instance] _root_.OAI.PartitionPilot.Forcing.GroundMainPrefix.withTopSmall
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI



namespace PartitionPilot.Forcing
open SetFormula SetRealization
universe u

namespace Name
variable {P : Type u} [PartialOrder P] [OrderTop P] (s : Presentation P)

theorem inputFunction (J : ZFSet.{u}) : FunctionGraphOn J (identityFunctionGraph J) :=
  ⟨J, (identityFunctionGraph_injection J).function⟩

theorem inputValue (J : ZFSet.{u}) (i : J.toSet) :
    (inputFunction J).value i = i.val :=
  (inputFunction J).value_eq_of_entry i
    ((pair_mem_identityFunctionGraph J i.val i.val).2 ⟨rfl, i.property⟩)

omit [PartialOrder P] [OrderTop P] in
theorem inputValid (J : ZFSet.{u}) (valid : ∀ z ∈ J, IsName s z) (i : J.toSet) :
    IsName s ((inputFunction J).value i) := by
  rw [inputValue]
  exact valid i.val i.property

noncomputable def inputEvaluationName (J : ZFSet.{u}) (valid : ∀ z ∈ J, IsName s z) : Name s :=
  indexedGraphName ⊤ (inputFunction J) (inputValid s J valid)

end Name

end PartitionPilot.Forcing



end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Geometry_GroundDefinableSelections
attribute [-instance] _root_.OAI.PartitionPilot.Forcing.GroundMainPrefix.withTopSmall
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace PartitionPilot.Forcing.SetFormula

def separationCodeFormula {n : Nat} (φ : SetFormula (n + 1)) : SetFormula (n + 2) :=
  exactSetFormula 0 (.conj (.mem 0 2)
    (reindex (extend 0 (fun j : Fin n => j.succ.succ.succ)) φ))

end PartitionPilot.Forcing.SetFormula

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Definability_ForcingWitnessFormulas
attribute [-instance] _root_.OAI.PartitionPilot.Forcing.GroundMainPrefix.withTopSmall
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace PartitionPilot.Forcing.SetFormula

def forcingWitnessFormula {k n m : Nat} (A : ForcingPrimitives k) (φ : SetFormula (n + 2))
    (params : Fin k → Fin m) (names : Fin n → Fin m) (z y : Fin m) : SetFormula m :=
  ex (exConditions (params A.carrier).succ
    (.conj (orderedPairFormula z.succ.succ 1 0)
      (.conj (domainApplication A.domain (fun j => (params j).succ.succ) 1)
        (.conj (domainApplication A.domain (fun j => (params j).succ.succ) y.succ.succ)
          (forcingTranslation A φ (fun j => (params j).succ.succ) 0
            (extend 1 (extend y.succ.succ (fun j => (names j).succ.succ))))))))

end PartitionPilot.Forcing.SetFormula

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Transfinite_GroundOrdinalOrderCodes
attribute [-instance] _root_.OAI.PartitionPilot.Forcing.GroundMainPrefix.withTopSmall
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace PartitionPilot.Forcing.SetFormula

def ordinalImageWitnessFormula : SetFormula 3 :=
  .conj (BoundedFormula.ordinalFormula 1).toFormula
    (ex (.conj (BoundedFormula.injectionFormula 2 3 0).toFormula
      (BoundedFormula.ordinalImageFormula 1 2 3 0).toFormula))

end PartitionPilot.Forcing.SetFormula

namespace PartitionPilot.Forcing.TransitiveGround

open SetFormula
universe u
variable (M : TransitiveGround.{u})

theorem ordinalImageOrder_mem
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    {A N f : ZFSet.{u}} (hA : A ∈ M.sets) (hN : N ∈ M.sets) (hf : f ∈ M.sets) :
    ordinalImageOrder A N f ∈ M.sets := by
  let params := extend A (extend N (extend f Fin.elim0))
  have selected := M.bounded_separation_mem separation
    (BoundedFormula.ordinalImageEntryFormula 0 1 2 3) params
    (Fin.cases hA (Fin.cases hN (Fin.cases hf (fun j => Fin.elim0 j))))
    (M.prod_mem pairing unions powers separation hN hN)
  have eq : ZFSet.sep (fun z => BoundedFormula.Truth
      (BoundedFormula.ordinalImageEntryFormula 0 1 2 3) (extend z params)) (ZFSet.prod N N) =
      ordinalImageOrder A N f := by
    apply ZFSet.ext
    intro z
    rw [ZFSet.mem_sep, BoundedFormula.truth_ordinalImageEntryFormula]
    exact ⟨And.right, fun hz => ⟨ordinalImageOrder_subset A N f hz, hz⟩⟩
  exact eq ▸ selected

theorem realize_ordinalImageWitnessFormula {r A N : ZFSet.{u}}
    (hr : r ∈ M.sets) (hA : A ∈ M.sets) (hN : N ∈ M.sets) :
    Realize M.sets ordinalImageWitnessFormula (extend r (extend A (extend N Fin.elim0))) ↔
      ordinalSetProperty A ∧ ∃ f ∈ M.sets,
        InjectionCode A N f ∧ r = ordinalImageOrder A N f := by
  have members : ∀ j, (extend r (extend A (extend N Fin.elim0))) j ∈ M.sets :=
    Fin.cases hr (Fin.cases hA (Fin.cases hN (fun j => Fin.elim0 j)))
  have ordinal : Realize M.sets (BoundedFormula.ordinalFormula 1).toFormula
      (extend r (extend A (extend N Fin.elim0))) ↔ ordinalSetProperty A :=
    (BoundedFormula.realize_ordinalFormula M 1 _ members).trans (ordinalSetProperty_iff A).symm
  change (Realize M.sets (BoundedFormula.ordinalFormula 1).toFormula _ ∧
    Realize M.sets (ex _) _) ↔ _
  rw [ordinal, realize_ex]
  apply and_congr Iff.rfl
  apply exists_congr
  intro f
  apply and_congr_right
  intro hf
  have extended : ∀ j, (extend f (extend r (extend A (extend N Fin.elim0)))) j ∈ M.sets :=
    Fin.cases hf members
  change (Realize M.sets (BoundedFormula.injectionFormula 2 3 0).toFormula _ ∧
    Realize M.sets (BoundedFormula.ordinalImageFormula 1 2 3 0).toFormula _) ↔ _
  rw [BoundedFormula.realize_toFormula M _ _ extended,
    BoundedFormula.realize_toFormula M _ _ extended,
    BoundedFormula.truth_injectionFormula, BoundedFormula.truth_ordinalImageFormula]
  rfl

end PartitionPilot.Forcing.TransitiveGround

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Geometry_GroundHartogs
attribute [-instance] _root_.OAI.PartitionPilot.Forcing.GroundMainPrefix.withTopSmall
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace PartitionPilot.Forcing.SetFormula

def representedOrdinalRelationFormula : SetFormula 2 :=
  ex (reindex (extend 1 (extend 0 (extend 2 Fin.elim0))) ordinalImageWitnessFormula)

end PartitionPilot.Forcing.SetFormula

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Definability_TaggedSumPresentations
attribute [-instance] _root_.OAI.PartitionPilot.Forcing.GroundMainPrefix.withTopSmall
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace PartitionPilot.Forcing
open SetRealization SetFormula
universe u

theorem mem_taggedSumCarrier (A B z : ZFSet.{u}) :
    z ∈ taggedSumCarrier A B ↔
      (∃ a ∈ A, z = ZFSet.pair (natSetCode 0) a) ∨ ∃ b ∈ B, z = ZFSet.pair (natSetCode 1) b := by
  simp only [taggedSumCarrier, ZFSet.mem_union, ZFSet.mem_prod, ZFSet.mem_singleton]
  constructor
  · rintro (⟨_, rfl, a, ha, equal⟩ | ⟨_, rfl, b, hb, equal⟩)
    · exact Or.inl ⟨a, ha, equal⟩
    · exact Or.inr ⟨b, hb, equal⟩
  · rintro (⟨a, ha, equal⟩ | ⟨b, hb, equal⟩)
    · exact Or.inl ⟨_, rfl, a, ha, equal⟩
    · exact Or.inr ⟨_, rfl, b, hb, equal⟩

def taggedSumPresentation {A B : Type u} (s : Presentation A) (t : Presentation B) : Presentation (A ⊕ B) where
  carrier := taggedSumCarrier s.carrier t.carrier
  encode := taggedSumEncode s t
  injective := taggedSumEncode_injective s t
  mem_carrier z := by
    rw [mem_taggedSumCarrier]
    constructor
    · rintro (⟨a, ha, equal⟩ | ⟨b, hb, equal⟩)
      · obtain ⟨a, rfl⟩ := (s.mem_carrier a).1 ha
        exact ⟨.inl a, equal.symm⟩
      · obtain ⟨b, rfl⟩ := (t.mem_carrier b).1 hb
        exact ⟨.inr b, equal.symm⟩
    · rintro ⟨a | b, rfl⟩
      · exact Or.inl ⟨s.encode a, s.encode_mem a, rfl⟩
      · exact Or.inr ⟨t.encode b, t.encode_mem b, rfl⟩

namespace TransitiveGround
variable (M : TransitiveGround.{u})
theorem taggedSumCarrier_mem
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    {A B : ZFSet.{u}} (hA : A ∈ M.sets) (hB : B ∈ M.sets) : taggedSumCarrier A B ∈ M.sets := by
  have zero : natSetCode 0 ∈ M.sets := M.empty_mem ⟨A, hA⟩
  have one : natSetCode 1 ∈ M.sets := M.insert_mem pairing unions zero zero
  have tag0 : ({natSetCode 0} : ZFSet.{u}) ∈ M.sets := by
    simpa only [ZFSet.pair_eq_singleton] using M.unorderedPair_mem pairing zero zero
  have tag1 : ({natSetCode 1} : ZFSet.{u}) ∈ M.sets := by
    simpa only [ZFSet.pair_eq_singleton] using M.unorderedPair_mem pairing one one
  exact M.binary_union_mem pairing unions (M.prod_mem pairing unions powers separation tag0 hA)
    (M.prod_mem pairing unions powers separation tag1 hB)

end TransitiveGround

end PartitionPilot.Forcing

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Forcing_GroundPairNameFamilies
attribute [-instance] _root_.OAI.PartitionPilot.Forcing.GroundMainPrefix.withTopSmall
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace PartitionPilot.Forcing
open SetFormula
universe u

namespace TransitiveGround
variable (M : TransitiveGround.{u})

theorem pairNameFamilyBound_mem
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    {one X Y : ZFSet.{u}} (hone : one ∈ M.sets) (hX : X ∈ M.sets) (hY : Y ∈ M.sets) :
    M.pairNameFamilyBound one X Y ∈ M.sets := by
  have hs : ({one} : ZFSet.{u}) ∈ M.sets := by
    simpa only [ZFSet.pair_eq_singleton] using M.unorderedPair_mem pairing hone hone
  exact M.groundPower_mem powers
    (M.prod_mem pairing unions powers separation
      (M.groundPower_mem powers (M.prod_mem pairing unions powers separation
        (M.binary_union_mem pairing unions hX hY) hs)) hs)

theorem orderedPairNameFamily_mem
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    {one X Y : ZFSet.{u}} (hone : one ∈ M.sets) (hX : X ∈ M.sets) (hY : Y ∈ M.sets) :
    orderedPairNameFamily one X Y ∈ M.sets := by
  let params := extend one (extend X (extend Y Fin.elim0))
  have members : ∀ j, params j ∈ M.sets :=
    Fin.cases hone (Fin.cases hX (Fin.cases hY (fun i => Fin.elim0 i)))
  have hBound := M.pairNameFamilyBound_mem pairing unions powers separation hone hX hY
  have subset := M.orderedPairNameFamily_subset_bound pairing hone hX hY
  have selected := M.separation_mem separation (orderedPairNameFamilyMemberFormula 0 1 2 3)
    params members hBound
  have equal : ZFSet.sep (fun z => Realize M.sets (orderedPairNameFamilyMemberFormula 0 1 2 3)
      (extend z params)) (M.pairNameFamilyBound one X Y) = orderedPairNameFamily one X Y := by
    apply ZFSet.ext
    intro z
    rw [ZFSet.mem_sep]
    constructor
    · rintro ⟨hz, formula⟩
      exact (M.realize_orderedPairNameFamilyMemberFormula pairing 0 1 2 3 _
        (Fin.cases (M.transitive hBound hz) members)).1 formula
    · intro hz
      exact ⟨subset hz, (M.realize_orderedPairNameFamilyMemberFormula pairing 0 1 2 3 _
        (Fin.cases (M.transitive hBound (subset hz)) members)).2 hz⟩
  exact equal ▸ selected

theorem iteratedPairNameFamily_mem
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    {one T : ZFSet.{u}} (hone : one ∈ M.sets) (hT : T ∈ M.sets) (n : Nat) :
    iteratedPairNameFamily one T n ∈ M.sets := by
  induction n with
  | zero => exact hT
  | succ n ih => exact M.orderedPairNameFamily_mem pairing unions powers separation hone ih hT

end TransitiveGround
end PartitionPilot.Forcing

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Transfinite_StageOneDataBoundLaws
attribute [-instance] _root_.OAI.PartitionPilot.Forcing.GroundMainPrefix.withTopSmall
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PartitionPilot.Forcing

namespace TransitiveGround

open SetFormula
universe u
variable (M : TransitiveGround.{u})

theorem groundSmallSubsets_mem (powers : Realize M.sets powerSet Fin.elim0)
    (separation : SeparationSchema M.sets)
    {B N : ZFSet.{u}} (hB : B ∈ M.sets) (hN : N ∈ M.sets) :
    M.groundSmallSubsets B N ∈ M.sets := by
  have hW := M.groundPower_mem powers hB
  have selected := M.separation_mem separation (hasInjectionFormula 0 1)
    (extend N Fin.elim0) (Fin.cases hN (fun i => Fin.elim0 i)) hW
  have eq : ZFSet.sep (fun D => Realize M.sets (hasInjectionFormula 0 1)
      (extend D (extend N Fin.elim0))) (M.groundPower B) = M.groundSmallSubsets B N := by
    apply ZFSet.ext
    intro D
    rw [ZFSet.mem_sep, groundSmallSubsets, ZFSet.mem_sep]
    apply and_congr_right
    intro hD
    exact M.realize_hasInjectionFormula 0 1 _
      (Fin.cases (M.transitive hW hD) (Fin.cases hN (fun i => Fin.elim0 i)))
  exact eq ▸ selected

theorem stageOneCandidateBound_mem
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    {rawRowCarrier I T : ZFSet.{u}} (hRow : rawRowCarrier ∈ M.sets)
    (hI : I ∈ M.sets) (hT : T ∈ M.sets) (omega : ZFSet.omega ∈ M.sets) :
    M.stageOneCandidateBound rawRowCarrier I T ∈ M.sets :=
  M.prod_mem pairing unions powers separation hRow (M.groundSmallSubsets_mem powers separation
    (M.stageOneAssignments_mem pairing unions powers separation hI hT) omega)

end TransitiveGround

open SetRealization
universe u

end PartitionPilot.Forcing

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Definability_GroundRefinementPairClassGraphs
attribute [-instance] _root_.OAI.PartitionPilot.Forcing.GroundMainPrefix.withTopSmall
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace PartitionPilot.Forcing



section
open SetFormula SetRealization
universe u v

theorem familyCodeGraph_restrict {I : Type v} [Small.{u} I]
    (key value : I → ZFSet.{u}) (injective : Function.Injective key) (p : I → Prop) :
    graphRestriction (ZFSet.range (fun i : {i // p i} => key i.val))
      (familyCodeGraph key value) =
        familyCodeGraph (fun i : {i // p i} => key i.val) (fun i => value i.val) := by
  apply ZFSet.ext
  intro z
  constructor
  · intro hz
    obtain ⟨x, hx, y, rfl, entry⟩ := mem_graphRestriction.1 hz
    obtain ⟨i, rfl⟩ := ZFSet.mem_range.1 hx
    have valueEqual := (pair_mem_familyCodeGraph key value injective i.val y).1 entry
    exact (mem_familyCodeGraph _ _ _).2 ⟨i, congrArg (ZFSet.pair (key i.val)) valueEqual.symm⟩
  · intro hz
    obtain ⟨i, rfl⟩ := (mem_familyCodeGraph _ _ z).1 hz
    exact pair_mem_graphRestriction.2
      ⟨(pair_mem_familyCodeGraph key value injective i.val _).2 rfl,
        ZFSet.mem_range.2 ⟨i, rfl⟩⟩

end



open SetRealization SetFormula
universe u




noncomputable def orderedPairNameGraph (one W f g : ZFSet.{u}) : ZFSet.{u} :=
  ZFSet.sep (fun x => ∃ w ∈ W, ∃ a b, ZFSet.pair w a ∈ f ∧ ZFSet.pair w b ∈ g ∧
    x = ZFSet.pair w (orderedPairNameCode one a b))
    (ZFSet.prod W (orderedPairNameFamily one (functionGraphRange W f) (functionGraphRange W g)))

theorem mem_orderedPairNameGraph (one W f g x : ZFSet.{u}) :
    x ∈ orderedPairNameGraph one W f g ↔
      ∃ w ∈ W, ∃ a b, ZFSet.pair w a ∈ f ∧ ZFSet.pair w b ∈ g ∧
        x = ZFSet.pair w (orderedPairNameCode one a b) := by
  rw [orderedPairNameGraph, ZFSet.mem_sep]
  refine ⟨And.right, ?_⟩
  intro h
  rcases h with ⟨w, hw, a, b, ha, hb, rfl⟩
  exact ⟨ZFSet.pair_mem_prod.2 ⟨hw, (mem_orderedPairNameFamily _ _ _ _).2
    ⟨a, (mem_functionGraphRange W f a).2 ⟨w, hw, ha⟩,
      b, (mem_functionGraphRange W g b).2 ⟨w, hw, hb⟩, rfl⟩⟩,
      ⟨w, hw, a, b, ha, hb, rfl⟩⟩

namespace TransitiveGround
variable (M : TransitiveGround.{u})

theorem realize_orderedPairNameGraphEntryFormula
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (env : Fin 5 → ZFSet.{u}) (members : ∀ j, env j ∈ M.sets) :
    Realize M.sets orderedPairNameGraphEntryFormula env ↔
      env 0 ∈ orderedPairNameGraph (env 4) (env 1) (env 2) (env 3) := by
  rw [orderedPairNameGraphEntryFormula, realize_ex, mem_orderedPairNameGraph]
  constructor
  · rintro ⟨w, hw, rest⟩
    obtain ⟨a, ha, rest⟩ := (realize_ex M.sets _ _).1 rest
    obtain ⟨b, hb, rest⟩ := (realize_ex M.sets _ _).1 rest
    obtain ⟨v, hv, member, left, right, pairName, pair⟩ := (realize_ex M.sets _ _).1 rest
    have all : ∀ j, extend v (extend b (extend a (extend w env))) j ∈ M.sets :=
      Fin.cases hv (Fin.cases hb (Fin.cases ha (Fin.cases hw members)))
    have l := (M.realize_pairMembershipFormula pairing 3 2 6 _ hw ha (members 2)).1 left
    have r := (M.realize_pairMembershipFormula pairing 3 1 7 _ hw hb (members 3)).1 right
    have named := (M.realize_orderedPairNameCodeFormula pairing 0 2 1 8 _ all).1 pairName
    have equal := (M.realize_orderedPairFormula pairing 4 3 0 _ (members 0) hw hv).1 pair
    exact ⟨w, member, a, b, l, r, equal.trans (congrArg (ZFSet.pair w) named)⟩
  · rintro ⟨w, hw, a, b, left, right, equal⟩
    have hwM := M.transitive (members 1) hw
    have ha := M.pair_right (M.transitive (members 2) left)
    have hb := M.pair_right (M.transitive (members 3) right)
    have hv := M.orderedPairNameCode_mem pairing (members 4) ha hb
    refine ⟨w, hwM, ?_⟩
    rw [realize_ex]
    refine ⟨a, ha, ?_⟩
    rw [realize_ex]
    refine ⟨b, hb, ?_⟩
    rw [realize_ex]
    refine ⟨orderedPairNameCode (env 4) a b, hv, hw, ?_, ?_, ?_, ?_⟩
    · exact (M.realize_pairMembershipFormula pairing 3 2 6 _ hwM ha (members 2)).2 left
    · exact (M.realize_pairMembershipFormula pairing 3 1 7 _ hwM hb (members 3)).2 right
    · exact (M.realize_orderedPairNameCodeFormula pairing 0 2 1 8 _
        (Fin.cases hv (Fin.cases hb (Fin.cases ha (Fin.cases hwM members))))).2 rfl
    · exact (M.realize_orderedPairFormula pairing 4 3 0 _ (members 0) hwM hv).2 equal

end TransitiveGround

namespace Name
variable {P : Type u} [PartialOrder P] [OrderTop P] {s : Presentation P}

noncomputable def refinementPairClassGraph (T : ZFSet.{u})
    (valid : ∀ z ∈ T, IsName s z) (Rf Rc : Name s)
    (W : ZFSet.{u}) (validW : ∀ z ∈ W, IsName s z) : ZFSet.{u} :=
  orderedPairNameGraph (s.encode ⊤) W
    (refinementClassGraph T valid Rf W validW) (refinementClassGraph T valid Rc W validW)

theorem pair_mem_refinementPairClassGraph (T : ZFSet.{u})
    (valid : ∀ z ∈ T, IsName s z) (Rf Rc : Name s)
    (W : ZFSet.{u}) (validW : ∀ z ∈ W, IsName s z) (w : Name s) (y : ZFSet.{u}) :
    ZFSet.pair w.val y ∈ refinementPairClassGraph T valid Rf Rc W validW ↔
      w.val ∈ W ∧ y = (orderedPair ⊤ (refinementClass T valid Rf w) (refinementClass T valid Rc w)).val := by
  rw [refinementPairClassGraph, mem_orderedPairNameGraph]
  constructor
  · rintro ⟨x, hx, a, b, left, right, equal⟩
    obtain ⟨same, value⟩ := ZFSet.pair_inj.1 equal
    rw [← same] at hx left right
    obtain ⟨_, rfl⟩ := (pair_mem_refinementClassGraph T valid Rf W validW w a).1 left
    obtain ⟨_, rfl⟩ := (pair_mem_refinementClassGraph T valid Rc W validW w b).1 right
    exact ⟨hx, value.trans (orderedPair_code ⊤ _ _).symm⟩
  · rintro ⟨hw, equal⟩
    exact ⟨w.val, hw, _, _,
      (pair_mem_refinementClassGraph T valid Rf W validW w _).2 ⟨hw, rfl⟩,
      (pair_mem_refinementClassGraph T valid Rc W validW w _).2 ⟨hw, rfl⟩,
      congrArg (ZFSet.pair w.val) (equal.trans (orderedPair_code ⊤ _ _))⟩

end Name


end PartitionPilot.Forcing

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Definability_DepthSlotCodes
attribute [-instance] _root_.OAI.PartitionPilot.Forcing.GroundMainPrefix.withTopSmall
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PartitionPilot.Forcing

open SetRealization
universe u

theorem pair_mem_natMulGraph (a b c : Nat) :
    ZFSet.pair (ZFSet.pair (natSetCode a) (natSetCode b)) (natSetCode c) ∈
      natMulGraph.{u} ↔ c = a * b := by
  change ZFSet.pair ((natPresentation.product natPresentation).encode (⟨a⟩, ⟨b⟩))
    (natPresentation.encode ⟨c⟩) ∈ (natPresentation.product natPresentation).graph
      natPresentation (fun n => ⟨n.1.down * n.2.down⟩) ↔ _
  rw [Presentation.pair_mem_graph]
  exact ⟨fun h => (congrArg ULift.down h).symm, fun h => ULift.ext _ _ h.symm⟩

theorem natAddGraph_isFunc :
    ZFSet.IsFunc (ZFSet.prod ZFSet.omega ZFSet.omega) ZFSet.omega natAddGraph.{u} :=
  (natPresentation.product natPresentation).graph_isFunc natPresentation _

theorem natMulGraph_isFunc :
    ZFSet.IsFunc (ZFSet.prod ZFSet.omega ZFSet.omega) ZFSet.omega natMulGraph.{u} :=
  (natPresentation.product natPresentation).graph_isFunc natPresentation _

theorem natAddSection_eq (a : Nat) :
    natAddSection.{u} a = indexedRelationSection ZFSet.omega ZFSet.omega natAddGraph (natSetCode a) := by
  apply ZFSet.ext
  intro z
  rw [natAddSection, Presentation.mem_graph, mem_indexedRelationSection]
  constructor
  · rintro ⟨n, rfl⟩
    exact ⟨natSetCode n.down, natPresentation.encode_mem n, natSetCode (a + n.down),
      natPresentation.encode_mem ⟨a + n.down⟩, rfl, (pair_mem_natAddGraph a n.down _).2 rfl⟩
  · rintro ⟨x, hx, y, hy, rfl, entry⟩
    obtain ⟨b, rfl⟩ := (mem_omega_iff_natSetCode x).1 hx
    obtain ⟨c, rfl⟩ := (mem_omega_iff_natSetCode y).1 hy
    have eq := (pair_mem_natAddGraph a b c).1 entry
    exact ⟨⟨b⟩, by simp only [natPresentation, eq]⟩

end PartitionPilot.Forcing

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Transfinite_GroundNaturalRecursion
attribute [-instance] _root_.OAI.PartitionPilot.Forcing.GroundMainPrefix.withTopSmall
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PartitionPilot.Forcing.TransitiveGround

open SetFormula SetRealization
universe u

theorem natural_recursion_graph_mem (M : TransitiveGround.{u})
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (infinite : Realize M.sets SetFormula.infinity Fin.elim0)
    {B : Type u} (s : Presentation B) (f : B → B) (b : B)
    (hB : s.carrier ∈ M.sets) (hf : s.graph s f ∈ M.sets) :
    natPresentation.graph s (fun n => natIterate f b n.down) ∈ M.sets := by
  have hw := M.omega_mem separation infinite
  have hb := M.transitive hB (s.encode_mem b)
  have hzero := M.empty_mem ⟨s.carrier, hB⟩
  let P := ZFSet.prod ZFSet.omega s.carrier
  have hP := M.prod_mem pairing unions powers separation hw hB
  let T := M.groundPower P
  have hT := M.groundPower_mem powers hP
  let params := extend ZFSet.omega (extend s.carrier (extend (s.graph s f)
    (extend (s.encode b) (extend T (extend ∅ Fin.elim0)))))
  have selected := M.bounded_separation_mem separation
    (BoundedFormula.iterationEntryFormula 0 1 2 3 4 5 6) params
    (Fin.cases hw (Fin.cases hB (Fin.cases hf (Fin.cases hb (Fin.cases hT
      (Fin.cases hzero (fun i => Fin.elim0 i))))))) hP
  have eq : ZFSet.sep (fun z => BoundedFormula.Truth
      (BoundedFormula.iterationEntryFormula 0 1 2 3 4 5 6) (extend z params)) P =
      natPresentation.graph s (fun n => natIterate f b n.down) := by
    apply ZFSet.ext
    intro z
    rw [ZFSet.mem_sep, BoundedFormula.truth_iterationEntryFormula _ _ _ _ _ _ _ _ rfl]
    change (z ∈ P ∧ ∃ n ∈ ZFSet.omega, ∃ y ∈ s.carrier, ∃ d ∈ ZFSet.omega, ∃ t ∈ T,
      z = ZFSet.pair n y ∧ d = insert n n ∧
        IterationTraceCode n d s.carrier (s.graph s f) (s.encode b) t ∧ ZFSet.pair n y ∈ t) ↔ _
    constructor
    · rintro ⟨_, n, hn, y, _, d, _, t, _, eq, succ, trace, out⟩
      obtain ⟨k, rfl⟩ := (mem_omega_iff_natSetCode n).1 hn
      have dcode : d = natSetCode (k + 1) := succ
      have value := (dcode ▸ trace).output s f b out
      rw [eq, value]
      exact (natPresentation.pair_mem_graph s (fun n => natIterate f b n.down) ⟨k⟩ _).2 rfl
    · intro hz
      have shape := (natPresentation.graph_isFunc s (fun n => natIterate f b n.down)).1 hz
      obtain ⟨k, eq⟩ := (natPresentation.mem_graph s (fun n => natIterate f b n.down) z).1 hz
      let t := finiteIterationTrace s f b k.down
      have ht := M.finiteIterationTrace_mem pairing unions separation infinite s f b k.down hB
      have code := finiteIterationTrace_code s f b k.down
      have bound : t ⊆ P := by
        intro a ha
        obtain ⟨i, hi, y, hy, rfl⟩ := ZFSet.mem_prod.1 (code.function.1 ha)
        obtain ⟨m, _, rfl⟩ := (mem_natSetCode i (k.down + 1)).1 hi
        exact ZFSet.pair_mem_prod.2 ⟨(mem_omega_iff_natSetCode _).2 ⟨m, rfl⟩, hy⟩
      exact ⟨shape, natSetCode k.down, natPresentation.encode_mem k,
        s.encode (natIterate f b k.down), s.encode_mem _, natSetCode (k.down + 1),
        (mem_omega_iff_natSetCode _).2 ⟨k.down + 1, rfl⟩, t,
        (M.mem_groundPower P t).2 ⟨ht, bound⟩, eq.symm, rfl, code,
        code.value s f b k.down (Nat.le_refl _)⟩
  exact eq ▸ selected

end PartitionPilot.Forcing.TransitiveGround

end

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Geometry_GroundFiniteWordLaws
attribute [-instance] _root_.OAI.PartitionPilot.Forcing.GroundMainPrefix.withTopSmall
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PartitionPilot.Forcing.TransitiveGround

open SetFormula SetRealization
universe u
variable (M : TransitiveGround.{u})

theorem natSuccessorGraph_mem
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (infinite : Realize M.sets SetFormula.infinity Fin.elim0) : natSuccessorGraph ∈ M.sets := by
  have hw := M.omega_mem separation infinite
  have bound := M.prod_mem pairing unions powers separation hw hw
  let params := extend ZFSet.omega Fin.elim0
  have selected := M.bounded_separation_mem separation
    (BoundedFormula.natSuccessorEntryFormula 0 1) params
    (Fin.cases hw (fun i => Fin.elim0 i)) bound
  have equal : ZFSet.sep (fun z => BoundedFormula.Truth
      (BoundedFormula.natSuccessorEntryFormula 0 1) (extend z params))
      (ZFSet.prod ZFSet.omega ZFSet.omega) = natSuccessorGraph := by
    apply ZFSet.ext
    intro z
    rw [ZFSet.mem_sep, BoundedFormula.truth_natSuccessorEntryFormula]
    change (z ∈ ZFSet.prod ZFSet.omega ZFSet.omega ∧ ∃ a ∈ ZFSet.omega,
      ∃ b ∈ ZFSet.omega, z = ZFSet.pair a b ∧ b = insert a a) ↔ _
    constructor
    · rintro ⟨_, a, ha, b, _, rfl, rfl⟩
      obtain ⟨a, rfl⟩ := (mem_omega_iff_natSetCode a).1 ha
      exact (pair_mem_natSuccessorGraph a (a + 1)).2 rfl
    · intro hz
      have shape := natSuccessorGraph_isFunc.1 hz
      obtain ⟨a, rfl⟩ := (natPresentation.mem_graph natPresentation
        (fun n => ⟨n.down + 1⟩) z).1 hz
      exact ⟨shape, natSetCode a.down, natPresentation.encode_mem a,
        natSetCode (a.down + 1), natPresentation.encode_mem ⟨a.down + 1⟩, rfl, rfl⟩
  exact equal ▸ selected

theorem natAddGraph_mem
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (infinite : Realize M.sets SetFormula.infinity Fin.elim0) : natAddGraph ∈ M.sets := by
  have hw := M.omega_mem separation infinite
  have hs := M.natSuccessorGraph_mem pairing unions powers separation infinite
  have hz := M.empty_mem ⟨ZFSet.omega, hw⟩
  let T := M.groundRelations ZFSet.omega ZFSet.omega
  have ht := M.groundRelations_mem pairing unions powers separation hw hw
  let P := ZFSet.prod (ZFSet.prod ZFSet.omega ZFSet.omega) ZFSet.omega
  have hp := M.prod_mem pairing unions powers separation
    (M.prod_mem pairing unions powers separation hw hw) hw
  let params := extend ZFSet.omega (extend natSuccessorGraph (extend T (extend ∅ Fin.elim0)))
  have selected := M.bounded_separation_mem separation
    (BoundedFormula.natAddEntryFormula 0 1 2 3 4) params
    (Fin.cases hw (Fin.cases hs (Fin.cases ht (Fin.cases hz (fun i => Fin.elim0 i))))) hp
  have equal : ZFSet.sep (fun z => BoundedFormula.Truth
      (BoundedFormula.natAddEntryFormula 0 1 2 3 4) (extend z params)) P = natAddGraph := by
    apply ZFSet.ext
    intro z
    rw [ZFSet.mem_sep, BoundedFormula.truth_natAddEntryFormula _ _ _ _ _ _ rfl]
    change (z ∈ P ∧ ∃ a ∈ ZFSet.omega, ∃ b ∈ ZFSet.omega, ∃ c ∈ ZFSet.omega,
      ∃ d ∈ ZFSet.omega, ∃ t ∈ T, z = ZFSet.pair (ZFSet.pair a b) c ∧ d = insert b b ∧
        IterationTraceCode b d ZFSet.omega natSuccessorGraph a t ∧ ZFSet.pair b c ∈ t) ↔ _
    constructor
    · rintro ⟨_, a, ha, b, hb, c, hc, d, _, t, _, rfl, rfl, trace, entry⟩
      obtain ⟨a, rfl⟩ := (mem_omega_iff_natSetCode a).1 ha
      obtain ⟨b, rfl⟩ := (mem_omega_iff_natSetCode b).1 hb
      obtain ⟨c, rfl⟩ := (mem_omega_iff_natSetCode c).1 hc
      have value := trace.output natPresentation (fun n => ⟨n.down + 1⟩) ⟨a⟩ entry
      have eq : natSetCode c = natSetCode (a + b) := by
        simpa only [natIterate_successor, natPresentation] using value
      exact (pair_mem_natAddGraph a b c).2 (natSetCode_injective eq)
    · intro h
      have shape := natAddGraph_isFunc.1 h
      obtain ⟨⟨a, b⟩, rfl⟩ := ((natPresentation.product natPresentation).mem_graph
        natPresentation (fun n => ⟨n.1.down + n.2.down⟩) z).1 h
      let f := fun n : ULift.{u} Nat => (⟨n.down + 1⟩ : ULift.{u} Nat)
      let t := finiteIterationTrace natPresentation f a b.down
      have code := finiteIterationTrace_code natPresentation f a b.down
      refine ⟨shape, natSetCode a.down, natPresentation.encode_mem a,
        natSetCode b.down, natPresentation.encode_mem b, natSetCode (a.down + b.down),
        natSetCode_mem_omega _, natSetCode (b.down + 1), natSetCode_mem_omega _, t,
        M.naturalFiniteTrace_mem_relations pairing unions separation infinite f a.down b.down,
        rfl, rfl, code, ?_⟩
      have iterate : natIterate f a b.down = ⟨a.down + b.down⟩ :=
        natIterate_successor a.down b.down
      have output := code.value natPresentation f a b.down (Nat.le_refl _)
      rw [iterate] at output
      exact output
  exact equal ▸ selected

theorem natMulGraph_mem
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (infinite : Realize M.sets SetFormula.infinity Fin.elim0) : natMulGraph ∈ M.sets := by
  have hw := M.omega_mem separation infinite
  have hadd := M.natAddGraph_mem pairing unions powers separation infinite
  have hz := M.empty_mem ⟨ZFSet.omega, hw⟩
  let T := M.groundRelations ZFSet.omega ZFSet.omega
  have ht := M.groundRelations_mem pairing unions powers separation hw hw
  let family := M.indexedRelationSections ZFSet.omega ZFSet.omega ZFSet.omega natAddGraph
  have spec := M.indexedRelationSections_spec pairing unions powers separation hw hw hw hadd
  let P := ZFSet.prod (ZFSet.prod ZFSet.omega ZFSet.omega) ZFSet.omega
  have hp := M.prod_mem pairing unions powers separation
    (M.prod_mem pairing unions powers separation hw hw) hw
  let params := extend ZFSet.omega (extend family (extend T (extend ∅ Fin.elim0)))
  have selected := M.bounded_separation_mem separation
    (BoundedFormula.natMulEntryFormula 0 1 2 3 4) params
    (Fin.cases hw (Fin.cases spec.1 (Fin.cases ht (Fin.cases hz (fun i => Fin.elim0 i))))) hp
  have equal : ZFSet.sep (fun z => BoundedFormula.Truth
      (BoundedFormula.natMulEntryFormula 0 1 2 3 4) (extend z params)) P = natMulGraph := by
    apply ZFSet.ext
    intro z
    rw [ZFSet.mem_sep, BoundedFormula.truth_natMulEntryFormula _ _ _ _ _ _ rfl]
    change (z ∈ P ∧ ∃ a ∈ ZFSet.omega, ∃ b ∈ ZFSet.omega, ∃ c ∈ ZFSet.omega,
      ∃ d ∈ ZFSet.omega, ∃ t ∈ T, ∃ step ∈ T,
        z = ZFSet.pair (ZFSet.pair a b) c ∧ d = insert b b ∧ ZFSet.pair a step ∈ family ∧
          IterationTraceCode b d ZFSet.omega step ∅ t ∧ ZFSet.pair b c ∈ t) ↔ _
    constructor
    · rintro ⟨_, a, ha, b, hb, c, hc, d, _, t, _, step, _, rfl, rfl, member, trace, entry⟩
      obtain ⟨a, rfl⟩ := (mem_omega_iff_natSetCode a).1 ha
      obtain ⟨b, rfl⟩ := (mem_omega_iff_natSetCode b).1 hb
      obtain ⟨c, rfl⟩ := (mem_omega_iff_natSetCode c).1 hc
      have eqStep : step = natAddSection a :=
        ((spec.2.2 _ _).1 member).2.trans (natAddSection_eq a).symm
      rw [eqStep] at trace
      have value := trace.output natPresentation (fun n => ⟨a + n.down⟩) ⟨0⟩ entry
      have eq : natSetCode c = natSetCode (a * b) := by
        simpa only [natIterate_add, natPresentation] using value
      exact (pair_mem_natMulGraph a b c).2 (natSetCode_injective eq)
    · intro h
      have shape := natMulGraph_isFunc.1 h
      obtain ⟨⟨a, b⟩, rfl⟩ := ((natPresentation.product natPresentation).mem_graph
        natPresentation (fun n => ⟨n.1.down * n.2.down⟩) z).1 h
      let f := fun n : ULift.{u} Nat => (⟨a.down + n.down⟩ : ULift.{u} Nat)
      let t := finiteIterationTrace natPresentation f ⟨0⟩ b.down
      have code := finiteIterationTrace_code natPresentation f ⟨0⟩ b.down
      have member : ZFSet.pair (natSetCode a.down) (natAddSection a.down) ∈ family :=
        (spec.2.2 _ _).2 ⟨natPresentation.encode_mem a, natAddSection_eq a.down⟩
      have stepBound : natAddSection a.down ∈ T := (ZFSet.pair_mem_prod.1 (spec.2.1.1 member)).2
      refine ⟨shape, natSetCode a.down, natPresentation.encode_mem a,
        natSetCode b.down, natPresentation.encode_mem b, natSetCode (a.down * b.down),
        natSetCode_mem_omega _, natSetCode (b.down + 1), natSetCode_mem_omega _, t,
        M.naturalFiniteTrace_mem_relations pairing unions separation infinite f 0 b.down,
        natAddSection a.down, stepBound, rfl, rfl, member, code, ?_⟩
      simpa only [t, f, natIterate_add, natPresentation] using code.value natPresentation f ⟨0⟩ b.down (Nat.le_refl _)
  exact equal ▸ selected

end PartitionPilot.Forcing.TransitiveGround

end


end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Definability_GroundRationalCodes
attribute [-instance] _root_.OAI.PartitionPilot.Forcing.GroundMainPrefix.withTopSmall
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace PartitionPilot.Forcing



section

open SetRealization
universe u

namespace TransitiveGround

open SetFormula
variable (M : TransitiveGround.{u})

theorem gridStep_graph_mem
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (infinite : Realize M.sets SetFormula.infinity Fin.elim0) :
    (natPresentation.product natPresentation).graph
      (natPresentation.product natPresentation) liftedGridStep ∈ M.sets := by
  have hw := M.omega_mem separation infinite
  have hs := M.prod_mem pairing unions powers separation hw hw
  have bound := M.prod_mem pairing unions powers separation hs hs
  let params := extend ZFSet.omega (extend (ZFSet.prod ZFSet.omega ZFSet.omega) Fin.elim0)
  have selected := M.bounded_separation_mem separation (BoundedFormula.gridEntryFormula 0 1 2)
    params (Fin.cases hw (Fin.cases hs (fun i => Fin.elim0 i))) bound
  have eq : ZFSet.sep (fun z => BoundedFormula.Truth (BoundedFormula.gridEntryFormula 0 1 2)
      (extend z params)) (ZFSet.prod (ZFSet.prod ZFSet.omega ZFSet.omega)
        (ZFSet.prod ZFSet.omega ZFSet.omega)) =
      (natPresentation.product natPresentation).graph (natPresentation.product natPresentation) liftedGridStep := by
    apply ZFSet.ext
    intro z
    rw [ZFSet.mem_sep, BoundedFormula.gridEntry_correct]
    exact ⟨And.right, fun h => ⟨((natPresentation.product natPresentation).graph_isFunc
      (natPresentation.product natPresentation) liftedGridStep).1 h, h⟩⟩
  exact eq ▸ selected

theorem omega_grid_equiv_graph_mem
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (infinite : Realize M.sets SetFormula.infinity Fin.elim0) :
    natPresentation.graph (natPresentation.product natPresentation) omegaGridEquiv ∈ M.sets := by
  have hw := M.omega_mem separation infinite
  have graph := M.natural_recursion_graph_mem pairing unions powers separation infinite
    (natPresentation.product natPresentation) liftedGridStep (⟨0⟩, ⟨0⟩)
    (M.prod_mem pairing unions powers separation hw hw)
    (M.gridStep_graph_mem pairing unions powers separation infinite)
  have eq : (fun n : ULift.{u} Nat => natIterate liftedGridStep (⟨0⟩, ⟨0⟩) n.down) = omegaGridEquiv :=
    funext gridIteration_eq
  rw [eq] at graph
  exact graph

theorem omega_product_countable
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (infinite : Realize M.sets SetFormula.infinity Fin.elim0) :
    M.groundEmbeddable (ZFSet.prod ZFSet.omega ZFSet.omega) ZFSet.omega := by
  have hw := M.omega_mem separation infinite
  have inverse := M.inverse_function_graph_mem natPresentation (natPresentation.product natPresentation)
    pairing unions powers separation omegaGridEquiv hw (M.prod_mem pairing unions powers separation hw hw)
    (M.omega_grid_equiv_graph_mem pairing unions powers separation infinite)
  exact ⟨(natPresentation.product natPresentation).graph natPresentation omegaGridEquiv.symm,
    inverse, (natPresentation.product natPresentation).graph_injection natPresentation
      omegaGridEquiv.symm omegaGridEquiv.symm.injective⟩

end TransitiveGround

end



end PartitionPilot.Forcing

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Forcing_GroundCountableFunctionForcing
attribute [-instance] _root_.OAI.PartitionPilot.Forcing.GroundMainPrefix.withTopSmall
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PartitionPilot.Forcing.TransitiveGround

open SetRealization SetFormula
universe u
variable (M : TransitiveGround.{u})

theorem countablePartialFunctions_mem
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (infinite : Realize M.sets infinity Fin.elim0)
    {X Y : ZFSet.{u}} (hX : X ∈ M.sets) (hY : Y ∈ M.sets) :
    M.smallPartialFunctions X Y ZFSet.omega ∈ M.sets :=
  M.smallPartialFunctions_mem pairing unions powers separation hX hY
    (M.omega_mem separation infinite)

theorem countableFunctionOrder_mem
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (infinite : Realize M.sets infinity Fin.elim0)
    {X Y : ZFSet.{u}} (hX : X ∈ M.sets) (hY : Y ∈ M.sets) :
    letI := M.smallFunctionOrder X Y ZFSet.omega
    (SetMembers.presentation (M.smallPartialFunctions X Y ZFSet.omega)).conditionOrder ∈ M.sets :=
  M.smallFunctionOrder_mem pairing unions powers separation hX hY
    (M.omega_mem separation infinite)

end PartitionPilot.Forcing.TransitiveGround

end

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Forcing_UniformGroundSizeWitnesses
attribute [-instance] _root_.OAI.PartitionPilot.Forcing.GroundMainPrefix.withTopSmall
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PartitionPilot.Forcing

universe u

namespace TransitiveGround

open SetFormula
variable (M : TransitiveGround.{u})

theorem sizeWitnessRelation_mem
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    {R W N : ZFSet.{u}} (hR : R ∈ M.sets) (hW : W ∈ M.sets) (hN : N ∈ M.sets) :
    sizeWitnessRelation R W N ∈ M.sets := by
  let params := extend R (extend W (extend N Fin.elim0))
  have selected := M.bounded_separation_mem separation (BoundedFormula.sizeWitnessEntryFormula 0 1 2 3)
    params (Fin.cases hR (Fin.cases hW (Fin.cases hN (fun i => Fin.elim0 i))))
    (M.prod_mem pairing unions powers separation hR hW)
  have eq : ZFSet.sep (fun z => BoundedFormula.Truth (BoundedFormula.sizeWitnessEntryFormula 0 1 2 3)
      (extend z params)) (ZFSet.prod R W) = sizeWitnessRelation R W N := by
    apply ZFSet.ext
    intro z
    rw [ZFSet.mem_sep, sizeWitnessRelation, ZFSet.mem_sep]
    exact and_congr Iff.rfl (BoundedFormula.truth_sizeWitnessEntryFormula 0 1 2 3 _)
  exact eq ▸ selected

theorem uniform_size_witnesses
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (choice : Realize M.sets SetFormula.choice Fin.elim0)
    {R B N : ZFSet.{u}} (hR : R ∈ M.sets) (hB : B ∈ M.sets) (hN : N ∈ M.sets)
    (subsets : ∀ p ∈ R, p ⊆ B) (small : ∀ p ∈ R, M.groundEmbeddable p N) :
    ∃ F ∈ M.sets, ZFSet.IsFunc R (M.groundRelations B N) F ∧
      ∀ p f, ZFSet.pair p f ∈ F → InjectionCode p N f := by
  let W := M.groundRelations B N
  have hW := M.groundRelations_mem pairing unions powers separation hB hN
  have hT := M.sizeWitnessRelation_mem pairing unions powers separation hR hW hN
  have total (p : ZFSet.{u}) (hp : p ∈ R) : ∃ f ∈ W, ZFSet.pair p f ∈ sizeWitnessRelation R W N := by
    obtain ⟨f, hf, code⟩ := small p hp
    have bound : f ⊆ ZFSet.prod B N := by
      intro z hz
      obtain ⟨x, hx, y, hy, rfl⟩ := ZFSet.mem_prod.1 (code.function.1 hz)
      exact ZFSet.pair_mem_prod.2 ⟨subsets p hp hx, hy⟩
    have hfW := (M.mem_groundRelations B N f).2 ⟨hf, bound⟩
    exact ⟨f, hfW, (pair_mem_sizeWitnessRelation R W N p f).2 ⟨hp, hfW, code⟩⟩
  obtain ⟨F, hF, func, selected⟩ := M.uniformize_relation pairing unions powers separation choice hR hW hT total
  exact ⟨F, hF, func, fun p f rel => ((pair_mem_sizeWitnessRelation R W N p f).1 (selected rel)).2.2⟩

end TransitiveGround

end PartitionPilot.Forcing

end

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Transfinite_GroundCountableFunctionClosure
attribute [-instance] _root_.OAI.PartitionPilot.Forcing.GroundMainPrefix.withTopSmall
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open scoped ZFSet


namespace PartitionPilot.Forcing

universe u

namespace TransitiveGround

open SetFormula
variable (M : TransitiveGround.{u})

theorem indexedSizeRelation_mem
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    {U R W N g F : ZFSet.{u}} (hU : U ∈ M.sets) (hR : R ∈ M.sets) (hW : W ∈ M.sets)
    (hN : N ∈ M.sets) (hg : g ∈ M.sets) (hF : F ∈ M.sets) :
    indexedSizeRelation U R W N g F ∈ M.sets := by
  let params := extend U (extend R (extend W (extend N (extend g (extend F Fin.elim0)))))
  have selected := M.bounded_separation_mem separation (BoundedFormula.indexedSizeEntryFormula 0 1 2 3 4 5 6)
    params (Fin.cases hU (Fin.cases hR (Fin.cases hW (Fin.cases hN (Fin.cases hg
      (Fin.cases hF (fun i => Fin.elim0 i)))))))
    (M.prod_mem pairing unions powers separation (M.prod_mem pairing unions powers separation hN hN) hU)
  have eq : ZFSet.sep (fun z => BoundedFormula.Truth (BoundedFormula.indexedSizeEntryFormula 0 1 2 3 4 5 6)
      (extend z params)) (ZFSet.prod (ZFSet.prod N N) U) = indexedSizeRelation U R W N g F := by
    apply ZFSet.ext
    intro z
    rw [ZFSet.mem_sep, indexedSizeRelation, ZFSet.mem_sep]
    exact and_congr Iff.rfl (BoundedFormula.truth_indexedSizeEntryFormula 0 1 2 3 4 5 6 _)
  exact eq ▸ selected

end TransitiveGround





end PartitionPilot.Forcing



namespace PartitionPilot.Forcing.TransitiveGround

open SetFormula
universe u
variable (M : TransitiveGround.{u})

theorem enumerated_union_embeds_product
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (choice : Realize M.sets SetFormula.choice Fin.elim0)
    {R B N g : ZFSet.{u}} (hR : R ∈ M.sets) (hB : B ∈ M.sets) (hN : N ∈ M.sets) (hg : g ∈ M.sets)
    (enumeration : ZFSet.IsFunc N R g) (onto : ∀ p ∈ R, ∃ n ∈ N, ZFSet.pair n p ∈ g)
    (subsets : ∀ p ∈ R, p ⊆ B) (small : ∀ p ∈ R, M.groundEmbeddable p N) :
    M.groundEmbeddable (⋃₀ R) (ZFSet.prod N N) := by
  obtain ⟨F, hF, family, codes⟩ := M.uniform_size_witnesses pairing unions powers separation choice
    hR hB hN subsets small
  have hW := M.groundRelations_mem pairing unions powers separation hB hN
  have hU := M.union_mem unions hR
  have graph := M.indexedSizeRelation_mem pairing unions powers separation hU hR hW hN hg hF
  exact M.groundEmbeddable_of_partial_surjection pairing unions powers separation choice
    (M.prod_mem pairing unions powers separation hN hN) hU graph
    (indexedSizeRelation_partial enumeration family codes) (indexedSizeRelation_onto onto family codes)

theorem countable_enumerated_union
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (infinite : Realize M.sets SetFormula.infinity Fin.elim0)
    (choice : Realize M.sets SetFormula.choice Fin.elim0)
    {R B g : ZFSet.{u}} (hR : R ∈ M.sets) (hB : B ∈ M.sets) (hg : g ∈ M.sets)
    (enumeration : ZFSet.IsFunc ZFSet.omega R g)
    (onto : ∀ p ∈ R, ∃ n ∈ ZFSet.omega, ZFSet.pair n p ∈ g)
    (subsets : ∀ p ∈ R, p ⊆ B) (small : ∀ p ∈ R, M.groundEmbeddable p ZFSet.omega) :
    M.groundEmbeddable (⋃₀ R) ZFSet.omega := by
  have hw := M.omega_mem separation infinite
  have hww := M.prod_mem pairing unions powers separation hw hw
  obtain ⟨f, hf, code⟩ := M.enumerated_union_embeds_product pairing unions powers separation choice
    hR hB hw hg enumeration onto subsets small
  obtain ⟨c, hc, ccode⟩ := M.omega_product_countable pairing unions powers separation infinite
  exact ⟨relationCompose (⋃₀ R) (ZFSet.prod ZFSet.omega ZFSet.omega) ZFSet.omega f c,
    M.relationCompose_mem pairing unions powers separation (M.union_mem unions hR) hww hw hf hc,
    code.compose ccode⟩

theorem countable_union_of_sequence_graph
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (infinite : Realize M.sets SetFormula.infinity Fin.elim0)
    (choice : Realize M.sets SetFormula.choice Fin.elim0)
    {Q B g : ZFSet.{u}} (hQ : Q ∈ M.sets) (hB : B ∈ M.sets) (hg : g ∈ M.sets)
    (enumeration : ZFSet.IsFunc ZFSet.omega Q g)
    (subsets : ∀ p ∈ Q, p ⊆ B) (small : ∀ p ∈ Q, M.groundEmbeddable p ZFSet.omega) :
    (⋃₀ relationImage ZFSet.omega Q g) ∈ M.sets ∧
      M.groundEmbeddable (⋃₀ relationImage ZFSet.omega Q g) ZFSet.omega := by
  let R := relationImage ZFSet.omega Q g
  have hR := M.relationImage_mem separation (M.omega_mem separation infinite) hQ hg
  have restricted : ZFSet.IsFunc ZFSet.omega R g := by
    refine ⟨?_, enumeration.2⟩
    intro z hz
    obtain ⟨n, hn, p, hp, rfl⟩ := ZFSet.mem_prod.1 (enumeration.1 hz)
    exact ZFSet.pair_mem_prod.2 ⟨hn, (mem_relationImage ZFSet.omega Q g p).2 ⟨hp, n, hn, hz⟩⟩
  exact ⟨M.union_mem unions hR,
    M.countable_enumerated_union pairing unions powers separation infinite choice hR hB hg restricted
      (fun p hp => ((mem_relationImage ZFSet.omega Q g p).1 hp).2)
      (fun p hp => subsets p ((mem_relationImage ZFSet.omega Q g p).1 hp).1)
      (fun p hp => small p ((mem_relationImage ZFSet.omega Q g p).1 hp).1)⟩






end PartitionPilot.Forcing.TransitiveGround



end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Definability_GroundBelowFunctionGraphs
attribute [-instance] _root_.OAI.PartitionPilot.Forcing.GroundMainPrefix.withTopSmall
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI



namespace PartitionPilot.Forcing
open SetFormula
universe u

open scoped ZFSet

noncomputable def functionSourceProjection (A f : ZFSet.{u}) : ZFSet.{u} :=
  graphRestriction f (productFirst A (⋃₀ ⋃₀ f))

end PartitionPilot.Forcing

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Transfinite_GroundCountableRelationSelections
attribute [-instance] _root_.OAI.PartitionPilot.Forcing.GroundMainPrefix.withTopSmall
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PartitionPilot.Forcing

open SetRealization
universe u

namespace TransitiveGround

open SetFormula
variable (M : TransitiveGround.{u})

theorem groundCountable_binary_union
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (infinite : Realize M.sets SetFormula.infinity Fin.elim0)
    (choice : Realize M.sets SetFormula.choice Fin.elim0)
    {A B : ZFSet.{u}} (hA : A ∈ M.sets) (hB : B ∈ M.sets)
    (countA : M.groundEmbeddable A ZFSet.omega)
    (countB : M.groundEmbeddable B ZFSet.omega) :
    M.groundEmbeddable (A ∪ B) ZFSet.omega := by
  have result := M.countable_enumerated_union pairing unions powers separation infinite choice
    (M.unorderedPair_mem pairing hA hB) (M.binary_union_mem pairing unions hA hB)
    (M.binaryUnionEnumeration_mem pairing unions powers separation infinite hA hB)
    (binaryUnionEnumeration_isFunc A B) (binaryUnionEnumeration_onto A B)
    (fun p hp => (ZFSet.mem_pair.1 hp).elim
      (fun eq => eq ▸ fun _ hz => ZFSet.mem_union.2 (Or.inl hz))
      (fun eq => eq ▸ fun _ hz => ZFSet.mem_union.2 (Or.inr hz)))
    (fun p hp => (ZFSet.mem_pair.1 hp).elim (fun eq => eq ▸ countA) (fun eq => eq ▸ countB))
  simpa only [ZFSet.sUnion_pair] using result

end TransitiveGround

end PartitionPilot.Forcing



end

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Geometry_GroundNaturalFamilyShift
attribute [-instance] _root_.OAI.PartitionPilot.Forcing.GroundMainPrefix.withTopSmall
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace PartitionPilot.Forcing

section

universe u

noncomputable def heightColumnGraph (S C Q h c : ZFSet.{u}) : ZFSet.{u} :=
  relationCompose S (ZFSet.prod C Q) Q h (productSecond {c} Q)

end



open SetFormula
universe u


end PartitionPilot.Forcing

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Transfinite_GroundMainStageFromCodes
attribute [-instance] _root_.OAI.PartitionPilot.Forcing.GroundMainPrefix.withTopSmall
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace PartitionPilot.Forcing



namespace GroundMainStage
open SetFormula
universe u
variable {M : TransitiveGround.{u}}

noncomputable def ofCodes
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    {P G r μ A m inv one b t C D rD height : ZFSet.{u}}
    (hP : P ∈ M.sets) (hG : G ∈ M.sets) (hr : r ∈ M.sets) (hμ : μ ∈ M.sets)
    (hA : A ∈ M.sets) (hm : m ∈ M.sets) (hInv : inv ∈ M.sets)
    (hC : C ∈ M.sets) (hD : D ∈ M.sets) (hrD : rD ∈ M.sets) (hHeight : height ∈ M.sets)
    (meet : MeetOrderCode P r μ) (group : GroupCode G m inv one)
    (action : PosetActionCode G P m one r A)
    (hb : b ∈ P) (least : ∀ x ∈ P, ZFSet.pair b x ∈ r)
    (ht : t ∈ P) (greatest : ∀ x ∈ P, ZFSet.pair x t ∈ r)
    (heightCode : StrictLexHeightCode P C D r height rD)
    (heightSmall : M.groundEmbeddable (relationImage P (ZFSet.prod C D) height) ZFSet.omega) :
    GroundMainStage M C D rD where
  carrier := P
  order := r
  meetGraph := μ
  actors := G
  multiplication := m
  inverse := inv
  identity := one
  action := A
  bottom := b
  top := t
  height := height
  carrier_ground := hP
  order_ground := hr
  meet_ground := hμ
  actors_ground := hG
  multiplication_ground := hm
  inverse_ground := hInv
  action_ground := hA
  height_ground := hHeight
  columns_ground := hC
  coordinates_ground := hD
  coordinate_order_ground := hrD
  meet := meet
  group_code := group
  action_code := action
  bottom_mem := hb
  least := least
  top_mem := ht
  greatest := greatest
  height_code := heightCode
  height_range_ground := M.relationImage_mem separation hP
    (M.prod_mem pairing unions powers separation hC hD) hHeight
  height_range_countable := heightSmall

end GroundMainStage

end PartitionPilot.Forcing

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Definability_NaturalStepFormulas
attribute [-instance] _root_.OAI.PartitionPilot.Forcing.GroundMainPrefix.withTopSmall
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace PartitionPilot.Forcing




open SetFormula
universe u

namespace SetFormula

def ordinalRecursionTraceFormula {k : Nat} (φ : SetFormula (k + 3)) : SetFormula (k + 2) :=
  ex <| .conj (BoundedFormula.functionFormula 1 0 2).toFormula <|
    .all <| imp (.mem 0 2) <| .all <| imp (.mem 0 2) <|
      imp (BoundedFormula.pairMembershipFormula 1 0 4).toFormula <|
        ex <| .conj (BoundedFormula.graphRestrictionFormula 0 2 3 5).toFormula <|
          reindex (extend 2 (extend 0 (extend 1
            (fun j => j.succ.succ.succ.succ.succ.succ)))) φ

def ordinalSuccessorTraceFormula {k : Nat} (φ : SetFormula (k + 3)) : SetFormula (k + 2) :=
  ex (.conj (BoundedFormula.successorFormula 0 1).toFormula
    (reindex (extend 0 (extend 2 (fun j => j.succ.succ.succ))) (ordinalRecursionTraceFormula φ)))

end SetFormula





namespace SetFormula

def naturalStepFormula {k : Nat} (successor : SetFormula (k + 2)) : SetFormula (k + 4) :=
  disj (.conj (BoundedFormula.emptyFormula 0).toFormula (.equal 2 3))
    (ex (ex (.conj (BoundedFormula.successorFormula 2 1).toFormula
      (.conj (BoundedFormula.pairMembershipFormula 1 0 3).toFormula
        (reindex (extend 0 (extend 4 (fun j => j.succ.succ.succ.succ.succ.succ))) successor)))))

end SetFormula


end PartitionPilot.Forcing

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Geometry_IntervalEmbeddingFamilyCodes
attribute [-instance] _root_.OAI.PartitionPilot.Forcing.GroundMainPrefix.withTopSmall
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open scoped ZFSet


namespace PartitionPilot.Forcing

universe u

noncomputable def canonicalEnumeration (A f : ZFSet.{u}) : ZFSet.{u} :=
  defaultInverse A ZFSet.omega f (canonicalEnumerationDefault A f)

end PartitionPilot.Forcing



end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Geometry_GroundTemplateIntervalFamilies
attribute [-instance] _root_.OAI.PartitionPilot.Forcing.GroundMainPrefix.withTopSmall
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace PartitionPilot.Forcing




universe u

noncomputable def endpointColumns (I C D f : ZFSet.{u}) : ZFSet.{u} :=
  relationCompose I (ZFSet.prod C (ZFSet.prod D D)) C f (productFirst C (ZFSet.prod D D))

noncomputable def endpointPairs (I C D f : ZFSet.{u}) : ZFSet.{u} :=
  relationCompose I (ZFSet.prod C (ZFSet.prod D D)) (ZFSet.prod D D) f (productSecond C (ZFSet.prod D D))

noncomputable def endpointLows (I C D f : ZFSet.{u}) : ZFSet.{u} :=
  relationCompose I (ZFSet.prod D D) D (endpointPairs I C D f) (productFirst D D)

noncomputable def endpointHighs (I C D f : ZFSet.{u}) : ZFSet.{u} :=
  relationCompose I (ZFSet.prod D D) D (endpointPairs I C D f) (productSecond D D)


end PartitionPilot.Forcing

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Definability_BatchGraphSetFormulas
attribute [-instance] _root_.OAI.PartitionPilot.Forcing.GroundMainPrefix.withTopSmall
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace PartitionPilot.Forcing



open SetFormula
universe u

namespace TransitiveGround
variable (M : TransitiveGround.{u})

variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
variable (unions : Realize M.sets SetFormula.union Fin.elim0)
variable (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
include pairing unions powers separation

theorem realize_canonicalMeetSetFormula {n} (output carrier order : Fin n)
    (env : Fin n → ZFSet.{u}) (members : ∀ i, env i ∈ M.sets) :
    Realize M.sets (canonicalMeetSetFormula output carrier order) env ↔
      env output = canonicalMeetGraph (env carrier) (env order) := by
  apply M.realize_exactBoundedSetFormula output _ env members
    (M.canonicalMeetGraph_mem pairing unions powers separation (members carrier) (members order))
  intro z
  exact BoundedFormula.truth_canonicalMeetEntryFormula 0 carrier.succ order.succ (extend z env)

theorem realize_codedAttachmentOrderSetFormula {n}
    (output carrier p fresh order inside shadow upper : Fin n)
    (env : Fin n → ZFSet.{u}) (members : ∀ i, env i ∈ M.sets)
    (carrier_eq : env carrier = taggedExtension (env p) (env fresh)) :
    Realize M.sets (codedAttachmentOrderSetFormula output carrier p fresh order inside shadow upper) env ↔
      env output = codedAttachmentOrder (env p) (env fresh) (env order)
        (env inside) (env shadow) (env upper) := by
  apply M.realize_exactBoundedSetFormula output _ env members
    (M.codedAttachmentOrder_mem pairing unions powers separation (members p) (members fresh)
      (members order) (members inside) (members shadow) (members upper))
  intro z
  rw [BoundedFormula.truth_codedAttachmentOrderEntryFormula]
  change (∃ x ∈ env carrier, ∃ y ∈ env carrier, z = ZFSet.pair x y ∧ _) ↔ _
  rw [carrier_eq, codedAttachmentOrder, ZFSet.mem_sep]
  constructor
  · intro witness
    refine ⟨?_, witness⟩
    obtain ⟨x, hx, y, hy, equal, _⟩ := witness
    rw [equal]
    exact ZFSet.pair_mem_prod.2 ⟨hx, hy⟩
  · exact And.right

end TransitiveGround




namespace SetFormula

def batchShadowSetFormula {n} (output i p qs ms anchors es qb mb ab eb : Fin n) : SetFormula n :=
  exactSetFormula output (reindex
    (Fin.cases 0 (Fin.cases i.succ (Fin.cases p.succ (Fin.cases qs.succ
      (Fin.cases ms.succ (Fin.cases anchors.succ (Fin.cases es.succ (Fin.cases qb.succ
        (Fin.cases mb.succ (Fin.cases ab.succ (Fin.cases eb.succ Fin.elim0)))))))))))
    BoundedFormula.batchShadowGraphFormula.toFormula)

end SetFormula

namespace TransitiveGround
variable (M : TransitiveGround.{u})

variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
variable (unions : Realize M.sets SetFormula.union Fin.elim0)
variable (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
include pairing unions powers separation

theorem realize_batchInsideSetFormula {n} (output i qs rs qb rb : Fin n)
    (env : Fin n → ZFSet.{u}) (members : ∀ x, env x ∈ M.sets)
    (qBound : env qb = ZFSet.sUnion (ZFSet.sUnion (env qs)))
    (rBound : env rb = ZFSet.sUnion (ZFSet.sUnion (env rs))) :
    Realize M.sets (batchInsideSetFormula output i qs rs qb rb) env ↔
      env output = batchAttachmentInsideGraph (env i) (env qs) (env rs) := by
  apply M.realize_exactBoundedSetFormula output _ env members
    (M.batchAttachmentInsideGraph_mem pairing unions powers separation (members i) (members qs) (members rs))
  intro z
  rw [BoundedFormula.truth_batchAttachmentInsideEntryFormula]
  change (∃ j ∈ env i, ∃ Q ∈ env qb, ∃ r ∈ env rb, ∃ q ∈ Q, ∃ t ∈ Q,
    z = ZFSet.pair (ZFSet.pair j q) (ZFSet.pair j t) ∧ ZFSet.pair j Q ∈ env qs ∧
      ZFSet.pair j r ∈ env rs ∧ ZFSet.pair q t ∈ r) ↔ _
  rw [qBound, rBound, batchAttachmentInsideGraph, ZFSet.mem_sep]
  constructor
  · intro witness
    refine ⟨?_, witness⟩
    obtain ⟨j, hj, Q, _, _, _, q, hq, t, ht, equal, entry, _⟩ := witness
    rw [equal]
    exact ZFSet.pair_mem_prod.2
      ⟨(pair_mem_indexedAttachmentDomain (env i) (env qs) j q).2 ⟨hj, Q, entry, hq⟩,
        (pair_mem_indexedAttachmentDomain (env i) (env qs) j t).2 ⟨hj, Q, entry, ht⟩⟩
  · exact And.right

theorem realize_batchUpperSetFormula {n} (output i p qs fs qb fb : Fin n)
    (env : Fin n → ZFSet.{u}) (members : ∀ x, env x ∈ M.sets)
    (qBound : env qb = ZFSet.sUnion (ZFSet.sUnion (env qs)))
    (fBound : env fb = ZFSet.sUnion (ZFSet.sUnion (env fs))) :
    Realize M.sets (batchUpperSetFormula output i p qs fs qb fb) env ↔
      env output = batchAttachmentUpperGraph (env i) (env p) (env qs) (env fs) := by
  apply M.realize_exactBoundedSetFormula output _ env members
    (M.batchAttachmentUpperGraph_mem pairing unions powers separation
      (members i) (members p) (members qs) (members fs))
  intro z
  rw [BoundedFormula.truth_batchAttachmentUpperEntryFormula]
  change (∃ j ∈ env i, ∃ Q ∈ env qb, ∃ F ∈ env fb, ∃ q ∈ Q, ∃ v ∈ env p,
    z = ZFSet.pair (ZFSet.pair j q) v ∧ ZFSet.pair j Q ∈ env qs ∧
      ZFSet.pair j F ∈ env fs ∧ v ∈ F) ↔ _
  rw [qBound, fBound, batchAttachmentUpperGraph, ZFSet.mem_sep]
  constructor
  · intro witness
    refine ⟨?_, witness⟩
    obtain ⟨j, hj, Q, _, _, _, q, hq, v, hv, equal, entry, _⟩ := witness
    rw [equal]
    exact ZFSet.pair_mem_prod.2
      ⟨(pair_mem_indexedAttachmentDomain (env i) (env qs) j q).2 ⟨hj, Q, entry, hq⟩, hv⟩
  · exact And.right

end TransitiveGround

end PartitionPilot.Forcing

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Forcing_ActionPostcompositionCodes
attribute [-instance] _root_.OAI.PartitionPilot.Forcing.GroundMainPrefix.withTopSmall
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PartitionPilot.Forcing

universe u

namespace RestrictedActionCode

variable {P r A g source target base : ZFSet.{u}}
variable (code : RestrictedActionCode P r A g source target base)
include code

theorem base_order {G m inv e : ZFSet.{u}} (group : GroupCode G m inv e)
    (action : PosetActionCode G P m e r A) (order : PartialOrderCode P r) (hg : g ∈ G)
    {x y x' y' : ZFSet.{u}} (xx' : ZFSet.pair x x' ∈ base)
    (yy' : ZFSet.pair y y' ∈ base) :
    ZFSet.pair x' y' ∈ r ↔ ZFSet.pair x y ∈ r :=
  action.raw_order_iff group order hg (code.entry_action xx') (code.entry_action yy')

theorem base_meet {G m inv e μ : ZFSet.{u}} (group : GroupCode G m inv e)
    (action : PosetActionCode G P m e r A) (meet : MeetOrderCode P r μ) (hg : g ∈ G)
    {x y z x' y' z' : ZFSet.{u}} (xyz : ZFSet.pair (ZFSet.pair x y) z ∈ μ)
    (xx' : ZFSet.pair x x' ∈ base) (yy' : ZFSet.pair y y' ∈ base)
    (zz' : ZFSet.pair z z' ∈ base) : ZFSet.pair (ZFSet.pair x' y') z' ∈ μ :=
  action.raw_map_meet group meet hg xyz (code.entry_action xx')
    (code.entry_action yy') (code.entry_action zz')

theorem singleAttachmentInputs {G m inv e μ F separator : ZFSet.{u}}
    (group : GroupCode G m inv e) (action : PosetActionCode G P m e r A)
    (meet : MeetOrderCode P r μ) (hg : g ∈ G) (hsource : source ∈ P)
    (htarget : target ∈ P) (filter : MeetFilterCode P r μ F)
    (hseparator : separator ∈ P) (lower : ZFSet.pair target separator ∈ r)
    (strict : ZFSet.pair separator target ∉ r)
    (upper : ∀ y ∈ F, ZFSet.pair separator y ∈ r) :
    SingleAttachmentInputs P P r r μ μ base F source separator := by
  have function := code.base_function action hg
  have targetEntry := code.source_entry meet.order hsource htarget
  have value_eq (b : ZFSet.{u}) (entry : ZFSet.pair source b ∈ base) : b = target := by
    obtain ⟨v, _, unique⟩ := function.2 source
      ((mem_attachmentIdeal P r source source).2 ⟨hsource, meet.order.refl source hsource⟩)
    exact (unique b entry).trans (unique target targetEntry).symm
  exact {
    oldOrder := meet
    templateOrder := meet
    anchor_mem := hsource
    base_function := function
    base_order := fun _ _ _ _ xx' yy' => code.base_order group action meet.order hg xx' yy'
    base_meet := fun _ _ _ _ _ _ xyz xx' yy' zz' => code.base_meet group action meet hg xyz xx' yy' zz'
    filter := filter
    separator_mem := hseparator
    base_le_separator := fun b entry => (value_eq b entry).symm ▸ lower
    separator_not_le_base := fun b entry => (value_eq b entry).symm ▸ strict
    separator_le_upper := upper }

end RestrictedActionCode

end PartitionPilot.Forcing

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Definability_TaskRepresentativeCodes
attribute [-instance] _root_.OAI.PartitionPilot.Forcing.GroundMainPrefix.withTopSmall
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PartitionPilot.Forcing

universe u

noncomputable def eligibleTaskSet (P G r μ A R U Labels : ZFSet.{u}) : ZFSet.{u} :=
  ZFSet.sep (fun z => ∃ a ∈ P, ∃ c ∈ P, ∃ base ∈ R, ∃ e ∈ P, ∃ F ∈ U, ∃ label ∈ Labels,
    z = literalTaskCode a c base e F label ∧ EligibleTaskCode P G r μ A a c base e F)
    (literalTaskBound P R U Labels)

theorem eligibleTaskSet_subset (P G r μ A R U Labels : ZFSet.{u}) :
    eligibleTaskSet P G r μ A R U Labels ⊆ literalTaskBound P R U Labels :=
  fun _ hz => (ZFSet.mem_sep.1 hz).1

theorem mem_eligibleTaskSet (P G r μ A R U Labels z : ZFSet.{u}) :
    z ∈ eligibleTaskSet P G r μ A R U Labels ↔
      ∃ a ∈ P, ∃ c ∈ P, ∃ base ∈ R, ∃ e ∈ P, ∃ F ∈ U, ∃ label ∈ Labels,
        z = literalTaskCode a c base e F label ∧ EligibleTaskCode P G r μ A a c base e F := by
  constructor
  · exact fun hz => (ZFSet.mem_sep.1 hz).2
  · rintro ⟨a, ha, c, hc, base, hBase, e, he, F, hF, label, hLabel, rfl, code⟩
    exact ZFSet.mem_sep.2 ⟨(literalTaskCode_mem_bound P R U Labels a c base e F label).2
      ⟨ha, hc, hBase, he, hF, hLabel⟩,
      a, ha, c, hc, base, hBase, e, he, F, hF, label, hLabel, rfl, code⟩

end PartitionPilot.Forcing

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Definability_GroundPushFilterFamilyFormulas
attribute [-instance] _root_.OAI.PartitionPilot.Forcing.GroundMainPrefix.withTopSmall
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section



namespace PartitionPilot.Forcing

universe u

namespace TransitiveGround
open SetFormula
variable (M : TransitiveGround.{u})

theorem realize_pushFilterFamilyEntryFormula {n} (z K I J L r Maps Fs : Fin n)
    (env : Fin n → ZFSet.{u}) (members : ∀ i, env i ∈ M.sets) :
    Realize M.sets (pushFilterFamilyEntryFormula z K I J L r Maps Fs) env ↔
      env z ∈ M.groundPairPushFilters (env K) (env I) (env J) (env L) (env r) (env Maps) (env Fs) := by
  simp only [pushFilterFamilyEntryFormula, realize_ex]
  constructor
  · rintro ⟨i, hiM, j, hjM, S, hSM, F, hFM, V, hVM, body⟩
    have extended : ∀ a, extend V (extend F (extend S (extend j (extend i env)))) a ∈ M.sets :=
      Fin.cases hVM (Fin.cases hFM (Fin.cases hSM (Fin.cases hjM (Fin.cases hiM members))))
    have spec := (BoundedFormula.realize_toFormula M _ _ extended).1 body
    simp only [BoundedFormula.Truth, BoundedFormula.truth_orderedTripleFormula,
      BoundedFormula.truth_pairMembershipFormula, BoundedFormula.truth_pushFilterFormula] at spec
    change i ∈ env I ∧ j ∈ env J ∧ env z = ZFSet.pair (ZFSet.pair i j) V ∧
      ZFSet.pair i j ∈ env K ∧ ZFSet.pair i S ∈ env Maps ∧ ZFSet.pair j F ∈ env Fs ∧
      V = pushFilterCode (env L) (env r) S F at spec
    obtain ⟨hi, hj, equal, hk, first, second, output⟩ := spec
    rw [equal]
    exact (pair_mem_pairPushFilterFamily _ _ _ _ _ _ _ _ _ _ _).2
      ⟨hk, (M.mem_groundPower _ _).2 ⟨hVM, output.symm ▸ pushFilterCode_subset _ _ _ _⟩,
        hi, hj, S, F, first, second, output⟩
  · intro member
    unfold groundPairPushFilters pairPushFilterFamily at member
    obtain ⟨_, i, hi, j, hj, S, _, F, _, V, hV, equal, first, second, output⟩ := ZFSet.mem_sep.1 member
    have hk : ZFSet.pair i j ∈ env K := (ZFSet.pair_mem_prod.1 ((equal ▸ (ZFSet.mem_sep.1 member).1))).1
    have hiM := M.transitive (members I) hi
    have hjM := M.transitive (members J) hj
    have hSM := M.pair_right (M.transitive (members Maps) first)
    have hFM := M.pair_right (M.transitive (members Fs) second)
    have hVM := ((M.mem_groundPower _ _).1 hV).1
    refine ⟨i, hiM, j, hjM, S, hSM, F, hFM, V, hVM, ?_⟩
    apply (BoundedFormula.realize_toFormula M _ _
      (Fin.cases hVM (Fin.cases hFM (Fin.cases hSM (Fin.cases hjM (Fin.cases hiM members)))))).2
    simp only [BoundedFormula.Truth, BoundedFormula.truth_orderedTripleFormula,
      BoundedFormula.truth_pairMembershipFormula, BoundedFormula.truth_pushFilterFormula]
    exact ⟨hi, hj, equal, hk, first, second, output⟩

theorem realize_pushFilterFamilyFormula
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    {n} (family K I J L r Maps Fs : Fin n)
    (env : Fin n → ZFSet.{u}) (members : ∀ i, env i ∈ M.sets) :
    Realize M.sets (pushFilterFamilyFormula family K I J L r Maps Fs) env ↔
      env family = M.groundPairPushFilters (env K) (env I) (env J) (env L) (env r) (env Maps) (env Fs) := by
  apply M.realize_exactSetFormula family _ env (members family)
  · intro z member
    unfold groundPairPushFilters pairPushFilterFamily at member
    obtain ⟨k, hk, V, hV, rfl⟩ := ZFSet.mem_prod.1 (ZFSet.mem_sep.1 member).1
    exact M.orderedPair_mem pairing (M.transitive (members K) hk) ((M.mem_groundPower _ _).1 hV).1
  · intro z hz
    exact M.realize_pushFilterFamilyEntryFormula 0 K.succ I.succ J.succ L.succ r.succ Maps.succ Fs.succ
      (extend z env) (Fin.cases hz members)

end TransitiveGround

end PartitionPilot.Forcing

end

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Geometry_TileStarIncomingCodes
attribute [-instance] _root_.OAI.PartitionPilot.Forcing.GroundMainPrefix.withTopSmall
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI



namespace PartitionPilot.Forcing
open SetRealization SetFormula
universe u

namespace TransitiveGround
variable (M : TransitiveGround.{u})
theorem shortestLengthGraph_mem
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (infinite : Realize M.sets infinity Fin.elim0)
    {A lengths : ZFSet.{u}} (hA : A ∈ M.sets) (hLengths : lengths ∈ M.sets) :
    shortestLengthGraph A lengths ∈ M.sets := by
  have hOmega := M.omega_mem separation infinite
  let params := extend A (extend ZFSet.omega (extend lengths Fin.elim0))
  have selected := M.bounded_separation_mem separation (BoundedFormula.shortestLengthEntryFormula 0 1 2 3)
    params (Fin.cases hA (Fin.cases hOmega (Fin.cases hLengths (fun i => Fin.elim0 i))))
    (M.prod_mem pairing unions powers separation hA hOmega)
  have equal : ZFSet.sep (fun z => BoundedFormula.Truth (BoundedFormula.shortestLengthEntryFormula 0 1 2 3)
      (extend z params)) (ZFSet.prod A ZFSet.omega) = shortestLengthGraph A lengths := by
    apply ZFSet.ext
    intro z
    rw [shortestLengthGraph, ZFSet.mem_sep, ZFSet.mem_sep]
    exact and_congr Iff.rfl (BoundedFormula.truth_shortestLengthEntryFormula _ _ _ _ _)
  exact equal ▸ selected

end TransitiveGround

end PartitionPilot.Forcing



end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Definability_TaggedGrowthLayerFormulas
attribute [-instance] _root_.OAI.PartitionPilot.Forcing.GroundMainPrefix.withTopSmall
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open scoped ZFSet



namespace PartitionPilot.Forcing
open SetRealization
universe u

namespace SeparatedLayerCode
variable {M : TransitiveGround.{u}}
variable {Qs rs μs L r μ birth t I Indices Maps W Components F : ZFSet.{u}}
variable (code : SeparatedLayerCode Qs rs μs L r μ birth t I Indices Maps W Components F)

noncomputable def toGrowthLayer
    (hMaps : Maps ∈ M.sets) (Space sourceOrder sourceMeet : ZFSet.{u} → ZFSet.{u})
    (agree : ∀ s ∈ t, ZFSet.pair s (Space s) ∈ Qs ∧
      ZFSet.pair s (sourceOrder s) ∈ rs ∧ ZFSet.pair s (sourceMeet s) ∈ μs) :
    CodedGrowthLayer M Space sourceOrder sourceMeet L r μ birth t := by
  classical
  let indices : FunctionGraphOn I Indices := ⟨t, code.indices⟩
  let maps : FunctionGraphOn I Maps := ⟨W, code.maps⟩
  let components : FunctionGraphOn F Components := ⟨I, code.components⟩
  let member (i : SetMembers I) : {i : ZFSet.{u} // i ∈ I} :=
    ⟨SetMembers.raw i, SetMembers.raw_mem i⟩
  let index (i : SetMembers I) := indices.value (member i)
  let e (i : SetMembers I) := maps.value (member i)
  have earlier (i : SetMembers I) : index i ∈ t :=
    (ZFSet.pair_mem_prod.1 (code.indices.1 (indices.value_entry (member i)))).2
  have embedding (i : SetMembers I) : MeetEmbeddingCode (Space (index i)) L
      (sourceOrder (index i)) r (sourceMeet (index i)) μ (e i) :=
    code.embedding _ (SetMembers.raw_mem i) _ (earlier i) _ _ _ _
      (indices.value_entry (member i)) (maps.value_entry (member i))
      (agree _ (earlier i)).1 (agree _ (earlier i)).2.1 (agree _ (earlier i)).2.2
  let Point := {x : ZFSet.{u} // x ∈ L ∧ ZFSet.pair x t ∈ birth}
  have inFiber (x : Point) : x.val ∈ F :=
    code.fiber.symm ▸ (mem_layerBirthFiber L birth t x.val).2 x.property
  let componentValue (x : Point) := components.value ⟨x.val, inFiber x⟩
  have componentMem (x : Point) : componentValue x ∈ I :=
    (ZFSet.pair_mem_prod.1 (code.components.1 (components.value_entry ⟨x.val, inFiber x⟩))).2
  let component (x : Point) : SetMembers I := SetMembers.ofMem (componentValue x) (componentMem x)
  have componentEntry (x : Point) : ZFSet.pair x.val (SetMembers.raw (component x)) ∈ Components := by
    change ZFSet.pair x.val (SetMembers.raw (SetMembers.ofMem _ _)) ∈ Components
    rw [SetMembers.raw_ofMem]
    exact components.value_entry ⟨x.val, inFiber x⟩
  refine CodedGrowthLayer.separated (SetMembers I) index e earlier
    (fun i => maps.value_mem M hMaps (member i)) embedding component ?_ ?_
  · intro x
    exact code.cover _ (SetMembers.raw_mem (component x)) _ (earlier (component x)) _ _ _
      x.property.1 (indices.value_entry (member (component x)))
      (maps.value_entry (member (component x))) (agree _ (earlier (component x))).1
      (componentEntry x)
  · intro x y different
    exact code.separated _ (inFiber x) _ (inFiber y)
      _ (SetMembers.raw_mem (component x)) _ (SetMembers.raw_mem (component y))
      (componentEntry x) (componentEntry y)
      (fun equal => different (SetMembers.raw_injective I equal))
end SeparatedLayerCode

end PartitionPilot.Forcing



namespace PartitionPilot.Forcing
open SetFormula
universe u

namespace GrowthLayerWitnessCode

noncomputable def toLayer {M : TransitiveGround.{u}}
    {Qs rs μs L r μ birth t N z : ZFSet.{u}}
    (code : GrowthLayerWitnessCode Qs rs μs L r μ birth t N z) (ground : z ∈ M.sets)
    (Space sourceOrder sourceMeet : ZFSet.{u} → ZFSet.{u}) (omega : N = ZFSet.omega)
    (history : ∀ s ∈ t, ZFSet.pair s (Space s) ∈ Qs ∧
      ZFSet.pair s (sourceOrder s) ∈ rs ∧ ZFSet.pair s (sourceMeet s) ∈ μs) :
    CodedGrowthLayer M Space sourceOrder sourceMeet L r μ birth t := by
  apply Classical.choice
  rcases code with ⟨D, injection, rfl, code⟩ |
    ⟨I, parts, Indices, Maps, W, injection, rfl, code⟩ |
    ⟨I, Indices, Maps, W, Components, F, rfl, code⟩
  · have fields := M.nonemptyTupleCode_field_mem 2 _ ground
    exact ⟨code.toLayer Space sourceOrder sourceMeet (fields 1) (fields 2) omega⟩
  · have fields := M.nonemptyTupleCode_field_mem 6 _ ground
    exact ⟨code.toLayer Space sourceOrder sourceMeet (fields 1) (fields 2) (fields 4)
      (fields 6) omega history⟩
  · have fields := M.nonemptyTupleCode_field_mem 6 _ ground
    exact ⟨code.toGrowthLayer (fields 3) Space sourceOrder sourceMeet history⟩
end GrowthLayerWitnessCode

namespace TransitiveGround
variable (M : TransitiveGround.{u})

theorem countableLayerWitness_mem (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    {D injection : ZFSet.{u}} (hD : D ∈ M.sets) (hInjection : injection ∈ M.sets) :
    countableLayerWitness D injection ∈ M.sets :=
  M.nonemptyTupleCode_mem pairing 2 _
    (Fin.cases (M.empty_mem ⟨D, hD⟩) (Fin.cases hD (fun _ => hInjection)))

end TransitiveGround

end PartitionPilot.Forcing



end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Transfinite_NonzeroLimitOrdinalCodes
attribute [-instance] _root_.OAI.PartitionPilot.Forcing.GroundMainPrefix.withTopSmall
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PartitionPilot.Forcing
open SetRealization
universe u

theorem ordinalMainIndex_le_iff {T : ZFSet.{u}} (ordinal : ordinalSetProperty T)
    (i j : SetMembers T) :
    @LE.le _ (ordinalMainIndexPreorder ordinal).toLE i j ↔
      SetMembers.raw i = SetMembers.raw j ∨ SetMembers.raw i ∈ SetMembers.raw j := Iff.rfl

theorem ordinalMainIndex_key_range (T : ZFSet.{u}) :
    ZFSet.range (@SetMembers.raw T) = T := by
  apply ZFSet.ext
  intro z
  rw [ZFSet.mem_range]
  constructor
  · rintro ⟨i, rfl⟩
    exact SetMembers.raw_mem i
  · intro hz
    exact ⟨SetMembers.ofMem z hz, SetMembers.raw_ofMem z hz⟩

theorem ordinalMainTransitionIndex_range {T : ZFSet.{u}} (ordinal : ordinalSetProperty T) :
    letI := ordinalMainIndexPreorder ordinal
    ZFSet.range (mainTransitionIndexKey (@SetMembers.raw T)) = chronologyPairs T := by
  let := ordinalMainIndexPreorder ordinal
  exact (mainTransitionIndex_range (@SetMembers.raw T)
    (fun i j => ordinalMainIndex_le_iff ordinal i j)).trans
      (congrArg chronologyPairs (ordinalMainIndex_key_range T))

theorem ordinalMainIndex_rank_le_iff {T : ZFSet.{u}} (ordinal : ordinalSetProperty T)
    (i j : SetMembers T) :
    ZFSet.rank (SetMembers.raw i) ≤ ZFSet.rank (SetMembers.raw j) ↔
      SetMembers.raw i = SetMembers.raw j ∨ SetMembers.raw i ∈ SetMembers.raw j := by
  have hi := ordinalSetProperty_eq_code_rank (SetMembers.raw i)
    (ordinalSetProperty_member ordinal (SetMembers.raw_mem i))
  have hj := ordinalSetProperty_eq_code_rank (SetMembers.raw j)
    (ordinalSetProperty_member ordinal (SetMembers.raw_mem j))
  constructor
  · intro before
    rcases lt_or_eq_of_le before with earlier | equal
    · exact Or.inr (by rw [hi, hj]; exact (mem_ordinalCode_iff _ _).2 earlier)
    · exact Or.inl (hi.trans ((congrArg ordinalCode equal).trans hj.symm))
  · rintro (equal | earlier)
    · exact le_of_eq (congrArg ZFSet.rank equal)
    · exact le_of_lt (ZFSet.rank_lt_of_mem earlier)

theorem ordinalMainIndex_total {T : ZFSet.{u}} (ordinal : ordinalSetProperty T)
    (i j : SetMembers T) :
    letI := ordinalMainIndexPreorder ordinal
    i ≤ j ∨ j ≤ i := by
  let := ordinalMainIndexPreorder ordinal
  rcases le_total (ZFSet.rank (SetMembers.raw i)) (ZFSet.rank (SetMembers.raw j)) with first | second
  · exact Or.inl ((ordinalMainIndex_rank_le_iff ordinal i j).1 first)
  · exact Or.inr ((ordinalMainIndex_rank_le_iff ordinal j i).1 second)

end PartitionPilot.Forcing

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Definability_GroundFunctionRangeFamilies
attribute [-instance] _root_.OAI.PartitionPilot.Forcing.GroundMainPrefix.withTopSmall
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open scoped ZFSet

namespace PartitionPilot.Forcing
open SetRealization
universe u v

noncomputable def decodedFamilyValue {A f : ZFSet.{u}} (function : FunctionGraphOn A f)
    (i : SetMembers A) : ZFSet.{u} :=
  function.value ⟨SetMembers.raw i, SetMembers.raw_mem i⟩

theorem decodedFamilyValue_entry {A f : ZFSet.{u}} (function : FunctionGraphOn A f)
    (i : SetMembers A) : ZFSet.pair (SetMembers.raw i) (decodedFamilyValue function i) ∈ f :=
  function.value_entry ⟨SetMembers.raw i, SetMembers.raw_mem i⟩

end PartitionPilot.Forcing

namespace PartitionPilot.Forcing
open SetFormula
universe u v

namespace TransitiveGround
variable (M : TransitiveGround.{u})
variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
variable (unions : Realize M.sets SetFormula.union Fin.elim0)
variable (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
include pairing unions powers separation

theorem familyCodeGraph_pair_projections {I : Type v} [Small.{u} I]
    (key left right : I → ZFSet.{u}) (injective : Function.Injective key)
    (domain : ZFSet.range key ∈ M.sets)
    (whole : familyCodeGraph key (fun i => ZFSet.pair (left i) (right i)) ∈ M.sets) :
    familyCodeGraph key left ∈ M.sets ∧ familyCodeGraph key right ∈ M.sets := by
  let F := familyCodeGraph key (fun i => ZFSet.pair (left i) (right i))
  let V := ⋃₀ ⋃₀ F
  let B := ⋃₀ ⋃₀ V
  have hV : V ∈ M.sets := M.union_mem unions (M.union_mem unions whole)
  have hB : B ∈ M.sets := M.union_mem unions (M.union_mem unions hV)
  have bounds (i : I) : left i ∈ B ∧ right i ∈ B := by
    have entry : ZFSet.pair (left i) (right i) ∈ V :=
      pair_second_mem_doubleUnion ((pair_mem_familyCodeGraph key _ injective i _).2 rfl)
    exact ⟨pair_first_mem_doubleUnion entry, pair_second_mem_doubleUnion entry⟩
  have function : ZFSet.IsFunc (ZFSet.range key) (ZFSet.prod B B) F := by
    refine ⟨?_, (familyCodeGraph_isFunc key _ injective).2⟩
    intro z hz
    obtain ⟨i, rfl⟩ := (mem_familyCodeGraph key _ z).1 hz
    exact ZFSet.pair_mem_prod.2 ⟨ZFSet.mem_range.2 ⟨i, rfl⟩,
      ZFSet.pair_mem_prod.2 (bounds i)⟩
  let first := relationCompose (ZFSet.range key) (ZFSet.prod B B) B F (productFirst B B)
  let second := relationCompose (ZFSet.range key) (ZFSet.prod B B) B F (productSecond B B)
  have firstGround : first ∈ M.sets := M.relationCompose_mem pairing unions powers separation
    domain (M.prod_mem pairing unions powers separation hB hB) hB whole
      (M.productFirst_mem pairing unions powers separation hB hB)
  have secondGround : second ∈ M.sets := M.relationCompose_mem pairing unions powers separation
    domain (M.prod_mem pairing unions powers separation hB hB) hB whole
      (M.productSecond_mem pairing unions powers separation hB hB)
  have firstFunction : FunctionGraphOn (ZFSet.range key) first := ⟨B,
    relationCompose_function_of_subset function (productFirst_function B B) (fun _ h => h)⟩
  have secondFunction : FunctionGraphOn (ZFSet.range key) second := ⟨B,
    relationCompose_function_of_subset function (productSecond_function B B) (fun _ h => h)⟩
  constructor
  · apply familyCodeGraph_ground_of_entries firstGround firstFunction key left rfl
    intro i
    exact (pair_mem_relationCompose _ _ _ _ _ _ _).2
      ⟨ZFSet.mem_range.2 ⟨i, rfl⟩, (bounds i).1, _, ZFSet.pair_mem_prod.2 (bounds i),
        (pair_mem_familyCodeGraph key _ injective i _).2 rfl,
        (mem_productFirst B B _).2 ⟨left i, (bounds i).1, right i, (bounds i).2, rfl⟩⟩
  · apply familyCodeGraph_ground_of_entries secondGround secondFunction key right rfl
    intro i
    exact (pair_mem_relationCompose _ _ _ _ _ _ _).2
      ⟨ZFSet.mem_range.2 ⟨i, rfl⟩, (bounds i).2, _, ZFSet.pair_mem_prod.2 (bounds i),
        (pair_mem_familyCodeGraph key _ injective i _).2 rfl,
        (mem_productSecond B B _).2 ⟨left i, (bounds i).1, right i, (bounds i).2, rfl⟩⟩

theorem familyCodeGraph_tuple_fields {I : Type v} [Small.{u} I]
    (key : I → ZFSet.{u}) (injective : Function.Injective key)
    (domain : ZFSet.range key ∈ M.sets) (k : Nat)
    (fields : I → Fin (k + 1) → ZFSet.{u})
    (whole : familyCodeGraph key (fun i => nonemptyTupleCode k (fields i)) ∈ M.sets) :
    ∀ j, familyCodeGraph key (fun i => fields i j) ∈ M.sets := by
  induction k with
  | zero => exact Fin.cases whole (fun j => Fin.elim0 j)
  | succ k ih =>
    have both := M.familyCodeGraph_pair_projections pairing unions powers separation key
      (fun i => fields i 0) (fun i => nonemptyTupleCode k (fun j => fields i j.succ))
      injective domain whole
    exact Fin.cases both.1 (ih (fun i j => fields i j.succ) both.2)

end TransitiveGround

end PartitionPilot.Forcing

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Forcing_GroundVaryingFamilyEvaluation
attribute [-instance] _root_.OAI.PartitionPilot.Forcing.GroundMainPrefix.withTopSmall
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PartitionPilot.Forcing

open SetFormula
universe u v
variable {I : Type v} [Small.{u} I]

theorem TransitiveGround.familyCodeGraph_evaluation_ground (M : TransitiveGround.{u})
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (key arguments graphs values : I → ZFSet.{u}) (injective : Function.Injective key)
    (domain : ZFSet.range key ∈ M.sets)
    (argumentsGround : familyCodeGraph key arguments ∈ M.sets)
    (graphsGround : familyCodeGraph key graphs ∈ M.sets)
    (lookup : ∀ i y, ZFSet.pair (arguments i) y ∈ graphs i ↔ y = values i) :
    familyCodeGraph key values ∈ M.sets := by
  let Ss := familyCodeGraph key graphs
  let Es := familyCodeGraph key arguments
  let P := ZFSet.sUnion (ZFSet.sUnion Es)
  let V := ZFSet.sUnion (ZFSet.sUnion Ss)
  let L := ZFSet.sUnion (ZFSet.sUnion (ZFSet.sUnion V))
  let evaluated := familyEvaluationGraph (ZFSet.range key) P L V Ss Es
  have hP : P ∈ M.sets := M.union_mem unions (M.union_mem unions argumentsGround)
  have hV : V ∈ M.sets := M.union_mem unions (M.union_mem unions graphsGround)
  have hL : L ∈ M.sets := M.union_mem unions (M.union_mem unions (M.union_mem unions hV))
  have ground : evaluated ∈ M.sets :=
    M.familyEvaluationGraph_mem pairing unions powers separation domain hP hL hV graphsGround argumentsGround
  have graphFunction : ZFSet.IsFunc (ZFSet.range key) V Ss :=
    (familyCodeGraph_function key graphs injective).to_isFunc
  have argumentFunction : ZFSet.IsFunc (ZFSet.range key) P Es :=
    (familyCodeGraph_function key arguments injective).to_isFunc
  have valueBound (i : I) : values i ∈ L := by
    have stored : graphs i ∈ V :=
      pair_second_mem_doubleUnion ((pair_mem_familyCodeGraph key graphs injective i _).2 rfl)
    have entry : ZFSet.pair (arguments i) (values i) ∈ ZFSet.sUnion V :=
      ZFSet.mem_sUnion.2 ⟨graphs i, stored, (lookup i _).2 rfl⟩
    exact pair_second_mem_doubleUnion entry
  have entries (i : I) (y : ZFSet.{u}) : ZFSet.pair (key i) y ∈ evaluated ↔ y = values i := by
    rw [familyEvaluationGraph_entry_iff graphFunction argumentFunction
      ((pair_mem_familyCodeGraph key graphs injective i _).2 rfl)
      ((pair_mem_familyCodeGraph key arguments injective i _).2 rfl), lookup i y]
    exact ⟨And.right, fun equal => ⟨equal.symm ▸ valueBound i, equal⟩⟩
  have function : FunctionGraphOn (ZFSet.range key) evaluated := by
    refine ⟨L, fun _ hz => (ZFSet.mem_sep.1 hz).1, ?_⟩
    intro x hx
    obtain ⟨i, rfl⟩ := ZFSet.mem_range.1 hx
    exact ⟨values i, (entries i _).2 rfl, fun y hy => (entries i y).1 hy⟩
  exact familyCodeGraph_ground_of_entries ground function key values rfl (fun i => (entries i _).2 rfl)

end PartitionPilot.Forcing

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Geometry_DecodedMeetMaps
attribute [-instance] _root_.OAI.PartitionPilot.Forcing.GroundMainPrefix.withTopSmall
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PartitionPilot.Forcing

universe u

namespace MeetEmbeddingCode

variable {P L rP rL μP μL S : ZFSet.{u}}
variable (embedding : MeetEmbeddingCode P L rP rL μP μL S)

theorem value_eq_iff (x : {x : ZFSet.{u} // x ∈ P})
    (y : {y : ZFSet.{u} // y ∈ L}) :
    embedding.value x = y ↔ ZFSet.pair x.val y.val ∈ S := by
  constructor
  · intro equal
    exact equal ▸ embedding.value_entry x
  · intro entry
    exact Subtype.ext ((show FunctionGraphOn P S from
      ⟨L, embedding.injection.function⟩).unique (embedding.value_entry x) entry)

theorem toMeetEmbedding_eq_iff (source : MeetOrderCode P rP μP)
    (target : MeetOrderCode L rL μL) (x : {x : ZFSet.{u} // x ∈ P})
    (y : {y : ZFSet.{u} // y ∈ L}) :
    (embedding.toMeetEmbedding source target).toFun x = y ↔
      ZFSet.pair x.val y.val ∈ S := embedding.value_eq_iff x y

end MeetEmbeddingCode

end PartitionPilot.Forcing

end

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Definability_GroundRegularFormulas
attribute [-instance] _root_.OAI.PartitionPilot.Forcing.GroundMainPrefix.withTopSmall
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PartitionPilot.Forcing

section
open SetFormula
universe u

namespace SetFormula

def cumulativeLevelFormula {n} (a v : Fin n) : SetFormula n :=
  ex (.conj
    (reindex (extend a.succ (extend 0 Fin.elim0))
      (ordinalSuccessorTraceFormula cumulativeStepFormula))
    (BoundedFormula.pairMembershipFormula a.succ v.succ 0).toFormula)

def cumulativeRankLtFormula {n} (x a : Fin n) : SetFormula n :=
  ex (.conj (cumulativeLevelFormula a.succ 0) (.mem x.succ 0))
end SetFormula

end

section
open SetFormula SetRealization
universe u
namespace SetFormula

def cumulativeRankValueFormula {n} (x b : Fin n) : SetFormula n :=
  .conj (BoundedFormula.ordinalFormula b).toFormula
    (ex (.conj (BoundedFormula.successorFormula 0 b.succ).toFormula
      (.conj (cumulativeRankLtFormula x.succ 0)
        (.neg (cumulativeRankLtFormula x.succ b.succ)))))

def cumulativeRankEntryFormula {n} (z a k : Fin n) : SetFormula n :=
  ex (.conj (.mem 0 a.succ) (ex (.conj (.mem 0 k.succ.succ)
    (.conj (BoundedFormula.orderedPairFormula z.succ.succ 1 0).toFormula
      (cumulativeRankValueFormula 1 0)))))
end SetFormula

end

open SetFormula SetRealization
universe u

end PartitionPilot.Forcing

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Geometry_GroundRowDistinguishing
attribute [-instance] _root_.OAI.PartitionPilot.Forcing.GroundMainPrefix.withTopSmall
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PartitionPilot.Forcing

universe u

noncomputable def rowCoordinateDomain (I C Y p : ZFSet.{u}) : ZFSet.{u} :=
  relationImage p (ZFSet.prod I C) (productFirst (ZFSet.prod I C) Y)

noncomputable def rowUsedColumns (I C Y p : ZFSet.{u}) : ZFSet.{u} :=
  relationImage (rowCoordinateDomain I C Y p) C (productSecond I C)

end PartitionPilot.Forcing



end

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Forcing_GroundRowAssignmentActions
attribute [-instance] _root_.OAI.PartitionPilot.Forcing.GroundMainPrefix.withTopSmall
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open scoped ZFSet



namespace PartitionPilot.Forcing
open SetFormula
universe u

namespace TransitiveGround
variable (M : TransitiveGround.{u})

theorem rowAssignmentActionGraph_mem
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    {G Q C B J rowMaps assignmentMaps : ZFSet.{u}}
    (hG : G ∈ M.sets) (hQ : Q ∈ M.sets) (hC : C ∈ M.sets) (hB : B ∈ M.sets) (hJ : J ∈ M.sets)
    (hRows : rowMaps ∈ M.sets) (hAssignments : assignmentMaps ∈ M.sets) :
    rowAssignmentActionGraph G Q C B J rowMaps assignmentMaps ∈ M.sets := by
  have hRowRange := M.union_mem unions (M.union_mem unions hRows)
  have hAssignmentRange := M.union_mem unions (M.union_mem unions hAssignments)
  let params : Fin 9 → ZFSet.{u} :=
    ![G,Q,C,B,J,⋃₀ ⋃₀ rowMaps,⋃₀ ⋃₀ assignmentMaps,rowMaps,assignmentMaps]
  have members : ∀ j, params j ∈ M.sets := Fin.cases hG (Fin.cases hQ (Fin.cases hC
    (Fin.cases hB (Fin.cases hJ (Fin.cases hRowRange (Fin.cases hAssignmentRange
      (Fin.cases hRows (Fin.cases hAssignments (fun j => Fin.elim0 j)))))))))
  have selected := M.bounded_separation_mem separation
    (BoundedFormula.rowAssignmentActionEntryFormula 0 1 2 3 4 5 6 7 8 9) params members
    (M.prod_mem pairing unions powers separation (M.prod_mem pairing unions powers separation hG hQ) hQ)
  have equal : ZFSet.sep (fun z => BoundedFormula.Truth
      (BoundedFormula.rowAssignmentActionEntryFormula 0 1 2 3 4 5 6 7 8 9) (extend z params))
      (ZFSet.prod (ZFSet.prod G Q) Q) = rowAssignmentActionGraph G Q C B J rowMaps assignmentMaps := by
    apply ZFSet.ext
    intro z
    rw [ZFSet.mem_sep, rowAssignmentActionGraph, ZFSet.mem_sep,
      BoundedFormula.truth_rowAssignmentActionEntryFormula]
    rfl
  exact equal ▸ selected

end TransitiveGround

end PartitionPilot.Forcing

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Geometry_GroundRowAssignmentProjections
attribute [-instance] _root_.OAI.PartitionPilot.Forcing.GroundMainPrefix.withTopSmall
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PartitionPilot.Forcing
open SetFormula
universe u

noncomputable def rowAssignmentRows (Q C B : ZFSet.{u}) : ZFSet.{u} :=
  graphRestriction Q (productFirst C B)

noncomputable def rowAssignmentData (Q C B : ZFSet.{u}) : ZFSet.{u} :=
  graphRestriction Q (productSecond C B)

theorem rowAssignmentRows_entry (Q C B p A x : ZFSet.{u}) :
    ZFSet.pair (ZFSet.pair p A) x ∈ rowAssignmentRows Q C B ↔
      ZFSet.pair p A ∈ Q ∧ p ∈ C ∧ A ∈ B ∧ x = p := by
  rw [rowAssignmentRows, pair_mem_graphRestriction, mem_productFirst]
  constructor
  · rintro ⟨⟨q,hq,D,hD,equal⟩,member⟩
    obtain ⟨left,right⟩ := ZFSet.pair_injective equal
    obtain ⟨rfl,rfl⟩ := ZFSet.pair_injective left
    exact ⟨member,hq,hD,right⟩
  · rintro ⟨member,hp,hA,equal⟩
    subst x
    exact ⟨⟨p,hp,A,hA,rfl⟩,member⟩

theorem rowAssignmentData_entry (Q C B p A x : ZFSet.{u}) :
    ZFSet.pair (ZFSet.pair p A) x ∈ rowAssignmentData Q C B ↔
      ZFSet.pair p A ∈ Q ∧ p ∈ C ∧ A ∈ B ∧ x = A := by
  rw [rowAssignmentData, pair_mem_graphRestriction, mem_productSecond]
  constructor
  · rintro ⟨⟨q,hq,D,hD,equal⟩,member⟩
    obtain ⟨left,right⟩ := ZFSet.pair_injective equal
    obtain ⟨rfl,rfl⟩ := ZFSet.pair_injective left
    exact ⟨member,hq,hD,right⟩
  · rintro ⟨member,hp,hA,equal⟩
    subst x
    exact ⟨⟨p,hp,A,hA,rfl⟩,member⟩

theorem restrict_function {Q A B f : ZFSet.{u}}
    (function : ZFSet.IsFunc A B f) (subset : Q ⊆ A) :
    ZFSet.IsFunc Q B (graphRestriction Q f) := by
  refine ⟨?_, ?_⟩
  · intro z hz
    obtain ⟨x,hx,y,rfl,entry⟩ := mem_graphRestriction.1 hz
    exact ZFSet.pair_mem_prod.2 ⟨hx,(ZFSet.pair_mem_prod.1 (function.1 entry)).2⟩
  · intro x hx
    obtain ⟨y,entry,unique⟩ := function.2 x (subset hx)
    exact ⟨y,pair_mem_graphRestriction.2 ⟨entry,hx⟩,
      fun z hz => unique z (pair_mem_graphRestriction.1 hz).1⟩

theorem rowAssignmentRows_function {Q C B : ZFSet.{u}} (subset : Q ⊆ ZFSet.prod C B) :
    ZFSet.IsFunc Q C (rowAssignmentRows Q C B) :=
  restrict_function (productFirst_function C B) subset

theorem rowAssignmentData_function {Q C B : ZFSet.{u}} (subset : Q ⊆ ZFSet.prod C B) :
    ZFSet.IsFunc Q B (rowAssignmentData Q C B) :=
  restrict_function (productSecond_function C B) subset

end PartitionPilot.Forcing

end

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Forcing_GroundFlatSuccessorFullActionGraph
attribute [-instance] _root_.OAI.PartitionPilot.Forcing.GroundMainPrefix.withTopSmall
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PartitionPilot.Forcing.TransitiveGround

open SetRealization SetFormula
universe u
variable (M : TransitiveGround.{u}) {X Y G : Type u} [Group G] [PartialOrder X]
variable (a : PosetAction G X) (s : Presentation X) (t : Presentation Y) (b : Presentation G)
variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
variable (unions : Realize M.sets SetFormula.union Fin.elim0)
variable (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
variable {N : ZFSet.{u}} (hX : s.carrier ∈ M.sets) (hY : t.carrier ∈ M.sets)
variable (hG : b.carrier ∈ M.sets) (hN : N ∈ M.sets) (graph : a.actionGraph s b ∈ M.sets)

noncomputable def smallFunctionAction :
    letI := M.smallFunctionOrder s.carrier t.carrier N
    PosetAction G (SetMembers (M.smallPartialFunctions s.carrier t.carrier N)) := by
  letI := M.smallFunctionOrder s.carrier t.carrier N
  have maps (g : G) : s.graph s (a.iso g).toEquiv ∈ M.sets :=
    M.actionGraph_section_mem a s b pairing unions powers separation hX graph g
      (M.transitive hG (b.encode_mem g))
  let iso (g : G) := M.renameSmallOrderIso s t pairing unions powers separation hX hY hN
    (a.iso g).toEquiv (maps g)
  have raw (g : G) (p : SetMembers (M.smallPartialFunctions s.carrier t.carrier N)) :
      SetMembers.raw (iso g p) = graphRename s t (a.iso g).toEquiv (SetMembers.raw p) :=
    M.raw_renameSmallOrderIso s t pairing unions powers separation hX hY hN (a.iso g).toEquiv (maps g) p
  exact {
    iso := iso
    one := by
      intro p
      apply SetMembers.raw_injective
      rw [raw]
      have eq : (a.iso 1).toEquiv = Equiv.refl X := by
        apply Equiv.ext
        exact a.one
      rw [eq]
      exact graphRename_refl s t (M.smallFunction_raw_properties s.carrier t.carrier N p).2.1.shape
    mul := by
      intro g h p
      apply SetMembers.raw_injective
      rw [raw, raw, raw]
      have eq : (a.iso (g * h)).toEquiv = (a.iso h).toEquiv.trans (a.iso g).toEquiv := by
        apply Equiv.ext
        exact a.mul g h
      rw [eq]
      exact (graphRename_comp s t (a.iso h).toEquiv (a.iso g).toEquiv (SetMembers.raw p)).symm }

theorem raw_smallFunctionAction (g : G) (p : SetMembers (M.smallPartialFunctions s.carrier t.carrier N)) :
    letI := M.smallFunctionOrder s.carrier t.carrier N
    SetMembers.raw ((M.smallFunctionAction a s t b pairing unions powers separation hX hY hG hN graph).iso g p) =
      graphRename s t (a.iso g).toEquiv (SetMembers.raw p) := SetMembers.raw_ofMem _ _

end PartitionPilot.Forcing.TransitiveGround

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Forcing_GroundOutsideRowNames
attribute [-instance] _root_.OAI.PartitionPilot.Forcing.GroundMainPrefix.withTopSmall
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace PartitionPilot.Forcing.TransitiveGround

open SetRealization SetFormula
universe u
variable (M : TransitiveGround.{u}) {X Y G : Type u} [Group G] [PartialOrder X]
variable (a : PosetAction G X) (s : Presentation X) (t : Presentation Y) (b : Presentation G)
variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
variable (unions : Realize M.sets SetFormula.union Fin.elim0)
variable (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
variable {N : ZFSet.{u}} (hX : s.carrier ∈ M.sets) (hY : t.carrier ∈ M.sets)
variable (hG : b.carrier ∈ M.sets) (hN : N ∈ M.sets) (graph : a.actionGraph s b ∈ M.sets)

theorem smallFunctionActionGraph_mem :
    letI := M.smallFunctionOrder s.carrier t.carrier N
    (M.smallFunctionAction a s t b pairing unions powers separation hX hY hG hN graph).actionGraph
      (SetMembers.presentation (M.smallPartialFunctions s.carrier t.carrier N)) b ∈ M.sets := by
  let := M.smallFunctionOrder s.carrier t.carrier N
  let act := M.smallFunctionAction a s t b pairing unions powers separation hX hY hG hN graph
  let c := SetMembers.presentation (M.smallPartialFunctions s.carrier t.carrier N)
  have carrier := M.smallPartialFunctions_mem pairing unions powers separation hX hY hN
  have bound := M.prod_mem pairing unions powers separation
    (M.prod_mem pairing unions powers separation hG carrier) carrier
  let params := extend b.carrier (extend c.carrier (extend s.carrier (extend t.carrier
    (extend (a.actionGraph s b) Fin.elim0))))
  have members : ∀ i, params i ∈ M.sets :=
    Fin.cases hG (Fin.cases carrier (Fin.cases hX (Fin.cases hY (Fin.cases graph (fun i => Fin.elim0 i)))))
  have correct (z : ZFSet.{u}) :
      BoundedFormula.Truth (BoundedFormula.smallActionEntryFormula 0 1 2 3 4 5) (extend z params) ↔
        z ∈ act.actionGraph c b := by
    rw [BoundedFormula.truth_smallActionEntryFormula]
    change (∃ g ∈ b.carrier, ∃ p ∈ c.carrier, ∃ q ∈ c.carrier,
      z = ZFSet.pair (ZFSet.pair g p) q ∧
        RenameActionRelation s.carrier t.carrier (a.actionGraph s b) g p q) ↔ _
    constructor
    · rintro ⟨g, hg, p, hp, q, hq, eq, relation⟩
      obtain ⟨g', rfl⟩ := (b.mem_carrier g).1 hg
      obtain ⟨p', rfl⟩ := (c.mem_carrier p).1 hp
      obtain ⟨q', rfl⟩ := (c.mem_carrier q).1 hq
      rw [eq]
      apply (act.triple_mem_actionGraph c b g' p' q').2
      apply SetMembers.raw_injective
      rw [M.raw_smallFunctionAction]
      exact (renameActionRelation_iff a s t b g'
        (M.smallFunction_raw_properties s.carrier t.carrier N q').2.1.shape).1 relation
    · intro hz
      obtain ⟨⟨g, p⟩, eq⟩ := ((b.product c).mem_graph c (fun x => act.iso x.1 x.2) z).1 hz
      refine ⟨b.encode g, b.encode_mem g, c.encode p, c.encode_mem p,
        c.encode (act.iso g p), c.encode_mem (act.iso g p), eq.symm, ?_⟩
      apply (renameActionRelation_iff a s t b g
        (M.smallFunction_raw_properties s.carrier t.carrier N (act.iso g p)).2.1.shape).2
      exact (M.raw_smallFunctionAction a s t b pairing unions powers separation hX hY hG hN graph g p).symm
  have selected := M.bounded_separation_mem separation (BoundedFormula.smallActionEntryFormula 0 1 2 3 4 5)
    params members bound
  have eq : ZFSet.sep (fun z => BoundedFormula.Truth (BoundedFormula.smallActionEntryFormula 0 1 2 3 4 5)
      (extend z params)) (ZFSet.prod (ZFSet.prod b.carrier c.carrier) c.carrier) = act.actionGraph c b := by
    apply ZFSet.ext
    intro z
    rw [ZFSet.mem_sep]
    exact ⟨fun h => (correct z).1 h.2,
      fun hz => ⟨((b.product c).graph_isFunc c (fun x => act.iso x.1 x.2)).1 hz, (correct z).2 hz⟩⟩
  exact eq ▸ selected

end PartitionPilot.Forcing.TransitiveGround



namespace PartitionPilot.Forcing

universe u

noncomputable def rowUsedRows (I C Y p : ZFSet.{u}) : ZFSet.{u} :=
  relationImage (rowCoordinateDomain I C Y p) I (productFirst I C)

end PartitionPilot.Forcing



namespace PartitionPilot.Forcing

open SetRealization
universe u

noncomputable def rowCoordinatePresentation {L : Type u} [Bot L]
    (s : Presentation L) (C : ZFSet.{u}) :
    Presentation ({i : L // i ≠ ⊥} × SetMembers C) :=
  s.nonbottom.product (SetMembers.presentation C)

namespace PosetAction

variable {G L : Type u} [Group G] [PartialOrder L] [OrderBot L]

noncomputable def rowCoordinates (a : PosetAction G L) (C : ZFSet.{u}) :
    letI := columnOrder C
    PosetAction G ({i : L // i ≠ ⊥} × SetMembers C) := by
  letI := columnOrder C
  exact a.nonbottom.productColumns (SetMembers C)

end PosetAction

namespace TransitiveGround

open SetFormula
variable (M : TransitiveGround.{u})

theorem rowCoordinate_carrier_mem {L : Type u} [Bot L]
    (s : Presentation L) (C : ZFSet.{u})
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (hL : s.carrier ∈ M.sets) (hC : C ∈ M.sets) :
    (rowCoordinatePresentation s C).carrier ∈ M.sets :=
  M.prod_mem pairing unions powers separation (M.nonbottom_carrier_mem s separation hL) hC

theorem rowCoordinate_graph_mem {G L : Type u} [Group G] [PartialOrder L] [OrderBot L]
    (a : PosetAction G L) (s : Presentation L) (b : Presentation G) (C : ZFSet.{u})
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (hL : s.carrier ∈ M.sets) (hC : C ∈ M.sets) (hG : b.carrier ∈ M.sets)
    (graph : a.actionGraph s b ∈ M.sets) :
    letI := columnOrder C
    (a.rowCoordinates C).actionGraph (rowCoordinatePresentation s C) b ∈ M.sets := by
  let := columnOrder C
  exact M.productColumns_actionGraph_mem a.nonbottom s.nonbottom (SetMembers.presentation C) b
    pairing unions powers separation (M.nonbottom_carrier_mem s separation hL) hC hG
    (M.nonbottom_actionGraph_mem a s b separation hL hG graph)

variable {G L : Type u} [Group G] [PartialOrder L] [OrderBot L]
variable (a : PosetAction G L) (s : Presentation L) (b : Presentation G) (C : ZFSet.{u})
variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
variable (unions : Realize M.sets SetFormula.union Fin.elim0)
variable (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
variable (infinite : Realize M.sets infinity Fin.elim0)
variable (hL : s.carrier ∈ M.sets) (hC : C ∈ M.sets) (hG : b.carrier ∈ M.sets)
variable (graph : a.actionGraph s b ∈ M.sets)

noncomputable def internalRowAction :
    letI := M.smallFunctionOrder (ZFSet.prod s.nonbottom.carrier C) (natSetCode 2) ZFSet.omega
    PosetAction G (SetMembers
      (M.smallPartialFunctions (ZFSet.prod s.nonbottom.carrier C) (natSetCode 2) ZFSet.omega)) := by
  letI := columnOrder C
  letI := M.smallFunctionOrder (ZFSet.prod s.nonbottom.carrier C) (natSetCode 2) ZFSet.omega
  exact M.smallFunctionAction (a.rowCoordinates C) (rowCoordinatePresentation s C)
    (natInitialPresentation 2) b pairing unions powers separation
    (M.rowCoordinate_carrier_mem s C pairing unions powers separation hL hC)
    (M.natSetCode_mem separation infinite 2) hG (M.omega_mem separation infinite)
    (M.rowCoordinate_graph_mem a s b C pairing unions powers separation hL hC hG graph)

theorem internalRowActionGraph_mem :
    letI := M.smallFunctionOrder (ZFSet.prod s.nonbottom.carrier C) (natSetCode 2) ZFSet.omega
    (M.internalRowAction a s b C pairing unions powers separation infinite hL hC hG graph).actionGraph
      (SetMembers.presentation
        (M.smallPartialFunctions (ZFSet.prod s.nonbottom.carrier C) (natSetCode 2) ZFSet.omega)) b ∈
          M.sets := by
  let := columnOrder C
  let := M.smallFunctionOrder (ZFSet.prod s.nonbottom.carrier C) (natSetCode 2) ZFSet.omega
  exact M.smallFunctionActionGraph_mem (a.rowCoordinates C) (rowCoordinatePresentation s C)
    (natInitialPresentation 2) b pairing unions powers separation
    (M.rowCoordinate_carrier_mem s C pairing unions powers separation hL hC)
    (M.natSetCode_mem separation infinite 2) hG (M.omega_mem separation infinite)
    (M.rowCoordinate_graph_mem a s b C pairing unions powers separation hL hC hG graph)

end TransitiveGround

end PartitionPilot.Forcing



namespace PartitionPilot.Forcing.TransitiveGround

open SetRealization SetFormula
universe u
variable (M : TransitiveGround.{u}) {L G : Type u}
variable [Group G] [PartialOrder L] [OrderBot L]

noncomputable def internalRowName (s : Presentation L) (C : ZFSet.{u})
    (hL : s.carrier ∈ M.sets) (i : {i : L // i ≠ ⊥}) :
    Name (SetMembers.presentation (M.smallPartialFunctions
      (ZFSet.prod s.nonbottom.carrier C) (natSetCode 2) ZFSet.omega)) := by
  letI := M.smallFunctionOrder (ZFSet.prod s.nonbottom.carrier C) (natSetCode 2) ZFSet.omega
  letI := M.smallFunctionTop (ZFSet.prod s.nonbottom.carrier C) (natSetCode 2) ZFSet.omega
    ⟨s.carrier, hL⟩
  exact M.binaryRowName s.nonbottom.carrier C ⊤ (s.encode i.val)

end PartitionPilot.Forcing.TransitiveGround



namespace PartitionPilot.Forcing.TransitiveGround

open SetRealization SetFormula
universe u
variable (M : TransitiveGround.{u}) {L G : Type u}
variable [Group G] [PartialOrder L] [OrderBot L]

noncomputable def internalRowSetName (s : Presentation L) (C : ZFSet.{u})
    (hL : s.carrier ∈ M.sets) :
    Name (SetMembers.presentation (M.smallPartialFunctions
      (ZFSet.prod s.nonbottom.carrier C) (natSetCode 2) ZFSet.omega)) := by
  letI := M.smallFunctionOrder (ZFSet.prod s.nonbottom.carrier C) (natSetCode 2) ZFSet.omega
  letI := M.smallFunctionTop (ZFSet.prod s.nonbottom.carrier C) (natSetCode 2) ZFSet.omega
    ⟨s.carrier, hL⟩
  exact M.binaryRowSetName s.nonbottom.carrier C ⊤

end PartitionPilot.Forcing.TransitiveGround



namespace PartitionPilot.Forcing

open SetRealization
universe u

noncomputable def outsideRowIndices {L : Type u} [PartialOrder L] [OrderBot L]
    (s : Presentation L) (B : L) : ZFSet.{u} :=
  ZFSet.sep (fun x => ZFSet.pair x (s.encode B) ∉ s.conditionOrder) s.nonbottom.carrier

namespace TransitiveGround

open SetFormula
variable (M : TransitiveGround.{u})

noncomputable def binaryRowSubsetName (I C : ZFSet.{u})
    (one : SetMembers (M.smallPartialFunctions (ZFSet.prod I C) (natSetCode 2) ZFSet.omega))
    (J : ZFSet.{u}) :
    Name (SetMembers.presentation (M.smallPartialFunctions (ZFSet.prod I C) (natSetCode 2) ZFSet.omega)) :=
  Name.assemble (fun i : SetMembers J => M.binaryRowName I C one (SetMembers.raw i)) (fun _ => one)

variable {L G : Type u} [Group G] [PartialOrder L] [OrderBot L]

noncomputable def internalOutsideRowsName (s : Presentation L) (C : ZFSet.{u})
    (hL : s.carrier ∈ M.sets) (B : L) :
    Name (SetMembers.presentation (M.smallPartialFunctions
      (ZFSet.prod s.nonbottom.carrier C) (natSetCode 2) ZFSet.omega)) := by
  letI := M.smallFunctionOrder (ZFSet.prod s.nonbottom.carrier C) (natSetCode 2) ZFSet.omega
  letI := M.smallFunctionTop (ZFSet.prod s.nonbottom.carrier C) (natSetCode 2) ZFSet.omega
    ⟨s.carrier, hL⟩
  exact M.binaryRowSubsetName s.nonbottom.carrier C ⊤ (outsideRowIndices s B)

end TransitiveGround

end PartitionPilot.Forcing

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Forcing_GroundPrincipalSupportZF
attribute [-instance] _root_.OAI.PartitionPilot.Forcing.GroundMainPrefix.withTopSmall
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PartitionPilot.Forcing.TransitiveGround

open SetRealization SetFormula
universe u
variable (M : TransitiveGround.{u}) {G I : Type u} [Group G] [PartialOrder I]
variable (d : PosetAction G I) (b : Presentation I) (t : Presentation G)

theorem realize_principalSupportEntry (z : ZFSet.{u}) (hz : z ∈ M.sets)
    (nodes : b.carrier ∈ M.sets) (group : t.carrier ∈ M.sets)
    (order : b.conditionOrder ∈ M.sets) (graph : d.actionGraph b t ∈ M.sets) :
    Realize M.sets (BoundedFormula.principalSupportEntryFormula 0 1 2 3 4).toFormula
      (extend z (extend b.carrier (extend t.carrier
        (extend b.conditionOrder (extend (d.actionGraph b t) Fin.elim0))))) ↔
      z ∈ supportBasisCode b t d.principalFix :=
  (BoundedFormula.realize_toFormula M _ _ (Fin.cases hz (Fin.cases nodes (Fin.cases group
    (Fin.cases order (Fin.cases graph (fun j => Fin.elim0 j))))))).trans
      (BoundedFormula.principalSupportEntry_correct d b t z)

theorem principalSupportBasis_mem
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (nodes : b.carrier ∈ M.sets) (group : t.carrier ∈ M.sets)
    (order : b.conditionOrder ∈ M.sets) (graph : d.actionGraph b t ∈ M.sets) :
    supportBasisCode b t d.principalFix ∈ M.sets := by
  obtain ⟨B, hB, bounds⟩ := M.exists_pair_bound pairing unions powers nodes group
  let params := extend b.carrier (extend t.carrier
    (extend b.conditionOrder (extend (d.actionGraph b t) Fin.elim0)))
  have selected := M.separation_mem separation (BoundedFormula.principalSupportEntryFormula 0 1 2 3 4).toFormula
    params (Fin.cases nodes (Fin.cases group (Fin.cases order (Fin.cases graph (fun j => Fin.elim0 j))))) hB
  have eq : ZFSet.sep (fun z => Realize M.sets
      (BoundedFormula.principalSupportEntryFormula 0 1 2 3 4).toFormula (extend z params)) B =
        supportBasisCode b t d.principalFix := by
    apply ZFSet.ext
    intro z
    rw [ZFSet.mem_sep]
    constructor
    · rintro ⟨hz, rel⟩
      exact (M.realize_principalSupportEntry d b t z (M.transitive hB hz) nodes group order graph).1 rel
    · intro hz
      have hzB : z ∈ B := by
        obtain ⟨⟨C, g⟩, _, eq⟩ := ((b.product t).mem_subset (fun z => z.2 ∈ d.principalFix z.1) z).1 hz
        exact eq ▸ bounds _ (b.encode_mem C) _ (t.encode_mem g)
      exact ⟨hzB, (M.realize_principalSupportEntry d b t z (M.transitive hB hzB) nodes group order graph).2 hz⟩
  exact eq ▸ selected

end PartitionPilot.Forcing.TransitiveGround

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Geometry_GroundFamilyValueUnions
attribute [-instance] _root_.OAI.PartitionPilot.Forcing.GroundMainPrefix.withTopSmall
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PartitionPilot.Forcing
open SetFormula
universe u v
variable {I : Type v} [Small.{u} I]

theorem TransitiveGround.familyCodeGraph_valueRange_mem (M : TransitiveGround.{u})
    (unions : Realize M.sets SetFormula.union Fin.elim0) (separation : SeparationSchema M.sets)
    (key value : I → ZFSet.{u}) (domain : ZFSet.range key ∈ M.sets)
    (whole : familyCodeGraph key value ∈ M.sets) : ZFSet.range value ∈ M.sets := by
  rw [familyCodeGraph_valueRange_eq key value]
  exact M.relationImage_mem separation domain (M.union_mem unions (M.union_mem unions whole)) whole

end PartitionPilot.Forcing

end

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Forcing_GroundNiceSupportEvaluation
attribute [-instance] _root_.OAI.PartitionPilot.Forcing.GroundMainPrefix.withTopSmall
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PartitionPilot.Forcing.TransitiveGround
open SetRealization SetFormula
universe u
variable (M : TransitiveGround.{u}) {I G P : Type u}
variable [Group G] [PartialOrder P]
variable (a : PosetAction G P) (s : Presentation P)
variable (T : ZFSet.{u}) (K : I → Subgroup G)

theorem codeFunction (N : ZFSet.{u}) : FunctionGraphOn N (identityFunctionGraph N) :=
  ⟨N, (identityFunctionGraph_injection N).function⟩

theorem codeValue (N : ZFSet.{u}) (i : N.toSet) :
    (codeFunction N).value i = i.val :=
  (codeFunction N).value_eq_of_entry i
    ((pair_mem_identityFunctionGraph N i.val i.val).2 ⟨rfl, i.property⟩)

theorem codeIsName (i : (M.niceSupportNameCodes a s T K).toSet) :
    IsName s ((codeFunction (M.niceSupportNameCodes a s T K)).value i) := by
  rw [codeValue]
  exact M.niceSupportNameCodes_valid a s T K i.val i.property

variable [OrderTop P]

noncomputable def niceSupportEvaluationName : Name s :=
  Name.indexedGraphName ⊤ (codeFunction (M.niceSupportNameCodes a s T K))
    (codeIsName M a s T K)

end PartitionPilot.Forcing.TransitiveGround

end

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Forcing_ActiveNameImageSymmetry
attribute [-instance] _root_.OAI.PartitionPilot.Forcing.GroundMainPrefix.withTopSmall
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI



namespace PartitionPilot.Forcing
open SetRealization SetFormula
universe u

namespace SetFormula

def activeNameImageEntryFormula : SetFormula 6 :=
  ex (ex (ex (.conj (.mem 2 4) (.conj (.mem 0 7)
    (.conj (orderedPairFormula 3 1 0)
      (.conj (pairMembershipFormula 2 1 6)
        (forcingTranslation (ordinaryGroundPrimitives 0 1) (.mem 0 1)
          ![7, 8] 0 ![2, 5])))))))

end SetFormula

end PartitionPilot.Forcing

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Definability_GroundAssignmentClassGraphs
attribute [-instance] _root_.OAI.PartitionPilot.Forcing.GroundMainPrefix.withTopSmall
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PartitionPilot.Forcing
open SetRealization SetFormula
universe u

def assignmentClassGraphFormula (side : Fin 2) : SetFormula 7 :=
  let w := prefixIndex 7 6
  let old := suffixIndex 7 6
  let representative := Fin.cases (w 3) (fun _ => w 4) side
  exBlock 6 (.conj (.mem (w 0) (old 1))
    (.conj (BoundedFormula.orderedPairFormula (old 0) (w 0) (w 1)).toFormula
      (.conj (BoundedFormula.stageOneAssignmentFormula (w 0) (w 2) (w 3) (w 4)).toFormula
        (.conj (BoundedFormula.pairMembershipFormula (w 2) (w 5) (old 2)).toFormula
          (reindex ![w 1, old 3, w 5, representative, old 4, old 5, old 6]
            refinementClassCodeFormula)))))

namespace TransitiveGround
variable (M : TransitiveGround.{u})

noncomputable def assignmentClassGraph (side : Fin 2)
    (A field T P order top : ZFSet.{u}) : ZFSet.{u} :=
  ZFSet.sep (fun z => Realize M.sets (assignmentClassGraphFormula side)
    (extend z ![A, field, T, P, order, top])) (ZFSet.prod A (M.groundRelations T P))

end TransitiveGround

namespace SetFormula

def refinementMapEntryFormula : SetFormula 8 :=
  ex (ex (ex (ex (ex (.conj (.mem 4 6) (.conj (.mem 0 10)
    (.conj (orderedPairFormula 5 1 0)
      (.conj (reindex ![3, 6, 8, 4, 10, 11, 12] refinementClassCodeFormula)
        (.conj (reindex ![2, 6, 9, 4, 10, 11, 12] refinementClassCodeFormula)
          (.conj (orderedPairNameCodeFormula 1 3 2 12)
            (forcingTranslation (ordinaryGroundPrimitives 0 1) (.mem 0 1)
              ![10, 11] 0 ![4, 7])))))))))))

def refinementMapCodeFormula : SetFormula 8 :=
  exactSetFormula 0 (reindex (extend 0 (fun j : Fin 7 => j.succ.succ)) refinementMapEntryFormula)

end SetFormula

namespace SetFormula

def refinementQuotientEntryFormula : SetFormula 7 :=
  ex (ex (ex (.conj (.mem 2 4) (.conj (.mem 0 7)
    (.conj (orderedPairFormula 3 1 0)
      (.conj (reindex ![1, 4, 6, 2, 7, 8, 9] refinementClassCodeFormula)
        (forcingTranslation (ordinaryGroundPrimitives 0 1) (.mem 0 1)
          ![7, 8] 0 ![2, 5])))))))

def refinementQuotientCodeFormula : SetFormula 7 :=
  exactSetFormula 0 (reindex (extend 0 (fun j : Fin 6 => j.succ.succ)) refinementQuotientEntryFormula)

end SetFormula
end PartitionPilot.Forcing

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Geometry_AssignmentIndexLevels
attribute [-instance] _root_.OAI.PartitionPilot.Forcing.GroundMainPrefix.withTopSmall
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PartitionPilot.Forcing
universe u

noncomputable def assignmentIndexLevels (I T eta levels : ZFSet.{u}) : ZFSet.{u} :=
  relationCompose (stageOneAssignments I T) I eta
    (productFirst I (ZFSet.prod T T)) levels

theorem pair_mem_assignmentIndexLevels (I T eta levels z level : ZFSet.{u}) :
    ZFSet.pair z level ∈ assignmentIndexLevels I T eta levels ↔
      ∃ i ∈ I, ∃ u ∈ T, ∃ w ∈ T,
        z = stageOneAssignment i u w ∧ level ∈ eta ∧ ZFSet.pair i level ∈ levels := by
  rw [assignmentIndexLevels, pair_mem_relationCompose]
  constructor
  · rintro ⟨_, hl, i, hi, projection, entry⟩
    obtain ⟨j, _, rest, hr, equal⟩ := (mem_productFirst I (ZFSet.prod T T) _).1 projection
    obtain ⟨hz, hji⟩ := ZFSet.pair_inj.1 equal
    obtain ⟨u, hu, w, hw, rfl⟩ := ZFSet.mem_prod.1 hr
    exact ⟨i, hi, u, hu, w, hw, hji ▸ hz, hl, entry⟩
  · rintro ⟨i, hi, u, hu, w, hw, rfl, hl, entry⟩
    refine ⟨(stageOneAssignment_mem_assignments I T i u w).2 ⟨hi, hu, hw⟩,
      hl, i, hi, ?_, entry⟩
    exact (mem_productFirst I (ZFSet.prod T T) _).2
      ⟨i, hi, ZFSet.pair u w, ZFSet.pair_mem_prod.2 ⟨hu, hw⟩, rfl⟩

theorem assignmentIndexLevels_entry (I T eta levels i u w level : ZFSet.{u}) :
    ZFSet.pair (stageOneAssignment i u w) level ∈ assignmentIndexLevels I T eta levels ↔
      i ∈ I ∧ u ∈ T ∧ w ∈ T ∧ level ∈ eta ∧ ZFSet.pair i level ∈ levels := by
  rw [pair_mem_assignmentIndexLevels]
  constructor
  · rintro ⟨j, hj, v, hv, x, hx, equal, hl, entry⟩
    obtain ⟨rfl, rfl, rfl⟩ := (stageOneAssignment_eq_iff i u w j v x).1 equal
    exact ⟨hj, hv, hx, hl, entry⟩
  · rintro ⟨hi, hu, hw, hl, entry⟩
    exact ⟨i, hi, u, hu, w, hw, rfl, hl, entry⟩

theorem assignmentIndexLevels_function {I T eta levels : ZFSet.{u}}
    (function : ZFSet.IsFunc I eta levels) :
    ZFSet.IsFunc (stageOneAssignments I T) eta (assignmentIndexLevels I T eta levels) := by
  refine ⟨?_, ?_⟩
  · intro z hz
    rw [assignmentIndexLevels, relationCompose] at hz
    exact (ZFSet.mem_sep.1 hz).1
  · intro z hz
    obtain ⟨i, hi, u, hu, w, hw, rfl⟩ := (mem_stageOneAssignments I T z).1 hz
    obtain ⟨level, entry, unique⟩ := function.2 i hi
    have hl := (ZFSet.pair_mem_prod.1 (function.1 entry)).2
    refine ⟨level, (assignmentIndexLevels_entry I T eta levels i u w level).2
      ⟨hi, hu, hw, hl, entry⟩, ?_⟩
    intro other ho
    exact unique other ((assignmentIndexLevels_entry I T eta levels i u w other).1 ho).2.2.2.2

end PartitionPilot.Forcing

end

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Forcing_GroundRefinementValidityForcing
attribute [-instance] _root_.OAI.PartitionPilot.Forcing.GroundMainPrefix.withTopSmall
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PartitionPilot.Forcing
open SetRealization SetFormula
universe u

namespace SetFormula

def refinementValidityForcingFormula {n : Nat}
    (U Rf Rc T carrier order condition : Fin n) : SetFormula n :=
  forcingTranslation (ordinaryGroundPrimitives (0 : Fin 2) 1)
    BoundedFormula.refinementValidityFormula.toFormula
    (extend carrier (extend order Fin.elim0)) condition
    (extend U (extend Rf (extend Rc (extend T Fin.elim0))))

end SetFormula

end PartitionPilot.Forcing

end

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Definability_GroundSelectedSupportTupleFamilies
attribute [-instance] _root_.OAI.PartitionPilot.Forcing.GroundMainPrefix.withTopSmall
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open scoped ZFSet


namespace PartitionPilot.Forcing.TransitiveGround
open SetRealization SetFormula
universe u
variable (M : TransitiveGround.{u}) {L G : Type u}
variable [Group G] [PartialOrder L] [OrderBot L]

noncomputable def internalRowTupleName (s : Presentation L) (C : ZFSet.{u})
    (hL : s.carrier ∈ M.sets) (δ : ZFSet.{u}) (positions : δ.toSet → {i : L // i ≠ ⊥}) :
    Name (SetMembers.presentation (M.smallPartialFunctions
      (ZFSet.prod s.nonbottom.carrier C) (natSetCode 2) ZFSet.omega)) := by
  letI := M.smallFunctionOrder (ZFSet.prod s.nonbottom.carrier C) (natSetCode 2) ZFSet.omega
  letI := M.smallFunctionTop (ZFSet.prod s.nonbottom.carrier C) (natSetCode 2) ZFSet.omega
    ⟨s.carrier, hL⟩
  exact Name.indexedTuple ⊤ δ (fun i => M.internalRowName s C hL (positions i))

end PartitionPilot.Forcing.TransitiveGround



namespace PartitionPilot.Forcing.TransitiveGround
open SetRealization SetFormula
universe u
variable (M : TransitiveGround.{u})

noncomputable def binaryRowNameGraph (I C : ZFSet.{u})
    (one : SetMembers (M.smallPartialFunctions (ZFSet.prod I C) (natSetCode 2) ZFSet.omega)) : ZFSet.{u} :=
  ZFSet.range (fun i : I => ZFSet.pair i.val (M.binaryRowName I C one i.val).val)

end PartitionPilot.Forcing.TransitiveGround



namespace PartitionPilot.Forcing
open SetFormula SetRealization
universe u

noncomputable def rowTupleTerms (one mu I W rows S : ZFSet.{u}) : ZFSet.{u} :=
  functionGraphRange S (rowTupleFamily one mu I W rows S)

end PartitionPilot.Forcing



end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Forcing_RenamedPairNameFamilies
attribute [-instance] _root_.OAI.PartitionPilot.Forcing.GroundMainPrefix.withTopSmall
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PartitionPilot.Forcing.Name
open SetRealization
universe u
variable {P Q : Type u} {s : Presentation P}

noncomputable def renamedFamily (t : Presentation Q) (f : P → Q)
    (T : ZFSet.{u}) (valid : ∀ x ∈ T, IsName s x) : ZFSet.{u} :=
  functionGraphRange T (renameFamilyGraph t f T valid)

theorem mem_renamedFamily (t : Presentation Q) (f : P → Q)
    (T : ZFSet.{u}) (valid : ∀ x ∈ T, IsName s x) (y : ZFSet.{u}) :
    y ∈ renamedFamily t f T valid ↔ ∃ σ : Name s, σ.val ∈ T ∧ y = (rename t f σ).val := by
  rw [renamedFamily, mem_functionGraphRange]
  constructor
  · rintro ⟨x, hx, entry⟩
    let σ : Name s := ⟨x, valid x hx⟩
    exact ⟨σ, hx, ((pair_mem_renameFamilyGraph t f T valid σ y).1 entry).2⟩
  · rintro ⟨σ, hσ, equal⟩
    exact ⟨σ.val, hσ, (pair_mem_renameFamilyGraph t f T valid σ y).2 ⟨hσ, equal⟩⟩

end PartitionPilot.Forcing.Name

end

namespace PartitionPilot.Forcing.Name
open SetRealization Compression.RecursiveMaps
universe u v
variable {P Q : Type u} {s : Presentation P}

theorem renamedFamily_valid (t : Presentation Q) (f : P → Q)
    (T : ZFSet.{u}) (valid : ∀ x ∈ T, IsName s x) :
    ∀ y ∈ renamedFamily t f T valid, IsName t y := by
  intro y hy
  obtain ⟨σ, _, rfl⟩ := (mem_renamedFamily t f T valid y).1 hy
  exact (rename t f σ).property

end PartitionPilot.Forcing.Name

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Definability_GroundLiftedRowTupleProvenance
attribute [-instance] _root_.OAI.PartitionPilot.Forcing.GroundMainPrefix.withTopSmall
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open scoped ZFSet

namespace PartitionPilot.Forcing
open SetRealization SetFormula
universe u

namespace TransitiveGround

theorem pairedGraph_mem (M : TransitiveGround.{u})
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    {L H K f g : ZFSet.{u}} (hL : L ∈ M.sets) (hH : H ∈ M.sets) (hK : K ∈ M.sets)
    (hf : f ∈ M.sets) (hg : g ∈ M.sets) : pairedGraph L H K f g ∈ M.sets := by
  let params := extend L (extend H (extend K (extend f (extend g Fin.elim0))))
  have selected := M.bounded_separation_mem separation (BoundedFormula.pairedGraphEntryFormula 0 1 2 3 4 5)
    params (Fin.cases hL (Fin.cases hH (Fin.cases hK (Fin.cases hf (Fin.cases hg (fun i => Fin.elim0 i))))))
    (M.prod_mem pairing unions powers separation hL (M.prod_mem pairing unions powers separation hH hK))
  have equal : ZFSet.sep (fun z => BoundedFormula.Truth
      (BoundedFormula.pairedGraphEntryFormula 0 1 2 3 4 5) (extend z params))
      (ZFSet.prod L (ZFSet.prod H K)) = pairedGraph L H K f g := by
    apply ZFSet.ext
    intro z
    rw [ZFSet.mem_sep, BoundedFormula.truth_pairedGraphEntryFormula]
    exact ⟨And.right, fun hz => ⟨(ZFSet.mem_sep.1 hz).1, hz⟩⟩
  exact equal ▸ selected

end TransitiveGround

end PartitionPilot.Forcing

namespace PartitionPilot.Forcing
open SetRealization SetFormula
universe u
variable {P : Type u} (c : Presentation P)
variable (one mu I W rows S : ZFSet.{u})
variable (valid : ∀ z ∈ (rowTupleTerms one mu I W rows S), IsName c z)

noncomputable def liftedRowTupleFamily (valid : ∀ z ∈ rowTupleTerms one mu I W rows S, IsName c z) : ZFSet.{u} :=
  relationCompose S (rowTupleTerms one mu I W rows S)
    (Name.renamedFamily c.pairEmpty id (rowTupleTerms one mu I W rows S) valid)
    (rowTupleFamily one mu I W rows S)
    (Name.renameFamilyGraph c.pairEmpty id (rowTupleTerms one mu I W rows S) valid)

end PartitionPilot.Forcing

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Geometry_GroundMixtureDensityRecovery
attribute [-instance] _root_.OAI.PartitionPilot.Forcing.GroundMainPrefix.withTopSmall
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PartitionPilot.Forcing.TransitiveGround
open SetRealization SetFormula Compression.RecursiveMaps
universe u
variable (M : TransitiveGround.{u}) {G P : Type u} [Group G] [PartialOrder P]
variable (a : PosetAction G P) (s : Presentation P)

variable [OrderTop P]

theorem niceVisibilityName_principal_hs {L : Type u} [PartialOrder L]
    (d : PosetAction G L) (base v : L)
    (directed : ∀ x y : L, ∃ z, x ≤ z ∧ y ≤ z) (T : ZFSet.{u})
    (children : ∀ τ : Name s, τ.val ∈ T →
      HereditarilySymmetric a s (d.principalSupportFamily base directed) τ) :
    HereditarilySymmetric a s (d.principalSupportFamily base directed)
      (M.niceVisibilityName a s T (d.principalFix v)) :=
  M.niceVisibilityName_hs a s (d.principalSupportFamily base directed)
    T (d.principalFix v) ⟨v, le_refl _⟩ children

end PartitionPilot.Forcing.TransitiveGround

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Forcing_GroundRenamedNameFamilyBounds
attribute [-instance] _root_.OAI.PartitionPilot.Forcing.GroundMainPrefix.withTopSmall
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PartitionPilot.Forcing
open SetRealization SetFormula Compression.RecursiveMaps
universe u
variable {G P L : Type u} [Group G] [PartialOrder P] [OrderTop P] [PartialOrder L]

structure NiceNameSystem (M : TransitiveGround.{u}) (a : PosetAction G P)
    (s : Presentation P) (b : Presentation L) (d : PosetAction G L) (base : L)
    (directed : ∀ x y : L, ∃ z, x ≤ z ∧ y ≤ z)
    (T : ZFSet.{u}) (valid : ∀ z ∈ T, IsName s z) : Prop where
  candidate_graph_ground : M.niceNameCandidateGraph a s b T d.principalFix ∈ M.sets
  candidate_graph_function : FunctionGraphOn b.carrier
    (M.niceNameCandidateGraph a s b T d.principalFix)
  candidate_entries : ∀ v z, ZFSet.pair (b.encode v) z ∈
    M.niceNameCandidateGraph a s b T d.principalFix ↔
      z = M.niceNameCandidates a s T (d.principalFix v)
  visibility_graph_ground : M.niceVisibilityGraph a s b T d.principalFix ∈ M.sets
  visibility_graph_function : FunctionGraphOn b.carrier
    (M.niceVisibilityGraph a s b T d.principalFix)
  visibility_entries : ∀ v z, ZFSet.pair (b.encode v) z ∈
    M.niceVisibilityGraph a s b T d.principalFix ↔
      z = (M.niceVisibilityName a s T (d.principalFix v)).val
  candidate_hs : ∀ v (τ : Name s), τ.val ∈ M.niceNameCandidates a s T (d.principalFix v) →
    HereditarilySymmetric a s (d.principalSupportFamily base directed) τ
  visibility_ground : ∀ v, (M.niceVisibilityName a s T (d.principalFix v)).val ∈ M.sets
  visibility_support : ∀ v, d.principalFix v ≤
    a.stabilizer s (M.niceVisibilityName a s T (d.principalFix v))
  visibility_hs : ∀ v, HereditarilySymmetric a s (d.principalSupportFamily base directed)
    (M.niceVisibilityName a s T (d.principalFix v))
  visibility_action : ∀ g v, a.act s g (M.niceVisibilityName a s T (d.principalFix v)) =
    M.niceVisibilityName a s T (d.principalFix (d.iso g v))
  normalization_candidate : ∀ v (τ : (M.nameDomain s).names),
    d.principalFix v ≤ a.stabilizer s τ.val →
    (Name.niceNormalize (M.nameDomain s) T valid τ).val ∈
      M.niceNameCandidates a s T (d.principalFix v)
  normalization_visible : ∀ v (τ : (M.nameDomain s).names),
    d.principalFix v ≤ a.stabilizer s τ.val →
    ∀ (H : ConditionFilter P), H.GenericFor (formulaFamily (M.nameDomain s)) →
    Name.eval {p | H.mem p} τ.val ⊆ Name.eval {p | H.mem p} (Name.familySet ⊤ T valid) →
    Name.eval {p | H.mem p} τ.val ∈
      Name.eval {p | H.mem p} (M.niceVisibilityName a s T (d.principalFix v))

end PartitionPilot.Forcing

namespace PartitionPilot.Forcing.TransitiveGround
open SetRealization SetFormula
universe u
variable (M : TransitiveGround.{u}) {P : Type u}
variable [PartialOrder P] [OrderTop P] (s : Presentation P)
variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
variable (unions : Realize M.sets SetFormula.union Fin.elim0)
variable (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
variable (collection : CollectionSchema M.sets)
variable (carrier : s.carrier ∈ M.sets) (order : s.conditionOrder ∈ M.sets)
variable {T : ZFSet.{u}} (hT : T ∈ M.sets) (valid : ∀ z ∈ T, IsName s z)

variable {G L : Type u} [Group G] [PartialOrder L]
variable (a : PosetAction G P) (b : Presentation L) (d : PosetAction G L)
variable (base : L) (directed : ∀ x y : L, ∃ z, x ≤ z ∧ y ≤ z)

noncomputable def stageOneVisibilityName
    (system : NiceNameSystem M a s b d base directed T valid) (v : L) :
    (M.nameDomain s).names :=
  ⟨M.niceVisibilityName a s T (d.principalFix v), system.visibility_ground v⟩

end PartitionPilot.Forcing.TransitiveGround

namespace PartitionPilot.Forcing.TransitiveGround
open SetRealization SetFormula Compression.RecursiveMaps
universe u
variable (M : TransitiveGround.{u}) {G P L : Type u}
variable [Group G] [PartialOrder P] [OrderTop P] [PartialOrder L]
variable (a : PosetAction G P) (s : Presentation P) (b : Presentation L)
variable (d : PosetAction G L) (base : L)
variable (directed : ∀ x y : L, ∃ z, x ≤ z ∧ y ≤ z)
variable (T : ZFSet.{u}) (H : ConditionFilter P)

noncomputable def visibleSupportProfile (z : ZFSet.{u}) : ZFSet.{u} :=
  b.subset (fun v => z ∈ Name.eval {p | H.mem p}
    (M.niceVisibilityName a s T (d.principalFix v)))

end PartitionPilot.Forcing.TransitiveGround

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Geometry_GroundNiceRefinementVisibility
attribute [-instance] _root_.OAI.PartitionPilot.Forcing.GroundMainPrefix.withTopSmall
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI



namespace PartitionPilot.Forcing
open SetFormula
universe u

def RefinementIndexSelectionCode (M : TransitiveGround.{u})
    (level r candidates relations T P order top z : ZFSet.{u}) : Prop :=
  ∃ C E U Rf Rc N V,
    z = refinementIndexCode level C E U Rf Rc ∧ ZFSet.pair C E ∈ r ∧ C ≠ E ∧
    ZFSet.pair C N ∈ candidates ∧ U ∈ N ∧ ZFSet.pair C V ∈ relations ∧
    Rf ∈ V ∧ Rc ∈ V ∧
    Realize M.sets (refinementValidityForcingFormula 0 1 2 3 4 5 6)
      ![U, Rf, Rc, T, P, order, top]

namespace SetFormula

def refinementIndexSelectionRawFormula {n} (z level r candidates relations T P order top : Fin n)
    (w : Fin 7 → Fin n) : SetFormula n :=
  .conj (BoundedFormula.refinementIndexFormula z level (w 0) (w 1) (w 2) (w 3) (w 4)).toFormula
  (.conj (BoundedFormula.pairMembershipFormula (w 0) (w 1) r).toFormula
  (.conj (.neg (.equal (w 0) (w 1)))
  (.conj (BoundedFormula.pairMembershipFormula (w 0) (w 5) candidates).toFormula
  (.conj (.mem (w 2) (w 5))
  (.conj (BoundedFormula.pairMembershipFormula (w 0) (w 6) relations).toFormula
  (.conj (.mem (w 3) (w 6)) (.conj (.mem (w 4) (w 6))
    (reindex ![w 2, w 3, w 4, T, P, order, top]
      (refinementValidityForcingFormula 0 1 2 3 4 5 6)))))))))

def refinementIndexSelectionFormula {n} (z level r candidates relations T P order top : Fin n) : SetFormula n :=
  let old := suffixIndex n 7
  exBlock 7 (refinementIndexSelectionRawFormula (old z) (old level) (old r)
    (old candidates) (old relations) (old T) (old P) (old order) (old top) (prefixIndex n 7))

end SetFormula

end PartitionPilot.Forcing



namespace PartitionPilot.Forcing.TransitiveGround
open SetFormula
universe u
variable (M : TransitiveGround.{u})

noncomputable def refinementIndices
    (level nodes r candidates relations T1 T2 T P order top : ZFSet.{u}) : ZFSet.{u} :=
  ZFSet.sep (RefinementIndexSelectionCode M level r candidates relations T P order top)
    (refinementIndexBound {level} nodes (M.groundRelations T1 P) (M.groundRelations T2 P))

theorem mem_refinementIndices
    (level nodes r candidates relations T1 T2 T P order top z : ZFSet.{u}) :
    z ∈ M.refinementIndices level nodes r candidates relations T1 T2 T P order top ↔
      z ∈ refinementIndexBound {level} nodes (M.groundRelations T1 P) (M.groundRelations T2 P) ∧
        RefinementIndexSelectionCode M level r candidates relations T P order top z :=
  ZFSet.mem_sep

theorem refinementIndexCode_mem_indices
    (level nodes r candidates relations T1 T2 T P order top C E U Rf Rc : ZFSet.{u}) :
    refinementIndexCode level C E U Rf Rc ∈
      M.refinementIndices level nodes r candidates relations T1 T2 T P order top ↔
    C ∈ nodes ∧ E ∈ nodes ∧ U ∈ M.groundRelations T1 P ∧
    Rf ∈ M.groundRelations T2 P ∧ Rc ∈ M.groundRelations T2 P ∧
    ZFSet.pair C E ∈ r ∧ C ≠ E ∧
    ∃ N V, ZFSet.pair C N ∈ candidates ∧ U ∈ N ∧
      ZFSet.pair C V ∈ relations ∧ Rf ∈ V ∧ Rc ∈ V ∧
      Realize M.sets (refinementValidityForcingFormula 0 1 2 3 4 5 6)
        ![U, Rf, Rc, T, P, order, top] := by
  rw [M.mem_refinementIndices, refinementIndexCode_mem_bound]
  constructor
  · rintro ⟨⟨_, hC, hE, hU, hf, hc⟩, c, e, a, f, t, N, V, equal, edge, strict, first, ha, second, hff, hcc, forced⟩
    obtain ⟨_, rfl, rfl, rfl, rfl, rfl⟩ := (refinementIndexCode_eq_iff _ _ _ _ _ _ _ _ _ _ _ _).1 equal
    exact ⟨hC, hE, hU, hf, hc, edge, strict, N, V, first, ha, second, hff, hcc, forced⟩
  · rintro ⟨hC, hE, hU, hf, hc, edge, strict, N, V, first, ha, second, hff, hcc, forced⟩
    exact ⟨⟨ZFSet.mem_singleton.2 rfl, hC, hE, hU, hf, hc⟩,
      C, E, U, Rf, Rc, N, V, rfl, edge, strict, first, ha, second, hff, hcc, forced⟩

end PartitionPilot.Forcing.TransitiveGround



namespace PartitionPilot.Forcing.TransitiveGround
open SetFormula SetRealization
universe u
variable (M : TransitiveGround.{u}) {G P L : Type u}
variable [Group G] [PartialOrder P] [OrderTop P] [PartialOrder L]
variable (a : PosetAction G P) (s : Presentation P) (b : Presentation L) (d : PosetAction G L)

noncomputable def niceRefinementIndices (level T1 T2 : ZFSet.{u})
    (valid : ∀ z ∈ T1, IsName s z) : ZFSet.{u} :=
  M.refinementIndices level b.carrier b.conditionOrder
    (M.niceNameCandidateGraph a s b T1 d.principalFix)
    (M.niceNameCandidateGraph a s b T2 d.principalFix) T1 T2
    (Name.familySet ⊤ T1 valid).val s.carrier s.conditionOrder (s.encode ⊤)

end PartitionPilot.Forcing.TransitiveGround



namespace PartitionPilot.Forcing.TransitiveGround
open SetFormula
universe u
variable (M : TransitiveGround.{u})
variable (level nodes r candidates relations T1 T2 T P order top : ZFSet.{u})
local notation "I" => M.refinementIndices level nodes r candidates relations T1 T2 T P order top
local notation "bounds" => (![Singleton.singleton level, nodes, nodes, M.groundRelations T1 P,
  M.groundRelations T2 P, M.groundRelations T2 P])

theorem refinementIndices_fields {z : ZFSet.{u}} (hz : z ∈ I) :
    ∃ fields : Fin 6 → ZFSet.{u}, z = nonemptyTupleCode 5 fields ∧ ∀ j, fields j ∈ bounds j := by
  obtain ⟨l, hl, C, hC, E, hE, U, hU, Rf, hf, Rc, hc, eq⟩ :=
    (mem_refinementIndexBound _ _ _ _ z).1 ((M.mem_refinementIndices _ _ _ _ _ _ _ _ _ _ _ _).1 hz).1
  refine ⟨![l, C, E, U, Rf, Rc], eq, ?_⟩
  exact Fin.cases hl (Fin.cases hC (Fin.cases hE (Fin.cases hU
    (Fin.cases hf (Fin.cases hc (fun j => Fin.elim0 j))))))

theorem refinementIndices_field_function (j : Fin 6) :
    ZFSet.IsFunc I (bounds j) (refinementIndexFieldGraph I (bounds j) j) := by
  apply refinementIndexFieldGraph_function
  intro z hz
  obtain ⟨v, equal, bound⟩ := M.refinementIndices_fields _ _ _ _ _ _ _ _ _ _ _ hz
  exact ⟨v, equal, bound j⟩

theorem refinementIndices_level_graph :
    refinementIndexFieldGraph I {level} 0 = ZFSet.prod I {level} := by
  apply ZFSet.ext
  intro z
  constructor
  · intro hz
    exact (ZFSet.mem_sep.1 hz).1
  · intro hz
    obtain ⟨x, hx, y, hy, rfl⟩ := ZFSet.mem_prod.1 hz
    obtain ⟨v, equal, bound⟩ := M.refinementIndices_fields _ _ _ _ _ _ _ _ _ _ _ hx
    have same : y = v 0 := (ZFSet.mem_singleton.1 hy).trans (ZFSet.mem_singleton.1 (bound 0)).symm
    exact (pair_mem_refinementIndexFieldGraph I {level} x y 0).2 ⟨hx, hy, v, equal, same⟩

end PartitionPilot.Forcing.TransitiveGround



namespace PartitionPilot.Forcing.TransitiveGround
open SetRealization
universe u
variable (M : TransitiveGround.{u}) {G P L : Type u}
variable [Group G] [PartialOrder P] [OrderTop P] [PartialOrder L]
variable (a : PosetAction G P) (s : Presentation P) (b : Presentation L) (d : PosetAction G L)

theorem exists_niceRefinementIndex_fields (level T1 T2 : ZFSet.{u})
    (valid1 : ∀ z ∈ T1, IsName s z) (valid2 : ∀ z ∈ T2, IsName s z)
    {z : ZFSet.{u}} (member : z ∈ M.niceRefinementIndices a s b d level T1 T2 valid1) :
    ∃ C E : L, ∃ U Rf Rc : (M.nameDomain s).names,
      z = refinementIndexCode level (b.encode C) (b.encode E) U.val.val Rf.val.val Rc.val.val := by
  have bound := ((M.mem_refinementIndices _ _ _ _ _ _ _ _ _ _ _ z).1 member).1
  obtain ⟨l, hl, C, hC, E, hE, U, hU, Rf, hf, Rc, hc, equal⟩ :=
    (mem_refinementIndexBound _ _ _ _ z).1 bound
  have same : l = level := ZFSet.mem_singleton.1 hl
  subst l
  obtain ⟨c, rfl⟩ := (b.mem_carrier C).1 hC
  obtain ⟨e, rfl⟩ := (b.mem_carrier E).1 hE
  have domain := (M.mem_groundRelations T1 s.carrier U).1 hU
  have fine := (M.mem_groundRelations T2 s.carrier Rf).1 hf
  have coarse := (M.mem_groundRelations T2 s.carrier Rc).1 hc
  exact ⟨c, e, ⟨Name.ofSubset valid1 domain.2, domain.1⟩,
    ⟨Name.ofSubset valid2 fine.2, fine.1⟩, ⟨Name.ofSubset valid2 coarse.2, coarse.1⟩, equal⟩

end PartitionPilot.Forcing.TransitiveGround



namespace PartitionPilot.Forcing
open SetRealization SetFormula
universe u
variable {G P L : Type u} [Group G] [PartialOrder P] [OrderTop P] [PartialOrder L]

structure NiceRefinementIndexSystem (M : TransitiveGround.{u})
    (a : PosetAction G P) (s : Presentation P) (b : Presentation L) (d : PosetAction G L)
    (level T1 T2 : ZFSet.{u}) (valid1 : ∀ z ∈ T1, IsName s z)
    (valid2 : ∀ z ∈ T2, IsName s z) : Prop where
  index_ground : M.niceRefinementIndices a s b d level T1 T2 valid1 ∈ M.sets
  family_ground : (Name.familySet ⊤ T1 valid1).val ∈ M.sets
  first_candidates_ground : M.niceNameCandidateGraph a s b T1 d.principalFix ∈ M.sets
  second_candidates_ground : M.niceNameCandidateGraph a s b T2 d.principalFix ∈ M.sets
  field_ground : ∀ j, refinementIndexFieldGraph (M.niceRefinementIndices a s b d level T1 T2 valid1)
    (M.niceRefinementIndexBounds s b level T1 T2 j) j ∈ M.sets
  field_function : ∀ j, ZFSet.IsFunc (M.niceRefinementIndices a s b d level T1 T2 valid1)
    (M.niceRefinementIndexBounds s b level T1 T2 j)
    (refinementIndexFieldGraph (M.niceRefinementIndices a s b d level T1 T2 valid1)
      (M.niceRefinementIndexBounds s b level T1 T2 j) j)
  level_graph : refinementIndexFieldGraph (M.niceRefinementIndices a s b d level T1 T2 valid1)
      {level} 0 = ZFSet.prod (M.niceRefinementIndices a s b d level T1 T2 valid1) {level}
  typed_entries : ∀ C E (U Rf Rc : (M.nameDomain s).names),
    refinementIndexCode level (b.encode C) (b.encode E) U.val.val Rf.val.val Rc.val.val ∈
      M.niceRefinementIndices a s b d level T1 T2 valid1 ↔
    C < E ∧ U.val.val ∈ M.niceNameCandidates a s T1 (d.principalFix C) ∧
      Rf.val.val ∈ M.niceNameCandidates a s T2 (d.principalFix C) ∧
      Rc.val.val ∈ M.niceNameCandidates a s T2 (d.principalFix C) ∧
      Forces (M.nameDomain s) BoundedFormula.refinementValidityFormula.toFormula
        (extend U (extend Rf (extend Rc (extend ⟨Name.familySet ⊤ T1 valid1, family_ground⟩ Fin.elim0)))) ⊤
  decoded : ∀ z ∈ M.niceRefinementIndices a s b d level T1 T2 valid1,
    ∃ C E : L, ∃ U Rf Rc : (M.nameDomain s).names,
      z = refinementIndexCode level (b.encode C) (b.encode E) U.val.val Rf.val.val Rc.val.val

end PartitionPilot.Forcing



namespace PartitionPilot.Forcing
open SetRealization SetFormula Compression.RecursiveMaps
universe u
variable {G P L : Type u} [Group G] [PartialOrder P] [OrderTop P] [PartialOrder L]

structure RefinementObjectSystem (M : TransitiveGround.{u}) (a : PosetAction G P)
    (s : Presentation P) (F : NormalSubgroupFamily G) (K : Subgroup G)
    (T : ZFSet.{u}) (valid : ∀ z ∈ T, IsName s z) (U Rf Rc : Name s) : Prop where
  ground : (Name.refinementQuotient T valid U Rf).val ∈ M.sets ∧
    (Name.refinementQuotient T valid U Rc).val ∈ M.sets ∧
    (Name.refinementNaturalMap T valid U Rf Rc).val ∈ M.sets
  support : K ≤ a.stabilizer s (Name.refinementQuotient T valid U Rf) ∧
    K ≤ a.stabilizer s (Name.refinementQuotient T valid U Rc) ∧
    K ≤ a.stabilizer s (Name.refinementNaturalMap T valid U Rf Rc)
  hs : HereditarilySymmetric a s F (Name.refinementQuotient T valid U Rf) ∧
    HereditarilySymmetric a s F (Name.refinementQuotient T valid U Rc) ∧
    HereditarilySymmetric a s F (Name.refinementNaturalMap T valid U Rf Rc)
  classes : ∀ w : Name s, w.val ∈ T →
    (Name.refinementClass T valid Rf w).val ∈ M.sets ∧
    (Name.refinementClass T valid Rc w).val ∈ M.sets ∧
    HereditarilySymmetric a s F (Name.refinementClass T valid Rf w) ∧
    HereditarilySymmetric a s F (Name.refinementClass T valid Rc w)
  class_graphs : Name.refinementClassGraph T valid Rf T valid ∈ M.sets ∧
    Name.refinementClassGraph T valid Rc T valid ∈ M.sets ∧
    Name.refinementPairClassGraph T valid Rf Rc T valid ∈ M.sets
  values : ∀ (H : ConditionFilter P), H.GenericFor (formulaFamily (M.nameDomain s)) →
    RefinementObjectValues {p | H.mem p} T valid U Rf Rc

end PartitionPilot.Forcing



end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Geometry_GroundAssignmentIndexLevels
attribute [-instance] _root_.OAI.PartitionPilot.Forcing.GroundMainPrefix.withTopSmall
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PartitionPilot.Forcing.TransitiveGround
open SetFormula
universe u
variable (M : TransitiveGround.{u})

theorem assignmentCut_small (separation : SeparationSchema M.sets)
    {levels alpha A N : ZFSet.{u}}
    (hLevels : levels ∈ M.sets) (hAlpha : alpha ∈ M.sets)
    (hA : A ∈ M.sets) (hN : N ∈ M.sets) (small : M.groundEmbeddable A N) :
    M.groundEmbeddable (assignmentCut levels alpha A) N :=
  M.groundEmbeddable_restrict separation
    (M.assignmentCut_mem separation hLevels hAlpha hA) hN
    (assignmentCut_subset levels alpha A) small

theorem assignmentSplice_countable
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (infinite : Realize M.sets infinity Fin.elim0)
    (choice : Realize M.sets SetFormula.choice Fin.elim0)
    {levels alpha Aq Ap : ZFSet.{u}}
    (hLevels : levels ∈ M.sets) (hAlpha : alpha ∈ M.sets)
    (hAq : Aq ∈ M.sets) (hAp : Ap ∈ M.sets)
    (smallq : M.groundEmbeddable Aq ZFSet.omega)
    (smallp : M.groundEmbeddable Ap ZFSet.omega) :
    M.groundEmbeddable (assignmentSplice levels alpha Aq Ap) ZFSet.omega :=
  M.groundEmbeddable_restrict separation
    (M.assignmentSplice_mem pairing unions separation hLevels hAlpha hAq hAp)
    (M.omega_mem separation infinite) (assignmentSplice_subset levels alpha Aq Ap)
    (M.groundCountable_binary_union pairing unions powers separation infinite choice
      hAq hAp smallq smallp)

theorem assignmentSplice_mem_groundSmallSubsets
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (infinite : Realize M.sets infinity Fin.elim0)
    (choice : Realize M.sets SetFormula.choice Fin.elim0)
    {J levels alpha Aq Ap : ZFSet.{u}}
    (hLevels : levels ∈ M.sets) (hAlpha : alpha ∈ M.sets)
    (memberq : Aq ∈ M.groundSmallSubsets J ZFSet.omega)
    (memberp : Ap ∈ M.groundSmallSubsets J ZFSet.omega) :
    assignmentSplice levels alpha Aq Ap ∈ M.groundSmallSubsets J ZFSet.omega := by
  obtain ⟨hAq, subsetq, smallq⟩ := (M.mem_groundSmallSubsets J ZFSet.omega Aq).1 memberq
  obtain ⟨hAp, subsetp, smallp⟩ := (M.mem_groundSmallSubsets J ZFSet.omega Ap).1 memberp
  refine (M.mem_groundSmallSubsets J ZFSet.omega _).2
    ⟨M.assignmentSplice_mem pairing unions separation hLevels hAlpha hAq hAp, ?_,
      M.assignmentSplice_countable pairing unions powers separation infinite choice
        hLevels hAlpha hAq hAp smallq smallp⟩
  intro z hz
  exact (ZFSet.mem_union.1 (assignmentSplice_subset levels alpha Aq Ap hz)).elim
    (fun member => subsetq member) (fun member => subsetp member)

end PartitionPilot.Forcing.TransitiveGround



namespace PartitionPilot.Forcing.TransitiveGround
open SetFormula
universe u
variable (M : TransitiveGround.{u})
variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
include pairing unions powers separation

theorem assignmentIndexLevels_mem {I T eta levels : ZFSet.{u}}
    (hI : I ∈ M.sets) (hT : T ∈ M.sets) (hEta : eta ∈ M.sets)
    (hLevels : levels ∈ M.sets) : assignmentIndexLevels I T eta levels ∈ M.sets :=
  M.relationCompose_mem pairing unions powers separation
    (M.stageOneAssignments_mem pairing unions powers separation hI hT) hI hEta
    (M.productFirst_mem pairing unions powers separation hI
      (M.prod_mem pairing unions powers separation hT hT)) hLevels

end PartitionPilot.Forcing.TransitiveGround

end

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Definability_FlatLimitConditionFormulas
attribute [-instance] _root_.OAI.PartitionPilot.Forcing.GroundMainPrefix.withTopSmall
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PartitionPilot.Forcing
open SetFormula
universe u

namespace TransitiveGround
variable (M : TransitiveGround.{u})

theorem realize_assignmentCutFormula {n : Nat} (cut levels alpha A : Fin n)
    (env : Fin n → ZFSet.{u}) (members : ∀ j, env j ∈ M.sets) :
    Realize M.sets (BoundedFormula.assignmentCutFormula cut levels alpha A).toFormula env ↔
      env cut = assignmentCut (env levels) (env alpha) (env A) :=
  (BoundedFormula.realize_toFormula M _ _ members).trans
    (BoundedFormula.truth_assignmentCutFormula cut levels alpha A env)

end TransitiveGround
end PartitionPilot.Forcing



end

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Transfinite_GroundStageOneAssignmentUnions
attribute [-instance] _root_.OAI.PartitionPilot.Forcing.GroundMainPrefix.withTopSmall
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PartitionPilot.Forcing

open SetRealization SetFormula
universe u

theorem stageOneAssignmentUnion_raw_eq {B : ZFSet.{u}} (seq : Nat → SetMembers B) :
    stageOneAssignmentUnion (fun n => SetMembers.raw (seq n)) = groundSequenceUnion seq := by
  apply ZFSet.ext
  intro z
  rw [mem_stageOneAssignmentUnion, mem_groundSequenceUnion]

namespace TransitiveGround
variable (M : TransitiveGround.{u})

theorem groundSmallSubset_union_mem
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (infinite : Realize M.sets SetFormula.infinity Fin.elim0)
    (choice : Realize M.sets SetFormula.choice Fin.elim0)
    {J : ZFSet.{u}} (hJ : J ∈ M.sets)
    (seq : Nat → SetMembers (M.groundSmallSubsets J ZFSet.omega))
    (graph : groundSequenceGraph seq ∈ M.sets) :
    stageOneAssignmentUnion (fun n => SetMembers.raw (seq n)) ∈ M.groundSmallSubsets J ZFSet.omega := by
  have hB := M.groundSmallSubsets_mem powers separation hJ (M.omega_mem separation infinite)
  have subsets (A : ZFSet.{u}) (member : A ∈ M.groundSmallSubsets J ZFSet.omega) : A ⊆ J :=
    ((M.mem_groundSmallSubsets J ZFSet.omega A).1 member).2.1
  have small (A : ZFSet.{u}) (member : A ∈ M.groundSmallSubsets J ZFSet.omega) :
      M.groundEmbeddable A ZFSet.omega :=
    ((M.mem_groundSmallSubsets J ZFSet.omega A).1 member).2.2
  obtain ⟨ground, countable⟩ := M.countable_union_of_sequence_graph pairing unions powers separation
    infinite choice hB hJ graph
    (natPresentation.graph_isFunc (SetMembers.presentation (M.groundSmallSubsets J ZFSet.omega))
      (fun n => seq n.down)) subsets small
  have equal := stageOneAssignmentUnion_raw_eq seq
  apply (M.mem_groundSmallSubsets J ZFSet.omega _).2
  refine ⟨equal.symm ▸ ground, ?_, equal.symm ▸ countable⟩
  exact stageOneAssignmentUnion_subset (fun n => subsets _ (SetMembers.raw_mem (seq n)))

end TransitiveGround

end PartitionPilot.Forcing

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Forcing_GroundRepresentedDomainConditions
attribute [-instance] _root_.OAI.PartitionPilot.Forcing.GroundMainPrefix.withTopSmall
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace PartitionPilot.Forcing
open SetRealization SetFormula
universe u

namespace SetFormula

def stageOneForcingAt {n m : Nat} (phi : SetFormula m) (p P r : Fin n)
    (names : Fin m → Fin n) : SetFormula n :=
  reindex (extend p (extend P (extend r names))) (stageOneForcingFormula phi)

def stageOneClassAt {n : Nat} (c T R w P r top : Fin n) : SetFormula n :=
  reindex (extend c (extend T (extend R (extend w
    (extend P (extend r (extend top Fin.elim0))))))) refinementClassCodeFormula

end SetFormula

end PartitionPilot.Forcing



namespace PartitionPilot.Forcing
open SetFormula
universe u

def PreparationForcingCode (M : TransitiveGround.{u})
    (P order q nodes visibility z F f : ZFSet.{u}) : Prop :=
  (∀ v V, ZFSet.pair v V ∈ visibility → v ∈ nodes →
    (v ∈ F → stageOneRawForces M P order q (.mem 0 1 : SetFormula 2) ![z, V]) ∧
    (v ∉ F → stageOneRawForces M P order q (.neg (.mem 0 1) : SetFormula 2) ![z, V])) ∧
  ∀ v tau, ZFSet.pair v tau ∈ f →
    stageOneRawForces M P order q (.equal 0 1 : SetFormula 2) ![z, tau]

namespace SetFormula

def preparationForcingFormula {n} (P order q nodes visibility z F f : Fin n) : SetFormula n :=
  .conj
    (allGraphFields visibility
      (imp (.mem 1 nodes.succ.succ)
        (.conj
          (imp (.mem 1 F.succ.succ)
            (stageOneForcingAt (.mem 0 1 : SetFormula 2) q.succ.succ P.succ.succ
              order.succ.succ ![z.succ.succ, 0]))
          (imp (.neg (.mem 1 F.succ.succ))
            (stageOneForcingAt (.neg (.mem 0 1) : SetFormula 2) q.succ.succ P.succ.succ
              order.succ.succ ![z.succ.succ, 0])))))
    (allGraphFields f
      (stageOneForcingAt (.equal 0 1 : SetFormula 2) q.succ.succ P.succ.succ
        order.succ.succ ![z.succ.succ, 0]))

end SetFormula

end PartitionPilot.Forcing



namespace PartitionPilot.Forcing.TransitiveGround
open SetRealization SetFormula
universe u
variable (M : TransitiveGround.{u})

def representedReuseFormula {n : Nat}
    (A q P order T idx cu classes : Fin n) : SetFormula n :=
  let old := suffixIndex n 3
  let v := prefixIndex n 3
  exBlock 3 (.conj (.mem (v 0) (old T))
    (.conj (.mem (v 1) (old T))
      (.conj (tripleMembershipFormula (old idx) (v 0) (v 1) (old A))
        (.conj (pairMembershipFormula (v 0) (v 2) (old classes))
          (stageOneForcingAt (.equal 0 1 : SetFormula 2) (old q) (old P)
            (old order) ![old cu, v 2])))))

def representedEntryFormula {n : Nat}
    (p P order cut T idx u U cu classes : Fin n) : SetFormula n :=
  let old := suffixIndex n 3
  let v := prefixIndex n 3
  exBlock 3 (.conj (BoundedFormula.orderedPairFormula (old p) (v 0) (v 1)).toFormula
    (.conj (pairMembershipFormula (old p) (v 2) (old cut))
      (disj (stageOneForcingAt (.neg (.mem 0 1) : SetFormula 2) (v 2) (old P)
        (old order) ![old u, old U])
        (.conj (stageOneForcingAt (.mem 0 1 : SetFormula 2) (v 2) (old P)
          (old order) ![old u, old U])
          (representedReuseFormula (v 1) (v 2) (old P) (old order) (old T)
            (old idx) (old cu) (old classes))))))

variable {P : Type u} [PartialOrder P] [OrderTop P] (s : Presentation P)

noncomputable def representedDomainConditions (upper levels alpha T : ZFSet.{u})
    (valid : ∀ z ∈ T, IsName s z) (idx : ZFSet.{u}) (U Rc u : (M.nameDomain s).names) : ZFSet.{u} :=
  let cut := rowAssignmentCutGraph upper s.carrier levels alpha
  let classes := Name.refinementClassGraph T valid Rc.val T valid
  let cu := (Name.refinementClass T valid Rc.val u.val).val
  let params : Fin 9 → ZFSet.{u} := ![s.carrier, s.conditionOrder, cut, T, idx, u.val.val, U.val.val, cu, classes]
  ZFSet.sep (fun p => Realize M.sets (representedEntryFormula 0 1 2 3 4 5 6 7 8 9)
    (extend p params)) upper

end PartitionPilot.Forcing.TransitiveGround

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Definability_VisibilityProfileFormulas
attribute [-instance] _root_.OAI.PartitionPilot.Forcing.GroundMainPrefix.withTopSmall
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PartitionPilot.Forcing

section
open SetRealization SetFormula
universe u

namespace SetFormula

def stageOneProfileAt {n : Nat} (P r lower nodes nodeOrder visibility E bu aw : Fin n) : SetFormula n :=
  .all (imp (.mem 0 nodes.succ)
    (imp (BoundedFormula.pairMembershipFormula E.succ 0 nodeOrder.succ).toFormula
      (ex (.conj (BoundedFormula.pairMembershipFormula 1 0 visibility.succ.succ).toFormula
        (stageOneForcingAt refinementProfileFormula lower.succ.succ P.succ.succ r.succ.succ
          (extend bu.succ.succ (extend aw.succ.succ (extend 0 Fin.elim0))))))))

def stageOneCompatibilityAt {n : Nat} (P r lower visibility maps C idx bu aw : Fin n) : SetFormula n :=
  ex (ex (.conj (BoundedFormula.pairMembershipFormula C.succ.succ 1 visibility.succ.succ).toFormula
    (.conj (BoundedFormula.pairMembershipFormula idx.succ.succ 0 maps.succ.succ).toFormula
      (stageOneForcingAt refinementCompatibilityFormula lower.succ.succ P.succ.succ r.succ.succ
        (extend aw.succ.succ (extend 1 (extend bu.succ.succ (extend 0 Fin.elim0))))))))

end SetFormula

end

open SetFormula
universe u

end PartitionPilot.Forcing

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Transfinite_GroundStandardInaccessible
attribute [-instance] _root_.OAI.PartitionPilot.Forcing.GroundMainPrefix.withTopSmall
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI



namespace PartitionPilot.Forcing
open SetFormula SetRealization
universe u




namespace GroundStandardInaccessible
variable {M : TransitiveGround.{u}} {K : ZFSet.{u}}
variable (standard : GroundStandardInaccessible M K)
variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
variable (unions : Realize M.sets SetFormula.union Fin.elim0)
variable (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
variable (hK : K ∈ M.sets)
include standard pairing unions powers separation hK

theorem omega_mem : ZFSet.omega ∈ K := by
  obtain ⟨k, eqK⟩ := (ordinalSetProperty_iff K).1 standard.1.1
  by_cases greater : Ordinal.omega0 < k
  · rw [eqK, ← ordinalCode_omega, mem_ordinalCode_iff]
    exact greater
  · have subset : K ⊆ ZFSet.omega := by
      rw [eqK, ← ordinalCode_omega, ordinalCode_subset_iff]
      exact le_of_not_gt greater
    exact False.elim (standard.2.1 ⟨identityFunctionGraph K,
      M.identityFunctionGraph_mem pairing unions powers separation hK,
      (identityFunctionGraph_injection K).retarget subset⟩)

end GroundStandardInaccessible

end PartitionPilot.Forcing

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Forcing_GroundTestedMeetFilters
attribute [-instance] _root_.OAI.PartitionPilot.Forcing.GroundMainPrefix.withTopSmall
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PartitionPilot.Forcing

namespace TransitiveGround
open SetFormula SetRealization
universe u
variable (M : TransitiveGround.{u})

noncomputable def generatedMeetFilter (P r μ A : ZFSet.{u}) : ZFSet.{u} :=
  relationImage (relationImage A P (M.finitePathClosure P (meetGeneratorSteps P μ A))) P r

end TransitiveGround

universe u

end PartitionPilot.Forcing

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Geometry_GroundEligibleCaps
attribute [-instance] _root_.OAI.PartitionPilot.Forcing.GroundMainPrefix.withTopSmall
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace PartitionPilot.Forcing

universe u






theorem eligibleTaskBatchInputs
    {P G r μ A R U Labels m inv one : ZFSet.{u}}
    (group : GroupCode G m inv one) (action : PosetActionCode G P m one r A)
    (meet : MeetOrderCode P r μ) :
    let I := eligibleTaskSet P G r μ A R U Labels
    AttachmentBatchInputs P r μ I
      (constantFamilyGraph I P) (constantFamilyGraph I r) (constantFamilyGraph I μ)
      (literalTaskSourceGraph I P R U Labels) (literalTaskBaseGraph I P R U Labels)
      (literalTaskFilterGraph I P R U Labels) (literalTaskSeparatorGraph I P R U Labels) := by
  let I := eligibleTaskSet P G r μ A R U Labels
  have subset : I ⊆ literalTaskBound P R U Labels := eligibleTaskSet_subset P G r μ A R U Labels
  refine ⟨meet, ⟨_, constantFamilyGraph_function I P⟩,
    ⟨_, constantFamilyGraph_function I r⟩, ⟨_, constantFamilyGraph_function I μ⟩,
    ⟨_, literalTaskFieldGraph_function subset 0⟩, ⟨_, literalTaskFieldGraph_function subset 2⟩,
    ⟨_, literalTaskFieldGraph_function subset 4⟩, ⟨_, literalTaskFieldGraph_function subset 3⟩, ?_⟩
  intro i hi Q r' μ' a' base' F' e' hQ hr hμ ha' hBase' hF' he'
  obtain ⟨a, ha, c, hc, base, hBase, e, he, F, hF, label, hLabel, rfl, code⟩ :=
    (mem_eligibleTaskSet P G r μ A R U Labels i).1 hi
  obtain rfl := ((pair_mem_constantFamilyGraph I P _ Q).1 hQ).2
  obtain rfl := ((pair_mem_constantFamilyGraph I r _ r').1 hr).2
  obtain rfl := ((pair_mem_constantFamilyGraph I μ _ μ').1 hμ).2
  obtain rfl := ((literalTaskFieldGraph_entry_iff ha hc hBase he hF hLabel 0).1 ha').2
  obtain rfl := ((literalTaskFieldGraph_entry_iff ha hc hBase he hF hLabel 2).1 hBase').2
  obtain rfl := ((literalTaskFieldGraph_entry_iff ha hc hBase he hF hLabel 4).1 hF').2
  obtain rfl := ((literalTaskFieldGraph_entry_iff ha hc hBase he hF hLabel 3).1 he').2
  obtain ⟨g, hg, represented⟩ := code.representative
  exact represented.singleAttachmentInputs group action meet hg ha hc code.filter he
    code.lower code.strict code.upper

end PartitionPilot.Forcing



namespace PartitionPilot.Forcing.TransitiveGround

open SetFormula
universe u
variable (M : TransitiveGround.{u})

noncomputable def groundEligibleTasks (P G r μ A Labels : ZFSet.{u}) : ZFSet.{u} :=
  eligibleTaskSet P G r μ A (M.groundRelations P P) (M.groundMeetFilters P r μ) Labels

theorem groundEligibleTaskBatchInputs
    {P G r μ A Labels m inv one : ZFSet.{u}}
    (group : GroupCode G m inv one) (action : PosetActionCode G P m one r A)
    (meet : MeetOrderCode P r μ) :
    let I := M.groundEligibleTasks P G r μ A Labels
    let R := M.groundRelations P P
    let U := M.groundMeetFilters P r μ
    AttachmentBatchInputs P r μ I
      (constantFamilyGraph I P) (constantFamilyGraph I r) (constantFamilyGraph I μ)
      (literalTaskSourceGraph I P R U Labels) (literalTaskBaseGraph I P R U Labels)
      (literalTaskFilterGraph I P R U Labels) (literalTaskSeparatorGraph I P R U Labels) :=
  eligibleTaskBatchInputs group action meet

end PartitionPilot.Forcing.TransitiveGround



end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Forcing_GroundRecursiveActions
attribute [-instance] _root_.OAI.PartitionPilot.Forcing.GroundMainPrefix.withTopSmall
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open scoped ZFSet


namespace PartitionPilot.Forcing.TransitiveGround

open SetFormula
universe u
variable (M : TransitiveGround.{u})

noncomputable def groundTaskTransport (P G r μ A Labels : ZFSet.{u}) : ZFSet.{u} :=
  taskTransportGraph G (M.groundEligibleTasks P G r μ A Labels) P
    (M.groundRelations P P) (M.groundMeetFilters P r μ) Labels A

end PartitionPilot.Forcing.TransitiveGround



namespace PartitionPilot.Forcing

universe u

namespace TransitiveGround

open SetFormula

noncomputable def groundEligibleFreshAction (M : TransitiveGround.{u})
    (P G r μ A Labels : ZFSet.{u}) : ZFSet.{u} :=
  let I := M.groundEligibleTasks P G r μ A Labels
  let R := M.groundRelations P P
  let U := M.groundMeetFilters P r μ
  let N := indexedAttachmentFresh I (constantFamilyGraph I P) (constantFamilyGraph I r)
    (literalTaskSourceGraph I P R U Labels)
  indexedTaskActionGraph G I P N (M.groundTaskTransport P G r μ A Labels)

end TransitiveGround






end PartitionPilot.Forcing



end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Forcing_EligibleBatchEquivariance
attribute [-instance] _root_.OAI.PartitionPilot.Forcing.GroundMainPrefix.withTopSmall
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PartitionPilot.Forcing.TransitiveGround

open SetFormula
universe u
variable (M : TransitiveGround.{u})

noncomputable def groundEligibleBatchAction (P G r μ A Labels : ZFSet.{u}) : ZFSet.{u} :=
  let I := M.groundEligibleTasks P G r μ A Labels
  let N := indexedAttachmentFresh I (constantFamilyGraph I P) (constantFamilyGraph I r)
    (literalTaskSourceGraph I P (M.groundRelations P P) (M.groundMeetFilters P r μ) Labels)
  taggedActionGraph G P N A (M.groundEligibleFreshAction P G r μ A Labels)

end PartitionPilot.Forcing.TransitiveGround

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Definability_GroundLiftedCompressionFormulas
attribute [-instance] _root_.OAI.PartitionPilot.Forcing.GroundMainPrefix.withTopSmall
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PartitionPilot.Forcing

universe u

namespace SetFormula

def sectionFamilyEntryFormula {n} (z I B C R : Fin n) : SetFormula n :=
  ex (.conj (.mem 0 I.succ) (ex
    (.conj (BoundedFormula.orderedPairFormula z.succ.succ 1 0).toFormula
      (BoundedFormula.indexedRelationSectionFormula 0 1 B.succ.succ C.succ.succ R.succ.succ).toFormula)))

def sectionFamilyFormula {n} (family I B C R : Fin n) : SetFormula n :=
  exactSetFormula family (sectionFamilyEntryFormula 0 I.succ B.succ C.succ R.succ)

end SetFormula

namespace TransitiveGround

open SetFormula
variable (M : TransitiveGround.{u})

theorem realize_sectionFamilyEntryFormula {n} (z I B C R : Fin n)
    (env : Fin n → ZFSet.{u}) (members : ∀ i, env i ∈ M.sets) :
    Realize M.sets (sectionFamilyEntryFormula z I B C R) env ↔
      env z ∈ M.indexedRelationSections (env I) (env B) (env C) (env R) := by
  rw [sectionFamilyEntryFormula, realize_ex]
  constructor
  · rintro ⟨i, hiM, hi, rest⟩
    obtain ⟨f, hfM, pair, sectionCode⟩ := (realize_ex M.sets _ _).1 rest
    have extended : ∀ j, extend f (extend i env) j ∈ M.sets := Fin.cases hfM (Fin.cases hiM members)
    have pairEq := (BoundedFormula.truth_orderedPairFormula z.succ.succ 1 0 _).1
      ((BoundedFormula.realize_toFormula M _ _ extended).1 pair)
    have sectionEq := (BoundedFormula.truth_indexedRelationSectionFormula 0 1
      B.succ.succ C.succ.succ R.succ.succ _).1
      ((BoundedFormula.realize_toFormula M _ _ extended).1 sectionCode)
    change env z = ZFSet.pair i f at pairEq
    change f = indexedRelationSection (env B) (env C) (env R) i at sectionEq
    rw [pairEq]
    exact (M.pair_mem_indexedRelationSections _ _ _ _ _ _).2
      ⟨hi, (M.mem_groundRelations _ _ _).2 ⟨hfM, sectionEq.symm ▸ indexedRelationSection_subset _ _ _ _⟩,
        sectionEq⟩
  · intro member
    obtain ⟨_, i, hi, f, hf, pairEq, sectionEq⟩ := ZFSet.mem_sep.1 member
    have hiM := M.transitive (members I) hi
    have hfM := ((M.mem_groundRelations _ _ _).1 hf).1
    refine ⟨i, hiM, hi, ?_⟩
    rw [realize_ex]
    refine ⟨f, hfM, ?_, ?_⟩
    · apply (BoundedFormula.realize_toFormula M _ _ (Fin.cases hfM (Fin.cases hiM members))).2
      exact (BoundedFormula.truth_orderedPairFormula z.succ.succ 1 0 _).2 pairEq
    · apply (BoundedFormula.realize_toFormula M _ _ (Fin.cases hfM (Fin.cases hiM members))).2
      exact (BoundedFormula.truth_indexedRelationSectionFormula 0 1
        B.succ.succ C.succ.succ R.succ.succ _).2 sectionEq

theorem realize_sectionFamilyFormula
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    {n} (family I B C R : Fin n) (env : Fin n → ZFSet.{u})
    (members : ∀ i, env i ∈ M.sets) :
    Realize M.sets (sectionFamilyFormula family I B C R) env ↔
      env family = M.indexedRelationSections (env I) (env B) (env C) (env R) := by
  apply M.realize_exactSetFormula family _ env (members family)
  · intro z member
    obtain ⟨_, i, hi, f, hf, pairEq, _⟩ := ZFSet.mem_sep.1 member
    exact pairEq.symm ▸ M.orderedPair_mem pairing (M.transitive (members I) hi)
      ((M.mem_groundRelations _ _ _).1 hf).1
  · intro z hz
    exact M.realize_sectionFamilyEntryFormula 0 I.succ B.succ C.succ R.succ
      (extend z env) (Fin.cases hz members)

end TransitiveGround

namespace SetFormula

def liftedCompressionGraphFormula {n}
    (output i j d l c ns b maps sources fs reps g action v w : Fin n) : SetFormula n :=
  exactSetFormula output (BoundedFormula.liftedCompressionEntryFormula 0
    i.succ j.succ d.succ l.succ c.succ ns.succ b.succ maps.succ sources.succ
    fs.succ reps.succ g.succ action.succ v.succ w.succ).toFormula

def liftedCompressionFamilyFormula {n}
    (family i j d l c ns b maps sources fs reps g action v w : Fin n) : SetFormula n :=
  ex (.conj (liftedCompressionGraphFormula 0 i.succ j.succ d.succ l.succ c.succ
    ns.succ b.succ maps.succ sources.succ fs.succ reps.succ g.succ action.succ v.succ w.succ)
    (sectionFamilyFormula family.succ i.succ l.succ c.succ 0))

end SetFormula

namespace TransitiveGround

open SetFormula
variable (M : TransitiveGround.{u})

theorem realize_liftedCompressionGraphFormula
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0) {n}
    (output i j d l c ns b maps sources fs reps g action v w : Fin n)
    (env : Fin n → ZFSet.{u}) (members : ∀ k, env k ∈ M.sets)
    (mapsBound : env v = ZFSet.sUnion (ZFSet.sUnion (env maps)))
    (filterBound : env w = ZFSet.sUnion (ZFSet.sUnion (env fs))) :
    Realize M.sets (liftedCompressionGraphFormula output i j d l c ns b maps sources
      fs reps g action v w) env ↔
      env output = liftedCompressionGraph (env i) (env j) (env d) (env l) (env c)
        (env ns) (env b) (env maps) (env sources) (env fs) (env reps) (env g) (env action) := by
  apply M.realize_exactSetFormula output _ env (members output)
  · intro z member
    obtain ⟨_, task, hi, x, hx, y, hy, rfl, _⟩ := ZFSet.mem_sep.1 member
    exact M.orderedPair_mem pairing
      (M.orderedPair_mem pairing (M.transitive (members i) hi) (M.transitive (members l) hx))
      (M.transitive (members c) hy)
  · intro z hz
    rw [BoundedFormula.realize_toFormula M _ _ (Fin.cases hz members)]
    exact BoundedFormula.truth_liftedCompressionEntryFormula_mem 0 i.succ j.succ d.succ
      l.succ c.succ ns.succ b.succ maps.succ sources.succ fs.succ reps.succ g.succ action.succ
      v.succ w.succ (extend z env) mapsBound filterBound

theorem realize_liftedCompressionFamilyFormula
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets) {n}
    (family i j d l c ns b maps sources fs reps g action v w : Fin n)
    (env : Fin n → ZFSet.{u}) (members : ∀ k, env k ∈ M.sets)
    (mapsBound : env v = ZFSet.sUnion (ZFSet.sUnion (env maps)))
    (filterBound : env w = ZFSet.sUnion (ZFSet.sUnion (env fs))) :
    Realize M.sets (liftedCompressionFamilyFormula family i j d l c ns b maps sources
      fs reps g action v w) env ↔
      env family = M.groundLiftedCompressionFamily (env i) (env j) (env d) (env l) (env c)
        (env ns) (env b) (env maps) (env sources) (env fs) (env reps) (env g) (env action) := by
  rw [liftedCompressionFamilyFormula, realize_ex]
  constructor
  · rintro ⟨graph, hgraph, graphCode, familyCode⟩
    have extended : ∀ k, extend graph env k ∈ M.sets := Fin.cases hgraph members
    have graphEq := (M.realize_liftedCompressionGraphFormula pairing 0 i.succ j.succ d.succ
      l.succ c.succ ns.succ b.succ maps.succ sources.succ fs.succ reps.succ g.succ action.succ
      v.succ w.succ (extend graph env) extended mapsBound filterBound).1 graphCode
    have familyEq := (M.realize_sectionFamilyFormula pairing family.succ i.succ l.succ c.succ 0
      (extend graph env) extended).1 familyCode
    change graph = liftedCompressionGraph (env i) (env j) (env d) (env l) (env c)
      (env ns) (env b) (env maps) (env sources) (env fs) (env reps) (env g) (env action) at graphEq
    change env family = M.indexedRelationSections (env i) (env l) (env c) graph at familyEq
    simpa only [groundLiftedCompressionFamily, graphEq] using familyEq
  · intro equal
    let graph := liftedCompressionGraph (env i) (env j) (env d) (env l) (env c)
      (env ns) (env b) (env maps) (env sources) (env fs) (env reps) (env g) (env action)
    have hgraph := M.liftedCompressionGraph_mem pairing unions powers separation
      (members i) (members j) (members d) (members l) (members c) (members ns) (members b)
      (members maps) (members sources) (members fs) (members reps) (members g) (members action)
    refine ⟨graph, hgraph, ?_, ?_⟩
    · apply (M.realize_liftedCompressionGraphFormula pairing 0 i.succ j.succ d.succ
        l.succ c.succ ns.succ b.succ maps.succ sources.succ fs.succ reps.succ g.succ action.succ
        v.succ w.succ (extend graph env) (Fin.cases hgraph members) mapsBound filterBound).2
      rfl
    · apply (M.realize_sectionFamilyFormula pairing family.succ i.succ l.succ c.succ 0
        (extend graph env) (Fin.cases hgraph members)).2
      exact equal

end TransitiveGround

end PartitionPilot.Forcing

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Definability_RecursivePrimitiveFormulas
attribute [-instance] _root_.OAI.PartitionPilot.Forcing.GroundMainPrefix.withTopSmall
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PartitionPilot.Forcing
open SetFormula
universe u

namespace TransitiveGround
variable (M : TransitiveGround.{u})
variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
variable (unions : Realize M.sets SetFormula.union Fin.elim0)
variable (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
include pairing unions powers separation

theorem realize_recursiveIndicesSetFormula {n} (output i j p bound sources filters : Fin n)
    (env : Fin n → ZFSet.{u}) (members : ∀ x, env x ∈ M.sets) :
    Realize M.sets (recursiveIndicesSetFormula output i j p bound sources filters) env ↔
      env output = recursiveAttachmentIndices (env i) (env j) (env p) (env bound)
        (env sources) (env filters) := by
  apply M.realize_exactBoundedSetFormula output _ env members
    (M.recursiveAttachmentIndices_mem pairing unions powers separation (members i) (members j)
      (members p) (members bound) (members sources) (members filters))
  intro z
  rw [BoundedFormula.truth_recursiveAttachmentIndexFormula]
  change (∃ x ∈ env i, ∃ y ∈ env j, ∃ a ∈ env p, ∃ F ∈ env bound,
    z = ZFSet.pair x y ∧ ZFSet.pair x a ∈ env sources ∧
      ZFSet.pair y F ∈ env filters ∧ a ∉ F) ↔ _
  rw [recursiveAttachmentIndices, ZFSet.mem_sep]
  constructor
  · intro witness
    refine ⟨?_, witness⟩
    obtain ⟨x, hx, y, hy, _, _, _, _, equal, _⟩ := witness
    rw [equal]
    exact ZFSet.pair_mem_prod.2 ⟨hx, hy⟩
  · exact And.right

theorem realize_pairFieldSetFormula {n} (left : Bool) (output i j k bound family : Fin n)
    (env : Fin n → ZFSet.{u}) (members : ∀ x, env x ∈ M.sets) :
    Realize M.sets (pairFieldSetFormula left output i j k bound family) env ↔
      env output = pairFieldGraph left (env i) (env j) (env k) (env bound) (env family) := by
  apply M.realize_exactBoundedSetFormula output _ env members
    (M.pairFieldGraph_mem pairing unions powers separation left (members i) (members j)
      (members k) (members bound) (members family))
  intro z
  rw [BoundedFormula.truth_pairFieldEntryFormula]
  change (∃ t ∈ env k, ∃ x ∈ env i, ∃ y ∈ env j, ∃ v ∈ env bound,
    z = ZFSet.pair t v ∧ t = ZFSet.pair x y ∧
      ZFSet.pair (if left then x else y) v ∈ env family) ↔ _
  rw [pairFieldGraph, ZFSet.mem_sep]
  constructor
  · intro witness
    refine ⟨?_, witness⟩
    obtain ⟨t, ht, _, _, _, _, v, hv, equal, _⟩ := witness
    rw [equal]
    exact ZFSet.pair_mem_prod.2 ⟨ht, hv⟩
  · exact And.right

theorem realize_pairSecondFieldSetFormula {n} (output i j k bound family : Fin n)
    (env : Fin n → ZFSet.{u}) (members : ∀ x, env x ∈ M.sets)
    (bound_eq : env bound = ZFSet.sUnion (ZFSet.sUnion (env family))) :
    Realize M.sets (pairFieldSetFormula false output i j k bound family) env ↔
      env output = pairSecondField (env i) (env j) (env k) (env family) := by
  rw [M.realize_pairFieldSetFormula pairing unions powers separation false output i j k bound family
    env members, bound_eq]
  rfl

end TransitiveGround
end PartitionPilot.Forcing

end

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Geometry_GroundBatchEmbeddingRecognition
attribute [-instance] _root_.OAI.PartitionPilot.Forcing.GroundMainPrefix.withTopSmall
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PartitionPilot.Forcing

namespace TransitiveGround
open SetFormula
universe u
variable (M : TransitiveGround.{u})

variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
variable (unions : Realize M.sets SetFormula.union Fin.elim0)
variable (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
include pairing unions powers separation

noncomputable def definable_canonicalMeet : GroundDefinableFunction M
    (fun env : Fin 2 → ZFSet.{u} => canonicalMeetGraph (env 0) (env 1)) where
  formula := canonicalMeetSetFormula 0 1 2
  closed := fun _env members => M.canonicalMeetGraph_mem pairing unions powers separation (members 0) (members 1)
  correct := fun env members z hz => M.realize_canonicalMeetSetFormula pairing unions powers separation
    0 1 2 (extend z env) (Fin.cases hz members)

noncomputable def definable_recursiveIndices : GroundDefinableFunction M
    (fun env : Fin 6 → ZFSet.{u} => recursiveAttachmentIndices
      (env 0) (env 1) (env 2) (env 3) (env 4) (env 5)) where
  formula := recursiveIndicesSetFormula 0 1 2 3 4 5 6
  closed := fun _env members => M.recursiveAttachmentIndices_mem pairing unions powers separation
    (members 0) (members 1) (members 2) (members 3) (members 4) (members 5)
  correct := fun env members z hz => M.realize_recursiveIndicesSetFormula pairing unions powers separation
    0 1 2 3 4 5 6 (extend z env) (Fin.cases hz members)

end TransitiveGround

end PartitionPilot.Forcing

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Transfinite_RecursiveStateFieldEnvironments
attribute [-instance] _root_.OAI.PartitionPilot.Forcing.GroundMainPrefix.withTopSmall
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open scoped ZFSet

namespace PartitionPilot.Forcing.RecursiveStateData
universe u

noncomputable def successorCodeFromEnvironment (M : TransitiveGround.{u})
    (env : Fin 18 → ZFSet.{u}) : ZFSet.{u} :=
  ((ofFields (fun j => env (j.castAdd 5))).successor M
    (env 13) (env 14) (env 15) (env 16) (env 17)).code

end PartitionPilot.Forcing.RecursiveStateData

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Definability_GroundDefinableRelationProducts
attribute [-instance] _root_.OAI.PartitionPilot.Forcing.GroundMainPrefix.withTopSmall
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PartitionPilot.Forcing
open SetFormula
universe u

namespace TransitiveGround

noncomputable def definable_nonemptyTuple (M : TransitiveGround.{u})
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0) (k : Nat) :
    GroundDefinableFunction M (fun env : Fin (k + 1) → ZFSet.{u} => nonemptyTupleCode k env) where
  formula := (BoundedFormula.nonemptyTupleFormula k 0 Fin.succ).toFormula
  closed := fun env members => M.nonemptyTupleCode_mem pairing k env members
  correct := by
    intro env members z hz
    rw [BoundedFormula.realize_toFormula M _ _ (Fin.cases hz members),
      BoundedFormula.truth_nonemptyTupleFormula]
    rfl

end TransitiveGround

end PartitionPilot.Forcing



end

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Geometry_GroundDefinableIndexBounds
attribute [-instance] _root_.OAI.PartitionPilot.Forcing.GroundMainPrefix.withTopSmall
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PartitionPilot.Forcing.TransitiveGround
open SetFormula
universe u
variable (M : TransitiveGround.{u})
variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
variable (unions : Realize M.sets SetFormula.union Fin.elim0)
variable (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)

noncomputable def definable_orderedPairNameFamily :
    GroundDefinableFunction M (fun env : Fin 3 → ZFSet.{u} => orderedPairNameFamily (env 0) (env 1) (env 2)) where
  formula := exactSetFormula 0 (orderedPairNameFamilyMemberFormula 0 2 3 4)
  closed := fun _ members => M.orderedPairNameFamily_mem pairing unions powers separation
    (members 0) (members 1) (members 2)
  correct := by
    intro env members z hz
    apply M.realize_exactSetFormula 0 _ (extend z env) hz
      (fun _ h => M.transitive (M.orderedPairNameFamily_mem pairing unions powers separation
        (members 0) (members 1) (members 2)) h)
    intro w hw
    exact M.realize_orderedPairNameFamilyMemberFormula pairing 0 2 3 4 _
      (Fin.cases hw (Fin.cases hz members))

end PartitionPilot.Forcing.TransitiveGround

end

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Forcing_GroundDefinableRefinementNameGraphs
attribute [-instance] _root_.OAI.PartitionPilot.Forcing.GroundMainPrefix.withTopSmall
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace PartitionPilot.Forcing
open SetRealization SetFormula
universe u
namespace SetFormula

def refinementOutputCodeFormula (kind : Fin 3) : SetFormula 8 :=
  Fin.cases (reindex ![0, 1, 2, 3, 5, 6, 7] refinementQuotientCodeFormula)
    (Fin.cases (reindex ![0, 1, 2, 4, 5, 6, 7] refinementQuotientCodeFormula)
      (fun _ => refinementMapCodeFormula)) kind

end SetFormula
namespace TransitiveGround
variable (M : TransitiveGround.{u})

theorem refinementNameBound_mem
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    {T P top : ZFSet.{u}} (hT : T ∈ M.sets) (hP : P ∈ M.sets) (htop : top ∈ M.sets) :
    M.refinementNameBound T P top ∈ M.sets := by
  have hc := M.groundRelations_mem pairing unions powers separation hT hP
  exact M.groundRelations_mem pairing unions powers separation
    (M.binary_union_mem pairing unions hc (M.orderedPairNameFamily_mem pairing unions powers separation htop hc hc)) hP

end TransitiveGround



namespace SetFormula

def refinementIndexNameGraphFormula (kind : Fin 3) : SetFormula 9 :=
  let w := prefixIndex 9 5
  let old := suffixIndex 9 5
  exBlock 5 (.conj (.mem (w 0) (old 1))
    (.conj (BoundedFormula.orderedPairFormula (old 0) (w 0) (w 1)).toFormula
      (.conj (BoundedFormula.pairMembershipFormula (w 0) (w 2) (old 2)).toFormula
        (.conj (BoundedFormula.pairMembershipFormula (w 0) (w 3) (old 3)).toFormula
          (.conj (BoundedFormula.pairMembershipFormula (w 0) (w 4) (old 4)).toFormula
            (reindex ![w 1, old 5, w 2, w 3, w 4, old 6, old 7, old 8]
              (refinementOutputCodeFormula kind)))))))

end SetFormula
namespace TransitiveGround
variable (M : TransitiveGround.{u})

noncomputable def refinementIndexNameGraph (kind : Fin 3)
    (I UF FF CF T P order top : ZFSet.{u}) : ZFSet.{u} :=
  ZFSet.sep (fun z => Realize M.sets (refinementIndexNameGraphFormula kind)
    (extend z ![I, UF, FF, CF, T, P, order, top]))
      (ZFSet.prod I (M.refinementNameBound T P top))

end TransitiveGround
end PartitionPilot.Forcing



namespace PartitionPilot.Forcing.TransitiveGround
open SetRealization SetFormula
universe u
variable (M : TransitiveGround.{u})
variable {G P L : Type u} [Group G] [PartialOrder P] [OrderTop P] [PartialOrder L]
variable (a : PosetAction G P) (s : Presentation P) (b : Presentation L) (d : PosetAction G L)

noncomputable def niceRefinementNameGraph (kind : Fin 3) (level T1 T2 : ZFSet.{u})
    (valid1 : ∀ z ∈ T1, IsName s z) : ZFSet.{u} :=
  let I := M.niceRefinementIndices a s b d level T1 T2 valid1
  let bounds := M.niceRefinementIndexBounds s b level T1 T2
  M.refinementIndexNameGraph kind I (refinementIndexFieldGraph I (bounds 3) 3)
    (refinementIndexFieldGraph I (bounds 4) 4) (refinementIndexFieldGraph I (bounds 5) 5)
    T1 s.carrier s.conditionOrder (s.encode ⊤)

variable {level T1 T2 : ZFSet.{u}} {valid1 : ∀ z ∈ T1, IsName s z} {valid2 : ∀ z ∈ T2, IsName s z}
variable (system : NiceRefinementIndexSystem M a s b d level T1 T2 valid1 valid2)

include system in
theorem niceRefinementIndex_field_entry (C E : L) (U Rf Rc : (M.nameDomain s).names)
    (member : refinementIndexCode level (b.encode C) (b.encode E) U.val.val Rf.val.val Rc.val.val ∈
      M.niceRefinementIndices a s b d level T1 T2 valid1) (j : Fin 6) (z : ZFSet.{u}) :
    ZFSet.pair (refinementIndexCode level (b.encode C) (b.encode E) U.val.val Rf.val.val Rc.val.val) z ∈
      refinementIndexFieldGraph (M.niceRefinementIndices a s b d level T1 T2 valid1)
        (M.niceRefinementIndexBounds s b level T1 T2 j) j ↔
      z = (![level, b.encode C, b.encode E, U.val.val, Rf.val.val, Rc.val.val] : Fin 6 → ZFSet.{u}) j := by
  let I := M.niceRefinementIndices a s b d level T1 T2 valid1
  let fields : Fin 6 → ZFSet.{u} := ![level, b.encode C, b.encode E, U.val.val, Rf.val.val, Rc.val.val]
  let B := M.niceRefinementIndexBounds s b level T1 T2 j
  change ZFSet.pair (nonemptyTupleCode 5 fields) z ∈ refinementIndexFieldGraph I B j ↔ z = fields j
  constructor
  · intro entry
    exact ((refinementIndexFieldGraph_entry I B fields j z).1 entry).2.2
  · intro equal
    obtain ⟨v, hv, _⟩ := (system.field_function j).2 _ member
    have value : v = fields j := ((refinementIndexFieldGraph_entry I B fields j v).1 hv).2.2
    exact equal.symm ▸ (value ▸ hv)

end PartitionPilot.Forcing.TransitiveGround




end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Definability_GroundPackedRefinementFormulaData
attribute [-instance] _root_.OAI.PartitionPilot.Forcing.GroundMainPrefix.withTopSmall
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace PartitionPilot.Forcing
open SetRealization SetFormula
universe u

namespace SetFormula

def stageOneSingleBodyAt {n : Nat} (d : Fin 15 → Fin n) (f : Fin 7 → Fin n)
    (t u w lower : Fin n) : SetFormula n :=
  .conj (.mem (f 0) (d 10))
    (.conj (.mem (f 1) (d 10))
    (.conj (.mem (f 5) (d 14))
    (.conj (.mem (f 6) (d 14))
    (.conj ((BoundedFormula.pairMembershipFormula t (f 0) (d 1)).toFormula)
    (.conj ((BoundedFormula.pairMembershipFormula t (f 1) (d 2)).toFormula)
    (.conj ((BoundedFormula.pairMembershipFormula t (f 2) (d 3)).toFormula)
    (.conj ((BoundedFormula.pairMembershipFormula t (f 3) (d 4)).toFormula)
    (.conj ((BoundedFormula.pairMembershipFormula t (f 4) (d 5)).toFormula)
    (.conj (stageOneClassAt (f 5) (d 6) (f 4) u (d 7) (d 8) (d 9))
    (.conj (stageOneClassAt (f 6) (d 6) (f 3) w (d 7) (d 8) (d 9))
    (.conj (stageOneForcingAt refinementActivityFormula lower (d 7) (d 8) (extend u (extend w (extend (f 2) Fin.elim0))))
    (.conj (stageOneProfileAt (d 7) (d 8) lower (d 10) (d 11) (d 13) (f 1) (f 5) (f 6))
    ((stageOneCompatibilityAt (d 7) (d 8) lower (d 13) (d 12) (f 0) t (f 5) (f 6)))))))))))))))

def stageOneSingleAt {n : Nat} (d : Fin 15 → Fin n) (t u w lower : Fin n) : SetFormula n :=
  exBlock 7 (stageOneSingleBodyAt (fun j => suffixIndex n 7 (d j)) (prefixIndex n 7)
    (suffixIndex n 7 t) (suffixIndex n 7 u) (suffixIndex n 7 w) (suffixIndex n 7 lower))

end SetFormula

namespace SetFormula

def stageOneCollisionBodyAt {n : Nat} (d : Fin 15 → Fin n) (f : Fin 6 → Fin n)
    (t u u' w w' lower : Fin n) : SetFormula n :=
  .conj (.mem (f 2) (d 14))
    (.conj (.mem (f 3) (d 14))
    (.conj (.mem (f 4) (d 14))
    (.conj (.mem (f 5) (d 14))
    (.conj ((BoundedFormula.pairMembershipFormula t (f 0) (d 4)).toFormula)
    (.conj ((BoundedFormula.pairMembershipFormula t (f 1) (d 5)).toFormula)
    (.conj (stageOneClassAt (f 2) (d 6) (f 1) u (d 7) (d 8) (d 9))
    (.conj (stageOneClassAt (f 3) (d 6) (f 1) u' (d 7) (d 8) (d 9))
    (.conj (stageOneClassAt (f 4) (d 6) (f 0) w (d 7) (d 8) (d 9))
    (.conj (stageOneClassAt (f 5) (d 6) (f 0) w' (d 7) (d 8) (d 9))
    ((stageOneForcingAt refinementCollisionFormula lower (d 7) (d 8) (extend (f 2) (extend (f 3) (extend (f 4) (extend (f 5) Fin.elim0)))))))))))))))

def stageOneCollisionAt {n : Nat} (d : Fin 15 → Fin n) (t u u' w w' lower : Fin n) : SetFormula n :=
  exBlock 6 (stageOneCollisionBodyAt (fun j => suffixIndex n 6 (d j)) (prefixIndex n 6)
    (suffixIndex n 6 t) (suffixIndex n 6 u) (suffixIndex n 6 u')
    (suffixIndex n 6 w) (suffixIndex n 6 w') (suffixIndex n 6 lower))

end SetFormula

namespace SetFormula

def stageOneSinglesFormula {n : Nat} (d : Fin 15 → Fin n) (A lower : Fin n) : SetFormula n :=
  let old := suffixIndex n 3
  let v := prefixIndex n 3
  allBlock 3 (imp (BoundedFormula.conj (.mem (v 0) (old (d 0)))
    (.conj (.mem (v 1) (old (d 6))) (.conj (.mem (v 2) (old (d 6)))
      (BoundedFormula.rightTripleMembershipFormula (v 0) (v 1) (v 2) (old A))))).toFormula
    (stageOneSingleAt (fun j => old (d j)) (v 0) (v 1) (v 2) (old lower)))

def stageOneCollisionsFormula {n : Nat} (d : Fin 15 → Fin n) (A lower : Fin n) : SetFormula n :=
  let old := suffixIndex n 5
  let v := prefixIndex n 5
  allBlock 5 (imp (BoundedFormula.conj (.mem (v 0) (old (d 0)))
    (.conj (.mem (v 1) (old (d 6))) (.conj (.mem (v 2) (old (d 6)))
      (.conj (.mem (v 3) (old (d 6))) (.conj (.mem (v 4) (old (d 6)))
        (.conj (BoundedFormula.rightTripleMembershipFormula (v 0) (v 1) (v 3) (old A))
          (BoundedFormula.rightTripleMembershipFormula (v 0) (v 2) (v 4) (old A)))))))).toFormula
    (stageOneCollisionAt (fun j => old (d j)) (v 0) (v 1) (v 2) (v 3) (v 4) (old lower)))

def stageOneTestsFormula {n : Nat} (d : Fin 15 → Fin n) (A lower : Fin n) : SetFormula n :=
  .conj (stageOneSinglesFormula d A lower) (stageOneCollisionsFormula d A lower)

end SetFormula

namespace SetFormula

def stageTwoConditionFormula {n : Nat} (d : Fin 15 → Fin n)
    (levels alpha z : Fin n) : SetFormula n :=
  let old := suffixIndex n 4
  let v := prefixIndex n 4
  exBlock 4 (.conj
    (BoundedFormula.orderedPairFormula (old z) (v 0) (v 1)).toFormula
    (.conj (BoundedFormula.assignmentCutFormula (v 2) (old levels) (old alpha) (v 1)).toFormula
      (.conj (BoundedFormula.orderedPairFormula (v 3) (v 0) (v 2)).toFormula
        (.conj (.mem (v 3) (old (d 7)))
          (stageOneTestsFormula (fun j => old (d j)) (v 1) (v 3))))))

end SetFormula

end PartitionPilot.Forcing



namespace PartitionPilot.Forcing
open SetFormula
universe u

theorem refinementFormulaDataCode_injective :
    Function.Injective (refinementFormulaDataCode.{u}) :=
  nonemptyTupleCode_injective 14

theorem packedSuccessorConditionCode_code_iff (M : TransitiveGround.{u})
    (levels alpha : ZFSet.{u}) (d : Fin 15 → ZFSet.{u}) (z : ZFSet.{u}) :
    PackedSuccessorConditionCode M levels alpha (refinementFormulaDataCode d) z ↔
      StageTwoConditionCode M levels alpha d z := by
  constructor
  · rintro ⟨stored, equal, valid⟩
    have same := refinementFormulaDataCode_injective equal
    exact same.symm ▸ valid
  · intro valid
    exact ⟨d, rfl, valid⟩

namespace TransitiveGround
variable (M : TransitiveGround.{u})

theorem refinementFormulaDataCode_fields_mem (d : Fin 15 → ZFSet.{u})
    (ground : refinementFormulaDataCode d ∈ M.sets) : ∀ j, d j ∈ M.sets :=
  M.nonemptyTupleCode_field_mem 14 d ground

end TransitiveGround

end PartitionPilot.Forcing



namespace PartitionPilot.Forcing.TransitiveGround
open SetRealization SetFormula
universe u
variable (M : TransitiveGround.{u}) {G P L : Type u}
variable [Group G] [PartialOrder P] [OrderTop P] [PartialOrder L]
variable (a : PosetAction G P) (s : Presentation P) (b : Presentation L) (d : PosetAction G L)
variable (level T T2 : ZFSet.{u}) (valid : ∀ z ∈ T, IsName s z)

noncomputable def refinementLevelFormulaData : Fin 15 → ZFSet.{u} :=
  let I := M.niceRefinementIndices a s b d level T T2 valid
  let bounds := M.niceRefinementIndexBounds s b level T T2
  ![I, refinementIndexFieldGraph I (bounds 1) 1, refinementIndexFieldGraph I (bounds 2) 2,
    refinementIndexFieldGraph I (bounds 3) 3, refinementIndexFieldGraph I (bounds 4) 4,
    refinementIndexFieldGraph I (bounds 5) 5, T, s.carrier, s.conditionOrder, s.encode ⊤,
    b.carrier, b.conditionOrder, M.niceRefinementNameGraph a s b d 2 level T T2 valid,
    M.niceVisibilityGraph a s b T d.principalFix, M.groundRelations T s.carrier]

end PartitionPilot.Forcing.TransitiveGround



namespace PartitionPilot.Forcing
open SetRealization SetFormula
universe u

namespace SetFormula

def packedSuccessorConditionFormula {n : Nat} (levels alpha data z : Fin n) : SetFormula n :=
  exBlock 15 (.conj
    (BoundedFormula.nonemptyTupleFormula 14 (suffixIndex n 15 data) (prefixIndex n 15)).toFormula
    (stageTwoConditionFormula (prefixIndex n 15) (suffixIndex n 15 levels)
      (suffixIndex n 15 alpha) (suffixIndex n 15 z)))

end SetFormula

end PartitionPilot.Forcing



namespace PartitionPilot.Forcing.TransitiveGround
open SetRealization SetFormula
universe u
variable (M : TransitiveGround.{u}) {G P L : Type u}
variable [Group G] [PartialOrder P] [OrderTop P] [PartialOrder L]
variable (a : PosetAction G P) (s : Presentation P) (b : Presentation L) (d : PosetAction G L)
variable (level T T2 : ZFSet.{u}) (valid : ∀ z ∈ T, IsName s z)

noncomputable def refinementLevelFormulaDataCode : ZFSet.{u} :=
  refinementFormulaDataCode (M.refinementLevelFormulaData a s b d level T T2 valid)

end PartitionPilot.Forcing.TransitiveGround

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Geometry_GroundNiceAssignmentClassFamilies
attribute [-instance] _root_.OAI.PartitionPilot.Forcing.GroundMainPrefix.withTopSmall
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI



namespace PartitionPilot.Forcing.TransitiveGround
open SetRealization SetFormula
universe u
variable (M : TransitiveGround.{u}) {G P L : Type u}
variable [Group G] [PartialOrder P] [OrderTop P] [PartialOrder L]
variable (a : PosetAction G P) (s : Presentation P) (b : Presentation L) (d : PosetAction G L)
variable (level T T2 : ZFSet.{u}) (valid : ∀ z ∈ T, IsName s z)
local notation "data" => M.refinementLevelFormulaData a s b d level T T2 valid

noncomputable def niceAssignmentClassGraphs (A : ZFSet.{u}) (side : Fin 2) : ZFSet.{u} :=
  M.assignmentClassGraph side A (data (Fin.cases 5 (fun _ => 4) side))
    T s.carrier s.conditionOrder (s.encode ⊤)

end PartitionPilot.Forcing.TransitiveGround

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Geometry_RepresentativeIndexSteps
attribute [-instance] _root_.OAI.PartitionPilot.Forcing.GroundMainPrefix.withTopSmall
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace PartitionPilot.Forcing
universe u

noncomputable def assignmentIndices (I T A : ZFSet.{u}) : ZFSet.{u} :=
  relationImage A I (productFirst I (ZFSet.prod T T))

noncomputable def representativeIndexStep (I T Q c X : ZFSet.{u}) : ZFSet.{u} :=
  X ∪ representativeIndexAdditions I T Q c X

end PartitionPilot.Forcing



namespace PartitionPilot.Forcing
universe u
variable (M : TransitiveGround.{u}) (d : Fin 15 → ZFSet.{u})

theorem stageOneRawTests_transfer {A B : ZFSet.{u}} (lower : ZFSet.{u})
    (tests : stageOneRawTests M d A lower)
    (guards : ∀ t ∈ d 0, ∀ u ∈ d 6, ∀ w ∈ d 6,
      stageOneAssignment t u w ∈ B → stageOneAssignment t u w ∈ A) :
    stageOneRawTests M d B lower :=
  ⟨fun t ht u hu w hw entry => tests.1 t ht u hu w hw (guards t ht u hu w hw entry),
    fun t ht u hu u' hu' w hw w' hw' entry entry' =>
      tests.2 t ht u hu u' hu' w hw w' hw'
        (guards t ht u hu w hw entry) (guards t ht u' hu' w' hw' entry')⟩

theorem stageOneRawTests_congr (A B lower : ZFSet.{u})
    (guards : ∀ t ∈ d 0, ∀ u ∈ d 6, ∀ w ∈ d 6,
      stageOneAssignment t u w ∈ A ↔ stageOneAssignment t u w ∈ B) :
    stageOneRawTests M d A lower ↔ stageOneRawTests M d B lower :=
  ⟨fun tests => stageOneRawTests_transfer M d lower tests
      (fun t ht u hu w hw entry => (guards t ht u hu w hw).2 entry),
    fun tests => stageOneRawTests_transfer M d lower tests
      (fun t ht u hu w hw entry => (guards t ht u hu w hw).1 entry)⟩

theorem stageTwoConditionCode_pair_iff (levels alpha row A : ZFSet.{u}) :
    StageTwoConditionCode M levels alpha d (ZFSet.pair row A) ↔
      ZFSet.pair row (assignmentCut levels alpha A) ∈ d 7 ∧
      stageOneRawTests M d A (ZFSet.pair row (assignmentCut levels alpha A)) := by
  constructor
  · rintro ⟨row', A', equal, member, tests⟩
    obtain ⟨rfl, rfl⟩ := ZFSet.pair_injective equal
    exact ⟨member, tests⟩
  · rintro ⟨member, tests⟩
    exact ⟨row, A, rfl, member, tests⟩

end PartitionPilot.Forcing



namespace PartitionPilot.Forcing
universe u





def stageOneRawCrossCollisions (M : TransitiveGround.{u}) (d : Fin 15 → ZFSet.{u})
    (A B lower : ZFSet.{u}) : Prop :=
  ∀ t ∈ d 0, ∀ u ∈ d 6, ∀ u' ∈ d 6, ∀ w ∈ d 6, ∀ w' ∈ d 6,
    stageOneAssignment t u w ∈ A → stageOneAssignment t u' w' ∈ B →
    stageOneRawCollision M d t u u' w w' lower ∧
      stageOneRawCollision M d t u' u w' w lower

end PartitionPilot.Forcing




namespace PartitionPilot.Forcing.TransitiveGround
open SetFormula
universe u
variable (M : TransitiveGround.{u})
variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
variable (unions : Realize M.sets SetFormula.union Fin.elim0)
variable (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)

noncomputable def storedAssignmentClassGraph (A : ZFSet.{u})
    (fields : Fin 15 → ZFSet.{u}) (side : Fin 2) : ZFSet.{u} :=
  M.assignmentClassGraph side (assignmentOnIndices (fields 0) (fields 6) A)
    (fields (Fin.cases 5 (fun _ => 4) side)) (fields 6) (fields 7) (fields 8) (fields 9)

end PartitionPilot.Forcing.TransitiveGround




namespace PartitionPilot.Forcing.TransitiveGround
open SetRealization SetFormula
universe u
variable (M : TransitiveGround.{u})

noncomputable def relationImageDefinition (separation : SeparationSchema M.sets) :
    GroundDefinableFunction M (fun env : Fin 3 → ZFSet.{u} =>
      relationImage (env 0) (env 1) (env 2)) where
  formula := (BoundedFormula.relationImageEqualityFormula 0 1 2 3).toFormula
  closed := fun _ members => M.relationImage_mem separation (members 0) (members 1) (members 2)
  correct := by
    intro env members z hz
    rw [BoundedFormula.realize_toFormula M _ _ (Fin.cases hz members),
      BoundedFormula.truth_relationImageEqualityFormula]
    rfl

end PartitionPilot.Forcing.TransitiveGround

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Definability_AssignmentQueryFormulas
attribute [-instance] _root_.OAI.PartitionPilot.Forcing.GroundMainPrefix.withTopSmall
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PartitionPilot.Forcing
universe u

noncomputable def assignmentQueryRelation (I T C D : ZFSet.{u}) : ZFSet.{u} :=
  ZFSet.sep (fun z => ∃ row L A,
    z = ZFSet.pair (ZFSet.pair row L) (ZFSet.pair row A) ∧
    assignmentOnIndices (assignmentIndices I T L) T A = L) (ZFSet.prod C D)

noncomputable def realizedAssignmentQueries (I T C D : ZFSet.{u}) : ZFSet.{u} :=
  relationImage D C (relationConverse C D (assignmentQueryRelation I T C D))

end PartitionPilot.Forcing

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Definability_CodedLayerRestrictions
attribute [-instance] _root_.OAI.PartitionPilot.Forcing.GroundMainPrefix.withTopSmall
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PartitionPilot.Forcing
universe u

theorem MeetEmbeddingCode.restrictTarget {A L Q rA rL μA μL e : ZFSet.{u}}
    (code : MeetEmbeddingCode A L rA rL μA μL e)
    (values : ∀ x y, ZFSet.pair x y ∈ e → y ∈ Q) :
    MeetEmbeddingCode A Q rA (heightOrderRestriction Q rL) μA
      (graphRestriction (ZFSet.prod Q Q) μL) e := by
  refine ⟨⟨⟨?_, code.injection.function.2⟩, code.injection.injective⟩, ?_, ?_⟩
  · intro z hz
    obtain ⟨x, hx, y, _, rfl⟩ := ZFSet.mem_prod.1 (code.injection.function.1 hz)
    exact ZFSet.pair_mem_prod.2 ⟨hx, values x y hz⟩
  · intro x y x' y' lower first second
    exact (pair_mem_heightOrderRestriction _ _ _ _).2
      ⟨code.monotone x y x' y' lower first second, values x x' first, values y y' second⟩
  · intro x y z x' y' z' meet first second third
    exact pair_mem_graphRestriction.2
      ⟨code.map_meet x y z x' y' z' meet first second third,
        ZFSet.pair_mem_prod.2 ⟨values x x' first, values y y' second⟩⟩

end PartitionPilot.Forcing

end

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Transfinite_RefinementHistoryPrefixLevels
attribute [-instance] _root_.OAI.PartitionPilot.Forcing.GroundMainPrefix.withTopSmall
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open scoped ZFSet


namespace PartitionPilot.Forcing
universe u

theorem refinementHistoryIndices_mono {alpha beta history : ZFSet.{u}}
    (subset : alpha ⊆ beta) :
    refinementHistoryIndices alpha history ⊆ refinementHistoryIndices beta history := by
  intro x hx
  obtain ⟨xi, hxi, I, entry, hi⟩ := (mem_refinementHistoryIndices alpha history x).1 hx
  exact (mem_refinementHistoryIndices beta history x).2 ⟨xi, subset hxi, I, entry, hi⟩

noncomputable def refinementHistoryLevels (alpha history : ZFSet.{u}) : ZFSet.{u} :=
  refinementIndexFieldGraph (refinementHistoryIndices alpha history) alpha 0

theorem pair_mem_refinementHistoryLevels {alpha history : ZFSet.{u}}
    (function : FunctionGraphOn alpha history)
    (literal : ∀ xi I, ZFSet.pair xi I ∈ history → RefinementIndexLevelCode I xi)
    (x xi : ZFSet.{u}) :
    ZFSet.pair x xi ∈ refinementHistoryLevels alpha history ↔
      ∃ I, ZFSet.pair xi I ∈ history ∧ x ∈ I := by
  rw [refinementHistoryLevels, pair_mem_refinementIndexFieldGraph]
  constructor
  · rintro ⟨hx, _, v, eqv, hxi⟩
    obtain ⟨eta, _, I, entry, hi⟩ := (mem_refinementHistoryIndices alpha history x).1 hx
    obtain ⟨w, eqw, hw⟩ := literal eta I entry x hi
    have same := nonemptyTupleCode_injective 5 (eqv.symm.trans eqw)
    have equal : xi = eta := hxi.trans ((congrFun same 0).trans hw)
    exact ⟨I, equal.symm ▸ entry, hi⟩
  · rintro ⟨I, entry, hi⟩
    obtain ⟨v, eqv, hv⟩ := literal xi I entry x hi
    exact ⟨(mem_refinementHistoryIndices alpha history x).2
      ⟨xi, function.pair_source entry, I, entry, hi⟩,
      function.pair_source entry, v, eqv, hv.symm⟩

theorem refinementHistoryLevels_function {alpha history : ZFSet.{u}}
    (literal : ∀ xi I, ZFSet.pair xi I ∈ history → RefinementIndexLevelCode I xi) :
    ZFSet.IsFunc (refinementHistoryIndices alpha history) alpha
      (refinementHistoryLevels alpha history) := by
  apply refinementIndexFieldGraph_function
  intro x hx
  obtain ⟨xi, hxi, I, entry, hi⟩ := (mem_refinementHistoryIndices alpha history x).1 hx
  obtain ⟨v, eqv, hv⟩ := literal xi I entry x hi
  exact ⟨v, eqv, hv.symm ▸ hxi⟩





noncomputable def refinementHistoryAssignmentLevels (alpha history T : ZFSet.{u}) : ZFSet.{u} :=
  assignmentIndexLevels (refinementHistoryIndices alpha history) T alpha
    (refinementHistoryLevels alpha history)

theorem mem_refinementHistoryAssignments (alpha history T z : ZFSet.{u}) :
    z ∈ stageOneAssignments (refinementHistoryIndices alpha history) T ↔
      ∃ xi ∈ alpha, ∃ I, ZFSet.pair xi I ∈ history ∧ z ∈ stageOneAssignments I T := by
  rw [mem_stageOneAssignments]
  constructor
  · rintro ⟨i, hi, u, hu, w, hw, rfl⟩
    obtain ⟨xi, hxi, I, entry, member⟩ := (mem_refinementHistoryIndices alpha history i).1 hi
    exact ⟨xi, hxi, I, entry,
      (stageOneAssignment_mem_assignments I T i u w).2 ⟨member, hu, hw⟩⟩
  · rintro ⟨xi, hxi, I, entry, member⟩
    obtain ⟨i, hi, u, hu, w, hw, rfl⟩ := (mem_stageOneAssignments I T z).1 member
    exact ⟨i, (mem_refinementHistoryIndices alpha history i).2 ⟨xi, hxi, I, entry, hi⟩,
      u, hu, w, hw, rfl⟩

theorem pair_mem_refinementHistoryAssignmentLevels {alpha history : ZFSet.{u}}
    (function : FunctionGraphOn alpha history)
    (literal : ∀ xi I, ZFSet.pair xi I ∈ history → RefinementIndexLevelCode I xi)
    (T z xi : ZFSet.{u}) :
    ZFSet.pair z xi ∈ refinementHistoryAssignmentLevels alpha history T ↔
      ∃ I, ZFSet.pair xi I ∈ history ∧ z ∈ stageOneAssignments I T := by
  rw [refinementHistoryAssignmentLevels, pair_mem_assignmentIndexLevels]
  constructor
  · rintro ⟨i, _, u, hu, w, hw, rfl, _, entry⟩
    obtain ⟨I, hI, hi⟩ := (pair_mem_refinementHistoryLevels function literal i xi).1 entry
    exact ⟨I, hI, (stageOneAssignment_mem_assignments I T i u w).2 ⟨hi, hu, hw⟩⟩
  · rintro ⟨I, entry, member⟩
    obtain ⟨i, hi, u, hu, w, hw, rfl⟩ := (mem_stageOneAssignments I T z).1 member
    exact ⟨i, (mem_refinementHistoryIndices alpha history i).2
      ⟨xi, function.pair_source entry, I, entry, hi⟩,
      u, hu, w, hw, rfl, function.pair_source entry,
      (pair_mem_refinementHistoryLevels function literal i xi).2 ⟨I, entry, hi⟩⟩

theorem refinementHistoryAssignmentLevels_entry {alpha history : ZFSet.{u}}
    (function : FunctionGraphOn alpha history)
    (literal : ∀ xi I, ZFSet.pair xi I ∈ history → RefinementIndexLevelCode I xi)
    (T i u w xi : ZFSet.{u}) :
    ZFSet.pair (stageOneAssignment i u w) xi ∈ refinementHistoryAssignmentLevels alpha history T ↔
      ∃ I, ZFSet.pair xi I ∈ history ∧ i ∈ I ∧ u ∈ T ∧ w ∈ T := by
  rw [pair_mem_refinementHistoryAssignmentLevels function literal]
  simp only [stageOneAssignment_mem_assignments]

theorem refinementHistoryAssignmentLevels_function {alpha history T : ZFSet.{u}}
    (literal : ∀ xi I, ZFSet.pair xi I ∈ history → RefinementIndexLevelCode I xi) :
    ZFSet.IsFunc (stageOneAssignments (refinementHistoryIndices alpha history) T) alpha
      (refinementHistoryAssignmentLevels alpha history T) :=
  assignmentIndexLevels_function (refinementHistoryLevels_function literal)

theorem refinementHistoryAssignmentCut_eq {alpha beta history : ZFSet.{u}}
    (function : FunctionGraphOn alpha history)
    (literal : ∀ xi I, ZFSet.pair xi I ∈ history → RefinementIndexLevelCode I xi)
    (subset : beta ⊆ alpha) (T A : ZFSet.{u}) :
    assignmentCut (refinementHistoryAssignmentLevels alpha history T) beta A =
      ZFSet.sep (fun z => z ∈ stageOneAssignments (refinementHistoryIndices beta history) T) A := by
  apply ZFSet.ext
  intro z
  rw [mem_assignmentCut, ZFSet.mem_sep]
  apply and_congr_right
  intro _
  rw [mem_refinementHistoryAssignments]
  constructor
  · rintro ⟨xi, hxi, entry⟩
    obtain ⟨I, hI, member⟩ := (pair_mem_refinementHistoryAssignmentLevels function literal T z xi).1 entry
    exact ⟨xi, hxi, I, hI, member⟩
  · rintro ⟨xi, hxi, I, entry, member⟩
    have _ : xi ∈ alpha := subset hxi
    exact ⟨xi, hxi, (pair_mem_refinementHistoryAssignmentLevels function literal T z xi).2
      ⟨I, entry, member⟩⟩

end PartitionPilot.Forcing



namespace PartitionPilot.Forcing
universe u

theorem refinementDataHistoryField_entry {stages history alpha : ZFSet.{u}}
    (function : FunctionGraphOn stages history) (d : Fin 15 → ZFSet.{u})
    (entry : ZFSet.pair alpha (refinementFormulaDataCode d) ∈ history) (j : Fin 15) (y : ZFSet.{u}) :
    ZFSet.pair alpha y ∈ refinementDataHistoryField stages history j ↔ y = d j := by
  rw [pair_mem_refinementDataHistoryField]
  constructor
  · rintro ⟨_, fields, stored, value⟩
    have same := refinementFormulaDataCode_injective (function.unique stored entry)
    exact value.trans (congrFun same j)
  · intro equal
    exact ⟨function.pair_source entry, d, entry, equal⟩

theorem refinementDataHistoryField_function {stages history : ZFSet.{u}}
    (function : FunctionGraphOn stages history)
    (decoded : ∀ alpha data, ZFSet.pair alpha data ∈ history →
      ∃ d : Fin 15 → ZFSet.{u}, data = refinementFormulaDataCode d) (j : Fin 15) :
    FunctionGraphOn stages (refinementDataHistoryField stages history j) := by
  refine ⟨tupleFieldBound 14 (⋃₀ ⋃₀ history), fun _ member => (ZFSet.mem_sep.1 member).1, ?_⟩
  intro alpha halpha
  obtain ⟨data, entry⟩ := function.total halpha
  obtain ⟨d, rfl⟩ := decoded alpha data entry
  refine ⟨d j, (refinementDataHistoryField_entry function d entry j _).2 rfl, ?_⟩
  intro y member
  exact (refinementDataHistoryField_entry function d entry j y).1 member

theorem refinementDataHistoryField_index_levels {stages history : ZFSet.{u}}
    (literal : ∀ alpha (d : Fin 15 → ZFSet.{u}),
      ZFSet.pair alpha (refinementFormulaDataCode d) ∈ history → RefinementIndexLevelCode (d 0) alpha) :
    ∀ alpha I, ZFSet.pair alpha I ∈ refinementDataHistoryField stages history 0 →
      RefinementIndexLevelCode I alpha := by
  intro alpha I entry
  obtain ⟨_, d, stored, rfl⟩ := (pair_mem_refinementDataHistoryField stages history alpha I 0).1 entry
  exact literal alpha d stored





theorem refinementDataHistoryField_domain_restrict {stages earlier history : ZFSet.{u}}
    (subset : earlier ⊆ stages) (j : Fin 15) :
    refinementDataHistoryField earlier history j =
      graphRestriction earlier (refinementDataHistoryField stages history j) := by
  apply ZFSet.ext
  intro z
  constructor
  · intro member
    obtain ⟨alpha, halpha, d, entry, rfl⟩ := (mem_refinementDataHistoryField _ _ _ _).1 member
    exact pair_mem_graphRestriction.2
      ⟨(pair_mem_refinementDataHistoryField _ _ _ _ _).2 ⟨subset halpha, d, entry, rfl⟩, halpha⟩
  · intro member
    obtain ⟨alpha, halpha, y, rfl, entry⟩ := mem_graphRestriction.1 member
    obtain ⟨_, d, stored, rfl⟩ := (pair_mem_refinementDataHistoryField _ _ _ _ _).1 entry
    exact (pair_mem_refinementDataHistoryField _ _ _ _ _).2 ⟨halpha, d, stored, rfl⟩

theorem refinementDataHistoryField_history_restrict (stages history : ZFSet.{u}) (j : Fin 15) :
    refinementDataHistoryField stages (graphRestriction stages history) j =
      refinementDataHistoryField stages history j := by
  apply ZFSet.ext
  intro z
  rw [mem_refinementDataHistoryField, mem_refinementDataHistoryField]
  constructor
  · rintro ⟨alpha, halpha, d, entry, equal⟩
    exact ⟨alpha, halpha, d, (pair_mem_graphRestriction.1 entry).1, equal⟩
  · rintro ⟨alpha, halpha, d, entry, equal⟩
    exact ⟨alpha, halpha, d, pair_mem_graphRestriction.2 ⟨entry, halpha⟩, equal⟩

theorem refinementDataHistoryField_restrict {stages earlier history : ZFSet.{u}}
    (subset : earlier ⊆ stages) (j : Fin 15) :
    refinementDataHistoryField earlier (graphRestriction earlier history) j =
      graphRestriction earlier (refinementDataHistoryField stages history j) := by
  rw [refinementDataHistoryField_history_restrict, refinementDataHistoryField_domain_restrict subset]





theorem refinementHistoryIndices_restrict {alpha beta history : ZFSet.{u}}
    (below : beta ⊆ alpha) :
    refinementHistoryIndices beta (graphRestriction alpha history) =
      refinementHistoryIndices beta history := by
  apply ZFSet.ext
  intro x
  rw [mem_refinementHistoryIndices, mem_refinementHistoryIndices]
  constructor
  · rintro ⟨xi, hxi, I, entry, member⟩
    exact ⟨xi, hxi, I, (pair_mem_graphRestriction.1 entry).1, member⟩
  · rintro ⟨xi, hxi, I, entry, member⟩
    exact ⟨xi, hxi, I, pair_mem_graphRestriction.2 ⟨entry, below hxi⟩, member⟩

theorem refinementHistoryAssignmentCut_restrict {stages alpha beta history : ZFSet.{u}}
    (function : FunctionGraphOn stages history)
    (literal : ∀ xi I, ZFSet.pair xi I ∈ history → RefinementIndexLevelCode I xi)
    (subset : alpha ⊆ stages) (below : beta ⊆ alpha) (T A : ZFSet.{u}) :
    assignmentCut (refinementHistoryAssignmentLevels alpha (graphRestriction alpha history) T) beta A =
      assignmentCut (refinementHistoryAssignmentLevels stages history T) beta A := by
  rw [refinementHistoryAssignmentCut_eq (function.restrict subset)
    (fun xi I entry => literal xi I (pair_mem_graphRestriction.1 entry).1) below]
  rw [refinementHistoryAssignmentCut_eq function literal (fun _ h => subset (below h))]
  rw [refinementHistoryIndices_restrict below]

theorem refinementDataHistoryIndices_prefix {stages alpha beta history : ZFSet.{u}}
    (subset : alpha ⊆ stages) (below : beta ⊆ alpha) :
    refinementHistoryIndices beta
      (refinementDataHistoryField alpha (graphRestriction alpha history) 0) =
        refinementHistoryIndices beta (refinementDataHistoryField stages history 0) := by
  rw [refinementDataHistoryField_restrict subset, refinementHistoryIndices_restrict below]

theorem refinementDataHistoryAssignmentCut_prefix {stages alpha beta history : ZFSet.{u}}
    (function : FunctionGraphOn stages history)
    (decoded : ∀ xi data, ZFSet.pair xi data ∈ history →
      ∃ d : Fin 15 → ZFSet.{u}, data = refinementFormulaDataCode d)
    (literal : ∀ xi (d : Fin 15 → ZFSet.{u}),
      ZFSet.pair xi (refinementFormulaDataCode d) ∈ history → RefinementIndexLevelCode (d 0) xi)
    (subset : alpha ⊆ stages) (below : beta ⊆ alpha) (T A : ZFSet.{u}) :
    assignmentCut (refinementHistoryAssignmentLevels alpha
      (refinementDataHistoryField alpha (graphRestriction alpha history) 0) T) beta A =
        assignmentCut (refinementHistoryAssignmentLevels stages
          (refinementDataHistoryField stages history 0) T) beta A := by
  rw [refinementDataHistoryField_restrict subset]
  exact refinementHistoryAssignmentCut_restrict
    (refinementDataHistoryField_function function decoded 0)
    (refinementDataHistoryField_index_levels literal) subset below T A

end PartitionPilot.Forcing

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Forcing_ForcingHistoryTestDecomposition
attribute [-instance] _root_.OAI.PartitionPilot.Forcing.GroundMainPrefix.withTopSmall
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PartitionPilot.Forcing
universe u

theorem forcingHistoryConditionCode_lookup_iff {M : TransitiveGround.{u}}
    {stages history levels z : ZFSet.{u}} (function : FunctionGraphOn stages history) :
    ForcingHistoryConditionCode M stages history levels z ↔
      ∀ alpha ∈ stages, ∀ data, ZFSet.pair alpha data ∈ history →
        PackedSuccessorConditionCode M levels alpha data z := by
  constructor
  · intro valid alpha member data entry
    obtain ⟨other, old, checked⟩ := valid alpha member
    exact function.unique old entry ▸ checked
  · intro valid alpha member
    obtain ⟨data, entry⟩ := function.total member
    exact ⟨data, entry, valid alpha member data entry⟩

end PartitionPilot.Forcing

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Definability_ForcingHistoryConditionFormulas
attribute [-instance] _root_.OAI.PartitionPilot.Forcing.GroundMainPrefix.withTopSmall
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PartitionPilot.Forcing
open SetFormula
universe u
namespace SetFormula

def forcingHistoryEntryFormula {n : Nat} (alpha history levels z : Fin n) : SetFormula n :=
  .ex (.conj (BoundedFormula.pairMembershipFormula alpha.succ 0 history.succ).toFormula
    (packedSuccessorConditionFormula levels.succ alpha.succ 0 z.succ))

def forcingHistoryConditionFormula {n : Nat} (stages history levels z : Fin n) : SetFormula n :=
  .all (.imp (.mem 0 stages.succ)
    (forcingHistoryEntryFormula 0 history.succ levels.succ z.succ))

end SetFormula
end PartitionPilot.Forcing

end

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Forcing_GroundForcingHistorySuccessors
attribute [-instance] _root_.OAI.PartitionPilot.Forcing.GroundMainPrefix.withTopSmall
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PartitionPilot.Forcing.TransitiveGround

section
open SetRealization SetFormula
universe u
variable (M : TransitiveGround.{u})

noncomputable def stageTwoConditions (rawRowCarrier I levels alpha : ZFSet.{u})
    (d : Fin 15 → ZFSet.{u}) : ZFSet.{u} :=
  ZFSet.sep (StageTwoConditionCode M levels alpha d)
    (M.stageOneCandidateBound rawRowCarrier I (d 6))

end

open SetFormula
universe u
variable (M : TransitiveGround.{u})

noncomputable def forcingHistoryConditions (rows I T stages history levels : ZFSet.{u}) : ZFSet.{u} :=
  ZFSet.sep (ForcingHistoryConditionCode M stages history levels) (M.stageOneCandidateBound rows I T)

theorem mem_forcingHistoryConditions (rows I T stages history levels z : ZFSet.{u}) :
    z ∈ M.forcingHistoryConditions rows I T stages history levels ↔
      z ∈ M.stageOneCandidateBound rows I T ∧ ForcingHistoryConditionCode M stages history levels z :=
  ZFSet.mem_sep

end PartitionPilot.Forcing.TransitiveGround

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Definability_ForcingHistoryOutputFormulas
attribute [-instance] _root_.OAI.PartitionPilot.Forcing.GroundMainPrefix.withTopSmall
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PartitionPilot.Forcing
open SetRealization SetFormula
universe u

namespace SetFormula

def forcingHistoryConditionsOutputFormula {n : Nat}
    (output rows I T stages history levels N : Fin n) : SetFormula n :=
  exactSetFormula output (.conj
    (stageOneCandidateFormula rows.succ I.succ T.succ N.succ 0)
    (forcingHistoryConditionFormula stages.succ history.succ levels.succ 0))

end SetFormula

end PartitionPilot.Forcing

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Definability_GroundCompositionFamilyFormulas
attribute [-instance] _root_.OAI.PartitionPilot.Forcing.GroundMainPrefix.withTopSmall
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PartitionPilot.Forcing

universe u

namespace TransitiveGround
open SetFormula
variable (M : TransitiveGround.{u})

theorem realize_compositionFamilyEntryFormula {n} (z K I J B D L Es Ss : Fin n)
    (env : Fin n → ZFSet.{u}) (members : ∀ i, env i ∈ M.sets) :
    Realize M.sets (compositionFamilyEntryFormula z K I J B D L Es Ss) env ↔
      env z ∈ M.groundPairCompositions (env K) (env I) (env J) (env B) (env D) (env L) (env Es) (env Ss) := by
  simp only [compositionFamilyEntryFormula, realize_ex]
  constructor
  · rintro ⟨i, hiM, j, hjM, ell, hellM, f, hfM, c, hcM, body⟩
    have extended : ∀ a, extend c (extend f (extend ell (extend j (extend i env)))) a ∈ M.sets :=
      Fin.cases hcM (Fin.cases hfM (Fin.cases hellM (Fin.cases hjM (Fin.cases hiM members))))
    have spec := (BoundedFormula.realize_toFormula M _ _ extended).1 body
    simp only [BoundedFormula.Truth, BoundedFormula.truth_orderedTripleFormula,
      BoundedFormula.truth_pairMembershipFormula, BoundedFormula.truth_compositionGraphFormula] at spec
    change i ∈ env I ∧ j ∈ env J ∧ env z = ZFSet.pair (ZFSet.pair i j) c ∧
      ZFSet.pair i j ∈ env K ∧ ZFSet.pair j ell ∈ env Es ∧ ZFSet.pair i f ∈ env Ss ∧
      c = relationCompose (env B) (env D) (env L) ell f at spec
    obtain ⟨hi, hj, equal, hk, first, second, output⟩ := spec
    rw [equal]
    exact (pair_mem_pairCompositionFamily _ _ _ _ _ _ _ _ _ _ _ _).2
      ⟨hk, hi, hj, (M.mem_groundRelations _ _ _).2
        ⟨hcM, fun w hw => (ZFSet.mem_sep.1 (output ▸ hw)).1⟩, ell, f, first, second, output⟩
  · intro member
    unfold groundPairCompositions pairCompositionFamily at member
    obtain ⟨_, i, hi, j, hj, ell, _, f, _, c, hc, equal, hk, first, second, output⟩ :=
      ZFSet.mem_sep.1 member
    have hiM := M.transitive (members I) hi
    have hjM := M.transitive (members J) hj
    have hellM := M.pair_right (M.transitive (members Es) first)
    have hfM := M.pair_right (M.transitive (members Ss) second)
    have hcM := ((M.mem_groundRelations _ _ _).1 hc).1
    refine ⟨i, hiM, j, hjM, ell, hellM, f, hfM, c, hcM, ?_⟩
    apply (BoundedFormula.realize_toFormula M _ _
      (Fin.cases hcM (Fin.cases hfM (Fin.cases hellM (Fin.cases hjM (Fin.cases hiM members)))))).2
    simp only [BoundedFormula.Truth, BoundedFormula.truth_orderedTripleFormula,
      BoundedFormula.truth_pairMembershipFormula, BoundedFormula.truth_compositionGraphFormula]
    exact ⟨hi, hj, equal, hk, first, second, output⟩

theorem realize_compositionFamilyFormula
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    {n} (family K I J B D L Es Ss : Fin n)
    (env : Fin n → ZFSet.{u}) (members : ∀ i, env i ∈ M.sets) :
    Realize M.sets (compositionFamilyFormula family K I J B D L Es Ss) env ↔
      env family = M.groundPairCompositions (env K) (env I) (env J) (env B) (env D) (env L) (env Es) (env Ss) := by
  apply M.realize_exactSetFormula family _ env (members family)
  · intro z member
    unfold groundPairCompositions pairCompositionFamily at member
    obtain ⟨k, hk, c, hc, rfl⟩ := ZFSet.mem_prod.1 (ZFSet.mem_sep.1 member).1
    exact M.orderedPair_mem pairing (M.transitive (members K) hk)
      ((M.mem_groundRelations _ _ _).1 hc).1
  · intro z hz
    exact M.realize_compositionFamilyEntryFormula 0 K.succ I.succ J.succ B.succ D.succ L.succ Es.succ Ss.succ
      (extend z env) (Fin.cases hz members)

end TransitiveGround

end PartitionPilot.Forcing

end

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Definability_GroundEligibleTaskSetRecognition
attribute [-instance] _root_.OAI.PartitionPilot.Forcing.GroundMainPrefix.withTopSmall
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PartitionPilot.Forcing
open SetFormula
universe u
namespace SetFormula

def groundEligibleTaskElementFormula {n} (z P G r μ A Labels : Fin n) : SetFormula n :=
  let old := suffixIndex n 6
  let field := prefixIndex n 6
  exBlock 6 (.conj (.mem (field 5) (old Labels))
    (.conj (BoundedFormula.literalTaskFormula (old z)
      (field 0) (field 1) (field 2) (field 3) (field 4) (field 5)).toFormula
      (BoundedFormula.eligibleTaskFormula (old P) (old G) (old r) (old μ) (old A)
        (field 0) (field 1) (field 2) (field 3) (field 4)).toFormula))

def groundEligibleTasksFormula {n} (output P G r μ A Labels : Fin n) : SetFormula n :=
  exactSetFormula output
    (groundEligibleTaskElementFormula 0 P.succ G.succ r.succ μ.succ A.succ Labels.succ)

end SetFormula

end PartitionPilot.Forcing

end

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Definability_GroundFlatCarrierSequences
attribute [-instance] _root_.OAI.PartitionPilot.Forcing.GroundMainPrefix.withTopSmall
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PartitionPilot.Forcing
open SetRealization SetFormula
universe u
variable {R : Type u} (c : Presentation R) (Q B : ZFSet.{u})
variable (shape : Q ⊆ ZFSet.prod c.carrier B)
local notation "s" => SetMembers.presentation Q

noncomputable def flatCarrierRow : SetMembers Q → R :=
  (s).decodeFunction c (rowAssignmentRows Q c.carrier B) (rowAssignmentRows_function shape)

noncomputable def flatCarrierData : SetMembers Q → SetMembers B :=
  (s).decodeFunction (SetMembers.presentation B) (rowAssignmentData Q c.carrier B) (rowAssignmentData_function shape)

theorem flatCarrier_coordinates (p : SetMembers Q) :
    SetMembers.raw p = ZFSet.pair (c.encode (flatCarrierRow c Q B shape p))
      (SetMembers.raw (flatCarrierData c Q B shape p)) := by
  have rowEdge := (s).decodeFunction_mem c (rowAssignmentRows Q c.carrier B) (rowAssignmentRows_function shape) p
  have dataEdge := (s).decodeFunction_mem (SetMembers.presentation B)
    (rowAssignmentData Q c.carrier B) (rowAssignmentData_function shape) p
  change ZFSet.pair (SetMembers.raw p) (c.encode (flatCarrierRow c Q B shape p)) ∈ _ at rowEdge
  change ZFSet.pair (SetMembers.raw p) (SetMembers.raw (flatCarrierData c Q B shape p)) ∈ _ at dataEdge
  obtain ⟨row, _hr, A, _hA, code⟩ := ZFSet.mem_prod.1 (shape (SetMembers.raw_mem p))
  rw [code, rowAssignmentRows_entry] at rowEdge
  rw [code, rowAssignmentData_entry] at dataEdge
  rw [rowEdge.2.2.2, dataEdge.2.2.2]
  exact code

theorem flatCarrier_coordinateGraphs :
    (s).graph c (flatCarrierRow c Q B shape) = rowAssignmentRows Q c.carrier B ∧
    (s).graph (SetMembers.presentation B) (flatCarrierData c Q B shape) = rowAssignmentData Q c.carrier B :=
  ⟨(s).graph_decodeFunction c _ _, (s).graph_decodeFunction (SetMembers.presentation B) _ _⟩

end PartitionPilot.Forcing

end

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Definability_GroundSeparatorFamilyFormulas
attribute [-instance] _root_.OAI.PartitionPilot.Forcing.GroundMainPrefix.withTopSmall
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open scoped ZFSet

section

namespace PartitionPilot.Forcing

universe u

theorem mem_recursiveSeparatorFamily (K I J D L Maps Ss z : ZFSet.{u}) :
    z ∈ recursiveSeparatorFamily K I J D L Maps Ss ↔
      ∃ i ∈ I, ∃ j ∈ J, ∃ S, ∃ e ∈ D, ∃ y ∈ L,
        z = ZFSet.pair (ZFSet.pair i j) y ∧ ZFSet.pair i j ∈ K ∧
          ZFSet.pair i S ∈ Maps ∧ ZFSet.pair j e ∈ Ss ∧ ZFSet.pair e y ∈ S := by
  unfold recursiveSeparatorFamily familyEvaluationGraph
  constructor
  · intro member
    obtain ⟨_, k, hk, S, _, e, he, y, hy, equal, first, second, image⟩ := ZFSet.mem_sep.1 member
    obtain ⟨_, _, i, hi, j, hj, rfl, mapEntry⟩ :=
      (pair_mem_pairFieldGraph true I J K (⋃₀ ⋃₀ Maps) Maps k S).1 first
    have sepEntry := ((pairFieldGraph_entry_iff false hi hj).1 second).2.2
    exact ⟨i, hi, j, hj, S, e, he, y, hy, equal, hk, mapEntry, sepEntry, image⟩
  · rintro ⟨i, hi, j, hj, S, e, he, y, hy, equal, hk, mapEntry, sepEntry, image⟩
    refine ZFSet.mem_sep.2 ⟨equal.symm ▸ ZFSet.pair_mem_prod.2 ⟨hk, hy⟩,
      ZFSet.pair i j, hk, S, pair_second_mem_doubleUnion mapEntry, e, he, y, hy, equal, ?_, ?_, image⟩
    · exact (pairFirstField_entry_iff hi hj).2 ⟨hk, mapEntry⟩
    · exact (pairFieldGraph_entry_iff false hi hj).2 ⟨hk, he, sepEntry⟩

namespace TransitiveGround
open SetFormula
variable (M : TransitiveGround.{u})

theorem realize_recursiveSeparatorEntryFormula {n} (z K I J D L Maps Ss : Fin n)
    (env : Fin n → ZFSet.{u}) (members : ∀ i, env i ∈ M.sets) :
    Realize M.sets (recursiveSeparatorEntryFormula z K I J D L Maps Ss) env ↔
      env z ∈ recursiveSeparatorFamily (env K) (env I) (env J) (env D) (env L) (env Maps) (env Ss) := by
  simp only [recursiveSeparatorEntryFormula, realize_ex]
  rw [mem_recursiveSeparatorFamily]
  constructor
  · rintro ⟨i, hiM, j, hjM, S, hSM, e, heM, y, hyM, body⟩
    have extended : ∀ a, extend y (extend e (extend S (extend j (extend i env)))) a ∈ M.sets :=
      Fin.cases hyM (Fin.cases heM (Fin.cases hSM (Fin.cases hjM (Fin.cases hiM members))))
    have spec := (BoundedFormula.realize_toFormula M _ _ extended).1 body
    simp only [BoundedFormula.Truth, BoundedFormula.truth_orderedTripleFormula,
      BoundedFormula.truth_pairMembershipFormula] at spec
    change i ∈ env I ∧ j ∈ env J ∧ e ∈ env D ∧ y ∈ env L ∧
      env z = ZFSet.pair (ZFSet.pair i j) y ∧ ZFSet.pair i j ∈ env K ∧
        ZFSet.pair i S ∈ env Maps ∧ ZFSet.pair j e ∈ env Ss ∧ ZFSet.pair e y ∈ S at spec
    exact ⟨i, spec.1, j, spec.2.1, S, e, spec.2.2.1, y, spec.2.2.2.1, spec.2.2.2.2⟩
  · rintro ⟨i, hi, j, hj, S, e, he, y, hy, equal, hk, mapEntry, sepEntry, image⟩
    have hiM := M.transitive (members I) hi
    have hjM := M.transitive (members J) hj
    have hSM := M.pair_right (M.transitive (members Maps) mapEntry)
    have heM := M.transitive (members D) he
    have hyM := M.transitive (members L) hy
    refine ⟨i, hiM, j, hjM, S, hSM, e, heM, y, hyM, ?_⟩
    apply (BoundedFormula.realize_toFormula M _ _
      (Fin.cases hyM (Fin.cases heM (Fin.cases hSM (Fin.cases hjM (Fin.cases hiM members)))))).2
    simp only [BoundedFormula.Truth, BoundedFormula.truth_orderedTripleFormula,
      BoundedFormula.truth_pairMembershipFormula]
    exact ⟨hi, hj, he, hy, equal, hk, mapEntry, sepEntry, image⟩

theorem realize_recursiveSeparatorFamilyFormula
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    {n} (family K I J D L Maps Ss : Fin n)
    (env : Fin n → ZFSet.{u}) (members : ∀ i, env i ∈ M.sets) :
    Realize M.sets (recursiveSeparatorFamilyFormula family K I J D L Maps Ss) env ↔
      env family = recursiveSeparatorFamily (env K) (env I) (env J) (env D) (env L) (env Maps) (env Ss) := by
  apply M.realize_exactSetFormula family _ env (members family)
  · intro z member
    unfold recursiveSeparatorFamily familyEvaluationGraph at member
    obtain ⟨k, hk, y, hy, rfl⟩ := ZFSet.mem_prod.1 (ZFSet.mem_sep.1 member).1
    exact M.orderedPair_mem pairing (M.transitive (members K) hk) (M.transitive (members L) hy)
  · intro z hz
    exact M.realize_recursiveSeparatorEntryFormula 0 K.succ I.succ J.succ D.succ L.succ Maps.succ Ss.succ
      (extend z env) (Fin.cases hz members)

end TransitiveGround

end PartitionPilot.Forcing

end

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Definability_GroundRecursiveActionFormulas
attribute [-instance] _root_.OAI.PartitionPilot.Forcing.GroundMainPrefix.withTopSmall
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PartitionPilot.Forcing

universe u

namespace SetFormula

def indexedTaskActionGraphFormula {n} (output G I P N T : Fin n) : SetFormula n :=
  exactSetFormula output (BoundedFormula.indexedTaskActionCompleteEntryFormula 0
    G.succ I.succ P.succ N.succ T.succ).toFormula

def taggedActionGraphFormula {n} (output G P N A B : Fin n) : SetFormula n :=
  exactSetFormula output (BoundedFormula.taggedActionCompleteEntryFormula 0
    G.succ P.succ N.succ A.succ B.succ).toFormula

def recursiveActionGraphFormula {n} (output G L I J K B N A T : Fin n) : SetFormula n :=
  ex (.conj (indexedTaskActionGraphFormula 0 G.succ I.succ J.succ K.succ T.succ)
    (ex (.conj (indexedTaskActionGraphFormula 0 G.succ.succ K.succ.succ B.succ.succ N.succ.succ 1)
      (taggedActionGraphFormula output.succ.succ G.succ.succ L.succ.succ N.succ.succ A.succ.succ 0))))

end SetFormula

namespace TransitiveGround

open SetFormula
variable (M : TransitiveGround.{u})

theorem realize_indexedTaskActionGraphFormula
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    {n} (output G I P N T : Fin n) (env : Fin n → ZFSet.{u})
    (members : ∀ k, env k ∈ M.sets) :
    Realize M.sets (indexedTaskActionGraphFormula output G I P N T) env ↔
      env output = indexedTaskActionGraph (env G) (env I) (env P) (env N) (env T) := by
  apply M.realize_exactSetFormula output _ env (members output)
  · intro z member
    obtain ⟨gx, hgx, y, hy, rfl⟩ := ZFSet.mem_prod.1 (ZFSet.mem_sep.1 member).1
    obtain ⟨g, hg, x, hx, rfl⟩ := ZFSet.mem_prod.1 hgx
    exact M.orderedPair_mem pairing
      (M.orderedPair_mem pairing (M.transitive (members G) hg) (M.transitive (members N) hx))
      (M.transitive (members N) hy)
  · intro z hz
    rw [BoundedFormula.realize_toFormula M _ _ (Fin.cases hz members)]
    exact BoundedFormula.truth_indexedTaskActionCompleteEntryFormula 0 G.succ I.succ P.succ N.succ T.succ _

theorem realize_taggedActionGraphFormula
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    {n} (output G P N A B : Fin n) (env : Fin n → ZFSet.{u})
    (members : ∀ k, env k ∈ M.sets) :
    Realize M.sets (taggedActionGraphFormula output G P N A B) env ↔
      env output = taggedActionGraph (env G) (env P) (env N) (env A) (env B) := by
  apply M.realize_exactSetFormula output _ env (members output)
  · intro z member
    rcases ZFSet.mem_union.1 member with old | fresh
    · exact M.transitive (members A) old
    · obtain ⟨_, g, hg, q, hq, t, ht, rfl, _⟩ := ZFSet.mem_sep.1 fresh
      exact M.orderedPair_mem pairing
        (M.orderedPair_mem pairing (M.transitive (members G) hg)
          (M.orderedPair_mem pairing (members P) (M.transitive (members N) hq)))
        (M.orderedPair_mem pairing (members P) (M.transitive (members N) ht))
  · intro z hz
    rw [BoundedFormula.realize_toFormula M _ _ (Fin.cases hz members)]
    exact BoundedFormula.truth_taggedActionCompleteEntryFormula 0 G.succ P.succ N.succ A.succ B.succ _

theorem realize_recursiveActionGraphFormula
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    {n} (output G L I J K B N A T : Fin n) (env : Fin n → ZFSet.{u})
    (members : ∀ k, env k ∈ M.sets) :
    Realize M.sets (recursiveActionGraphFormula output G L I J K B N A T) env ↔
      env output = taggedActionGraph (env G) (env L) (env N) (env A)
        (indexedTaskActionGraph (env G) (env K) (env B) (env N)
          (indexedTaskActionGraph (env G) (env I) (env J) (env K) (env T))) := by
  rw [recursiveActionGraphFormula, realize_ex]
  constructor
  · rintro ⟨indexAction, hIndex, indexCode, rest⟩
    obtain ⟨freshAction, hFresh, freshCode, taggedCode⟩ := (realize_ex M.sets _ _).1 rest
    have firstMembers : ∀ k, extend indexAction env k ∈ M.sets := Fin.cases hIndex members
    have secondMembers : ∀ k, extend freshAction (extend indexAction env) k ∈ M.sets :=
      Fin.cases hFresh firstMembers
    have indexEq := (M.realize_indexedTaskActionGraphFormula pairing 0 G.succ I.succ J.succ
      K.succ T.succ (extend indexAction env) firstMembers).1 indexCode
    have freshEq := (M.realize_indexedTaskActionGraphFormula pairing 0 G.succ.succ K.succ.succ
      B.succ.succ N.succ.succ 1 _ secondMembers).1 freshCode
    have taggedEq := (M.realize_taggedActionGraphFormula pairing output.succ.succ G.succ.succ
      L.succ.succ N.succ.succ A.succ.succ 0 _ secondMembers).1 taggedCode
    change indexAction = indexedTaskActionGraph (env G) (env I) (env J) (env K) (env T) at indexEq
    change freshAction = indexedTaskActionGraph (env G) (env K) (env B) (env N) indexAction at freshEq
    change env output = taggedActionGraph (env G) (env L) (env N) (env A) freshAction at taggedEq
    exact taggedEq.trans (congrArg (taggedActionGraph (env G) (env L) (env N) (env A))
      (freshEq.trans (congrArg (indexedTaskActionGraph (env G) (env K) (env B) (env N)) indexEq)))
  · intro equal
    let indexAction := indexedTaskActionGraph (env G) (env I) (env J) (env K) (env T)
    have hIndex := M.indexedTaskActionGraph_mem pairing unions powers separation
      (members G) (members I) (members J) (members K) (members T)
    let freshAction := indexedTaskActionGraph (env G) (env K) (env B) (env N) indexAction
    have hFresh := M.indexedTaskActionGraph_mem pairing unions powers separation
      (members G) (members K) (members B) (members N) hIndex
    have firstMembers : ∀ k, extend indexAction env k ∈ M.sets := Fin.cases hIndex members
    have secondMembers : ∀ k, extend freshAction (extend indexAction env) k ∈ M.sets :=
      Fin.cases hFresh firstMembers
    refine ⟨indexAction, hIndex, ?_, ?_⟩
    · exact (M.realize_indexedTaskActionGraphFormula pairing 0 G.succ I.succ J.succ
        K.succ T.succ _ firstMembers).2 rfl
    · rw [realize_ex]
      refine ⟨freshAction, hFresh, ?_, ?_⟩
      · exact (M.realize_indexedTaskActionGraphFormula pairing 0 G.succ.succ K.succ.succ
          B.succ.succ N.succ.succ 1 _ secondMembers).2 rfl
      · exact (M.realize_taggedActionGraphFormula pairing output.succ.succ G.succ.succ
          L.succ.succ N.succ.succ A.succ.succ 0 _ secondMembers).2 equal

end TransitiveGround

end PartitionPilot.Forcing

end

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Geometry_GroundTaskRepresentativeRecognition
attribute [-instance] _root_.OAI.PartitionPilot.Forcing.GroundMainPrefix.withTopSmall
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PartitionPilot.Forcing
open SetFormula
universe u

namespace SetFormula

def groundTaskRepresentativesFormula {n} (Reps P G r μ A Labels : Fin n) : SetFormula n :=
  let old := suffixIndex n 3
  let field := prefixIndex n 3
  exBlock 3 (.conj (groundEligibleTasksFormula (field 0) (old P) (old G)
    (old r) (old μ) (old A) (old Labels))
    (.conj (groundRelationsFormula (field 1) (old P) (old P))
      (.conj (groundMeetFiltersFormula (field 2) (old P) (old r) (old μ))
        (BoundedFormula.taskRepresentativesFormula (old Reps) (field 0) (old P) (old G)
          (old r) (old A) (field 1) (field 2) (old Labels)).toFormula)))

end SetFormula

end PartitionPilot.Forcing

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Geometry_InitialCompressionAccounting
attribute [-instance] _root_.OAI.PartitionPilot.Forcing.GroundMainPrefix.withTopSmall
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PartitionPilot.Forcing

namespace TransitiveGround

open SetFormula
universe u
variable (M : TransitiveGround.{u})

noncomputable def initialCompressionData (P G r μ A Labels : ZFSet.{u}) : RecursiveStateData.{u} :=
  let I := M.groundEligibleTasks P G r μ A Labels
  let R := M.groundRelations P P
  let U := M.groundMeetFilters P r μ
  let Sources := literalTaskSourceGraph I P R U Labels
  let Base := literalTaskBaseGraph I P R U Labels
  { D := P
    rD := r
    μD := μ
    J := I
    Qs := constantFamilyGraph I P
    rs := constantFamilyGraph I r
    μs := constantFamilyGraph I μ
    As := Sources
    Es := Base
    Fs := literalTaskFilterGraph I P R U Labels
    Ss := literalTaskSeparatorGraph I P R U Labels
    Maps := M.batchEmbeddingFamily I P (constantFamilyGraph I P)
      (constantFamilyGraph I r) Sources Base
    A := M.groundEligibleBatchAction P G r μ A Labels }

end TransitiveGround

end PartitionPilot.Forcing

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Transfinite_GroundInitialCompressionHistory
attribute [-instance] _root_.OAI.PartitionPilot.Forcing.GroundMainPrefix.withTopSmall
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open scoped ZFSet

namespace PartitionPilot.Forcing.TransitiveGround

open SetFormula
universe u
variable (M : TransitiveGround.{u})
variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
variable (unions : Realize M.sets SetFormula.union Fin.elim0)
variable (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)

noncomputable def definable_pairCompositions :
    GroundDefinableFunction M (fun env : Fin 8 → ZFSet.{u} =>
      M.groundPairCompositions (env 0) (env 1) (env 2) (env 3) (env 4) (env 5) (env 6) (env 7)) where
  formula := compositionFamilyFormula 0 1 2 3 4 5 6 7 8
  closed _env members := M.pairCompositionFamily_mem pairing unions powers separation
    (members 0) (members 1) (members 2) (members 3) (members 4) (members 5) (members 6) (members 7)
    (M.groundRelations_mem pairing unions powers separation (members 3) (members 5))
  correct env members z hz := M.realize_compositionFamilyFormula pairing 0 1 2 3 4 5 6 7 8
    (extend z env) (Fin.cases hz members)

noncomputable def definable_pairPushFilters :
    GroundDefinableFunction M (fun env : Fin 7 → ZFSet.{u} =>
      M.groundPairPushFilters (env 0) (env 1) (env 2) (env 3) (env 4) (env 5) (env 6)) where
  formula := pushFilterFamilyFormula 0 1 2 3 4 5 6 7
  closed _env members := M.pairPushFilterFamily_mem pairing unions powers separation
    (members 0) (members 1) (members 2) (members 3) (members 4) (members 5) (members 6)
    (M.groundPower_mem powers (members 3))
  correct env members z hz := M.realize_pushFilterFamilyFormula pairing 0 1 2 3 4 5 6 7
    (extend z env) (Fin.cases hz members)

noncomputable def definable_recursiveSeparators :
    GroundDefinableFunction M (fun env : Fin 7 → ZFSet.{u} =>
      recursiveSeparatorFamily (env 0) (env 1) (env 2) (env 3) (env 4) (env 5) (env 6)) where
  formula := recursiveSeparatorFamilyFormula 0 1 2 3 4 5 6 7
  closed _env members := M.recursiveSeparatorFamily_mem pairing unions powers separation
    (members 0) (members 1) (members 2) (members 3) (members 4) (members 5) (members 6)
  correct env members z hz := M.realize_recursiveSeparatorFamilyFormula pairing 0 1 2 3 4 5 6 7
    (extend z env) (Fin.cases hz members)

noncomputable def definable_recursiveAction :
    GroundDefinableFunction M (fun env : Fin 9 → ZFSet.{u} =>
      taggedActionGraph (env 0) (env 1) (env 6) (env 7)
        (indexedTaskActionGraph (env 0) (env 4) (env 5) (env 6)
          (indexedTaskActionGraph (env 0) (env 2) (env 3) (env 4) (env 8)))) where
  formula := recursiveActionGraphFormula 0 1 2 3 4 5 6 7 8 9
  closed env members := by
    have index := M.indexedTaskActionGraph_mem pairing unions powers separation
      (members 0) (members 2) (members 3) (members 4) (members 8)
    have fresh := M.indexedTaskActionGraph_mem pairing unions powers separation
      (members 0) (members 4) (members 5) (members 6) index
    exact M.taggedActionGraph_mem pairing unions powers separation
      (members 0) (members 1) (members 6) (members 7) fresh
  correct env members z hz := M.realize_recursiveActionGraphFormula pairing unions powers separation
    0 1 2 3 4 5 6 7 8 9 (extend z env) (Fin.cases hz members)

end PartitionPilot.Forcing.TransitiveGround

namespace PartitionPilot.Forcing
open SetFormula
universe u

namespace SetFormula

def decodedSuccessorFormula (definition : SetFormula 19) : SetFormula 7 :=
  exBlock 13 (.conj
    (BoundedFormula.nonemptyTupleFormula 12 (suffixIndex 7 13 0) (prefixIndex 7 13)).toFormula
    (reindex (extend (suffixIndex 7 13 1)
      (Fin.addCases (m := 13) (n := 5) (prefixIndex 7 13)
        (fun j => suffixIndex 7 13 j.succ.succ))) definition))

end SetFormula

end PartitionPilot.Forcing

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Transfinite_OwnerBirthLayers
attribute [-instance] _root_.OAI.PartitionPilot.Forcing.GroundMainPrefix.withTopSmall
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PartitionPilot.Forcing
universe u

theorem OwnerStampCode.injective {T stamps : ZFSet.{u}}
    (code : OwnerStampCode T stamps) {n m : Nat} {t : ZFSet.{u}}
    (first : ZFSet.pair (natSetCode n) t ∈ stamps)
    (second : ZFSet.pair (natSetCode m) t ∈ stamps) : n = m := by
  have notBefore : ¬ n < m := fun h => ZFSet.mem_irrefl t ((code.strict n m t t first second).2 h)
  have notAfter : ¬ m < n := fun h => ZFSet.mem_irrefl t ((code.strict m n t t second first).2 h)
  omega

theorem ownerBirthGraph_stamp_fiber {P B T T0 old levels stamps : ZFSet.{u}}
    (oldFunction : ZFSet.IsFunc P T0 old)
    (stampCode : OwnerStampCode T stamps)
    (oldBefore : ∀ x a n t, ZFSet.pair x a ∈ old →
      ZFSet.pair (natSetCode n) t ∈ stamps → a ∈ t)
    {n : Nat} {t x : ZFSet.{u}} (stamp : ZFSet.pair (natSetCode n) t ∈ stamps) :
    ZFSet.pair x t ∈ ownerBirthGraph P B T old levels stamps ↔
      x ∈ ownerFresh P B ∧ ZFSet.pair x (natSetCode n) ∈ levels := by
  constructor
  · intro entry
    have fresh : x ∉ P := by
      intro oldPoint
      exact ZFSet.mem_irrefl t (oldBefore x t n t ((ownerBirthGraph_old_iff oldPoint).1 entry) stamp)
    obtain ⟨hx, _, k, level, value⟩ := (ownerBirthGraph_fresh_nat_iff oldFunction fresh).1 entry
    have equal := stampCode.injective value stamp
    exact ⟨(mem_ownerFresh P B x).2 ⟨hx, fresh⟩, equal ▸ level⟩
  · rintro ⟨fresh, level⟩
    have hx := (mem_ownerFresh P B x).1 fresh
    exact (ownerBirthGraph_fresh_nat_iff oldFunction hx.2).2
      ⟨hx.1, (ZFSet.pair_mem_prod.1 (stampCode.function.1 stamp)).2, n, level, stamp⟩

theorem ownerBirthGraph_earlier_of_level {P B T T0 old levels stamps : ZFSet.{u}}
    (oldFunction : ZFSet.IsFunc P T0 old)
    (levelFunction : ZFSet.IsFunc (ownerFresh P B) ZFSet.omega levels)
    (stampCode : OwnerStampCode T stamps)
    (oldBefore : ∀ x a n t, ZFSet.pair x a ∈ old →
      ZFSet.pair (natSetCode n) t ∈ stamps → a ∈ t)
    {n : Nat} {t x a : ZFSet.{u}} (stamp : ZFSet.pair (natSetCode n) t ∈ stamps)
    (entry : ZFSet.pair x a ∈ ownerBirthGraph P B T old levels stamps)
    (earlier : x ∈ P ∨ ∃ k < n, ZFSet.pair x (natSetCode k) ∈ levels) : a ∈ t := by
  rcases earlier with oldPoint | ⟨k, before, level⟩
  · exact oldBefore x a n t ((ownerBirthGraph_old_iff oldPoint).1 entry) stamp
  · have fresh := (ZFSet.pair_mem_prod.1 (levelFunction.1 level)).1
    have hx := (mem_ownerFresh P B x).1 fresh
    obtain ⟨_, _, j, actualLevel, actualStamp⟩ := (ownerBirthGraph_fresh_nat_iff oldFunction hx.2).1 entry
    obtain ⟨_, _, unique⟩ := levelFunction.2 x fresh
    have equal : j = k := natSetCode_injective
      ((unique _ actualLevel).trans (unique _ level).symm)
    exact (stampCode.strict j n a t actualStamp stamp).2 (equal.symm ▸ before)

noncomputable def ownerBirthGraph_separated
    {M : TransitiveGround.{u}} {P B L r μ T T0 old levels stamps : ZFSet.{u}}
    {Space sourceOrder sourceMeet : ZFSet.{u} → ZFSet.{u}}
    (oldFunction : ZFSet.IsFunc P T0 old) (oldSubset : P ⊆ B) (times : T0 ⊆ T)
    (levelFunction : ZFSet.IsFunc (ownerFresh P B) ZFSet.omega levels)
    (stampCode : OwnerStampCode T stamps)
    (oldBefore : ∀ x a n t, ZFSet.pair x a ∈ old →
      ZFSet.pair (natSetCode n) t ∈ stamps → a ∈ t)
    {n : Nat} {t : ZFSet.{u}} (stamp : ZFSet.pair (natSetCode n) t ∈ stamps)
    (I : Type u) (index e : I → ZFSet.{u})
    (copyEarlier : ∀ i, index i ∈ t) (groundCopy : ∀ i, e i ∈ M.sets)
    (embedding : ∀ i, MeetEmbeddingCode (Space (index i)) L
      (sourceOrder (index i)) r (sourceMeet (index i)) μ (e i))
    (component : {x : ZFSet.{u} // x ∈ ownerFresh P B ∧
      ZFSet.pair x (natSetCode n) ∈ levels} → I)
    (cover : ∀ x : {x : ZFSet.{u} // x ∈ ownerFresh P B ∧
      ZFSet.pair x (natSetCode n) ∈ levels}, x.val ∈ L →
        x.val ∈ relationImage (Space (index (component x))) L (e (component x)))
    (separated : ∀ x y : {x : ZFSet.{u} // x ∈ ownerFresh P B ∧
      ZFSet.pair x (natSetCode n) ∈ levels}, x.val ∈ L → y.val ∈ L →
      component x ≠ component y → ∃ z ∈ B, ZFSet.pair (ZFSet.pair x.val y.val) z ∈ μ ∧
        (z ∈ P ∨ ∃ k < n, ZFSet.pair z (natSetCode k) ∈ levels)) :
    CodedGrowthLayer M Space sourceOrder sourceMeet L r μ
      (ownerBirthGraph P B T old levels stamps) t := by
  let born := ownerBirthGraph_function oldFunction oldSubset times levelFunction stampCode.function
  let fresh (x : {x : ZFSet.{u} // x ∈ L ∧
      ZFSet.pair x t ∈ ownerBirthGraph P B T old levels stamps}) :
      {x : ZFSet.{u} // x ∈ ownerFresh P B ∧ ZFSet.pair x (natSetCode n) ∈ levels} :=
    ⟨x.val, (ownerBirthGraph_stamp_fiber oldFunction stampCode oldBefore stamp).1 x.property.2⟩
  refine .separated I index e copyEarlier groundCopy embedding (fun x => component (fresh x)) ?_ ?_
  · intro x
    exact cover (fresh x) x.property.1
  · intro x y different
    obtain ⟨z, hz, meet, earlier⟩ := separated (fresh x) (fresh y) x.property.1 y.property.1 different
    obtain ⟨a, entry, _⟩ := born.2 z hz
    exact Or.inl ⟨z, a, meet, entry,
      ownerBirthGraph_earlier_of_level oldFunction levelFunction stampCode oldBefore stamp entry earlier⟩

end PartitionPilot.Forcing

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Geometry_RectangleFulfillmentAtBound
attribute [-instance] _root_.OAI.PartitionPilot.Forcing.GroundMainPrefix.withTopSmall
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI



namespace PartitionPilot.Forcing
universe u

def RectangleFulfillmentCode (P G r μ A Q H R ν B e a : ZFSet.{u}) : Prop :=
  ∀ c ∈ P, ∀ b ∈ P, ∀ d ∈ P, ∀ g ∈ G, ∀ h ∈ G,
    ExternalRectangleCode P G r μ A c b d g h →
      ∃ k ∈ H, ∃ l ∈ H, RectangleActorPairCode P μ A Q H R ν B e a c b d g h k l

end PartitionPilot.Forcing



end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Geometry_GroundTileStarIncidence
attribute [-instance] _root_.OAI.PartitionPilot.Forcing.GroundMainPrefix.withTopSmall
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PartitionPilot.Forcing

section
open SetRealization SetFormula Compression.RecursiveMaps.CosetGeometry
universe u

variable {J S R : Type u} [Group J]
variable (e : Presentation (External J S)) (s : Presentation S) (r : Presentation R)
variable (q : Presentation (Vertex J S))

noncomputable def tileStarVertexPresentation : Presentation (TileStars.Vertex J S R) := taggedSumPresentation q (e.product r)
noncomputable def tileStarEdgePresentation : Presentation (TileStars.Edge J S R) := taggedSumPresentation (e.product r) (e.product s)

namespace TransitiveGround
variable (M : TransitiveGround.{u})
theorem tileStarCarriers_mem
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    {Q E R S : ZFSet.{u}} (hQ : Q ∈ M.sets) (hE : E ∈ M.sets) (hR : R ∈ M.sets) (hS : S ∈ M.sets) :
    tileStarVertexCarrier Q E R ∈ M.sets ∧ tileStarEdgeCarrier E R S ∈ M.sets ∧ tileStarDartCarrier E R S ∈ M.sets := by
  have center := M.prod_mem pairing unions powers separation hE hR
  have edge := M.taggedSumCarrier_mem pairing unions powers separation center (M.prod_mem pairing unions powers separation hE hS)
  have zero : natSetCode 0 ∈ M.sets := M.empty_mem ⟨E, hE⟩
  have one : natSetCode 1 ∈ M.sets := M.insert_mem pairing unions zero zero
  have two : natSetCode 2 ∈ M.sets := M.insert_mem pairing unions one one
  exact ⟨M.taggedSumCarrier_mem pairing unions powers separation hQ center, edge,
    M.prod_mem pairing unions powers separation edge two⟩

end TransitiveGround

end

open SetFormula
universe u

theorem pair_mem_tileStarSourceGraph (E R S Q C request generators multiplication d v : ZFSet.{u}) :
    ZFSet.pair d v ∈ tileStarSourceGraph E R S Q C request generators multiplication ↔
      d ∈ tileStarDartCarrier E R S ∧ v ∈ tileStarVertexCarrier Q E R ∧
        TileStarSourceEntry E R S Q (tileStarEdgeCarrier E R S) C request generators multiplication d v := by
  rw [tileStarSourceGraph, ZFSet.mem_sep]
  constructor
  · rintro ⟨_, d', hd, v', hv, equal, entry⟩
    obtain ⟨rfl, rfl⟩ := ZFSet.pair_inj.1 equal
    exact ⟨hd, hv, entry⟩
  · rintro ⟨hd, hv, entry⟩
    exact ⟨ZFSet.pair_mem_prod.2 ⟨hd, hv⟩, d, hd, v, hv, rfl, entry⟩

theorem pair_mem_tileStarReverseGraph (E R S d v : ZFSet.{u}) :
    ZFSet.pair d v ∈ tileStarReverseGraph E R S ↔
      d ∈ tileStarDartCarrier E R S ∧ v ∈ tileStarDartCarrier E R S ∧
        TileStarReverseEntry (tileStarEdgeCarrier E R S) d v := by
  rw [tileStarReverseGraph, ZFSet.mem_sep]
  constructor
  · rintro ⟨_, d', hd, v', hv, equal, entry⟩
    obtain ⟨rfl, rfl⟩ := ZFSet.pair_inj.1 equal
    exact ⟨hd, hv, entry⟩
  · rintro ⟨hd, hv, entry⟩
    exact ⟨ZFSet.pair_mem_prod.2 ⟨hd, hv⟩, d, hd, v, hv, rfl, entry⟩

namespace TransitiveGround
variable (M : TransitiveGround.{u})
variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
variable (unions : Realize M.sets SetFormula.union Fin.elim0)
variable (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)

include pairing unions powers separation in
theorem tileStarSourceGraph_mem {E R S Q C request generators multiplication : ZFSet.{u}}
    (hE : E ∈ M.sets) (hR : R ∈ M.sets) (hS : S ∈ M.sets) (hQ : Q ∈ M.sets) (hC : C ∈ M.sets) (hrequest : request ∈ M.sets) (hgenerators : generators ∈ M.sets) (hmultiplication : multiplication ∈ M.sets) :
    tileStarSourceGraph E R S Q C request generators multiplication ∈ M.sets := by
  have hzero : natSetCode 0 ∈ M.sets := M.empty_mem ⟨E, hE⟩
  have hone : natSetCode 1 ∈ M.sets := M.insert_mem pairing unions hzero hzero
  have carriers := M.tileStarCarriers_mem pairing unions powers separation hQ hE hR hS
  have hD := carriers.2.2
  have hV := carriers.1
  have hEdges := carriers.2.1
  let params := extend (tileStarDartCarrier E R S) (extend (tileStarVertexCarrier Q E R) (extend (E) (extend (R) (extend (S) (extend (Q) (extend (tileStarEdgeCarrier E R S) (extend (C) (extend (request) (extend (generators) (extend (multiplication) (extend (natSetCode 0) (extend (natSetCode 1) (Fin.elim0)))))))))))))
  have selected := M.bounded_separation_mem separation
    (BoundedFormula.tileStarSourceEntryFormula 0 1 2 3 4 5 6 7 8 9 10 11 12 13) params
    (Fin.cases hD (Fin.cases hV (Fin.cases hE (Fin.cases hR (Fin.cases hS (Fin.cases hQ (Fin.cases hEdges (Fin.cases hC (Fin.cases hrequest (Fin.cases hgenerators (Fin.cases hmultiplication (Fin.cases hzero (Fin.cases hone (fun i => Fin.elim0 i)))))))))))))) (M.prod_mem pairing unions powers separation hD hV)
  have equal : ZFSet.sep (fun z => BoundedFormula.Truth
      (BoundedFormula.tileStarSourceEntryFormula 0 1 2 3 4 5 6 7 8 9 10 11 12 13) (extend z params))
      (ZFSet.prod (tileStarDartCarrier E R S) (tileStarVertexCarrier Q E R)) = tileStarSourceGraph E R S Q C request generators multiplication := by
    apply ZFSet.ext
    intro z
    rw [tileStarSourceGraph, ZFSet.mem_sep, ZFSet.mem_sep]
    exact and_congr Iff.rfl (BoundedFormula.truth_tileStarSourceEntryFormula 0 1 2 3 4 5 6 7 8 9 10 11 12 13 _ rfl rfl)
  exact equal ▸ selected

include pairing unions powers separation in
theorem tileStarReverseGraph_mem {E R S : ZFSet.{u}}
    (hE : E ∈ M.sets) (hR : R ∈ M.sets) (hS : S ∈ M.sets) :
    tileStarReverseGraph E R S ∈ M.sets := by
  have hzero : natSetCode 0 ∈ M.sets := M.empty_mem ⟨E, hE⟩
  have hone : natSetCode 1 ∈ M.sets := M.insert_mem pairing unions hzero hzero
  have carriers := M.tileStarCarriers_mem pairing unions powers separation hE hE hR hS
  have hD := carriers.2.2
  have hV := carriers.2.2
  have hEdges := carriers.2.1
  let params := extend (tileStarDartCarrier E R S) (extend (tileStarDartCarrier E R S) (extend (tileStarEdgeCarrier E R S) (extend (natSetCode 0) (extend (natSetCode 1) (Fin.elim0)))))
  have selected := M.bounded_separation_mem separation
    (BoundedFormula.tileStarReverseEntryFormula 0 1 2 3 4 5) params
    (Fin.cases hD (Fin.cases hV (Fin.cases hEdges (Fin.cases hzero (Fin.cases hone (fun i => Fin.elim0 i)))))) (M.prod_mem pairing unions powers separation hD hV)
  have equal : ZFSet.sep (fun z => BoundedFormula.Truth
      (BoundedFormula.tileStarReverseEntryFormula 0 1 2 3 4 5) (extend z params))
      (ZFSet.prod (tileStarDartCarrier E R S) (tileStarDartCarrier E R S)) = tileStarReverseGraph E R S := by
    apply ZFSet.ext
    intro z
    rw [tileStarReverseGraph, ZFSet.mem_sep, ZFSet.mem_sep]
    exact and_congr Iff.rfl (BoundedFormula.truth_tileStarReverseEntryFormula 0 1 2 3 4 5 _ rfl rfl)
  exact equal ▸ selected

include pairing unions powers separation in
theorem dartAdjacencyGraph_mem {D V source target : ZFSet.{u}}
    (hD : D ∈ M.sets) (hV : V ∈ M.sets) (hs : source ∈ M.sets) (ht : target ∈ M.sets) :
    dartAdjacencyGraph D V source target ∈ M.sets :=
  M.relationCompose_mem pairing unions powers separation hV hD hV
    (M.relationConverse_mem pairing unions powers separation hD hV hs) ht

end TransitiveGround

end PartitionPilot.Forcing

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Geometry_GroundCompressionHeightSteps
attribute [-instance] _root_.OAI.PartitionPilot.Forcing.GroundMainPrefix.withTopSmall
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace PartitionPilot.Forcing

open Compression.RecursiveMaps
universe u

theorem lexHeightOrder_code {C D rD : ZFSet.{u}}
    (columns : ordinalSetProperty C) (target : StrictLinearOrderCode D rD) :
    StrictLinearOrderCode (ZFSet.prod C D) (lexHeightOrder C D rD) := by
  refine ⟨fun _ hz => (ZFSet.mem_sep.1 hz).1, ?_, ?_, ?_⟩
  · intro x hx hxx
    obtain ⟨c, _, q, hq, rfl⟩ := ZFSet.mem_prod.1 hx
    rcases ((pair_mem_lexHeightOrder C D rD c q c q).1 hxx).2.2.2.2 with less | same
    · exact ZFSet.mem_irrefl c less
    · exact target.irrefl q hq same.2
  · intro x y z hxy hyz
    have xy := ZFSet.pair_mem_prod.1 (ZFSet.mem_sep.1 hxy).1
    have yz := ZFSet.pair_mem_prod.1 (ZFSet.mem_sep.1 hyz).1
    obtain ⟨c, hc, q, hq, rfl⟩ := ZFSet.mem_prod.1 xy.1
    obtain ⟨d, _, v, _, rfl⟩ := ZFSet.mem_prod.1 xy.2
    obtain ⟨b, hb, w, hw, rfl⟩ := ZFSet.mem_prod.1 yz.2
    have left := ((pair_mem_lexHeightOrder C D rD c q d v).1 hxy).2.2.2.2
    have right := ((pair_mem_lexHeightOrder C D rD d v b w).1 hyz).2.2.2.2
    apply (pair_mem_lexHeightOrder C D rD c q b w).2
    refine ⟨hc, hq, hb, hw, ?_⟩
    rcases left with lower | ⟨same, inside⟩
    · rcases right with lower' | ⟨same', _⟩
      · exact Or.inl (columns.2 b hb d lower' c lower)
      · exact Or.inl (same' ▸ lower)
    · rcases right with lower' | ⟨same', inside'⟩
      · exact Or.inl (same.symm ▸ lower')
      · exact Or.inr ⟨same.trans same', target.trans q v w inside inside'⟩
  · intro x hx y hy
    obtain ⟨c, hc, q, hq, rfl⟩ := ZFSet.mem_prod.1 hx
    obtain ⟨d, hd, v, hv, rfl⟩ := ZFSet.mem_prod.1 hy
    rcases ordinalSetProperty_mem_compare columns hc hd with lower | same | greater
    · exact Or.inl ((pair_mem_lexHeightOrder C D rD c q d v).2 ⟨hc, hq, hd, hv, Or.inl lower⟩)
    · subst d
      rcases target.compare q hq v hv with lower | same | greater
      · exact Or.inl ((pair_mem_lexHeightOrder C D rD c q c v).2
          ⟨hc, hq, hc, hv, Or.inr ⟨rfl, lower⟩⟩)
      · exact Or.inr (Or.inl (congrArg (ZFSet.pair c) same))
      · exact Or.inr (Or.inr ((pair_mem_lexHeightOrder C D rD c v c q).2
          ⟨hc, hv, hc, hq, Or.inr ⟨rfl, greater⟩⟩))
    · exact Or.inr (Or.inr ((pair_mem_lexHeightOrder C D rD d v c q).2
        ⟨hd, hv, hc, hq, Or.inl greater⟩))

namespace StrictLexHeightCode

noncomputable def toStrictHeight {L C D r μ h rD : ZFSet.{u}}
    (code : StrictLexHeightCode L C D r h rD) (meet : MeetOrderCode L r μ)
    (columns : ordinalSetProperty C) (target : StrictLinearOrderCode D rD) :
    StrictHeight meet.toMeetOrder (lexHeightOrder_code columns target).toLinearHeightOrder.toHeightOrder where
  value := code.value
  strict x y lower different := by
    have xEntry := code.value_entry x
    have yEntry := code.value_entry y
    obtain ⟨c, hc, q, hq, ex⟩ := ZFSet.mem_prod.1 (code.value x).property
    obtain ⟨d, hd, v, hv, ey⟩ := ZFSet.mem_prod.1 (code.value y).property
    have xHeight : ZFSet.pair x.val (ZFSet.pair c q) ∈ h := ex ▸ xEntry
    have yHeight : ZFSet.pair y.val (ZFSet.pair d v) ∈ h := ey ▸ yEntry
    have lex := code.strict x.val x.property y.val y.property c q d v lower
      (fun equal => different (Subtype.ext equal)) xHeight yHeight
    change ZFSet.pair (code.value x).val (code.value y).val ∈ lexHeightOrder C D rD
    rw [ex, ey]
    exact (pair_mem_lexHeightOrder C D rD c q d v).2 ⟨hc, hq, hd, hv, lex⟩

end StrictLexHeightCode

namespace TemplateHeightFamilyInputs

variable {P rP μP I Qs rs μs As Es Fs Ss Vs vrs Hs C D rD old Cs los his E : ZFSet.{u}}
  {d : AttachmentBatchInputs P rP μP I Qs rs μs As Es Fs Ss}
  (t : TemplateHeightFamilyInputs d Vs vrs Hs)
  (e : BatchHeightEndpointCode d C D old rD Cs los his)
  (embeddings : FunctionGraphOn I E)
  (maps : ∀ i, IntervalEmbeddingCode (t.ranges.value i) D (t.orders.value i) rD
    (e.low i) (e.high i) (embeddings.value i))

include t e embeddings maps

noncomputable def componentStrictHeight (columns : ordinalSetProperty C)
    (target : StrictLinearOrderCode D rD) (i : {i : ZFSet.{u} // i ∈ I}) :
    StrictHeight (d.templates.order i) (lexHeightOrder_code columns target).toLinearHeightOrder.toHeightOrder where
  value := t.componentValue e embeddings maps i
  strict x y lower different := by
    obtain ⟨c, hc, q, hq, ex, colx, a, _, heightx, imagex⟩ := t.componentValue_spec e embeddings maps i x
    obtain ⟨b, hb, z, hz, ey, coly, v, _, heighty, imagey⟩ := t.componentValue_spec e embeddings maps i y
    have same : c = b := (show FunctionGraphOn I Cs from ⟨C, e.columns⟩).unique colx coly
    have strict := t.strict i x.val y.val a v lower (fun equal => different (Subtype.ext equal)) heightx heighty
    have imageStrict := ((maps i).order a v q z imagex imagey).1 strict
    change ZFSet.pair (t.componentValue e embeddings maps i x).val
      (t.componentValue e embeddings maps i y).val ∈ lexHeightOrder C D rD
    rw [ex, ey]
    exact (pair_mem_lexHeightOrder C D rD c q b z).2 ⟨hc, hq, hb, hz, Or.inr ⟨same, imageStrict⟩⟩

theorem component_lower (oldCode : StrictLexHeightCode P C D rP old rD)
    (columns : ordinalSetProperty C) (target : StrictLinearOrderCode D rD)
    (x : d.templates.Fresh) :
    (lexHeightOrder_code columns target).toLinearHeightOrder.lt
      ((oldCode.toStrictHeight d.oldOrder columns target).value (d.templates.base x.1))
      ((t.componentStrictHeight e embeddings maps columns target x.1).value x.2.val) := by
  obtain ⟨c, hc, z, hz, value, column, a, _, _, image⟩ :=
    t.componentValue_spec e embeddings maps x.1 x.2.val
  have base := e.base x.1 c (e.low x.1) column (e.low_entry x.1)
  have baseValue := oldCode.value_eq_of_entry (d.templates.base x.1) base
  have hlo := (ZFSet.pair_mem_prod.1 (e.lows.1 (e.low_entry x.1))).2
  have lower := ((maps x.1).inside a z image).1
  change ZFSet.pair (oldCode.value (d.templates.base x.1)).val
    (t.componentValue e embeddings maps x.1 x.2.val).val ∈ lexHeightOrder C D rD
  rw [baseValue, value]
  exact (pair_mem_lexHeightOrder C D rD c (e.low x.1) c z).2 ⟨hc, hlo, hc, hz, Or.inr ⟨rfl, lower⟩⟩

theorem component_upper (oldCode : StrictLexHeightCode P C D rP old rD)
    (columns : ordinalSetProperty C) (target : StrictLinearOrderCode D rD)
    (x : d.templates.Fresh) :
    (lexHeightOrder_code columns target).toLinearHeightOrder.lt
      ((t.componentStrictHeight e embeddings maps columns target x.1).value x.2.val)
      ((oldCode.toStrictHeight d.oldOrder columns target).value (d.templates.separator x.1)) := by
  obtain ⟨c, hc, z, hz, value, column, a, _, _, image⟩ :=
    t.componentValue_spec e embeddings maps x.1 x.2.val
  obtain ⟨b, hb, v, hv, sepValue⟩ := ZFSet.mem_prod.1 (oldCode.value (d.templates.separator x.1)).property
  have sepEntry : ZFSet.pair (d.separator x.1) (ZFSet.pair b v) ∈ old :=
    sepValue ▸ oldCode.value_entry (d.templates.separator x.1)
  have upper := e.interval_upper x.1 column (e.high_entry x.1) ((maps x.1).inside a z image).2 sepEntry
  change ZFSet.pair (t.componentValue e embeddings maps x.1 x.2.val).val
    (oldCode.value (d.templates.separator x.1)).val ∈ lexHeightOrder C D rD
  rw [value, sepValue]
  exact (pair_mem_lexHeightOrder C D rD c z b v).2 ⟨hc, hz, hb, hv, upper⟩

noncomputable def extendedHeight (oldCode : StrictLexHeightCode P C D rP old rD)
    (columns : ordinalSetProperty C) (target : StrictLinearOrderCode D rD) :
    StrictHeight d.templates.extension (lexHeightOrder_code columns target).toLinearHeightOrder.toHeightOrder :=
  AttachmentHeight.extend d.templates (oldCode.toStrictHeight d.oldOrder columns target)
    (t.componentStrictHeight e embeddings maps columns target)
    (t.component_lower e embeddings maps oldCode columns target)
    (t.component_upper e embeddings maps oldCode columns target)

end TemplateHeightFamilyInputs

end PartitionPilot.Forcing



end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Transfinite_MainStageTaskCodes
attribute [-instance] _root_.OAI.PartitionPilot.Forcing.GroundMainPrefix.withTopSmall
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PartitionPilot.Forcing.GroundMainStage
universe u
variable {M : TransitiveGround.{u}} {C D rD : ZFSet.{u}}
variable (stage : GroundMainStage M C D rD) (Labels : ZFSet.{u})

noncomputable def compressionInitial : RecursiveStateData.{u} :=
  M.initialCompressionData stage.carrier stage.actors stage.order stage.meetGraph stage.action Labels

noncomputable def compressionTasks : ZFSet.{u} :=
  M.groundEligibleTasks stage.carrier stage.actors stage.order stage.meetGraph stage.action Labels

noncomputable def compressionSources : ZFSet.{u} :=
  literalTaskSourceGraph (stage.compressionTasks Labels) stage.carrier
    (M.groundRelations stage.carrier stage.carrier)
    (M.groundMeetFilters stage.carrier stage.order stage.meetGraph) Labels

noncomputable def compressionFilters : ZFSet.{u} :=
  literalTaskFilterGraph (stage.compressionTasks Labels) stage.carrier
    (M.groundRelations stage.carrier stage.carrier)
    (M.groundMeetFilters stage.carrier stage.order stage.meetGraph) Labels

noncomputable def compressionTargets : ZFSet.{u} :=
  literalTaskTargetGraph (stage.compressionTasks Labels) stage.carrier
    (M.groundRelations stage.carrier stage.carrier)
    (M.groundMeetFilters stage.carrier stage.order stage.meetGraph) Labels

noncomputable def compressionSeparators : ZFSet.{u} :=
  literalTaskSeparatorGraph (stage.compressionTasks Labels) stage.carrier
    (M.groundRelations stage.carrier stage.carrier)
    (M.groundMeetFilters stage.carrier stage.order stage.meetGraph) Labels

noncomputable def compressionTaskAction : ZFSet.{u} :=
  M.groundTaskTransport stage.carrier stage.actors stage.order stage.meetGraph stage.action Labels

end PartitionPilot.Forcing.GroundMainStage

end

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Transfinite_GroundCompressionPrefixGraphs
attribute [-instance] _root_.OAI.PartitionPilot.Forcing.GroundMainPrefix.withTopSmall
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PartitionPilot.Forcing

open SetFormula
universe u

theorem compressionPrefixGraph_entries {base limit old stages stamps final s y : ZFSet.{u}}
    (times : CompressionStampCode base stamps limit) :
    ZFSet.pair s y ∈ compressionPrefixGraph base limit old stages stamps final ↔
      (s = limit ∧ y = final) ∨
        ((s ∈ base ∨ s = base) ∧ ZFSet.pair s y ∈ old) ∨
          ∃ n, s = compressionStamp base n ∧ ZFSet.pair (natSetCode n) y ∈ stages := by
  rw [compressionPrefixGraph, ZFSet.mem_insert_iff, ZFSet.mem_union,
    ZFSet.pair_inj, pair_mem_graphRestriction, pair_mem_relationCompose]
  constructor
  · rintro (terminal | ⟨entry, old⟩ | ⟨_, _, k, hk, reverse, entry⟩)
    · exact Or.inl terminal
    · exact Or.inr (Or.inl ⟨(ZFSet.mem_insert_iff.1 old).symm, entry⟩)
    · obtain ⟨n, rfl⟩ := (mem_omega_iff_natSetCode k).1 hk
      exact Or.inr (Or.inr ⟨n,
        (times.entries n s).1 ((pair_mem_relationConverse _ _ _ _ _).1 reverse).2.2, entry⟩)
  · rintro (terminal | ⟨old, entry⟩ | ⟨n,rfl,entry⟩)
    · exact Or.inl terminal
    · exact Or.inr (Or.inl ⟨entry, ZFSet.mem_insert_iff.2 old.symm⟩)
    · exact Or.inr (Or.inr ⟨times.stamp_mem_limit n, pair_second_mem_doubleUnion entry,
        natSetCode n, natSetCode_mem_omega n,
        (pair_mem_relationConverse _ _ _ _ _).2 ⟨natSetCode_mem_omega n,
          times.stamp_mem_limit n, (times.entries n _).2 rfl⟩, entry⟩)

end PartitionPilot.Forcing

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Geometry_GroundCompressionStarIncidence
attribute [-instance] _root_.OAI.PartitionPilot.Forcing.GroundMainPrefix.withTopSmall
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace PartitionPilot.Forcing
open SetFormula
universe u

namespace TransitiveGround
variable (M : TransitiveGround.{u})

theorem externalCosetRelation_mem
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    {E G inclusion multiplication : ZFSet.{u}}
    (hE : E ∈ M.sets) (hG : G ∈ M.sets) (hInclusion : inclusion ∈ M.sets)
    (hMultiplication : multiplication ∈ M.sets) :
    externalCosetRelation E G inclusion multiplication ∈ M.sets := by
  let params := extend E (extend G (extend inclusion (extend multiplication Fin.elim0)))
  have selected := M.bounded_separation_mem separation
    (BoundedFormula.externalCosetEntryFormula 0 1 2 3 4) params
    (Fin.cases hE (Fin.cases hG (Fin.cases hInclusion (Fin.cases hMultiplication (fun i => Fin.elim0 i)))))
    (M.prod_mem pairing unions powers separation hE hE)
  have equal : ZFSet.sep (fun z => BoundedFormula.Truth
      (BoundedFormula.externalCosetEntryFormula 0 1 2 3 4) (extend z params)) (ZFSet.prod E E) =
      externalCosetRelation E G inclusion multiplication := by
    apply ZFSet.ext
    intro z
    rw [externalCosetRelation, ZFSet.mem_sep, ZFSet.mem_sep]
    exact and_congr Iff.rfl (BoundedFormula.truth_externalCosetEntryFormula 0 1 2 3 4 _)
  exact equal ▸ selected

end TransitiveGround

end PartitionPilot.Forcing



namespace PartitionPilot.Forcing
open SetRealization SetFormula Compression.RecursiveMaps.CosetGeometry
universe u




namespace TransitiveGround
variable (M : TransitiveGround.{u})
noncomputable def externalStarEdges (G S R m one : ZFSet.{u}) : ZFSet.{u} :=
  tileStarEdgeCarrier (M.externalGroupCarrier G S m one) R S

end TransitiveGround

end PartitionPilot.Forcing



namespace PartitionPilot.Forcing
open SetRealization SetFormula
universe u

theorem pair_mem_tileStarRequestGraph {R S a c b : ZFSet.{u}}
    (ha : a ∈ R) (hc : c ∈ natSetCode 2) (hs : ZFSet.pair a c ∈ S) :
    ZFSet.pair (ZFSet.pair a c) b ∈ tileStarRequestGraph R S ↔ a = b := by
  rw [tileStarRequestGraph, pair_mem_graphRestriction, mem_productFirst]
  constructor
  · rintro ⟨⟨x, _, y, _, equal⟩, _⟩
    have eq := ZFSet.pair_inj.1 equal
    exact ((ZFSet.pair_inj.1 eq.1).1).trans eq.2.symm
  · rintro rfl
    exact ⟨⟨a, ha, c, hc, rfl⟩, hs⟩

end PartitionPilot.Forcing



namespace PartitionPilot.Forcing
open SetRealization SetFormula Compression.RecursiveMaps.CosetGeometry
universe u
namespace TransitiveGround
variable (M : TransitiveGround.{u})
noncomputable def externalStarReverse (G S R m one : ZFSet.{u}) : ZFSet.{u} :=
  tileStarReverseGraph (M.externalGroupCarrier G S m one) R S

end TransitiveGround

end PartitionPilot.Forcing

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Geometry_GroundCodedBinaryHeights
attribute [-instance] _root_.OAI.PartitionPilot.Forcing.GroundMainPrefix.withTopSmall
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open scoped ZFSet


section

namespace PartitionPilot.Forcing
open SetRealization Compression.RecursiveMaps SetFormula
universe u

noncomputable def StrictLinearOrderCode.smallOrder {H rH : ZFSet.{u}}
    (code : StrictLinearOrderCode H rH) : LinearHeightOrder (SetMembers H) where
  lt x y := ZFSet.pair (SetMembers.raw x) (SetMembers.raw y) ∈ rH
  irrefl x := code.irrefl _ (SetMembers.raw_mem x)
  trans {x y z} := code.trans (SetMembers.raw x) (SetMembers.raw y) (SetMembers.raw z)
  compare x y := (code.compare _ (SetMembers.raw_mem x) _ (SetMembers.raw_mem y)).imp id
    (fun h => h.imp (fun eq => SetMembers.raw_injective H eq) id)

noncomputable def StrictHeightGraphCode.smallHeight {L H rL rH h μ : ZFSet.{u}}
    (code : StrictHeightGraphCode L H rL rH h) (meet : MeetOrderCode L rL μ)
    (linear : StrictLinearOrderCode H rH) :
    StrictHeight meet.toSmallMeetOrder linear.smallOrder.toHeightOrder where
  value := (SetMembers.presentation L).decodeFunction (SetMembers.presentation H) h code.function
  strict x y lower different := code.strict _ (SetMembers.raw_mem x) _ (SetMembers.raw_mem y)
    (fun eq => different (SetMembers.raw_injective L eq)) lower _ _
    ((SetMembers.presentation L).decodeFunction_mem (SetMembers.presentation H) h code.function x)
    ((SetMembers.presentation L).decodeFunction_mem (SetMembers.presentation H) h code.function y)

end PartitionPilot.Forcing

end


end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Geometry_GroundExternalLocalHeightSelection
attribute [-instance] _root_.OAI.PartitionPilot.Forcing.GroundMainPrefix.withTopSmall
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open scoped ZFSet



namespace PartitionPilot.Forcing
open SetFormula
universe u

namespace TransitiveGround
theorem vertexImageDomains_mem (M : TransitiveGround.{u})
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    {Requests N U Q V images : ZFSet.{u}}
    (hRequests : Requests ∈ M.sets) (hN : N ∈ M.sets) (hU : U ∈ M.sets)
    (hQ : Q ∈ M.sets) (hV : V ∈ M.sets) (hImages : images ∈ M.sets) :
    vertexImageDomains Requests N U Q V images ∈ M.sets := by
  let params := extend Requests (extend N (extend U (extend Q (extend V (extend images Fin.elim0)))))
  have selected := M.bounded_separation_mem separation
    (BoundedFormula.vertexImageDomainsEntryFormula 0 1 2 3 4 5 6) params
    (Fin.cases hRequests (Fin.cases hN (Fin.cases hU (Fin.cases hQ
      (Fin.cases hV (Fin.cases hImages (fun j => Fin.elim0 j)))))))
    (M.prod_mem pairing unions powers separation hRequests hQ)
  have equal : ZFSet.sep (fun z => BoundedFormula.Truth
      (BoundedFormula.vertexImageDomainsEntryFormula 0 1 2 3 4 5 6) (extend z params))
      (ZFSet.prod Requests Q) = vertexImageDomains Requests N U Q V images := by
    apply ZFSet.ext
    intro z
    rw [ZFSet.mem_sep, BoundedFormula.truth_vertexImageDomainsEntryFormula]
    exact ⟨And.right, fun hz => ⟨(ZFSet.mem_sep.1 hz).1, hz⟩⟩
  exact equal ▸ selected
end TransitiveGround

end PartitionPilot.Forcing



end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Geometry_GroundExternalTileSlotSupports
attribute [-instance] _root_.OAI.PartitionPilot.Forcing.GroundMainPrefix.withTopSmall
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PartitionPilot.Forcing

section
open SetFormula
universe u

theorem pair_mem_externalTileSlotSupports (V E I U B action vertexImages v j x : ZFSet.{u}) :
    ZFSet.pair (ZFSet.pair v j) x ∈ externalTileSlotSupports V E I U B action vertexImages ↔
      v ∈ V ∧ j ∈ natSetCode 3 ∧ x ∈ B ∧ ∃ w ∈ E, ∃ r ∈ I, ∃ u ∈ U, ∃ z ∈ B,
        v = ZFSet.pair (natSetCode 1) (ZFSet.pair w r) ∧
          ZFSet.pair (ZFSet.pair (ZFSet.pair r j) u) z ∈ vertexImages ∧
          ZFSet.pair (ZFSet.pair w z) x ∈ action := by
  rw [externalTileSlotSupports, ZFSet.mem_sep]
  constructor
  · rintro ⟨_, v', hv, j', hj, x', hx, w, hw, r, hr, u, hu, z, hz, equal, body⟩
    obtain ⟨left, rfl⟩ := ZFSet.pair_inj.1 equal
    obtain ⟨rfl, rfl⟩ := ZFSet.pair_inj.1 left
    exact ⟨hv, hj, hx, w, hw, r, hr, u, hu, z, hz, body⟩
  · rintro ⟨hv, hj, hx, w, hw, r, hr, u, hu, z, hz, body⟩
    exact ⟨ZFSet.pair_mem_prod.2 ⟨ZFSet.pair_mem_prod.2 ⟨hv, hj⟩, hx⟩,
      v, hv, j, hj, x, hx, w, hw, r, hr, u, hu, z, hz, rfl, body⟩

end

namespace TransitiveGround
open SetFormula
universe u
variable (M : TransitiveGround.{u})

theorem externalTileSlotSupports_mem
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (infinite : Realize M.sets infinity Fin.elim0)
    {V E I U B action vertexImages : ZFSet.{u}}
    (hV : V ∈ M.sets) (hE : E ∈ M.sets) (hI : I ∈ M.sets) (hU : U ∈ M.sets)
    (hB : B ∈ M.sets) (hAction : action ∈ M.sets) (hImages : vertexImages ∈ M.sets) :
    externalTileSlotSupports V E I U B action vertexImages ∈ M.sets := by
  have hOne := M.natSetCode_mem separation infinite 1
  have hThree := M.natSetCode_mem separation infinite 3
  let params := extend V (extend E (extend I (extend U (extend B (extend action
    (extend vertexImages (extend (natSetCode 1) (extend (natSetCode 3) Fin.elim0))))))))
  have selected := M.bounded_separation_mem separation
    (BoundedFormula.externalTileSlotSupportFormula 0 1 2 3 4 5 6 7 8 9) params
    (Fin.cases hV (Fin.cases hE (Fin.cases hI (Fin.cases hU (Fin.cases hB
      (Fin.cases hAction (Fin.cases hImages (Fin.cases hOne (Fin.cases hThree (fun i => Fin.elim0 i))))))))))
    (M.prod_mem pairing unions powers separation (M.prod_mem pairing unions powers separation hV hThree) hB)
  have equal : ZFSet.sep (fun y => BoundedFormula.Truth
      (BoundedFormula.externalTileSlotSupportFormula 0 1 2 3 4 5 6 7 8 9) (extend y params))
      (ZFSet.prod (ZFSet.prod V (natSetCode 3)) B) =
      externalTileSlotSupports V E I U B action vertexImages := by
    apply ZFSet.ext
    intro y
    rw [ZFSet.mem_sep, BoundedFormula.truth_externalTileSlotSupportFormula _ _ _ _ _ _ _ _ _ _ _ rfl rfl]
    exact ⟨And.right, fun h => ⟨(ZFSet.mem_sep.1 h).1, h⟩⟩
  exact equal ▸ selected

end TransitiveGround

end PartitionPilot.Forcing

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Definability_LeastSlotOwnerCodes
attribute [-instance] _root_.OAI.PartitionPilot.Forcing.GroundMainPrefix.withTopSmall
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PartitionPilot.Forcing
open SetFormula SetRealization
universe u

namespace TransitiveGround
theorem leastSupportGraph_mem (M : TransitiveGround.{u})
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (infinite : Realize M.sets infinity Fin.elim0)
    {V Q depths supports : ZFSet.{u}} (hV : V ∈ M.sets) (hQ : Q ∈ M.sets)
    (hDepths : depths ∈ M.sets) (hSupports : supports ∈ M.sets) :
    leastSupportGraph V Q depths supports ∈ M.sets := by
  have hOmega := M.omega_mem separation infinite
  let params := extend V (extend Q (extend ZFSet.omega (extend depths (extend supports Fin.elim0))))
  have selected := M.bounded_separation_mem separation (BoundedFormula.leastSupportEntryFormula 0 1 2 3 4 5)
    params (Fin.cases hV (Fin.cases hQ (Fin.cases hOmega (Fin.cases hDepths
      (Fin.cases hSupports (fun i => Fin.elim0 i)))))) (M.prod_mem pairing unions powers separation hQ hV)
  have equal : ZFSet.sep (fun z => BoundedFormula.Truth (BoundedFormula.leastSupportEntryFormula 0 1 2 3 4 5)
      (extend z params)) (ZFSet.prod Q V) = leastSupportGraph V Q depths supports := by
    apply ZFSet.ext
    intro z
    rw [leastSupportGraph, ZFSet.mem_sep, ZFSet.mem_sep]
    exact and_congr Iff.rfl (BoundedFormula.truth_leastSupportEntryFormula _ _ _ _ _ _ _)
  exact equal ▸ selected
end TransitiveGround

end PartitionPilot.Forcing



namespace PartitionPilot.Forcing
open SetFormula
universe u

theorem pair_mem_leastSlotOwnerGraph (P B V owner supports x j : ZFSet.{u}) :
    ZFSet.pair x j ∈ leastSlotOwnerGraph P B V owner supports ↔
      x ∈ B ∧ j ∈ natSetCode 3 ∧ x ∉ P ∧ ∃ v ∈ V,
        ZFSet.pair x v ∈ owner ∧ LeastSlotCode supports v x j := by
  rw [leastSlotOwnerGraph, ZFSet.mem_sep]
  constructor
  · rintro ⟨_, x', hx, j', hj, v, hv, equal, fresh, owned, code⟩
    obtain ⟨rfl, rfl⟩ := ZFSet.pair_inj.1 equal
    exact ⟨hx, hj, fresh, v, hv, owned, code⟩
  · rintro ⟨hx, hj, fresh, v, hv, owned, code⟩
    exact ⟨ZFSet.pair_mem_prod.2 ⟨hx, hj⟩, x, hx, j, hj, v, hv, rfl, fresh, owned, code⟩

theorem pair_mem_leastSlotOwnerGraph_of_owner {P B V owner supports x j v : ZFSet.{u}}
    (function : ZFSet.IsFunc B V owner) (owned : ZFSet.pair x v ∈ owner) :
    ZFSet.pair x j ∈ leastSlotOwnerGraph P B V owner supports ↔
      j ∈ natSetCode 3 ∧ x ∉ P ∧ LeastSlotCode supports v x j := by
  have shape := ZFSet.pair_mem_prod.1 (function.1 owned)
  rw [pair_mem_leastSlotOwnerGraph]
  constructor
  · rintro ⟨_, hj, fresh, v', _, owned', code⟩
    have equal := (show FunctionGraphOn B owner from ⟨V, function⟩).unique owned' owned
    exact ⟨hj, fresh, equal ▸ code⟩
  · rintro ⟨hj, fresh, code⟩
    exact ⟨shape.1, hj, fresh, v, shape.2, owned, code⟩

theorem leastSlotOwnerGraph_partial {P B V owner supports : ZFSet.{u}}
    (function : ZFSet.IsFunc B V owner) :
    PartialFunctionCode B (natSetCode 3) (leastSlotOwnerGraph P B V owner supports) := by
  refine ⟨fun _ hz => (ZFSet.mem_sep.1 hz).1, ?_⟩
  intro x j k first second
  obtain ⟨_, hj, _, v, _, owned, code⟩ := (pair_mem_leastSlotOwnerGraph _ _ _ _ _ _ _).1 first
  have other := (pair_mem_leastSlotOwnerGraph_of_owner function owned).1 second
  exact code.unique other.2.2 hj other.1

theorem leastSlotOwnerGraph_function {P B V owner supports : ZFSet.{u}}
    (function : ZFSet.IsFunc B V owner)
    (cover : ∀ x ∈ B, x ∉ P → ∀ v, ZFSet.pair x v ∈ owner →
      ∃ j ∈ natSetCode 3, ZFSet.pair (ZFSet.pair v j) x ∈ supports) :
    ZFSet.IsFunc (ZFSet.sep (fun x => x ∉ P) B) (natSetCode 3)
      (leastSlotOwnerGraph P B V owner supports) := by
  refine ⟨?_, ?_⟩
  · intro z hz
    have shape := (ZFSet.mem_sep.1 hz).1
    obtain ⟨x, hx, j, hj, rfl⟩ := ZFSet.mem_prod.1 shape
    have fresh := ((pair_mem_leastSlotOwnerGraph _ _ _ _ _ _ _).1 hz).2.2.1
    exact ZFSet.pair_mem_prod.2 ⟨ZFSet.mem_sep.2 ⟨hx, fresh⟩, hj⟩
  · intro x hx
    obtain ⟨hx, fresh⟩ := ZFSet.mem_sep.1 hx
    obtain ⟨v, owned, _⟩ := function.2 x hx
    obtain ⟨j, hj, code⟩ := exists_leastSlotCode (cover x hx fresh v owned)
    refine ⟨j, (pair_mem_leastSlotOwnerGraph_of_owner function owned).2 ⟨hj, fresh, code⟩, ?_⟩
    intro k other
    exact (leastSlotOwnerGraph_partial function).unique x k j other
      ((pair_mem_leastSlotOwnerGraph_of_owner function owned).2 ⟨hj, fresh, code⟩)

theorem leastSlotOwnerGraph_monotone {P B V owner supports order x y j k : ZFSet.{u}}
    (first : ZFSet.pair x j ∈ leastSlotOwnerGraph P B V owner supports)
    (second : ZFSet.pair y k ∈ leastSlotOwnerGraph P B V owner supports)
    (sameOwner : ∀ v w, ZFSet.pair x v ∈ owner → ZFSet.pair y w ∈ owner → v = w)
    (ideals : ∀ v ∈ V, ∀ t ∈ natSetCode 3, ∀ a ∈ B, ∀ b ∈ B,
      ZFSet.pair a b ∈ order → ZFSet.pair (ZFSet.pair v t) b ∈ supports →
        ZFSet.pair (ZFSet.pair v t) a ∈ supports)
    (lower : ZFSet.pair x y ∈ order) : j = k ∨ j ∈ k := by
  obtain ⟨hx, hj, _, v, hv, owned, code⟩ := (pair_mem_leastSlotOwnerGraph _ _ _ _ _ _ _).1 first
  obtain ⟨hy, hk, _, w, _, owned', code'⟩ := (pair_mem_leastSlotOwnerGraph _ _ _ _ _ _ _).1 second
  have equal := sameOwner v w owned owned'
  subst w
  exact code.le hj hk (ideals v hv k hk x hx y hy lower code'.1)

end PartitionPilot.Forcing

end

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Geometry_GroundPreparationFamilyImages
attribute [-instance] _root_.OAI.PartitionPilot.Forcing.GroundMainPrefix.withTopSmall
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PartitionPilot.Forcing
open SetFormula
universe u
namespace TransitiveGround

theorem leastSlotOwnerGraph_mem (M : TransitiveGround.{u})
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (infinite : Realize M.sets infinity Fin.elim0)
    {P B V owner supports : ZFSet.{u}} (hP : P ∈ M.sets) (hB : B ∈ M.sets)
    (hV : V ∈ M.sets) (hOwner : owner ∈ M.sets) (hSupports : supports ∈ M.sets) :
    leastSlotOwnerGraph P B V owner supports ∈ M.sets := by
  have hThree := M.natSetCode_mem separation infinite 3
  let params := extend P (extend B (extend V (extend owner (extend supports (extend (natSetCode 3) Fin.elim0)))))
  have selected := M.bounded_separation_mem separation
    (BoundedFormula.leastSlotOwnerEntryFormula 0 1 2 3 4 5 6) params
    (Fin.cases hP (Fin.cases hB (Fin.cases hV (Fin.cases hOwner
      (Fin.cases hSupports (Fin.cases hThree (fun i => Fin.elim0 i)))))))
    (M.prod_mem pairing unions powers separation hB hThree)
  have equal : ZFSet.sep (fun z => BoundedFormula.Truth
      (BoundedFormula.leastSlotOwnerEntryFormula 0 1 2 3 4 5 6) (extend z params))
      (ZFSet.prod B (natSetCode 3)) = leastSlotOwnerGraph P B V owner supports := by
    apply ZFSet.ext
    intro z
    rw [ZFSet.mem_sep, BoundedFormula.truth_leastSlotOwnerEntryFormula _ _ _ _ _ _ _ _ rfl]
    exact ⟨And.right, fun h => ⟨(ZFSet.mem_sep.1 h).1, h⟩⟩
  exact equal ▸ selected

end TransitiveGround
end PartitionPilot.Forcing

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Definability_GroundPairedCompositionRows
attribute [-instance] _root_.OAI.PartitionPilot.Forcing.GroundMainPrefix.withTopSmall
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PartitionPilot.Forcing.TransitiveGround
open SetFormula
universe u
variable (M : TransitiveGround.{u})
variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
variable (unions : Realize M.sets SetFormula.union Fin.elim0)
variable (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
include pairing unions powers separation

theorem exists_pairedCompositionRow {I a R U B C H J F e g : ZFSet.{u}}
    (hI : I ∈ M.sets) (ha : a ∈ M.sets) (hR : R ∈ M.sets) (hU : U ∈ M.sets)
    (hB : B ∈ M.sets) (hC : C ∈ M.sets) (hH : H ∈ M.sets) (hJ : J ∈ M.sets)
    (hF : F ∈ M.sets) (he : e ∈ M.sets) (hg : g ∈ M.sets)
    (function : ZFSet.IsFunc I (ZFSet.prod R R) F) :
    ∃ row ∈ M.sets, FunctionGraphOn (ZFSet.prod {a} I) row ∧
      ∀ i f k z, ZFSet.pair i (ZFSet.pair f k) ∈ F →
        (ZFSet.pair (ZFSet.pair a i) z ∈ row ↔
          z = ZFSet.pair (relationCompose U B C f e) (relationCompose U H J k g)) := by
  let first := relationCompose I (ZFSet.prod R R) R F (productFirst R R)
  let second := relationCompose I (ZFSet.prod R R) R F (productSecond R R)
  have hRR := M.prod_mem pairing unions powers separation hR hR
  have firstGround : first ∈ M.sets := M.relationCompose_mem pairing unions powers separation
    hI hRR hR hF (M.productFirst_mem pairing unions powers separation hR hR)
  have secondGround : second ∈ M.sets := M.relationCompose_mem pairing unions powers separation
    hI hRR hR hF (M.productSecond_mem pairing unions powers separation hR hR)
  have firstFunction : ZFSet.IsFunc I R first :=
    relationCompose_function_of_subset function (productFirst_function R R) (fun _ h => h)
  have secondFunction : ZFSet.IsFunc I R second :=
    relationCompose_function_of_subset function (productSecond_function R R) (fun _ h => h)
  have entries (i f k : ZFSet.{u}) (entry : ZFSet.pair i (ZFSet.pair f k) ∈ F) :
      ZFSet.pair i f ∈ first ∧ ZFSet.pair i k ∈ second := by
    obtain ⟨hi, pairBound⟩ := ZFSet.pair_mem_prod.1 (function.1 entry)
    obtain ⟨hf, hk⟩ := ZFSet.pair_mem_prod.1 pairBound
    exact ⟨(pair_mem_relationCompose _ _ _ _ _ _ _).2 ⟨hi, hf, _, pairBound, entry,
      (mem_productFirst R R _).2 ⟨f, hf, k, hk, rfl⟩⟩,
      (pair_mem_relationCompose _ _ _ _ _ _ _).2 ⟨hi, hk, _, pairBound, entry,
      (mem_productSecond R R _).2 ⟨f, hf, k, hk, rfl⟩⟩⟩
  have hA : ({a} : ZFSet.{u}) ∈ M.sets := by
    simpa only [ZFSet.pair_eq_singleton] using M.unorderedPair_mem pairing ha ha
  have hK := M.prod_mem pairing unions powers separation hA hI
  have one := M.groundPairCompositions_spec pairing unions powers separation
    hK hA hI hU hB hC firstGround
    (M.constantFamilyGraph_mem pairing unions powers separation hA he)
    ⟨R, firstFunction⟩ ⟨{e}, constantFamilyGraph_function {a} e⟩ (fun _ h => h)
  have two := M.groundPairCompositions_spec pairing unions powers separation
    hK hA hI hU hH hJ secondGround
    (M.constantFamilyGraph_mem pairing unions powers separation hA hg)
    ⟨R, secondFunction⟩ ⟨{g}, constantFamilyGraph_function {a} g⟩ (fun _ h => h)
  let row := pairedGraph (ZFSet.prod {a} I) (M.groundRelations U C) (M.groundRelations U J)
    (M.groundPairCompositions (ZFSet.prod {a} I) {a} I U B C first (constantFamilyGraph {a} e))
    (M.groundPairCompositions (ZFSet.prod {a} I) {a} I U H J second (constantFamilyGraph {a} g))
  have rowFunction := pairedGraph_function_of_subset one.2.1 two.2.1 (fun _ h => h)
  refine ⟨row, M.pairedGraph_mem pairing unions powers separation hK
    (M.groundRelations_mem pairing unions powers separation hU hC)
    (M.groundRelations_mem pairing unions powers separation hU hJ) one.1 two.1,
    ⟨_, rowFunction⟩, ?_⟩
  intro i f k z entry
  have hi := (ZFSet.pair_mem_prod.1 (function.1 entry)).1
  have keyMember : ZFSet.pair a i ∈ ZFSet.prod {a} I := ZFSet.pair_mem_prod.2 ⟨ZFSet.mem_singleton.2 rfl, hi⟩
  have left := one.2.2 a i f e (relationCompose U B C f e) (entries i f k entry).1
    ((pair_mem_constantFamilyGraph {a} e a e).2 ⟨ZFSet.mem_singleton.2 rfl, rfl⟩)
  have right := two.2.2 a i k g (relationCompose U H J k g) (entries i f k entry).2
    ((pair_mem_constantFamilyGraph {a} g a g).2 ⟨ZFSet.mem_singleton.2 rfl, rfl⟩)
  have leftEntry := left.2 ⟨keyMember, rfl⟩
  have rightEntry := right.2 ⟨keyMember, rfl⟩
  have actual : ZFSet.pair (ZFSet.pair a i)
      (ZFSet.pair (relationCompose U B C f e) (relationCompose U H J k g)) ∈ row :=
    (pair_mem_pairedGraph _ _ _ _ _ _ _ _).2 ⟨keyMember,
      (ZFSet.pair_mem_prod.1 (one.2.1.1 leftEntry)).2,
      (ZFSet.pair_mem_prod.1 (two.2.1.1 rightEntry)).2, leftEntry, rightEntry⟩
  exact ⟨fun hz => (FunctionGraphOn.unique ⟨_, rowFunction⟩ hz actual), fun equal => equal.symm ▸ actual⟩

end PartitionPilot.Forcing.TransitiveGround

end

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Transfinite_GroundStageOneOrder
attribute [-instance] _root_.OAI.PartitionPilot.Forcing.GroundMainPrefix.withTopSmall
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PartitionPilot.Forcing
open SetFormula
universe u

namespace TransitiveGround

theorem rowAssignmentOrder_mem (M : TransitiveGround.{u})
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    {Q C B r : ZFSet.{u}} (hQ : Q ∈ M.sets) (hC : C ∈ M.sets)
    (hB : B ∈ M.sets) (hr : r ∈ M.sets) : rowAssignmentOrder Q C B r ∈ M.sets := by
  let params := extend C (extend B (extend r Fin.elim0))
  have selected := M.bounded_separation_mem separation
    (BoundedFormula.rowAssignmentOrderFormula 0 1 2 3) params
    (Fin.cases hC (Fin.cases hB (Fin.cases hr (fun j => Fin.elim0 j))))
    (M.prod_mem pairing unions powers separation hQ hQ)
  have equal : ZFSet.sep (fun z => BoundedFormula.Truth
      (BoundedFormula.rowAssignmentOrderFormula 0 1 2 3) (extend z params))
      (ZFSet.prod Q Q) = rowAssignmentOrder Q C B r := by
    apply ZFSet.ext
    intro z
    rw [ZFSet.mem_sep, mem_rowAssignmentOrder]
    exact and_congr Iff.rfl (BoundedFormula.truth_rowAssignmentOrderFormula 0 1 2 3 _)
  exact equal ▸ selected

end TransitiveGround

end PartitionPilot.Forcing

end

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Transfinite_GroundFlatLimitAdequacy
attribute [-instance] _root_.OAI.PartitionPilot.Forcing.GroundMainPrefix.withTopSmall
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PartitionPilot.Forcing.TransitiveGround
open SetFormula
universe u
variable (M : TransitiveGround.{u})

theorem refinementHistoryCandidate_cut (separation : SeparationSchema M.sets)
    {stages indexHistory rows T beta row A : ZFSet.{u}}
    (function : FunctionGraphOn stages indexHistory)
    (literal : ∀ xi I, ZFSet.pair xi I ∈ indexHistory → RefinementIndexLevelCode I xi)
    (below : beta ⊆ stages)
    (hLevels : refinementHistoryAssignmentLevels stages indexHistory T ∈ M.sets)
    (hBeta : beta ∈ M.sets) (omega : ZFSet.omega ∈ M.sets)
    (candidate : ZFSet.pair row A ∈
      M.stageOneCandidateBound rows (refinementHistoryIndices stages indexHistory) T) :
    ZFSet.pair row (assignmentCut (refinementHistoryAssignmentLevels stages indexHistory T) beta A) ∈
      M.stageOneCandidateBound rows (refinementHistoryIndices beta indexHistory) T := by
  obtain ⟨hrow, hA, _, small⟩ := (M.pair_mem_stageOneCandidateBound _ _ _ _ _).1 candidate
  apply (M.pair_mem_stageOneCandidateBound _ _ _ _ _).2
  refine ⟨hrow, M.assignmentCut_mem separation hLevels hBeta hA, ?_,
    M.assignmentCut_small separation hLevels hBeta hA omega small⟩
  rw [refinementHistoryAssignmentCut_eq function literal below]
  exact fun _ member => (ZFSet.mem_sep.1 member).2

end PartitionPilot.Forcing.TransitiveGround

end

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Forcing_GroundNiceRefinementIndexActionLaws
attribute [-instance] _root_.OAI.PartitionPilot.Forcing.GroundMainPrefix.withTopSmall
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PartitionPilot.Forcing.TransitiveGround

section
open SetRealization SetFormula
universe u
variable (M : TransitiveGround.{u}) {G P L : Type u}
variable [Group G] [PartialOrder P] [OrderTop P] [PartialOrder L]
variable (a : PosetAction G P) (s : Presentation P) (b : Presentation L) (d : PosetAction G L)
variable (level T1 T2 : ZFSet.{u})
variable (valid1 : ∀ z ∈ T1, IsName s z) (valid2 : ∀ z ∈ T2, IsName s z)

noncomputable def niceRefinementIndexCoordinateGraphs (g : G) : Fin 6 → ZFSet.{u} :=
  ![identityFunctionGraph {level}, b.graph b (d.iso g), b.graph b (d.iso g),
    Name.renameFamilyGraph s (a.iso g) (M.groundRelations T1 s.carrier)
      (fun z hz => Name.isName_of_subset valid1 ((M.mem_groundRelations T1 s.carrier z).1 hz).2),
    Name.renameFamilyGraph s (a.iso g) (M.groundRelations T2 s.carrier)
      (fun z hz => Name.isName_of_subset valid2 ((M.mem_groundRelations T2 s.carrier z).1 hz).2),
    Name.renameFamilyGraph s (a.iso g) (M.groundRelations T2 s.carrier)
      (fun z hz => Name.isName_of_subset valid2 ((M.mem_groundRelations T2 s.carrier z).1 hz).2)]

noncomputable def niceRefinementIndexActionGraph (g : G) : ZFSet.{u} :=
  ZFSet.sep (fun z => z ∈ tupleRelationProduct 5
    (M.niceRefinementIndexCoordinateGraphs a s b d level T1 T2 valid1 valid2 g))
    (ZFSet.prod (M.niceRefinementIndices a s b d level T1 T2 valid1)
      (M.niceRefinementIndices a s b d level T1 T2 valid1))

theorem pair_mem_niceRefinementIndexActionGraph (g : G) (x y : Fin 6 → ZFSet.{u}) :
    ZFSet.pair (nonemptyTupleCode 5 x) (nonemptyTupleCode 5 y) ∈
      M.niceRefinementIndexActionGraph a s b d level T1 T2 valid1 valid2 g ↔
    nonemptyTupleCode 5 x ∈ M.niceRefinementIndices a s b d level T1 T2 valid1 ∧
    nonemptyTupleCode 5 y ∈ M.niceRefinementIndices a s b d level T1 T2 valid1 ∧
      ∀ j, ZFSet.pair (x j) (y j) ∈
        M.niceRefinementIndexCoordinateGraphs a s b d level T1 T2 valid1 valid2 g j := by
  rw [niceRefinementIndexActionGraph, ZFSet.mem_sep, ZFSet.pair_mem_prod,
    pair_mem_tupleRelationProduct]
  exact and_assoc

end

open SetRealization SetFormula
universe u

end PartitionPilot.Forcing.TransitiveGround

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Forcing_GroundRefinementAssignmentActionFamilies
attribute [-instance] _root_.OAI.PartitionPilot.Forcing.GroundMainPrefix.withTopSmall
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI



namespace PartitionPilot.Forcing.TransitiveGround
open SetRealization SetFormula
universe u
variable (M : TransitiveGround.{u}) {G P L : Type u}
variable [Group G] [PartialOrder P] [OrderTop P] [PartialOrder L]
variable (a : PosetAction G P) (s : Presentation P) (b : Presentation L) (d : PosetAction G L)
variable (level T T2 : ZFSet.{u}) (valid : ∀ z ∈ T, IsName s z) (valid2 : ∀ z ∈ T2, IsName s z)
local notation "I" => M.niceRefinementIndices a s b d level T T2 valid
local notation "indexGraph" => M.niceRefinementIndexActionGraph a s b d level T T2 valid valid2

noncomputable def refinementAssignmentActionGraph (g : G) : ZFSet.{u} :=
  relationProduct I (ZFSet.prod T T) I (ZFSet.prod T T) (indexGraph g)
    (relationProduct T T T T (Name.renameFamilyGraph s (a.iso g) T valid)
      (Name.renameFamilyGraph s (a.iso g) T valid))

theorem pair_mem_refinementAssignmentActionGraph (g : G) (i u w i' u' w' : ZFSet.{u}) :
    ZFSet.pair (stageOneAssignment i u w) (stageOneAssignment i' u' w') ∈
      M.refinementAssignmentActionGraph a s b d level T T2 valid valid2 g ↔
    i ∈ I ∧ u ∈ T ∧ w ∈ T ∧ i' ∈ I ∧ u' ∈ T ∧ w' ∈ T ∧
      ZFSet.pair i i' ∈ indexGraph g ∧
      ZFSet.pair u u' ∈ Name.renameFamilyGraph s (a.iso g) T valid ∧
      ZFSet.pair w w' ∈ Name.renameFamilyGraph s (a.iso g) T valid := by
  simp only [refinementAssignmentActionGraph, stageOneAssignment,
    pair_mem_relationProduct, ZFSet.pair_mem_prod]
  tauto

end PartitionPilot.Forcing.TransitiveGround



end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Geometry_GroundRefinementAssignmentImages
attribute [-instance] _root_.OAI.PartitionPilot.Forcing.GroundMainPrefix.withTopSmall
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PartitionPilot.Forcing.TransitiveGround
open SetRealization SetFormula
universe u
variable (M : TransitiveGround.{u}) {G P L : Type u}
variable [Group G] [PartialOrder P] [OrderTop P] [PartialOrder L]
variable (a : PosetAction G P) (s : Presentation P) (b : Presentation L) (d : PosetAction G L)
variable (level T T2 : ZFSet.{u}) (valid : ∀ z ∈ T, IsName s z) (valid2 : ∀ z ∈ T2, IsName s z)
local notation "I" => M.niceRefinementIndices a s b d level T T2 valid
local notation "J" => stageOneAssignments I T
local notation "graph" => M.refinementAssignmentActionGraph a s b d level T T2 valid valid2

noncomputable def refinementAssignmentImage (g : G) (A : ZFSet.{u}) : ZFSet.{u} :=
  relationImage A J (graph g)

end PartitionPilot.Forcing.TransitiveGround

end

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Definability_GroundStageOneFormulaData
attribute [-instance] _root_.OAI.PartitionPilot.Forcing.GroundMainPrefix.withTopSmall
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PartitionPilot.Forcing.TransitiveGround
open SetRealization SetFormula
universe u
variable (M : TransitiveGround.{u}) {G P L : Type u}
variable [Group G] [PartialOrder P] [OrderTop P] [PartialOrder L]
variable (a : PosetAction G P) (s : Presentation P) (b : Presentation L) (d : PosetAction G L)
variable (T T2 : ZFSet.{u}) (valid : ∀ z ∈ T, IsName s z)

noncomputable def stageOneFormulaData : Fin 15 → ZFSet.{u} :=
  let I := M.niceRefinementIndices a s b d ∅ T T2 valid
  let bounds := M.niceRefinementIndexBounds s b ∅ T T2
  ![I, refinementIndexFieldGraph I (bounds 1) 1, refinementIndexFieldGraph I (bounds 2) 2,
    refinementIndexFieldGraph I (bounds 3) 3, refinementIndexFieldGraph I (bounds 4) 4,
    refinementIndexFieldGraph I (bounds 5) 5, T, s.carrier, s.conditionOrder, s.encode ⊤,
    b.carrier, b.conditionOrder, M.niceRefinementNameGraph a s b d 2 ∅ T T2 valid,
    M.niceVisibilityGraph a s b T d.principalFix, M.groundRelations T s.carrier]

end PartitionPilot.Forcing.TransitiveGround

end

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Forcing_GroundStageOneRawNames
attribute [-instance] _root_.OAI.PartitionPilot.Forcing.GroundMainPrefix.withTopSmall
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PartitionPilot.Forcing.TransitiveGround
open SetRealization SetFormula
universe u
variable (M : TransitiveGround.{u}) {P : Type u}
variable [PartialOrder P] [OrderTop P] (s : Presentation P)
variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
variable (unions : Realize M.sets SetFormula.union Fin.elim0)
variable (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
variable (collection : CollectionSchema M.sets)
variable (carrier : s.carrier ∈ M.sets) (order : s.conditionOrder ∈ M.sets)
variable {T : ZFSet.{u}} (hT : T ∈ M.sets) (valid : ∀ z ∈ T, IsName s z)

variable {G L : Type u} [Group G] [PartialOrder L]
variable (a : PosetAction G P) (b : Presentation L) (d : PosetAction G L)
variable {T2 : ZFSet.{u}} {valid2 : ∀ z ∈ T2, IsName s z}
variable (indices : NiceRefinementIndexSystem M a s b d ∅ T T2 valid valid2)

variable (base : L) (directed : ∀ x y : L, ∃ z, x ≤ z ∧ y ≤ z)
variable (system : NiceNameSystem M a s b d base directed T valid)

theorem stageOneFormulaData_visibility (v : L) (z : ZFSet.{u}) :
    ZFSet.pair (b.encode v) z ∈ M.stageOneFormulaData a s b d T T2 valid 13 ↔
      z = (M.stageOneVisibilityName s valid a b d base directed system v).val.val :=
  system.visibility_entries v z

end PartitionPilot.Forcing.TransitiveGround

end

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Geometry_GroundMainFinalSeparatedActors
attribute [-instance] _root_.OAI.PartitionPilot.Forcing.GroundMainPrefix.withTopSmall
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PartitionPilot.Forcing

namespace TransitiveGround

open SetRealization SetFormula Compression.RecursiveMaps.CosetGeometry
universe u
variable (M : TransitiveGround.{u})

theorem decoded_supportBasis_mem {G L m i e R A : ZFSet.{u}}
    (group : GroupCode G m i e) (order : PartialOrderCode L R)
    (action : PosetActionCode G L m e R A)
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (hL : L ∈ M.sets) (hG : G ∈ M.sets) (hR : R ∈ M.sets) (hA : A ∈ M.sets) :
    letI := group.toGroup
    letI := order.toPartialOrder
    supportBasisCode (SetMembers.presentation L) (SetMembers.presentation G)
      (action.toPosetAction group order).principalFix ∈ M.sets := by
  let := group.toGroup
  let := order.toPartialOrder
  have order_mem : (SetMembers.presentation L).conditionOrder ∈ M.sets := by
    rw [order.conditionOrder_eq]
    exact hR
  have action_mem : (action.toPosetAction group order).actionGraph
      (SetMembers.presentation L) (SetMembers.presentation G) ∈ M.sets := by
    rw [action.actionGraph_eq group order]
    exact hA
  exact M.principalSupportBasis_mem (action.toPosetAction group order)
    (SetMembers.presentation L) (SetMembers.presentation G) pairing unions powers separation hL hG order_mem action_mem

end TransitiveGround

namespace GroundMainFinalGeometry
open SetFormula SetRealization
universe u
variable {M : TransitiveGround.{u}} {C D rD : ZFSet.{u}}
variable (geometry : GroundMainFinalGeometry M C D rD)

noncomputable def decodedAction :
    letI := geometry.group_code.toGroup
    letI := geometry.meet.order.toPartialOrder
    PosetAction (SetMembers geometry.actors) (SetMembers geometry.carrier) :=
  geometry.action_code.toPosetAction geometry.group_code geometry.meet.order

theorem decoded_order_eq :
    letI := geometry.meet.order.toPartialOrder
    (SetMembers.presentation geometry.carrier).conditionOrder = geometry.order :=
  geometry.meet.order.conditionOrder_eq

theorem decoded_action_eq :
    letI := geometry.group_code.toGroup
    letI := geometry.meet.order.toPartialOrder
    geometry.decodedAction.actionGraph (SetMembers.presentation geometry.carrier)
      (SetMembers.presentation geometry.actors) = geometry.action :=
  geometry.action_code.actionGraph_eq geometry.group_code geometry.meet.order

theorem decoded_supportBasis_ground
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets) :
    letI := geometry.group_code.toGroup
    letI := geometry.meet.order.toPartialOrder
    supportBasisCode (SetMembers.presentation geometry.carrier) (SetMembers.presentation geometry.actors)
      geometry.decodedAction.principalFix ∈ M.sets :=
  M.decoded_supportBasis_mem geometry.group_code geometry.meet.order geometry.action_code
    pairing unions powers separation geometry.carrier_ground geometry.actors_ground
    geometry.order_ground geometry.action_ground

end GroundMainFinalGeometry

end PartitionPilot.Forcing

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Transfinite_ExternalChronologyStageLaws
attribute [-instance] _root_.OAI.PartitionPilot.Forcing.GroundMainPrefix.withTopSmall
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace PartitionPilot.Forcing
open SetFormula
universe u

namespace TransitiveGround
variable (M : TransitiveGround.{u})

variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
variable (unions : Realize M.sets SetFormula.union Fin.elim0)
variable (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
variable (infinite : Realize M.sets infinity Fin.elim0)
variable {P B levels : ZFSet.{u}} (hP : P ∈ M.sets) (hB : B ∈ M.sets) (hLevels : levels ∈ M.sets)
include pairing unions powers separation infinite hP hB hLevels

theorem ownerLevelPrefixPoints_mem : ownerLevelPrefixPoints P B levels ∈ M.sets := by
  have hOmega := M.omega_mem separation infinite
  let params := extend P (extend B (extend levels (extend ZFSet.omega Fin.elim0)))
  have selected := M.bounded_separation_mem separation
    (BoundedFormula.ownerLevelPrefixPointFormula 0 1 2 3 4) params
    (Fin.cases hP (Fin.cases hB (Fin.cases hLevels (Fin.cases hOmega (fun i => Fin.elim0 i)))))
    (M.prod_mem pairing unions powers separation hOmega hB)
  have equal : ZFSet.sep (fun z => BoundedFormula.Truth
      (BoundedFormula.ownerLevelPrefixPointFormula 0 1 2 3 4) (extend z params))
      (ZFSet.prod ZFSet.omega B) = ownerLevelPrefixPoints P B levels := by
    apply ZFSet.ext
    intro z
    rw [ZFSet.mem_sep, BoundedFormula.truth_ownerLevelPrefixPointFormula _ _ _ _ _ _ rfl]
    exact ⟨And.right, fun h => ⟨(ZFSet.mem_sep.1 h).1, h⟩⟩
  exact equal ▸ selected

theorem ownerLevelPrefix_mem (subset : P ⊆ B) {n : ZFSet.{u}} (hn : n ∈ ZFSet.omega) :
    ownerLevelPrefix P B levels n ∈ M.sets := by
  rw [← ownerLevelPrefixPoints_fiber subset hn]
  exact M.relationFiber_mem separation hB (M.ownerLevelPrefixPoints_mem pairing unions powers separation infinite hP hB hLevels)
    (M.transitive (M.omega_mem separation infinite) hn)

theorem ownerLevelPrefixFamily_spec (subset : P ⊆ B) :
    M.ownerLevelPrefixFamily P B levels ∈ M.sets ∧
      FunctionGraphOn ZFSet.omega (M.ownerLevelPrefixFamily P B levels) ∧
      ∀ n S, ZFSet.pair n S ∈ M.ownerLevelPrefixFamily P B levels ↔
        n ∈ ZFSet.omega ∧ S = ownerLevelPrefix P B levels n := by
  have hOmega := M.omega_mem separation infinite
  have hPoints := M.ownerLevelPrefixPoints_mem pairing unions powers separation infinite hP hB hLevels
  refine ⟨M.relationFiberFamily_mem pairing unions powers separation hOmega hB hPoints,
    ⟨M.groundPower B, M.relationFiberFamily_function separation hOmega hB hPoints⟩, ?_⟩
  intro n S
  change ZFSet.pair n S ∈ M.relationFiberFamily _ _ _ ↔ _
  rw [M.relationFiberFamily_entries separation hOmega hB hPoints]
  exact ⟨fun h => ⟨h.1, h.2.trans (ownerLevelPrefixPoints_fiber subset h.1)⟩,
    fun h => ⟨h.1, h.2.trans (ownerLevelPrefixPoints_fiber subset h.1).symm⟩⟩

end TransitiveGround





theorem MeetOrderCode.restrict_lower {B Q r μ : ZFSet.{u}}
    (meet : MeetOrderCode B r μ) (subset : Q ⊆ B)
    (lower : ∀ x ∈ B, ∀ y ∈ Q, ZFSet.pair x y ∈ r → x ∈ Q) :
    MeetOrderCode Q (heightOrderRestriction Q r) (graphRestriction (ZFSet.prod Q Q) μ) := by
  have productSubset : ZFSet.prod Q Q ⊆ ZFSet.prod B B := by
    intro z hz
    obtain ⟨x, hx, y, hy, rfl⟩ := ZFSet.mem_prod.1 hz
    exact ZFSet.pair_mem_prod.2 ⟨subset hx, subset hy⟩
  have function := (show FunctionGraphOn (ZFSet.prod B B) μ from ⟨B, meet.operation⟩).restrict productSubset
  have result : ∀ x y z, ZFSet.pair (ZFSet.pair x y) z ∈ graphRestriction (ZFSet.prod Q Q) μ → z ∈ Q := by
    intro x y z entry
    obtain ⟨entry, domain⟩ := pair_mem_graphRestriction.1 entry
    exact lower z (ZFSet.pair_mem_prod.1 (meet.operation.1 entry)).2
      x (ZFSet.pair_mem_prod.1 domain).1 (meet.lower_left x y z entry)
  refine ⟨meet.order.heightOrderRestriction subset, ⟨?_, function.to_isFunc.2⟩, ?_, ?_, ?_⟩
  · intro z hz
    obtain ⟨a, ha, w, rfl, _⟩ := mem_graphRestriction.1 hz
    obtain ⟨x, hx, y, hy, rfl⟩ := ZFSet.mem_prod.1 ha
    exact ZFSet.pair_mem_prod.2 ⟨ZFSet.pair_mem_prod.2 ⟨hx, hy⟩, result x y w hz⟩
  · intro x y z entry
    have domain := ZFSet.pair_mem_prod.1 (pair_mem_graphRestriction.1 entry).2
    exact (pair_mem_heightOrderRestriction _ _ _ _).2
      ⟨meet.lower_left x y z (pair_mem_graphRestriction.1 entry).1, result x y z entry, domain.1⟩
  · intro x y z entry
    have domain := ZFSet.pair_mem_prod.1 (pair_mem_graphRestriction.1 entry).2
    exact (pair_mem_heightOrderRestriction _ _ _ _).2
      ⟨meet.lower_right x y z (pair_mem_graphRestriction.1 entry).1, result x y z entry, domain.2⟩
  · intro x y z w hw entry left right
    exact (pair_mem_heightOrderRestriction _ _ _ _).2
      ⟨meet.greatest x y z w (subset hw) (pair_mem_graphRestriction.1 entry).1
        (ZFSet.mem_sep.1 left).1 (ZFSet.mem_sep.1 right).1, hw, result x y z entry⟩

theorem StrictLexHeightCode.restrict_order {B Q C D r height rD : ZFSet.{u}}
    (code : StrictLexHeightCode B C D r height rD) (subset : Q ⊆ B) :
    StrictLexHeightCode Q C D (heightOrderRestriction Q r) (graphRestriction Q height) rD := by
  have function := (show FunctionGraphOn B height from ⟨ZFSet.prod C D, code.function⟩).restrict subset
  refine ⟨⟨?_, function.to_isFunc.2⟩, ?_⟩
  · intro z hz
    obtain ⟨x, hx, y, rfl, entry⟩ := mem_graphRestriction.1 hz
    exact ZFSet.pair_mem_prod.2 ⟨hx, (ZFSet.pair_mem_prod.1 (code.function.1 entry)).2⟩
  · intro x hx y hy c q d v lower distinct first second
    exact code.strict x (subset hx) y (subset hy) c q d v (ZFSet.mem_sep.1 lower).1 distinct
      (pair_mem_graphRestriction.1 first).1 (pair_mem_graphRestriction.1 second).1

namespace TransitiveGround
variable (M : TransitiveGround.{u})

variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
variable (unions : Realize M.sets SetFormula.union Fin.elim0)
variable (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
include pairing unions powers separation

theorem chronologyRestrictionFamily_mem (kind : Fin 3) {I Ps f : ZFSet.{u}}
    (hI : I ∈ M.sets) (hPs : Ps ∈ M.sets) (hf : f ∈ M.sets) :
    M.chronologyRestrictionFamily kind I Ps f ∈ M.sets := by
  have hW := M.groundPower_mem powers hf
  let params := extend I (extend Ps (extend (ZFSet.sUnion (ZFSet.sUnion Ps)) (extend (ZFSet.sUnion (ZFSet.sUnion f))
    (extend (M.groundPower f) (extend f Fin.elim0)))))
  have selected := M.bounded_separation_mem separation
    (BoundedFormula.chronologyRestrictionFamilyFormula kind 0 1 2 3 4 5 6) params
    (Fin.cases hI (Fin.cases hPs (Fin.cases (M.union_mem unions (M.union_mem unions hPs))
      (Fin.cases (M.union_mem unions (M.union_mem unions hf)) (Fin.cases hW
        (Fin.cases hf (fun i => Fin.elim0 i)))))))
    (M.prod_mem pairing unions powers separation hI hW)
  have equal : ZFSet.sep (fun z => BoundedFormula.Truth
      (BoundedFormula.chronologyRestrictionFamilyFormula kind 0 1 2 3 4 5 6) (extend z params))
      (ZFSet.prod I (M.groundPower f)) = M.chronologyRestrictionFamily kind I Ps f := by
    apply ZFSet.ext
    intro z
    rw [ZFSet.mem_sep, chronologyRestrictionFamily, ZFSet.mem_sep,
      BoundedFormula.truth_chronologyRestrictionFamilyFormula kind _ _ _ _ _ _ _ _ rfl]
    rfl
  exact equal ▸ selected

end TransitiveGround

end PartitionPilot.Forcing



end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Forcing_IdealInsertionProfileTransport
attribute [-instance] _root_.OAI.PartitionPilot.Forcing.GroundMainPrefix.withTopSmall
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PartitionPilot.Forcing.IdealEmbeddingCode
open Compression Compression.RecursiveMaps
universe u
variable {P Q rP rQ μP μQ e : ZFSet.{u}}
variable (code : IdealEmbeddingCode P Q rP rQ μP μQ e)
variable (source : MeetOrderCode P rP μP) (target : MeetOrderCode Q rQ μQ)

noncomputable def toIdealEmbedding : IdealEmbedding source.toMeetOrder target.toMeetOrder where
  toMeetEmbedding := code.toMeetEmbeddingCode.toMeetEmbedding source target
  ideal v z lower := by
    obtain ⟨x, hx, _, entry⟩ := code.ideal v.val _ z.val
      (code.toMeetEmbeddingCode.toMeetEmbedding_entry source target v) z.property lower
    exact ⟨⟨x, hx⟩, (code.toMeetEmbeddingCode.toMeetEmbedding_eq_iff source target ⟨x,hx⟩ z).2 entry⟩

end PartitionPilot.Forcing.IdealEmbeddingCode

end

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Geometry_GroundRawRefinementDataIdentification
attribute [-instance] _root_.OAI.PartitionPilot.Forcing.GroundMainPrefix.withTopSmall
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI



namespace PartitionPilot.Forcing.TransitiveGround
open SetFormula
universe u
variable (M : TransitiveGround.{u})
variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
variable (unions : Realize M.sets SetFormula.union Fin.elim0)
variable (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)

noncomputable def definable_refinementIndexFieldGraph (j : Fin 6) :
    GroundDefinableFunction M (fun env : Fin 2 → ZFSet.{u} => refinementIndexFieldGraph (env 0) (env 1) j) where
  formula := exactSetFormula 0 (.conj (BoundedFormula.productElementFormula 0 2 3).toFormula
    (refinementIndexFieldFormula 0 2 j))
  closed := fun _ members => M.refinementIndexFieldGraph_mem pairing unions powers separation
    (members 0) (members 1) j
  correct := by
    intro env members z hz
    apply M.realize_exactSetFormula 0 _ (extend z env) hz
      (fun _ h => M.transitive (M.refinementIndexFieldGraph_mem pairing unions powers separation
        (members 0) (members 1) j) h)
    intro w hw
    have all : ∀ k, (extend w (extend z env)) k ∈ M.sets := Fin.cases hw (Fin.cases hz members)
    change (Realize M.sets (BoundedFormula.productElementFormula 0 2 3).toFormula _ ∧
      Realize M.sets (refinementIndexFieldFormula 0 2 j) _) ↔ _
    rw [BoundedFormula.realize_toFormula M _ _ all, BoundedFormula.truth_productElementFormula,
      M.realize_refinementIndexFieldFormula 0 2 j _ all]
    rw [refinementIndexFieldGraph, ZFSet.mem_sep]
    rfl

end PartitionPilot.Forcing.TransitiveGround




end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Geometry_GroundRawLayerPushforward
attribute [-instance] _root_.OAI.PartitionPilot.Forcing.GroundMainPrefix.withTopSmall
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PartitionPilot.Forcing
open SetFormula
universe u

noncomputable def mapFamilyDiagonal (I : ZFSet.{u}) : ZFSet.{u} :=
  pairedGraph I I I (identityFunctionGraph I) (identityFunctionGraph I)

namespace TransitiveGround
variable (M : TransitiveGround.{u})

noncomputable def mapFamilyPushforward (I U A B Maps e : ZFSet.{u}) : ZFSet.{u} :=
  relationCompose I (ZFSet.prod I I) (M.groundRelations U B) (mapFamilyDiagonal I)
    (M.groundPairCompositions (ZFSet.prod I I) I I U A B Maps (constantFamilyGraph I e))

end TransitiveGround

end PartitionPilot.Forcing

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Definability_LinkedMainInvariantCodes
attribute [-instance] _root_.OAI.PartitionPilot.Forcing.GroundMainPrefix.withTopSmall
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PartitionPilot.Forcing
open SetFormula
universe u

namespace SetFormula

def linkedMainInvariantFormula {n} (K Labels C D P G cutoff serial : Fin n) : SetFormula n :=
  .conj (groundBelowFormula P K) (.conj (groundBelowFormula G K)
    (.conj (groundBelowFormula Labels K) (.conj (cumulativeRankLtFormula P K)
      (.conj (cumulativeRankLtFormula G K) (.conj (cumulativeRankLtFormula Labels K)
        (.conj (.mem cutoff K) (.conj (cumulativeRankLtFormula C K)
          (.conj (cumulativeRankLtFormula D K) (cumulativeRankLtFormula serial K)))))))))
end SetFormula

end PartitionPilot.Forcing

end

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Geometry_GroundFiniteSeedBounds
attribute [-instance] _root_.OAI.PartitionPilot.Forcing.GroundMainPrefix.withTopSmall
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PartitionPilot.Forcing
open SetFormula
universe u

theorem natSetCode_identity_injection_omega (n : Nat) :
    InjectionCode (natSetCode n) ZFSet.omega (identityFunctionGraph (natSetCode n) : ZFSet.{u}) := by
  apply (identityFunctionGraph_injection (natSetCode n)).retarget
  intro x hx
  obtain ⟨k, _, rfl⟩ := (mem_natSetCode x n).1 hx
  exact natSetCode_mem_omega k

namespace TransitiveGround
variable (M : TransitiveGround.{u})

theorem natSetCode_countable
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (infinite : Realize M.sets infinity Fin.elim0) (n : Nat) :
    M.groundEmbeddable (natSetCode n) ZFSet.omega :=
  ⟨identityFunctionGraph (natSetCode n),
    M.identityFunctionGraph_mem pairing unions powers separation
      (M.natSetCode_mem separation infinite n), natSetCode_identity_injection_omega n⟩

end TransitiveGround

end PartitionPilot.Forcing

end

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Definability_InitialMainAlgebraCodes
attribute [-instance] _root_.OAI.PartitionPilot.Forcing.GroundMainPrefix.withTopSmall
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PartitionPilot.Forcing.InitialMainAlgebra
universe u

def identity : ZFSet.{u} := bottom
def order : ZFSet.{u} :=
  {ZFSet.pair bottom bottom, ZFSet.pair bottom top, ZFSet.pair top top}
def meetGraph : ZFSet.{u} :=
  {ZFSet.pair (ZFSet.pair bottom bottom) bottom,
    ZFSet.pair (ZFSet.pair bottom top) bottom,
    ZFSet.pair (ZFSet.pair top bottom) bottom,
    ZFSet.pair (ZFSet.pair top top) top}
def multiplication : ZFSet.{u} := {ZFSet.pair (ZFSet.pair identity identity) identity}
def inverse : ZFSet.{u} := {ZFSet.pair identity identity}
def action : ZFSet.{u} :=
  {ZFSet.pair (ZFSet.pair identity bottom) bottom, ZFSet.pair (ZFSet.pair identity top) top}

theorem bottom_ne_top : (bottom : ZFSet.{u}) ≠ top := by
  intro equal
  have := natSetCode_injective equal
  exact Nat.zero_ne_one this

theorem mem_carrier (x : ZFSet.{u}) : x ∈ carrier ↔ x = bottom ∨ x = top := by
  change x ∈ insert (natSetCode 1) (insert (natSetCode 0) ∅) ↔ _
  simp only [ZFSet.mem_insert_iff, ZFSet.notMem_empty, or_false]
  exact or_comm

theorem mem_actors (x : ZFSet.{u}) : x ∈ actors ↔ x = identity := by
  change x ∈ insert (natSetCode 0) ∅ ↔ _
  simp only [ZFSet.mem_insert_iff, ZFSet.notMem_empty, or_false]
  rfl

theorem bottom_mem : (bottom : ZFSet.{u}) ∈ carrier := (mem_carrier _).2 (Or.inl rfl)
theorem top_mem : (top : ZFSet.{u}) ∈ carrier := (mem_carrier _).2 (Or.inr rfl)
theorem identity_mem : (identity : ZFSet.{u}) ∈ actors := (mem_actors _).2 rfl

theorem pair_mem_order (x y : ZFSet.{u}) : ZFSet.pair x y ∈ order ↔
    (x = bottom ∧ y = bottom) ∨ (x = bottom ∧ y = top) ∨ (x = top ∧ y = top) := by
  simp only [order, ZFSet.mem_insert_iff, ZFSet.mem_singleton, ZFSet.pair_inj]

theorem pair_mem_meetGraph (x y z : ZFSet.{u}) : ZFSet.pair (ZFSet.pair x y) z ∈ meetGraph ↔
    ((x = bottom ∧ y = bottom) ∧ z = bottom) ∨
      ((x = bottom ∧ y = top) ∧ z = bottom) ∨
        ((x = top ∧ y = bottom) ∧ z = bottom) ∨ ((x = top ∧ y = top) ∧ z = top) := by
  simp only [meetGraph, ZFSet.mem_insert_iff, ZFSet.mem_singleton, ZFSet.pair_inj]

theorem pair_mem_multiplication (x y z : ZFSet.{u}) :
    ZFSet.pair (ZFSet.pair x y) z ∈ multiplication ↔ (x = identity ∧ y = identity) ∧ z = identity := by
  simp only [multiplication, ZFSet.mem_singleton, ZFSet.pair_inj]

theorem pair_mem_inverse (x y : ZFSet.{u}) : ZFSet.pair x y ∈ inverse ↔ x = identity ∧ y = identity := by
  simp only [inverse, ZFSet.mem_singleton, ZFSet.pair_inj]

theorem pair_mem_action (g x y : ZFSet.{u}) : ZFSet.pair (ZFSet.pair g x) y ∈ action ↔
    ((g = identity ∧ x = bottom) ∧ y = bottom) ∨ ((g = identity ∧ x = top) ∧ y = top) := by
  simp only [action, ZFSet.mem_pair, ZFSet.pair_inj]

theorem least (x : ZFSet.{u}) (hx : x ∈ carrier) : ZFSet.pair bottom x ∈ order := by
  rcases (mem_carrier x).1 hx with rfl | rfl <;> simp [pair_mem_order]

theorem greatest (x : ZFSet.{u}) (hx : x ∈ carrier) : ZFSet.pair x top ∈ order := by
  rcases (mem_carrier x).1 hx with rfl | rfl <;> simp [pair_mem_order]

theorem meet_function : ZFSet.IsFunc (ZFSet.prod carrier carrier) carrier (meetGraph : ZFSet.{u}) := by
  constructor
  · intro z hz
    simp only [meetGraph, ZFSet.mem_insert_iff, ZFSet.mem_singleton] at hz
    rcases hz with rfl | rfl | rfl | rfl
    · exact ZFSet.pair_mem_prod.2 ⟨ZFSet.pair_mem_prod.2 ⟨bottom_mem, bottom_mem⟩, bottom_mem⟩
    · exact ZFSet.pair_mem_prod.2 ⟨ZFSet.pair_mem_prod.2 ⟨bottom_mem, top_mem⟩, bottom_mem⟩
    · exact ZFSet.pair_mem_prod.2 ⟨ZFSet.pair_mem_prod.2 ⟨top_mem, bottom_mem⟩, bottom_mem⟩
    · exact ZFSet.pair_mem_prod.2 ⟨ZFSet.pair_mem_prod.2 ⟨top_mem, top_mem⟩, top_mem⟩
  · intro z hz
    obtain ⟨x, hx, y, hy, rfl⟩ := ZFSet.mem_prod.1 hz
    rcases (mem_carrier x).1 hx with rfl | rfl <;>
      rcases (mem_carrier y).1 hy with rfl | rfl <;>
        simp [pair_mem_meetGraph, bottom_ne_top, Ne.symm bottom_ne_top]

theorem meet_code : MeetOrderCode carrier order (meetGraph : ZFSet.{u}) where
  order := {
    relation := by
      intro z hz
      simp only [order, ZFSet.mem_insert_iff, ZFSet.mem_singleton] at hz
      rcases hz with rfl | rfl | rfl <;> simp [mem_carrier]
    refl := by
      intro x hx
      rcases (mem_carrier x).1 hx with rfl | rfl <;> simp [pair_mem_order]
    antisymm := by
      intro x hx y hy xy yx
      rcases (mem_carrier x).1 hx with rfl | rfl <;>
        rcases (mem_carrier y).1 hy with rfl | rfl <;>
          simp_all [pair_mem_order, bottom_ne_top, Ne.symm bottom_ne_top]
    trans := by
      intro x hx y hy z hz xy yz
      rcases (mem_carrier x).1 hx with rfl | rfl <;>
        rcases (mem_carrier y).1 hy with rfl | rfl <;>
          rcases (mem_carrier z).1 hz with rfl | rfl <;>
            simp_all [pair_mem_order, bottom_ne_top, Ne.symm bottom_ne_top] }
  operation := meet_function
  lower_left := by
    intro x y z entry
    rcases (pair_mem_meetGraph x y z).1 entry with
      ⟨⟨rfl, rfl⟩, rfl⟩ | ⟨⟨rfl, rfl⟩, rfl⟩ | ⟨⟨rfl, rfl⟩, rfl⟩ | ⟨⟨rfl, rfl⟩, rfl⟩ <;>
        simp [pair_mem_order]
  lower_right := by
    intro x y z entry
    rcases (pair_mem_meetGraph x y z).1 entry with
      ⟨⟨rfl, rfl⟩, rfl⟩ | ⟨⟨rfl, rfl⟩, rfl⟩ | ⟨⟨rfl, rfl⟩, rfl⟩ | ⟨⟨rfl, rfl⟩, rfl⟩ <;>
        simp [pair_mem_order]
  greatest := by
    intro x y z w hw entry wx wy
    rcases (pair_mem_meetGraph x y z).1 entry with
      ⟨⟨rfl, rfl⟩, rfl⟩ | ⟨⟨rfl, rfl⟩, rfl⟩ | ⟨⟨rfl, rfl⟩, rfl⟩ | ⟨⟨rfl, rfl⟩, rfl⟩ <;>
        rcases (mem_carrier w).1 hw with rfl | rfl <;>
          simp_all [pair_mem_order, bottom_ne_top, Ne.symm bottom_ne_top]

theorem group_code : GroupCode actors multiplication inverse (identity : ZFSet.{u}) where
  mul_function := by
    constructor
    · intro z hz
      rw [multiplication, ZFSet.mem_singleton] at hz
      rw [hz]
      simp [mem_actors]
    · intro z hz
      obtain ⟨x, hx, y, hy, rfl⟩ := ZFSet.mem_prod.1 hz
      obtain rfl := (mem_actors x).1 hx
      obtain rfl := (mem_actors y).1 hy
      simp [pair_mem_multiplication]
  inv_function := by
    constructor
    · intro z hz
      rw [inverse, ZFSet.mem_singleton] at hz
      rw [hz]
      simp [mem_actors]
    · intro x hx
      obtain rfl := (mem_actors x).1 hx
      simp [pair_mem_inverse]
  identity_mem := identity_mem
  one_mul := by
    intro x hx
    obtain rfl := (mem_actors x).1 hx
    simp [pair_mem_multiplication]
  mul_one := by
    intro x hx
    obtain rfl := (mem_actors x).1 hx
    simp [pair_mem_multiplication]
  inv_mul := by
    intro x hx y hy entry
    obtain rfl := (mem_actors x).1 hx
    obtain rfl := (mem_actors y).1 hy
    simp [pair_mem_multiplication]
  mul_assoc := by
    intro x hx y hy z hz a ha b hb c hc xy yz az
    obtain rfl := (mem_actors x).1 hx
    obtain rfl := (mem_actors y).1 hy
    obtain rfl := (mem_actors z).1 hz
    obtain rfl := (mem_actors a).1 ha
    obtain rfl := (mem_actors b).1 hb
    obtain rfl := (mem_actors c).1 hc
    simp [pair_mem_multiplication]

theorem action_code : PosetActionCode actors carrier multiplication identity order (action : ZFSet.{u}) where
  function := by
    constructor
    · intro z hz
      simp only [action, ZFSet.mem_pair] at hz
      rcases hz with rfl | rfl <;> simp [mem_actors, mem_carrier]
    · intro z hz
      obtain ⟨g, hg, x, hx, rfl⟩ := ZFSet.mem_prod.1 hz
      obtain rfl := (mem_actors g).1 hg
      rcases (mem_carrier x).1 hx with rfl | rfl <;>
        simp [pair_mem_action, bottom_ne_top, Ne.symm bottom_ne_top]
  one := by
    intro x hx
    rcases (mem_carrier x).1 hx with rfl | rfl <;> simp [pair_mem_action]
  mul := by
    intro g hg h hh k hk x hx y hy z hz gh hxY gyZ
    obtain rfl := (mem_actors g).1 hg
    obtain rfl := (mem_actors h).1 hh
    obtain rfl := (mem_actors k).1 hk
    rcases (pair_mem_action identity x y).1 hxY with ⟨⟨_, rfl⟩, rfl⟩ | ⟨⟨_, rfl⟩, rfl⟩ <;>
      simpa only using gyZ
  monotone := by
    intro g hg x hx y hy z hz w hw gxZ gyW xy
    rcases (pair_mem_action g x z).1 gxZ with ⟨⟨rfl, rfl⟩, rfl⟩ | ⟨⟨rfl, rfl⟩, rfl⟩ <;>
      rcases (pair_mem_action identity y w).1 gyW with ⟨⟨_, rfl⟩, rfl⟩ | ⟨⟨_, rfl⟩, rfl⟩ <;>
        exact xy

end PartitionPilot.Forcing.InitialMainAlgebra

end

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Geometry_GroundInitialMainAlgebra
attribute [-instance] _root_.OAI.PartitionPilot.Forcing.GroundMainPrefix.withTopSmall
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PartitionPilot.Forcing.TransitiveGround
open SetFormula InitialMainAlgebra
universe u
variable (M : TransitiveGround.{u})

theorem initialMainAlgebra_ground
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (separation : SeparationSchema M.sets) (infinite : Realize M.sets infinity Fin.elim0) :
    carrier ∈ M.sets ∧ actors ∈ M.sets ∧ order ∈ M.sets ∧ meetGraph ∈ M.sets ∧
      multiplication ∈ M.sets ∧ inverse ∈ M.sets ∧ action ∈ M.sets := by
  have h0 := M.natSetCode_mem separation infinite 0
  have h1 := M.natSetCode_mem separation infinite 1
  have h2 := M.natSetCode_mem separation infinite 2
  have p00 := M.orderedPair_mem pairing h0 h0
  have p01 := M.orderedPair_mem pairing h0 h1
  have p10 := M.orderedPair_mem pairing h1 h0
  have p11 := M.orderedPair_mem pairing h1 h1
  have m000 := M.orderedPair_mem pairing p00 h0
  have m010 := M.orderedPair_mem pairing p01 h0
  have m100 := M.orderedPair_mem pairing p10 h0
  have m111 := M.orderedPair_mem pairing p11 h1
  have a011 := M.orderedPair_mem pairing p01 h1
  refine ⟨h2, h1, ?_, ?_, ?_, ?_, ?_⟩
  · exact M.insert_mem pairing unions p00 (M.unorderedPair_mem pairing p01 p11)
  · exact M.insert_mem pairing unions m000
      (M.insert_mem pairing unions m010 (M.unorderedPair_mem pairing m100 m111))
  · simpa only [multiplication, identity, bottom, ZFSet.pair_eq_singleton] using
      M.unorderedPair_mem pairing m000 m000
  · simpa only [inverse, identity, bottom, ZFSet.pair_eq_singleton] using
      M.unorderedPair_mem pairing p00 p00
  · exact M.unorderedPair_mem pairing m000 a011

end PartitionPilot.Forcing.TransitiveGround

end

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Geometry_GroundTwoPointHeights
attribute [-instance] _root_.OAI.PartitionPilot.Forcing.GroundMainPrefix.withTopSmall
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PartitionPilot.Forcing
open SetFormula
universe u

namespace TransitiveGround
variable (M : TransitiveGround.{u})

theorem unorderedPair_countable
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (infinite : Realize M.sets infinity Fin.elim0)
    {a b : ZFSet.{u}} (ha : a ∈ M.sets) (hb : b ∈ M.sets) :
    M.groundEmbeddable ({a, b} : ZFSet.{u}) ZFSet.omega := by
  have nonempty : M.sets.Nonempty := ⟨a, ha⟩
  have zero := M.empty_mem nonempty
  have single := M.groundEmbeddable_insert pairing unions powers separation infinite zero hb
    (M.empty_groundEmbeddable ZFSet.omega nonempty)
  exact M.groundEmbeddable_insert pairing unions powers separation infinite
    (M.insert_mem pairing unions hb zero) ha single

theorem twoPointHeight_range_countable
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (infinite : Realize M.sets infinity Fin.elim0)
    {a b c d0 d1 C D : ZFSet.{u}} (hC : C ∈ M.sets) (hD : D ∈ M.sets)
    (hc : c ∈ C) (h0 : d0 ∈ D) (h1 : d1 ∈ D) :
    M.groundEmbeddable (relationImage {a, b} (ZFSet.prod C D)
      (twoPointHeight a b c d0 d1)) ZFSet.omega := by
  rw [twoPointHeight_image hc h0 h1]
  exact M.unorderedPair_countable pairing unions powers separation infinite
    (M.orderedPair_mem pairing (M.transitive hC hc) (M.transitive hD h0))
    (M.orderedPair_mem pairing (M.transitive hC hc) (M.transitive hD h1))

end TransitiveGround

end PartitionPilot.Forcing

end

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Transfinite_GroundInitialMainStage
attribute [-instance] _root_.OAI.PartitionPilot.Forcing.GroundMainPrefix.withTopSmall
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PartitionPilot.Forcing

section
open SetFormula
universe u

theorem InitialMainAlgebra.carrier_eq_pair :
    (InitialMainAlgebra.carrier : ZFSet.{u}) =
      {InitialMainAlgebra.bottom, InitialMainAlgebra.top} := by
  apply ZFSet.ext
  intro x
  rw [InitialMainAlgebra.mem_carrier, ZFSet.mem_pair]

end

end PartitionPilot.Forcing

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Transfinite_GroundMainStageCandidates
attribute [-instance] _root_.OAI.PartitionPilot.Forcing.GroundMainPrefix.withTopSmall
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PartitionPilot.Forcing
open SetFormula
universe u

namespace SetFormula

def mainStageValidityFormula {n}
    (P r μ G m inv one A b t height C D rD N : Fin n) : SetFormula n :=
  let lift (i : Fin n) := i.succ.succ.succ
  ex (ex (ex ((BoundedFormula.mainStageWitnessFormula
    (lift P) (lift r) (lift μ) (lift G) (lift m) (lift inv) (lift one)
    (lift A) (lift b) (lift t) (lift height) (lift C) (lift D) (lift rD)
    2 1 (lift N) 0).toFormula)))

def validMainStageCodeFormula {n}
    (z P r μ G m inv one A b t height C D rD N : Fin n) : SetFormula n :=
  .conj (BoundedFormula.mainStageFormula z P r μ G m inv one A b t height).toFormula
    (mainStageValidityFormula P r μ G m inv one A b t height C D rD N)

end SetFormula

namespace GroundMainStage
variable {M : TransitiveGround.{u}}

noncomputable def ofValidity
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    {P r μ G m inv one A b t height C D rD : ZFSet.{u}}
    (hP : P ∈ M.sets) (hr : r ∈ M.sets) (hμ : μ ∈ M.sets) (hG : G ∈ M.sets)
    (hm : m ∈ M.sets) (hInv : inv ∈ M.sets) (hA : A ∈ M.sets) (hHeight : height ∈ M.sets)
    (hC : C ∈ M.sets) (hD : D ∈ M.sets) (hrD : rD ∈ M.sets)
    (valid : MainStageValidity M P r μ G m inv one A b t height C D rD) :
    GroundMainStage M C D rD :=
  ofCodes pairing unions powers separation hP hG hr hμ hA hm hInv hC hD hrD hHeight
    valid.1.meet valid.1.group valid.1.action valid.1.bottom_mem valid.1.least
    valid.1.top_mem valid.1.greatest valid.1.height_code valid.2

end GroundMainStage

end PartitionPilot.Forcing

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Geometry_GroundGrowthLayerRecognition
attribute [-instance] _root_.OAI.PartitionPilot.Forcing.GroundMainPrefix.withTopSmall
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open scoped ZFSet

section

namespace PartitionPilot.Forcing
open SetFormula
universe u

namespace SetFormula

def separatedGrowthWitnessFormula {n} (z Qs rs μs L r μ birth t : Fin n) : SetFormula n :=
  let old := suffixIndex n 10
  let field := prefixIndex n 10
  exBlock 10 (BoundedFormula.separatedTaggedLayerFormula (old z)
    (field 0) (field 1) (field 2) (field 3) (field 4) (field 5) (field 6)
    (old Qs) (old rs) (old μs) (old L) (old r) (old μ) (old birth) (old t)
    (field 7) (field 8) (field 9)).toFormula

def growthLayerWitnessFormula {n} (z Qs rs μs L r μ birth t N : Fin n) : SetFormula n :=
  disj (countableGrowthWitnessFormula z L birth t N)
    (disj (copyGrowthWitnessFormula z Qs rs μs L r μ birth t N)
      (separatedGrowthWitnessFormula z Qs rs μs L r μ birth t))
end SetFormula

end PartitionPilot.Forcing

end

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Definability_SerializedChronologyFormulas
attribute [-instance] _root_.OAI.PartitionPilot.Forcing.GroundMainPrefix.withTopSmall
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PartitionPilot.Forcing
open SetFormula
universe u

namespace SetFormula
def chronologyLayerClause {n} (T N : Fin n) (graphs : Fin 5 → Fin n)
    (layers s t L r μ birth z : Fin n) : SetFormula n :=
  imp (BoundedFormula.chronologyLayerLookupFormula T graphs layers s t L r μ birth z).toFormula
    (growthLayerWitnessFormula z (graphs 0) (graphs 1) (graphs 2) L r μ birth t N)

def chronologyLayerEntriesFormula {n} (T N : Fin n) (graphs : Fin 5 → Fin n)
    (layers : Fin n) : SetFormula n :=
  let old := suffixIndex n 7
  let field := prefixIndex n 7
  allBlock 7 (chronologyLayerClause (old T) (old N) (fun j => old (graphs j))
    (old layers) (field 0) (field 1) (field 2) (field 3) (field 4) (field 5) (field 6))
end SetFormula

namespace SetFormula

def serializedChronologyFormula {n} (T V C D rD N : Fin n)
    (graphs : Fin 5 → Fin n) (W layers : Fin n) : SetFormula n :=
  .conj (BoundedFormula.ordinalFormula T).toFormula
    (.conj (BoundedFormula.chronologyCoreFormula T V C D rD graphs).toFormula
      (.conj (chronologyLayerFunctionFormula T W layers)
        (chronologyLayerEntriesFormula T N graphs layers)))
end SetFormula

end PartitionPilot.Forcing

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Transfinite_GroundLinkedMainStageCodeLaws
attribute [-instance] _root_.OAI.PartitionPilot.Forcing.GroundMainPrefix.withTopSmall
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PartitionPilot.Forcing

section
open SetFormula
universe u v

namespace SetFormula
def serializedChronologyCandidateFormula {n} (z C D rD N : Fin n) : SetFormula n :=
  let old := suffixIndex n 10
  let field := prefixIndex n 10
  let graphs := chronologyCandidateGraphs field
  exBlock 10 (.conj
    (BoundedFormula.serializedChronologyTupleFormula (old z) (field 9) (field 0) (field 1)
      graphs (field 7) (field 8)).toFormula
    (serializedChronologyFormula (field 0) (field 1) (old C) (old D) (old rD) (old N)
      graphs (field 7) (field 8)))
end SetFormula

namespace SetFormula

def linkedMainStageRawFormula {n} (K Labels C D rD N z : Fin n) (f : Fin 24 → Fin n) : SetFormula n :=
  .conj (BoundedFormula.linkedMainStageTupleFormula z (f 22) (f 11) (f 23)).toFormula
    (.conj (validMainStageCodeFormula (f 22) (f 0) (f 1) (f 2) (f 3) (f 4) (f 5) (f 6)
      (f 7) (f 8) (f 9) (f 10) C D rD N)
    (.conj (BoundedFormula.serializedChronologyTupleFormula (f 23) (f 21) (f 12) (f 13)
      (linkedChronologyGraphs f) (f 19) (f 20)).toFormula
    (.conj (serializedChronologyFormula (f 12) (f 13) C D rD N (linkedChronologyGraphs f) (f 19) (f 20))
    (.conj (BoundedFormula.linkedTerminalFormula (f 11) (f 12) (f 0) (f 1) (f 2) (f 10)
      (linkedChronologyGraphs f)).toFormula
      (linkedMainInvariantFormula K Labels C D (f 0) (f 3) (f 11) (f 23))))))
end SetFormula

end

end PartitionPilot.Forcing

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Definability_LinkedMainTransitionRawCodes
attribute [-instance] _root_.OAI.PartitionPilot.Forcing.GroundMainPrefix.withTopSmall
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section



namespace PartitionPilot.Forcing
open SetFormula
universe u

namespace SetFormula

def linkedMainTransitionRawFormula {n}
    (K Labels C D rD N sourceCode targetCode z points actors sourceBirth targetBirth : Fin n)
    (source target : Fin 24 → Fin n) : SetFormula n :=
  .conj (linkedMainStageRawFormula K Labels C D rD N sourceCode source)
    (.conj (linkedMainStageRawFormula K Labels C D rD N targetCode target)
      (BoundedFormula.linkedTransitionLawsFormula z points actors sourceBirth targetBirth source target).toFormula)

end SetFormula

end PartitionPilot.Forcing

end

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Geometry_GroundLinkedTransitionRetarget
attribute [-instance] _root_.OAI.PartitionPilot.Forcing.GroundMainPrefix.withTopSmall
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PartitionPilot.Forcing

section
open SetFormula
universe u

namespace SetFormula

def linkedMainTransitionFormula {n} (K Labels C D rD N sourceCode targetCode z : Fin n) : SetFormula n :=
  let old := suffixIndex n 52
  let fresh := prefixIndex n 52
  exBlock 52 (linkedMainTransitionRawFormula (old K) (old Labels) (old C) (old D) (old rD) (old N)
    (old sourceCode) (old targetCode) (old z) (fresh 48) (fresh 49) (fresh 50) (fresh 51)
    (fun j => fresh (j.castAdd 28)) (fun j => fresh (Fin.natAdd 24 (j.castAdd 4))))

end SetFormula

end

universe u

end PartitionPilot.Forcing

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Transfinite_GroundMainPrefixDecoding
attribute [-instance] _root_.OAI.PartitionPilot.Forcing.GroundMainPrefix.withTopSmall
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PartitionPilot.Forcing

namespace MainPrefixGraphCode
open SetRealization
universe u
variable {M : TransitiveGround.{u}} {K Labels C D rD T S E : ZFSet.{u}}

noncomputable def decodedTransitionIndex (i j : SetMembers T)
    (before : SetMembers.raw i = SetMembers.raw j ∨ SetMembers.raw i ∈ SetMembers.raw j) :
    {q : ZFSet.{u} // q ∈ chronologyPairs T} :=
  ⟨ZFSet.pair (SetMembers.raw j) (SetMembers.raw i),
    (pair_mem_chronologyPairs T _ _).2 ⟨SetMembers.raw_mem j, SetMembers.raw_mem i, before⟩⟩

end MainPrefixGraphCode

end PartitionPilot.Forcing

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Definability_PreparedCertificateCodes
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section



namespace PartitionPilot.Forcing
open SetFormula
universe u

namespace SetFormula

def preparedCertificateFormula {n}
    (P order q nodes nodeOrder meet N visibility top omega z F B f e names : Fin n) : SetFormula n :=
  .conj (BoundedFormula.meetFilterFormula nodes nodeOrder meet F).toFormula
    (.conj (BoundedFormula.coinitialBelowFormula nodeOrder F F B).toFormula
      (.conj (BoundedFormula.exMem B (.equal 0 0)).toFormula
        (.conj (BoundedFormula.synchronizedEnumerationFormula omega N B f e names).toFormula
          (.conj (allGraphFields f
            (BoundedFormula.visibilitySupportAt 1 0 nodes.succ.succ N.succ.succ
              visibility.succ.succ top.succ.succ).toFormula)
            (preparationForcingFormula P order q nodes visibility z F f)))))

end SetFormula

end PartitionPilot.Forcing

end

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Forcing_GroundRawRefinementStageWitnesses
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


section

namespace PartitionPilot.SetRealization.Presentation
open Forcing
universe u
variable {P : Type u} [PartialOrder P] (s : Presentation P)

theorem conditionOrder_code : PartialOrderCode s.carrier s.conditionOrder := by
  refine ⟨(s.product s).subset_carrier _, ?_, ?_, ?_⟩
  · intro x hx
    obtain ⟨x, rfl⟩ := (s.mem_carrier x).1 hx
    exact (s.pair_mem_conditionOrder x x).2 le_rfl
  · intro x hx y hy xy yx
    obtain ⟨x, rfl⟩ := (s.mem_carrier x).1 hx
    obtain ⟨y, rfl⟩ := (s.mem_carrier y).1 hy
    exact congrArg s.encode (le_antisymm ((s.pair_mem_conditionOrder x y).1 xy)
      ((s.pair_mem_conditionOrder y x).1 yx))
  · intro x hx y hy z hz xy yz
    obtain ⟨x, rfl⟩ := (s.mem_carrier x).1 hx
    obtain ⟨y, rfl⟩ := (s.mem_carrier y).1 hy
    obtain ⟨z, rfl⟩ := (s.mem_carrier z).1 hz
    exact (s.pair_mem_conditionOrder x z).2 (le_trans
      ((s.pair_mem_conditionOrder x y).1 xy) ((s.pair_mem_conditionOrder y z).1 yz))

end PartitionPilot.SetRealization.Presentation

namespace PartitionPilot.Forcing.PosetAction
open SetRealization
universe u
variable {G P : Type u} [Group G] [PartialOrder P]
variable (a : PosetAction G P) (s : Presentation P) (t : Presentation G)

theorem actionGraph_code : PosetActionCode t.carrier s.carrier
    ((t.product t).graph t (fun gh => gh.1 * gh.2)) (t.encode 1)
    s.conditionOrder (a.actionGraph s t) := by
  refine ⟨(t.product s).graph_isFunc s _, ?_, ?_, ?_⟩
  · intro x hx
    obtain ⟨x, rfl⟩ := (s.mem_carrier x).1 hx
    exact (a.triple_mem_actionGraph s t 1 x x).2 (a.one x)
  · intro g hg h hh k hk x hx y hy z hz gh xy yz
    obtain ⟨g, rfl⟩ := (t.mem_carrier g).1 hg
    obtain ⟨h, rfl⟩ := (t.mem_carrier h).1 hh
    obtain ⟨k, rfl⟩ := (t.mem_carrier k).1 hk
    obtain ⟨x, rfl⟩ := (s.mem_carrier x).1 hx
    obtain ⟨y, rfl⟩ := (s.mem_carrier y).1 hy
    obtain ⟨z, rfl⟩ := (s.mem_carrier z).1 hz
    have product := ((t.product t).pair_mem_graph t _ (g, h) k).1 gh
    have first := (a.triple_mem_actionGraph s t h x y).1 xy
    have second := (a.triple_mem_actionGraph s t g y z).1 yz
    apply (a.triple_mem_actionGraph s t k x z).2
    rw [← product, a.mul, first, second]
  · intro g hg x hx y hy z hz w hw xz yw xy
    obtain ⟨g, rfl⟩ := (t.mem_carrier g).1 hg
    obtain ⟨x, rfl⟩ := (s.mem_carrier x).1 hx
    obtain ⟨y, rfl⟩ := (s.mem_carrier y).1 hy
    obtain ⟨z, rfl⟩ := (s.mem_carrier z).1 hz
    obtain ⟨w, rfl⟩ := (s.mem_carrier w).1 hw
    have first := (a.triple_mem_actionGraph s t g x z).1 xz
    have second := (a.triple_mem_actionGraph s t g y w).1 yw
    apply (s.pair_mem_conditionOrder z w).2
    rw [← first, ← second]
    exact (a.iso g).monotone ((s.pair_mem_conditionOrder x y).1 xy)

end PartitionPilot.Forcing.PosetAction

end


end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Transfinite_GroundStructuralHistoryTestUnions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open scoped ZFSet



namespace PartitionPilot.Forcing
universe u

structure RefinementDataHistory (stages history T : ZFSet.{u}) : Prop where
  function : FunctionGraphOn stages history
  decoded : ∀ alpha data, ZFSet.pair alpha data ∈ history →
    ∃ d : Fin 15 → ZFSet.{u}, data = refinementFormulaDataCode d
  terms : ∀ alpha (d : Fin 15 → ZFSet.{u}),
    ZFSet.pair alpha (refinementFormulaDataCode d) ∈ history → d 6 = T
  literal : ∀ alpha (d : Fin 15 → ZFSet.{u}),
    ZFSet.pair alpha (refinementFormulaDataCode d) ∈ history → RefinementIndexLevelCode (d 0) alpha

noncomputable def refinementDataHistoryLevels (stages history T : ZFSet.{u}) : ZFSet.{u} :=
  refinementHistoryAssignmentLevels stages (refinementDataHistoryField stages history 0) T

namespace RefinementDataHistory
variable {stages history T : ZFSet.{u}} (valid : RefinementDataHistory stages history T)
include valid

theorem index_function : FunctionGraphOn stages (refinementDataHistoryField stages history 0) :=
  refinementDataHistoryField_function valid.function valid.decoded 0

theorem index_literal : ∀ alpha I, ZFSet.pair alpha I ∈ refinementDataHistoryField stages history 0 →
    RefinementIndexLevelCode I alpha :=
  refinementDataHistoryField_index_levels valid.literal

theorem levels_function :
    ZFSet.IsFunc (stageOneAssignments (refinementDataHistoryIndices stages history) T) stages
      (refinementDataHistoryLevels stages history T) :=
  refinementHistoryAssignmentLevels_function valid.index_literal

theorem coverage : ForcingHistoryLevelCoverage stages history (refinementDataHistoryLevels stages history T) := by
  intro beta _ d entry t ht u hu w hw
  apply (refinementHistoryAssignmentLevels_entry valid.index_function valid.index_literal T t u w beta).2
  have same := valid.terms beta d entry
  exact ⟨d 0, (refinementDataHistoryField_entry valid.function d entry 0 _).2 rfl,
    ht, same ▸ hu, same ▸ hw⟩

end RefinementDataHistory




namespace RefinementDataHistory
variable {stages history T : ZFSet.{u}} (valid : RefinementDataHistory stages history T)
include valid

theorem restrict {earlier : ZFSet.{u}} (subset : earlier ⊆ stages) :
    RefinementDataHistory earlier (graphRestriction earlier history) T := by
  refine ⟨valid.function.restrict subset, ?_, ?_, ?_⟩
  · intro alpha data entry
    exact valid.decoded alpha data (pair_mem_graphRestriction.1 entry).1
  · intro alpha d entry
    exact valid.terms alpha d (pair_mem_graphRestriction.1 entry).1
  · intro alpha d entry
    exact valid.literal alpha d (pair_mem_graphRestriction.1 entry).1

theorem prefix_cut {alpha beta : ZFSet.{u}} (subset : alpha ⊆ stages) (below : beta ⊆ alpha)
    (A : ZFSet.{u}) :
    assignmentCut (refinementDataHistoryLevels alpha (graphRestriction alpha history) T) beta A =
      assignmentCut (refinementDataHistoryLevels stages history T) beta A :=
  refinementDataHistoryAssignmentCut_prefix valid.function valid.decoded valid.literal subset below T A

end RefinementDataHistory
end PartitionPilot.Forcing



namespace PartitionPilot.Forcing.RefinementDataHistory
universe u
variable {stages history T : ZFSet.{u}} (valid : RefinementDataHistory stages history T)
variable {beta : ZFSet.{u}} {d : Fin 15 → ZFSet.{u}}
variable (entry : ZFSet.pair beta (refinementFormulaDataCode d) ∈ history)
include valid entry

theorem assignment_level_iff (t : ZFSet.{u}) (ht : t ∈ d 0)
    (u : ZFSet.{u}) (hu : u ∈ d 6) (w : ZFSet.{u}) (hw : w ∈ d 6) (xi : ZFSet.{u}) :
    ZFSet.pair (stageOneAssignment t u w) xi ∈ refinementDataHistoryLevels stages history T ↔
      xi = beta := by
  have actual := valid.coverage beta (valid.function.pair_source entry) d entry t ht u hu w hw
  have source := (ZFSet.pair_mem_prod.1 (valid.levels_function.1 actual)).1
  obtain ⟨value, _, unique⟩ := valid.levels_function.2 _ source
  exact ⟨fun member => (unique xi member).trans (unique beta actual).symm,
    fun equal => equal.symm ▸ actual⟩

end PartitionPilot.Forcing.RefinementDataHistory



end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Definability_RefinementDataHistoryEntryFormulas
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PartitionPilot.Forcing
open SetFormula
universe u

theorem pair_mem_refinementDataHistoryLevels (stages history T assignment xi : ZFSet.{u}) :
    ZFSet.pair assignment xi ∈ refinementDataHistoryLevels stages history T ↔
      ∃ i ∈ refinementDataHistoryIndices stages history, ∃ u ∈ T, ∃ w ∈ T,
        assignment = stageOneAssignment i u w ∧ xi ∈ stages ∧
          ∃ fields : Fin 6 → ZFSet.{u}, i = nonemptyTupleCode 5 fields ∧ xi = fields 0 := by
  change ZFSet.pair assignment xi ∈ assignmentIndexLevels
    (refinementDataHistoryIndices stages history) T stages
    (refinementIndexFieldGraph (refinementDataHistoryIndices stages history) stages 0) ↔ _
  rw [pair_mem_assignmentIndexLevels]
  constructor
  · rintro ⟨i, hi, u, hu, w, hw, equal, hxi, entry⟩
    exact ⟨i, hi, u, hu, w, hw, equal, hxi,
      ((pair_mem_refinementIndexFieldGraph _ _ _ _ _).1 entry).2.2⟩
  · rintro ⟨i, hi, u, hu, w, hw, equal, hxi, fields⟩
    exact ⟨i, hi, u, hu, w, hw, equal, hxi,
      (pair_mem_refinementIndexFieldGraph _ _ _ _ _).2 ⟨hi, hxi, fields⟩⟩

end PartitionPilot.Forcing

end

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Transfinite_RefinementBirthEnumerationFairness
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PartitionPilot.Forcing

section
universe u

theorem refinementDataHistoryIndices_subset {stages alpha history : ZFSet.{u}}
    (subset : alpha ⊆ stages) :
    refinementDataHistoryIndices alpha (graphRestriction alpha history) ⊆
      refinementDataHistoryIndices stages history := by
  change refinementHistoryIndices alpha
    (refinementDataHistoryField alpha (graphRestriction alpha history) 0) ⊆ _
  rw [refinementDataHistoryIndices_prefix subset (fun _ h => h)]
  exact refinementHistoryIndices_mono subset

theorem refinementDataHistoryAssignments_subset {stages alpha history : ZFSet.{u}}
    (subset : alpha ⊆ stages) (T : ZFSet.{u}) :
    stageOneAssignments (refinementDataHistoryIndices alpha (graphRestriction alpha history)) T ⊆
      stageOneAssignments (refinementDataHistoryIndices stages history) T := by
  intro z member
  obtain ⟨t, ht, u, hu, w, hw, rfl⟩ := (mem_stageOneAssignments _ _ z).1 member
  exact (mem_stageOneAssignments _ _ _).2
    ⟨t, refinementDataHistoryIndices_subset subset ht, u, hu, w, hw, rfl⟩

theorem RefinementDataHistory.prefix_assignments_cut {stages history T alpha A : ZFSet.{u}}
    (valid : RefinementDataHistory stages history T) (subset : alpha ⊆ stages)
    (data : A ⊆ stageOneAssignments (refinementDataHistoryIndices alpha (graphRestriction alpha history)) T) :
    assignmentCut (refinementDataHistoryLevels stages history T) alpha A = A := by
  rw [← valid.prefix_cut subset (fun _ h => h) A]
  exact assignmentCut_full (valid.restrict subset).levels_function data

end

end PartitionPilot.Forcing

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Transfinite_GroundDefinableRefinementHistories
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PartitionPilot.Forcing
open SetFormula
universe u
namespace SetFormula

noncomputable def refinementDataHistoryIndicesSetFormula {n : Nat}
    (output stages history : Fin n) : SetFormula n :=
  exactSetFormula output
    (BoundedFormula.refinementDataHistoryIndicesEntryFormula stages.succ history.succ 0).toFormula

noncomputable def refinementDataHistoryLevelsSetFormula {n : Nat}
    (output stages history T : Fin n) : SetFormula n :=
  exactSetFormula output
    (BoundedFormula.refinementDataHistoryLevelsEntryFormula stages.succ history.succ T.succ 0).toFormula

end SetFormula
end PartitionPilot.Forcing

end

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Definability_RefinementHistoryOrderOutputFormulas
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PartitionPilot.Forcing
open SetRealization SetFormula
universe u

namespace SetFormula

noncomputable def refinementHistoryForcingOutputFormula {n : Nat}
    (output rows T stages history N : Fin n) : SetFormula n :=
  let old := suffixIndex n 2
  let v := prefixIndex n 2
  exBlock 2 (.conj (refinementDataHistoryIndicesSetFormula (v 0) (old stages) (old history))
    (.conj (refinementDataHistoryLevelsSetFormula (v 1) (old stages) (old history) (old T))
      (forcingHistoryConditionsOutputFormula (old output) (old rows) (v 0) (old T)
        (old stages) (old history) (v 1) (old N))))

end SetFormula

end PartitionPilot.Forcing



end

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Definability_SupportedCertificateFamilyFormulas
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section



namespace PartitionPilot.Forcing
open SetFormula
universe u

def supportedCertificateFamilyFormula : SetFormula 12 :=
  (BoundedFormula.allMem 0
    (BoundedFormula.supportedCertificateEntryFormula 0 2 3 4 5 6 7 8 9 10 11 12)).toFormula

end PartitionPilot.Forcing

end

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Geometry_GroundIndexedMixedOperationLifts
attribute [-instance] _root_.OAI.PartitionPilot.Forcing.GroundMainPrefix.withTopSmall
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PartitionPilot.Forcing
universe u

namespace TransitiveGround
open SetFormula
variable (M : TransitiveGround.{u})

theorem indexedMixedBinaryLift_mem
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    {T UG UP G P A JG JP : ZFSet.{u}} (hT : T ∈ M.sets) (hUG : UG ∈ M.sets)
    (hUP : UP ∈ M.sets) (hG : G ∈ M.sets) (hP : P ∈ M.sets)
    (hA : A ∈ M.sets) (hJG : JG ∈ M.sets) (hJP : JP ∈ M.sets) :
    indexedMixedBinaryLift T UG UP G P A JG JP ∈ M.sets := by
  have hBA := M.union_mem unions (M.union_mem unions hA)
  have hBJG := M.union_mem unions (M.union_mem unions hJG)
  have hBJP := M.union_mem unions (M.union_mem unions hJP)
  let params := extend T (extend UG (extend UP (extend G (extend P (extend A (extend JG
    (extend JP (extend A.sUnion.sUnion (extend JG.sUnion.sUnion
      (extend JP.sUnion.sUnion Fin.elim0))))))))))
  have selected := M.bounded_separation_mem separation BoundedFormula.indexedMixedBinaryLiftEntryFormula
    params (Fin.cases hT (Fin.cases hUG (Fin.cases hUP (Fin.cases hG (Fin.cases hP
      (Fin.cases hA (Fin.cases hJG (Fin.cases hJP (Fin.cases hBA (Fin.cases hBJG
        (Fin.cases hBJP (fun i => Fin.elim0 i))))))))))))
    (M.prod_mem pairing unions powers separation
      (M.prod_mem pairing unions powers separation hG hP) hP)
  have equal : ZFSet.sep (fun z => BoundedFormula.Truth BoundedFormula.indexedMixedBinaryLiftEntryFormula
      (extend z params)) (ZFSet.prod (ZFSet.prod G P) P) = indexedMixedBinaryLift T UG UP G P A JG JP := by
    apply ZFSet.ext
    intro z
    rw [ZFSet.mem_sep, indexedMixedBinaryLift, ZFSet.mem_sep,
      BoundedFormula.truth_indexedMixedBinaryLiftEntryFormula]
    rfl
  exact equal ▸ selected

end TransitiveGround
end PartitionPilot.Forcing

end

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Geometry_GroundIndexedOperationLifts
attribute [-instance] _root_.OAI.PartitionPilot.Forcing.GroundMainPrefix.withTopSmall
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PartitionPilot.Forcing
universe u

namespace TransitiveGround
open SetFormula
open scoped ZFSet
variable (M : TransitiveGround.{u})

theorem indexedRelationLift_mem
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    {T U Q R J : ZFSet.{u}} (hT : T ∈ M.sets) (hU : U ∈ M.sets)
    (hQ : Q ∈ M.sets) (hR : R ∈ M.sets) (hJ : J ∈ M.sets) :
    indexedRelationLift T U Q R J ∈ M.sets := by
  have hBR := M.union_mem unions (M.union_mem unions hR)
  have hBJ := M.union_mem unions (M.union_mem unions hJ)
  let params := extend T (extend U (extend Q (extend R (extend J
    (extend (⋃₀ ⋃₀ R) (extend (⋃₀ ⋃₀ J) Fin.elim0))))))
  have selected := M.bounded_separation_mem separation BoundedFormula.indexedRelationLiftEntryFormula
    params (Fin.cases hT (Fin.cases hU (Fin.cases hQ (Fin.cases hR (Fin.cases hJ
      (Fin.cases hBR (Fin.cases hBJ (fun i => Fin.elim0 i))))))))
    (M.prod_mem pairing unions powers separation hQ hQ)
  have equal : ZFSet.sep (fun z => BoundedFormula.Truth BoundedFormula.indexedRelationLiftEntryFormula
      (extend z params)) (ZFSet.prod Q Q) = indexedRelationLift T U Q R J := by
    apply ZFSet.ext
    intro z
    rw [ZFSet.mem_sep, indexedRelationLift, ZFSet.mem_sep,
      BoundedFormula.truth_indexedRelationLiftEntryFormula]
    rfl
  exact equal ▸ selected

theorem indexedBinaryLift_mem
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    {T U Q B J : ZFSet.{u}} (hT : T ∈ M.sets) (hU : U ∈ M.sets)
    (hQ : Q ∈ M.sets) (hB : B ∈ M.sets) (hJ : J ∈ M.sets) :
    indexedBinaryLift T U Q B J ∈ M.sets := by
  have hBB := M.union_mem unions (M.union_mem unions hB)
  have hBJ := M.union_mem unions (M.union_mem unions hJ)
  let params := extend T (extend U (extend Q (extend B (extend J
    (extend (⋃₀ ⋃₀ B) (extend (⋃₀ ⋃₀ J) Fin.elim0))))))
  have selected := M.bounded_separation_mem separation BoundedFormula.indexedBinaryLiftEntryFormula
    params (Fin.cases hT (Fin.cases hU (Fin.cases hQ (Fin.cases hB (Fin.cases hJ
      (Fin.cases hBB (Fin.cases hBJ (fun i => Fin.elim0 i))))))))
    (M.prod_mem pairing unions powers separation
      (M.prod_mem pairing unions powers separation hQ hQ) hQ)
  have equal : ZFSet.sep (fun z => BoundedFormula.Truth BoundedFormula.indexedBinaryLiftEntryFormula
      (extend z params)) (ZFSet.prod (ZFSet.prod Q Q) Q) = indexedBinaryLift T U Q B J := by
    apply ZFSet.ext
    intro z
    rw [ZFSet.mem_sep, indexedBinaryLift, ZFSet.mem_sep,
      BoundedFormula.truth_indexedBinaryLiftEntryFormula]
    rfl
  exact equal ▸ selected

end TransitiveGround
end PartitionPilot.Forcing

end

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Geometry_GroundIndexedValueLifts
attribute [-instance] _root_.OAI.PartitionPilot.Forcing.GroundMainPrefix.withTopSmall
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PartitionPilot.Forcing
open SetFormula SetRealization
universe u
namespace TransitiveGround
variable (M : TransitiveGround.{u})

theorem indexedValueLift_mem
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    {T U Q V F J : ZFSet.{u}} (hT : T ∈ M.sets) (hU : U ∈ M.sets)
    (hQ : Q ∈ M.sets) (hV : V ∈ M.sets) (hF : F ∈ M.sets) (hJ : J ∈ M.sets) :
    indexedValueLift T U Q V F J ∈ M.sets := by
  have hBF := M.union_mem unions (M.union_mem unions hF)
  have hBJ := M.union_mem unions (M.union_mem unions hJ)
  let params := extend T (extend U (extend Q (extend V (extend F (extend J
    (extend (ZFSet.sUnion (ZFSet.sUnion F))
      (extend (ZFSet.sUnion (ZFSet.sUnion J)) Fin.elim0)))))))
  have selected := M.bounded_separation_mem separation BoundedFormula.indexedValueLiftEntryFormula params
    (Fin.cases hT (Fin.cases hU (Fin.cases hQ (Fin.cases hV (Fin.cases hF
      (Fin.cases hJ (Fin.cases hBF (Fin.cases hBJ (fun i => Fin.elim0 i)))))))))
    (M.prod_mem pairing unions powers separation hQ hV)
  have equal : ZFSet.sep (fun z => BoundedFormula.Truth BoundedFormula.indexedValueLiftEntryFormula
      (extend z params)) (ZFSet.prod Q V) = indexedValueLift T U Q V F J := by
    apply ZFSet.ext
    intro z
    rw [ZFSet.mem_sep, indexedValueLift, ZFSet.mem_sep,
      BoundedFormula.truth_indexedValueLiftEntryFormula]
    rfl
  exact equal ▸ selected

end TransitiveGround

end PartitionPilot.Forcing

end

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Transfinite_GroundChronologyLayerRelation
attribute [-instance] _root_.OAI.PartitionPilot.Forcing.GroundMainPrefix.withTopSmall
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PartitionPilot.Forcing
open SetFormula
universe u

namespace SetFormula

def chronologyLayerRelationFormula : SetFormula 8 :=
  let old := suffixIndex 8 6
  let v := prefixIndex 8 6
  exBlock 6 (.conj
    (BoundedFormula.chronologyLayerPairLookupFormula (old 0) (old 2) (old 3) (old 4) (old 5) (old 6) v).toFormula
    (growthLayerWitnessFormula (old 1) (old 3) (old 4) (old 5) (v 2) (v 3) (v 4) (v 5) (v 1) (old 7)))
end SetFormula

end PartitionPilot.Forcing

end

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Forcing_GroundBatchEarlierLayerWitnesses
attribute [-instance] _root_.OAI.PartitionPilot.Forcing.GroundMainPrefix.withTopSmall
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PartitionPilot.Forcing

section
open SetFormula
universe u

noncomputable def fixedTopLayerWitness (P : ZFSet.{u}) : ZFSet.{u} :=
  countableLayerWitness {P} {ZFSet.pair P ∅}

end

end PartitionPilot.Forcing

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Transfinite_GroundLinkedMainStageLevels
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PartitionPilot.Forcing
open SetFormula
universe u

namespace SetFormula
def linkedMainStageFormula {n} (K Labels C D rD N z : Fin n) : SetFormula n :=
  let old := suffixIndex n 24
  exBlock 24 (linkedMainStageRawFormula (old K) (old Labels) (old C) (old D) (old rD) (old N) (old z)
    (prefixIndex n 24))
end SetFormula

end PartitionPilot.Forcing



end

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Definability_MainPrefixValidityFormulas
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PartitionPilot.Forcing
open SetFormula
universe u

namespace SetFormula

def mainPrefixIdentityFormula {n} (E : Fin n) : SetFormula n :=
  let v := prefixIndex n 3
  allBlock 3 (BoundedFormula.imp
    (BoundedFormula.pairedTransitionEntryFormula (v 0) (v 0) (v 1) (v 2) (suffixIndex n 3 E))
    (.conj (BoundedFormula.graphDiagonalFormula (v 1))
      (BoundedFormula.graphDiagonalFormula (v 2)))).toFormula

def mainPrefixCompositionFormula {n} (E : Fin n) : SetFormula n :=
  let v := prefixIndex n 9
  let old := suffixIndex n 9 E
  allBlock 9 (BoundedFormula.imp
    (BoundedFormula.pairedTransitionEntryFormula (v 0) (v 1) (v 3) (v 4) old)
    (BoundedFormula.imp
      (BoundedFormula.pairedTransitionEntryFormula (v 1) (v 2) (v 5) (v 6) old)
      (BoundedFormula.imp
        (BoundedFormula.pairedTransitionEntryFormula (v 0) (v 2) (v 7) (v 8) old)
        (.conj (BoundedFormula.graphCompositionFormula (v 3) (v 5) (v 7))
          (BoundedFormula.graphCompositionFormula (v 4) (v 6) (v 8)))))).toFormula

end SetFormula

namespace SetFormula

def mainPrefixStagesFormula {n} (K Labels C D rD N S : Fin n) : SetFormula n :=
  let old := suffixIndex n 2
  let v := prefixIndex n 2
  allBlock 2 (imp (BoundedFormula.pairMembershipFormula (v 0) (v 1) (old S)).toFormula
    (linkedMainStageFormula (old K) (old Labels) (old C) (old D) (old rD) (old N) (v 1)))

def mainPrefixTransitionsFormula {n} (K Labels C D rD N S E : Fin n) : SetFormula n :=
  let old := suffixIndex n 5
  let v := prefixIndex n 5
  allBlock 5 (imp (BoundedFormula.conj
    (BoundedFormula.pairMembershipFormula (v 0) (v 2) (old S))
    (.conj (BoundedFormula.pairMembershipFormula (v 1) (v 3) (old S))
      (BoundedFormula.tripleMembershipFormula (v 1) (v 0) (v 4) (old E)))).toFormula
    (linkedMainTransitionFormula (old K) (old Labels) (old C) (old D) (old rD) (old N)
      (v 2) (v 3) (v 4)))

end SetFormula

end PartitionPilot.Forcing

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Geometry_GroundIdentityInsertionTasks
attribute [-instance] _root_.OAI.PartitionPilot.Forcing.GroundMainPrefix.withTopSmall
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PartitionPilot.Forcing
universe u

noncomputable def identityIdealGraph (P r C : ZFSet.{u}) : ZFSet.{u} :=
  identityFunctionGraph (attachmentIdeal P r C)

noncomputable def identityInsertionTask (P r C E F label : ZFSet.{u}) : ZFSet.{u} :=
  literalTaskCode C C (identityIdealGraph P r C) E F label

end PartitionPilot.Forcing



namespace PartitionPilot.Forcing
open SetFormula
universe u

noncomputable def identityInsertionTaskGraph (Labels I P r C E F : ZFSet.{u}) : ZFSet.{u} :=
  ZFSet.sep (fun z => ∃ label ∈ Labels, ∃ task ∈ I,
    z = ZFSet.pair label task ∧ task = identityInsertionTask P r C E F label)
    (ZFSet.prod Labels I)

end PartitionPilot.Forcing

end

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Transfinite_GroundTaskBearingSuccessorDecoding
attribute [-instance] _root_.OAI.PartitionPilot.Forcing.GroundMainPrefix.withTopSmall
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace PartitionPilot.Forcing
universe u





structure MainSuccessorOutputCode (f : Fin 30 → ZFSet.{u}) : Prop where
  transition : MainTransitionLaws (f 0) (f 1) (f 2) (f 3) (f 4) (f 5) (f 6) (f 7)
    (f 8) (f 9) (f 10) (f 11) (f 12) (f 13) (f 14) (f 15) (f 16) (f 17) (f 18) (f 19)
  strict_top : StrictSuccessorTopCode (f 0) (f 1) (f 3) (f 18) (f 29)
  separation : SeparationFulfillmentCode (f 0) (f 2) (f 1) (f 3) (f 5) (f 7) (f 13) (f 18)
  rectangles : RectangleFulfillmentCode (f 0) (f 6) (f 2) (f 4) (f 12)
    (f 1) (f 7) (f 3) (f 5) (f 13) (f 18) (f 19)
  old_profiles : OldProfilePreservationCode (f 0) (f 2) (f 4) (f 1) (f 3) (f 5) (f 18) (f 26)
  task_caps : TaskCapFamilyCode (f 21) (f 0) (f 1) (f 3) (f 5) (f 18)
    (f 23) (f 24) (f 25) (f 26) (f 28)
  compression_actors : CompressionActorFulfillmentCode (f 21) (f 0) (f 6) (f 1) (f 7)
    (f 3) (f 13) (f 18) (f 19) (f 22) (f 27) (f 20) (f 28)

end PartitionPilot.Forcing



namespace PartitionPilot.Forcing
open SetFormula
universe u

namespace SetFormula

def mainSuccessorTaskBindingsFormula {n} (Labels : Fin n) (f : Fin 30 → Fin n) : SetFormula n :=
  .conj (groundEligibleTasksFormula (f 21) (f 0) (f 6) (f 2) (f 4) (f 12) Labels)
    (.conj (groundLiteralTaskFieldFormula 0 (f 22) (f 21) (f 0) (f 2) (f 4) Labels)
      (.conj (groundLiteralTaskFieldFormula 1 (f 23) (f 21) (f 0) (f 2) (f 4) Labels)
        (.conj (groundLiteralTaskFieldFormula 3 (f 24) (f 21) (f 0) (f 2) (f 4) Labels)
          (.conj (groundLiteralTaskFieldFormula 4 (f 25) (f 21) (f 0) (f 2) (f 4) Labels)
            (.conj (relativePowerFormula (f 0) (f 26))
              (groundTaskRepresentativesFormula (f 27) (f 0) (f 6) (f 2) (f 4) (f 12) Labels))))))

end SetFormula

end PartitionPilot.Forcing



namespace PartitionPilot.Forcing
open SetFormula
universe u v w

namespace SetFormula

def taskBearingMainSuccessorRawFormula {n}
    (K Labels C D rD N sourceCode targetCode z points actors sourceBirth targetBirth : Fin n)
    (source target : Fin 24 → Fin n) (extra : Fin 8 → Fin n) : SetFormula n :=
  .conj (linkedMainTransitionRawFormula K Labels C D rD N sourceCode targetCode z
    points actors sourceBirth targetBirth source target)
    (.conj (.mem (source 11) (target 11))
      (.conj (BoundedFormula.mainSuccessorOutputFormula
        (linkedSuccessorOutputFields source target points actors extra)).toFormula
        (mainSuccessorTaskBindingsFormula Labels
          (linkedSuccessorOutputFields source target points actors extra))))

end SetFormula

end PartitionPilot.Forcing



namespace PartitionPilot.Forcing
open SetFormula
universe u

namespace SetFormula

def taskBearingMainSuccessorFormula {n}
    (K Labels C D rD N sourceCode targetCode z : Fin n) : SetFormula n :=
  let old := suffixIndex n 60
  let fresh := prefixIndex n 60
  exBlock 60 (taskBearingMainSuccessorRawFormula (old K) (old Labels) (old C) (old D)
    (old rD) (old N) (old sourceCode) (old targetCode) (old z)
    (fresh 48) (fresh 49) (fresh 50) (fresh 51)
    (fun j => fresh (j.castAdd 36))
    (fun j => fresh (Fin.natAdd 24 (j.castAdd 12)))
    (fun j => fresh (Fin.natAdd 52 j)))

end SetFormula

end PartitionPilot.Forcing



end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Transfinite_GroundOmegaOneTaskBearingSuccessorFunction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI



namespace PartitionPilot.Forcing
open SetFormula
universe u

namespace SetFormula

def taskBearingSuccessorPairFormula {n}
    (K Labels C D rD N S V source output : Fin n) : SetFormula n :=
  .ex (.conj (.mem 0 S.succ) (.ex (.conj (.mem 0 V.succ.succ)
    (.conj (BoundedFormula.orderedPairFormula output.succ.succ 1 0).toFormula
      (taskBearingMainSuccessorFormula K.succ.succ Labels.succ.succ C.succ.succ
        D.succ.succ rD.succ.succ N.succ.succ source.succ.succ 1 0)))))

end SetFormula

end PartitionPilot.Forcing




end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Definability_LinkedProfileTransitionRawCodes
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PartitionPilot.Forcing
open SetFormula
universe u

namespace SetFormula
def linkedProfilePreservingTransitionRawFormula {n}
    (K Labels C D rD N sourceCode targetCode z points actors sourceBirth targetBirth Families : Fin n)
    (source target : Fin 24 → Fin n) : SetFormula n :=
  .conj (linkedMainTransitionRawFormula K Labels C D rD N sourceCode targetCode z points actors
    sourceBirth targetBirth source target)
    (.conj (relativePowerFormula (source 0) Families)
      (BoundedFormula.oldProfilePreservationFormula (source 0) (source 1) (source 2)
        (target 0) (target 1) (target 2) points Families).toFormula)

end SetFormula

end PartitionPilot.Forcing

end

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Geometry_GroundLinkedProfileTransitionRecognition
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PartitionPilot.Forcing
open SetFormula
universe u

namespace SetFormula

def linkedProfilePreservingTransitionFormula {n} (K Labels C D rD N sourceCode targetCode z : Fin n) : SetFormula n :=
  let old := suffixIndex n 53
  let fresh := prefixIndex n 53
  exBlock 53 (linkedProfilePreservingTransitionRawFormula (old K) (old Labels) (old C) (old D) (old rD) (old N)
    (old sourceCode) (old targetCode) (old z) (fresh 48) (fresh 49) (fresh 50) (fresh 51) (fresh 52)
    (fun j => fresh (j.castAdd 29)) (fun j => fresh (Fin.natAdd 24 (j.castAdd 5))))

end SetFormula

end PartitionPilot.Forcing

end

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Transfinite_MainPrefixHistoryUnionRecognition
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open scoped ZFSet



namespace PartitionPilot.Forcing
open SetFormula
universe u
namespace SetFormula

def mainPrefixProfileGraphFormula {n} (K Labels C D rD N S E : Fin n) : SetFormula n :=
  let old := suffixIndex n 5
  let v := prefixIndex n 5
  allBlock 5 (imp (BoundedFormula.conj
    (BoundedFormula.pairMembershipFormula (v 0) (v 2) (old S))
    (.conj (BoundedFormula.pairMembershipFormula (v 1) (v 3) (old S))
      (BoundedFormula.tripleMembershipFormula (v 1) (v 0) (v 4) (old E)))).toFormula
    (linkedProfilePreservingTransitionFormula (old K) (old Labels) (old C) (old D) (old rD) (old N)
      (v 2) (v 3) (v 4)))

end SetFormula

end PartitionPilot.Forcing



namespace PartitionPilot.Forcing
open SetFormula
universe u

namespace SetFormula
def mainPrefixHistoryFieldMemFormula {n} (p x : Fin n) (j : Fin 3) : SetFormula n :=
  let old := suffixIndex n 5
  let field := prefixIndex n 5
  let selected : Fin 3 → Fin (n + 5) := Fin.cases (field 1) (Fin.cases (field 2) (fun _ => field 3))
  exBlock 5 (BoundedFormula.conj
    (BoundedFormula.pairMembershipFormula (field 0) (field 4) (old p))
    (.conj (BoundedFormula.mainPrefixTupleFormula (field 4) (field 1) (field 2) (field 3))
      (.mem (old x) (selected j)))).toFormula

end SetFormula

end PartitionPilot.Forcing



namespace PartitionPilot.Forcing
open SetFormula
universe u

namespace SetFormula
def mainPrefixHistoryFieldUnionFormula {n} (p output : Fin n) (j : Fin 3) : SetFormula n :=
  exactSetFormula output (mainPrefixHistoryFieldMemFormula p.succ 0 j)

def mainPrefixHistoryUnionFormula {n} (p q : Fin n) : SetFormula n :=
  let old := suffixIndex n 3
  let field := prefixIndex n 3
  exBlock 3 (.conj (BoundedFormula.mainPrefixTupleFormula (old q) (field 0) (field 1) (field 2)).toFormula
    (conjBlock 3 (fun j => mainPrefixHistoryFieldUnionFormula (old p) (field j) j)))

end SetFormula

end PartitionPilot.Forcing

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Transfinite_GroundInitialPreservedMainPrefix
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open scoped ZFSet

namespace PartitionPilot.Forcing
open SetFormula
universe u
namespace SetFormula

def mainPrefixGraphBodyFormula {n} (K Labels C D rD N T S E J : Fin n) : SetFormula n :=
  .conj (BoundedFormula.ordinalFormula T).toFormula
    (.conj (functionGraphOnFormula T S)
      (.conj (functionGraphOnFormula J E)
        (.conj (mainPrefixStagesFormula K Labels C D rD N S)
          (.conj (mainPrefixTransitionsFormula K Labels C D rD N S E)
            (.conj (mainPrefixIdentityFormula E) (mainPrefixCompositionFormula E))))))

def mainPrefixGraphFormula {n} (K Labels C D rD N T S E : Fin n) : SetFormula n :=
  ex (.conj (BoundedFormula.chronologyPairsEquationFormula 0 T.succ).toFormula
    (mainPrefixGraphBodyFormula K.succ Labels.succ C.succ D.succ rD.succ N.succ
      T.succ S.succ E.succ 0))

end SetFormula

namespace SetFormula
def mainPrefixFormula {n} (K Labels C D rD N z : Fin n) : SetFormula n :=
  let old := suffixIndex n 3
  let field := prefixIndex n 3
  exBlock 3 (.conj (BoundedFormula.mainPrefixTupleFormula (old z) (field 0) (field 1) (field 2)).toFormula
    (mainPrefixGraphFormula (old K) (old Labels) (old C) (old D) (old rD) (old N)
      (field 0) (field 1) (field 2)))
end SetFormula

end PartitionPilot.Forcing

namespace PartitionPilot.Forcing
open SetFormula
universe u

namespace SetFormula
def preservedMainPrefixFormula {n} (K Labels C D rD N z : Fin n) : SetFormula n :=
  let old := suffixIndex n 3
  let field := prefixIndex n 3
  exBlock 3 (.conj (BoundedFormula.mainPrefixTupleFormula (old z) (field 0) (field 1) (field 2)).toFormula
    (.conj (mainPrefixGraphFormula (old K) (old Labels) (old C) (old D) (old rD) (old N)
      (field 0) (field 1) (field 2))
      (mainPrefixProfileGraphFormula (old K) (old Labels) (old C) (old D) (old rD) (old N)
        (field 1) (field 2))))
end SetFormula

end PartitionPilot.Forcing

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Transfinite_GroundMainPrefixSelectedStepTotality
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PartitionPilot.Forcing

section
open SetFormula
universe u

namespace SetFormula
def mainPrefixRecursionIndexFormula {n} (Omega z : Fin n) : SetFormula n :=
  let old := suffixIndex n 3
  let field := prefixIndex n 3
  exBlock 3 (BoundedFormula.conj
    (BoundedFormula.mainPrefixTupleFormula (old z) (field 0) (field 1) (field 2))
    (.conj (.mem (field 0) (old Omega)) (.neg (BoundedFormula.emptyFormula (field 0))))).toFormula

end SetFormula

end

open SetFormula SetRealization
universe u v w

end PartitionPilot.Forcing

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Definability_PreservedMainPrefixHistoryFormulas
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PartitionPilot.Forcing

open SetFormula
universe u

namespace SetFormula
def mainPrefixExtensionFormula {n} (old next : Fin n) : SetFormula n :=
  let outer := suffixIndex n 6
  let field := prefixIndex n 6
  exBlock 6 (.conj
    (BoundedFormula.mainPrefixTupleFormula (outer old) (field 0) (field 1) (field 2)).toFormula
    (.conj (BoundedFormula.mainPrefixTupleFormula (outer next) (field 3) (field 4) (field 5)).toFormula
      (BoundedFormula.mainPrefixFieldExtensionFormula
        (field 0) (field 1) (field 2) (field 3) (field 4) (field 5)).toFormula))

end SetFormula

namespace SetFormula

def mainPrefixLimitStepRawFormula {n} (K Labels C D rD N old next : Fin n)
    (w : Fin 32 → Fin n) : SetFormula n :=
  let v := mainPrefixLimitTargetFields w
  .conj (BoundedFormula.successorFormula (w 7) (w 0)).toFormula
  (.conj (BoundedFormula.mainPrefixTupleFormula old (w 0) (w 1) (w 2)).toFormula
  (.conj (BoundedFormula.mainPrefixTupleFormula next (w 7) (w 3) (w 4)).toFormula
  (.conj (mainPrefixExtensionFormula old next)
  (.conj (BoundedFormula.pairMembershipFormula (w 0) (w 5) (w 3)).toFormula
  (.conj (linkedMainStageRawFormula K Labels C D rD N (w 5) v)
  (.conj (BoundedFormula.pairMembershipFormula (v 11) (w 6) (v 17)).toFormula
    (BoundedFormula.mainLimitCoverageFormula (w 0) (w 1) (w 4)
      (v 0) (v 3) (v 1) (v 9) (v 11) (w 6)).toFormula))))))

def mainPrefixLimitStepFormula {n} (K Labels C D rD N old next : Fin n) : SetFormula n :=
  let outer := suffixIndex n 32
  exBlock 32 (mainPrefixLimitStepRawFormula (outer K) (outer Labels) (outer C)
    (outer D) (outer rD) (outer N) (outer old) (outer next) (prefixIndex n 32))

end SetFormula

namespace SetFormula
def mainPrefixSelectedStepFormula {n} (f old next : Fin n) : SetFormula n :=
  exBlock 10 (BoundedFormula.mainPrefixSelectedStepBody
    (suffixIndex n 10 f) (suffixIndex n 10 old) (suffixIndex n 10 next)
    (prefixIndex n 10)).toFormula

end SetFormula

namespace SetFormula
def mainPrefixConditionalStepFormula {n} (K Labels C D rD N f old next : Fin n) : SetFormula n :=
  let outer := suffixIndex n 3
  let field := prefixIndex n 3
  disj (mainPrefixSelectedStepFormula f old next)
    (exBlock 3 (.conj
      (BoundedFormula.mainPrefixTupleFormula (outer old) (field 0) (field 1) (field 2)).toFormula
      (.conj (BoundedFormula.nonzeroLimitOrdinalFormula (field 0)).toFormula
        (mainPrefixLimitStepFormula (outer K) (outer Labels) (outer C) (outer D)
          (outer rD) (outer N) (outer old) (outer next)))))

end SetFormula

end PartitionPilot.Forcing

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Definability_MainPrefixTraceStepFormulas
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PartitionPilot.Forcing
open SetFormula
universe u

namespace SetFormula
def mainPrefixAtIndexFormula {n} (T q : Fin n) : SetFormula n :=
  exBlock 2 (BoundedFormula.mainPrefixTupleFormula (suffixIndex n 2 q)
    (suffixIndex n 2 T) (prefixIndex n 2 0) (prefixIndex n 2 1)).toFormula

def mainPrefixAtSuccessorFormula {n} (α q : Fin n) : SetFormula n :=
  ex (.conj (BoundedFormula.successorFormula 0 α.succ).toFormula
    (mainPrefixAtIndexFormula 0 q.succ))

def mainPrefixHistoryExtendsFormula {n} (p q : Fin n) : SetFormula n :=
  .all (.all (imp (BoundedFormula.pairMembershipFormula 1 0 p.succ.succ).toFormula
    (mainPrefixExtensionFormula 0 q.succ.succ)))

end SetFormula

end PartitionPilot.Forcing



namespace PartitionPilot.Forcing
open SetFormula
universe u

namespace SetFormula
def mainPrefixTraceBranchFormula {n} (seed g α p y : Fin n) : SetFormula n :=
  disj (.conj (BoundedFormula.emptyFormula α).toFormula (.equal y seed))
    (.conj (.neg (BoundedFormula.emptyFormula α).toFormula)
      (ex (.conj (mainPrefixHistoryUnionFormula p.succ 0)
        (BoundedFormula.pairMembershipFormula 0 y.succ g.succ).toFormula)))

def mainPrefixTraceStepFormula {n} (B seed g α p y : Fin n) : SetFormula n :=
  .conj (.mem y B) (.conj (mainPrefixAtSuccessorFormula α y)
    (.conj (mainPrefixHistoryExtendsFormula p y) (mainPrefixTraceBranchFormula seed g α p y)))

end SetFormula

end PartitionPilot.Forcing

end

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Transfinite_MainPrefixSelectedTraceLaws
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PartitionPilot.Forcing

section
open SetFormula
universe u

def mainPrefixRecursionFormula : SetFormula 6 :=
  mainPrefixTraceStepFormula 3 4 5 0 1 2

end

end PartitionPilot.Forcing

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Geometry_GroundIndexedImageCovers
attribute [-instance] _root_.OAI.PartitionPilot.Forcing.GroundMainPrefix.withTopSmall
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PartitionPilot.Forcing
open SetFormula
universe u

noncomputable def indexedImageCover (I U V maps : ZFSet.{u}) : ZFSet.{u} :=
  relationCompose V (ZFSet.prod I U) I
    (relationConverse (ZFSet.prod I U) V (mapFamilyApplicationGraph I U V maps))
    (productFirst I U)

end PartitionPilot.Forcing

end

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Geometry_GroundTaskBearingInsertionFulfillment
attribute [-instance] _root_.OAI.PartitionPilot.Forcing.GroundMainPrefix.withTopSmall
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PartitionPilot.Forcing

section
open SetFormula
universe u

noncomputable def identityTaskCapFamily (Labels I P Q r Caps c e F : ZFSet.{u}) : ZFSet.{u} :=
  relationCompose Labels I Q (identityInsertionTaskGraph Labels I P r c e F) Caps

end

end PartitionPilot.Forcing

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Geometry_GroundCertificateProfileImageFamilies
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PartitionPilot.Forcing

section
open SetFormula
universe u

namespace SetFormula

def preparedFamilyEntries {n}
    (P order q nodes nodeOrder meet N visibility top omega k enumerations : Fin n) : SetFormula n :=
  .all (.all (.all (.all (.all (.all
    (imp (.conj (BoundedFormula.certificateGraphEntryAt 5 4 3 2
        k.succ.succ.succ.succ.succ.succ).toFormula
      (BoundedFormula.enumerationGraphEntryAt 5 1 0
        enumerations.succ.succ.succ.succ.succ.succ).toFormula)
      (preparedCertificateFormula P.succ.succ.succ.succ.succ.succ
        order.succ.succ.succ.succ.succ.succ q.succ.succ.succ.succ.succ.succ
        nodes.succ.succ.succ.succ.succ.succ nodeOrder.succ.succ.succ.succ.succ.succ
        meet.succ.succ.succ.succ.succ.succ N.succ.succ.succ.succ.succ.succ
        visibility.succ.succ.succ.succ.succ.succ top.succ.succ.succ.succ.succ.succ
        omega.succ.succ.succ.succ.succ.succ 5 4 3 2 1 0)))))))

def preparedCertificateFamilyFormula {n}
    (P order q nodes nodeOrder meet N visibility top omega J C E k enumerations : Fin n) : SetFormula n :=
  .conj (BoundedFormula.functionFormula J C k).toFormula
    (.conj (BoundedFormula.functionFormula J E enumerations).toFormula
      (preparedFamilyEntries P order q nodes nodeOrder meet N visibility top omega k enumerations))

end SetFormula

end

end PartitionPilot.Forcing

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Definability_GroundPreparationEventSupportGraphs
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PartitionPilot.Forcing
open SetFormula
universe u
namespace BoundedFormula

def eventSupportSetFormula {n} (nodes event output : Fin n) : BoundedFormula n :=
  .conj (.allMem output (.mem 0 nodes.succ))
    (.allMem nodes (.conj
      (imp (.mem 0 output.succ) (preparationEventSupportFormula 0 event.succ))
      (imp (preparationEventSupportFormula 0 event.succ) (.mem 0 output.succ))))

def eventSupportGraphFormula : BoundedFormula 2 :=
  exPairFields 0 (eventSupportSetFormula 3 1 0)

end BoundedFormula

end PartitionPilot.Forcing

end

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Forcing_GroundFixedIndexAssignmentSlices
attribute [-instance] _root_.OAI.PartitionPilot.Forcing.GroundMainPrefix.withTopSmall
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PartitionPilot.Forcing
open SetRealization
universe u

noncomputable def fixedIndexAssignmentPairs (idx T A : ZFSet.{u}) : ZFSet.{u} :=
  relationImage (assignmentOnIndices {idx} T A) (ZFSet.prod T T)
    (productSecond {idx} (ZFSet.prod T T))

noncomputable def fixedIndexAssignmentClassGraph (idx T A B graph : ZFSet.{u}) : ZFSet.{u} :=
  relationCompose (fixedIndexAssignmentPairs idx T A) (stageOneAssignments {idx} T) B
    (relationConverse (stageOneAssignments {idx} T) (ZFSet.prod T T)
      (productSecond {idx} (ZFSet.prod T T))) graph

end PartitionPilot.Forcing

end

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Forcing_GroundOrdinaryEqualityDecisionFusion
attribute [-instance] _root_.OAI.PartitionPilot.Forcing.GroundMainPrefix.withTopSmall
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PartitionPilot.Forcing.TransitiveGround
open SetRealization SetFormula
universe u
variable (M : TransitiveGround.{u})

noncomputable def ordinaryEqualityDecisionFamily (T Q order tau : ZFSet.{u}) : ZFSet.{u} :=
  familyCodeGraph (fun sigma : T => sigma.val)
    (fun sigma => M.ordinaryEqualityDecisions Q order sigma.val tau)

end PartitionPilot.Forcing.TransitiveGround



end

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Forcing_StructuralForcingStageWitnessStep
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open scoped ZFSet


namespace PartitionPilot.Forcing.PosetActionCode
open SetRealization
universe u
variable {G P : Type u} [Group G] [PartialOrder P]
variable (t : Presentation G) (s : Presentation P) {A : ZFSet.{u}}
variable (h : PosetActionCode t.carrier s.carrier
  ((t.product t).graph t (fun gh => gh.1 * gh.2)) (t.encode 1) s.conditionOrder A)

noncomputable def presentedAct (g : G) (p : P) : P :=
  (t.product s).decodeFunction s A h.function (g, p)

theorem presentedAct_entry (g : G) (p : P) :
    ZFSet.pair (ZFSet.pair (t.encode g) (s.encode p)) (s.encode (h.presentedAct t s g p)) ∈ A :=
  (t.product s).decodeFunction_mem s A h.function (g, p)

theorem presentedAct_eq_iff (g : G) (p q : P) :
    h.presentedAct t s g p = q ↔ ZFSet.pair (ZFSet.pair (t.encode g) (s.encode p)) (s.encode q) ∈ A :=
  (t.product s).decodeFunction_iff s A h.function (g, p) q

theorem presentedAct_one (p : P) : h.presentedAct t s 1 p = p :=
  (h.presentedAct_eq_iff t s 1 p p).2 (h.one _ (s.encode_mem p))

theorem presentedAct_mul (g j : G) (p : P) :
    h.presentedAct t s (g * j) p = h.presentedAct t s g (h.presentedAct t s j p) := by
  apply (h.presentedAct_eq_iff t s _ _ _).2
  exact h.mul _ (t.encode_mem g) _ (t.encode_mem j) _ (t.encode_mem (g * j))
    _ (s.encode_mem p) _ (s.encode_mem _) _ (s.encode_mem _)
    (((t.product t).pair_mem_graph t (fun gh => gh.1 * gh.2) (g, j) (g * j)).2 rfl)
    (h.presentedAct_entry t s j p) (h.presentedAct_entry t s g (h.presentedAct t s j p))

theorem presentedAct_inv_left (g : G) (p : P) :
    h.presentedAct t s g⁻¹ (h.presentedAct t s g p) = p := by
  rw [← h.presentedAct_mul t s, inv_mul_cancel, h.presentedAct_one t s]

theorem presentedAct_inv_right (g : G) (p : P) :
    h.presentedAct t s g (h.presentedAct t s g⁻¹ p) = p := by
  rw [← h.presentedAct_mul t s, mul_inv_cancel, h.presentedAct_one t s]

theorem presentedAct_monotone (g : G) : Monotone (h.presentedAct t s g) := by
  intro p q below
  apply (s.pair_mem_conditionOrder _ _).1
  exact h.monotone _ (t.encode_mem g) _ (s.encode_mem p) _ (s.encode_mem q)
    _ (s.encode_mem _) _ (s.encode_mem _) (h.presentedAct_entry t s g p)
    (h.presentedAct_entry t s g q) ((s.pair_mem_conditionOrder p q).2 below)

theorem presentedAct_le_iff (g : G) (p q : P) :
    h.presentedAct t s g p ≤ h.presentedAct t s g q ↔ p ≤ q := by
  constructor
  · intro below
    have back := h.presentedAct_monotone t s g⁻¹ below
    simpa only [h.presentedAct_inv_left t s] using back
  · exact fun below => h.presentedAct_monotone t s g below

noncomputable def toPresentedPosetAction : PosetAction G P where
  iso g := {
    toFun := h.presentedAct t s g
    invFun := h.presentedAct t s g⁻¹
    left_inv := h.presentedAct_inv_left t s g
    right_inv := h.presentedAct_inv_right t s g
    map_rel_iff' := h.presentedAct_le_iff t s g _ _ }
  one := h.presentedAct_one t s
  mul := h.presentedAct_mul t s

theorem toPresentedPosetAction_graph : (h.toPresentedPosetAction t s).actionGraph s t = A :=
  (t.product s).graph_decodeFunction s A h.function

end PartitionPilot.Forcing.PosetActionCode



namespace PartitionPilot.Forcing
open SetRealization
universe u
variable {G R : Type u} [Group G] [PartialOrder R]
variable (a : PosetAction G R) (c : Presentation R) (t : Presentation G)
variable (Q J B : ZFSet.{u})

theorem presentedRowAssignmentGraph_code
    (shape : Q ⊆ ZFSet.prod c.carrier (ZFSet.powerset J))
    (laws : RelationActionLaws G J (fun g => rawActionSection (t.encode g) B J))
    (preserves : ∀ g : G, ∀ r : R, ∀ A,
      ZFSet.pair (c.encode r) A ∈ Q →
      ZFSet.pair (c.encode (a.iso g r)) (relationImage A J (rawActionSection (t.encode g) B J)) ∈ Q) :
    PosetActionCode t.carrier Q ((t.product t).graph t (fun gh => gh.1 * gh.2)) (t.encode 1)
      (rawRowAssignmentOrder Q c.conditionOrder)
      (rawRowAssignmentActionGraph t.carrier Q c.carrier (⋃₀ ⋃₀ Q) J (a.actionGraph c t) B) := by
  refine ⟨presentedRowAssignmentGraph_function a c t Q J B shape preserves, ?_, ?_, ?_⟩
  · intro p hp
    obtain ⟨r, A, hA, rfl⟩ := exists_presentedRowAssignmentCoordinates c shape hp
    exact (presentedRowAssignmentGraph_entry a c t Q J B 1 r r A A).2
      ⟨hp, hp, a.one r, (laws.image_one (ZFSet.mem_powerset.1 hA)).symm⟩
  · intro g hg h hh k hk p hp q hq r hr product first second
    obtain ⟨g, rfl⟩ := (t.mem_carrier g).1 hg
    obtain ⟨h, rfl⟩ := (t.mem_carrier h).1 hh
    obtain ⟨k, rfl⟩ := (t.mem_carrier k).1 hk
    have gh := ((t.product t).pair_mem_graph t (fun gh => gh.1 * gh.2) (g, h) k).1 product
    obtain ⟨rp, A, hA, rfl⟩ := exists_presentedRowAssignmentCoordinates c shape hp
    obtain ⟨rq, D, _, rfl⟩ := exists_presentedRowAssignmentCoordinates c shape hq
    obtain ⟨rr, E, _, rfl⟩ := exists_presentedRowAssignmentCoordinates c shape hr
    obtain ⟨_, _, firstRow, rfl⟩ := (presentedRowAssignmentGraph_entry a c t Q J B h rp rq A D).1 first
    obtain ⟨_, _, secondRow, rfl⟩ := (presentedRowAssignmentGraph_entry a c t Q J B g rq rr _ E).1 second
    apply (presentedRowAssignmentGraph_entry a c t Q J B k rp rr A _).2
    refine ⟨hp, hr, ?_, ?_⟩
    · rw [← gh, a.mul, firstRow, secondRow]
    · rw [← gh]
      exact (laws.image_mul g h (ZFSet.mem_powerset.1 hA)).symm
  · intro g hg p hp q hq r hr s hs first second below
    obtain ⟨g, rfl⟩ := (t.mem_carrier g).1 hg
    obtain ⟨rp, A, _, rfl⟩ := exists_presentedRowAssignmentCoordinates c shape hp
    obtain ⟨rq, D, _, rfl⟩ := exists_presentedRowAssignmentCoordinates c shape hq
    obtain ⟨rr, E, _, rfl⟩ := exists_presentedRowAssignmentCoordinates c shape hr
    obtain ⟨rs, F, _, rfl⟩ := exists_presentedRowAssignmentCoordinates c shape hs
    obtain ⟨_, _, firstRow, rfl⟩ := (presentedRowAssignmentGraph_entry a c t Q J B g rp rr A E).1 first
    obtain ⟨_, _, secondRow, rfl⟩ := (presentedRowAssignmentGraph_entry a c t Q J B g rq rs D F).1 second
    obtain ⟨_, _, rows, assignments⟩ := (pair_mem_rawRowAssignmentOrder _ _ _ _ _ _).1 below
    apply (pair_mem_rawRowAssignmentOrder _ _ _ _ _ _).2
    refine ⟨hr, hs, ?_, ?_⟩
    · apply (c.pair_mem_conditionOrder rr rs).2
      rw [← firstRow, ← secondRow]
      exact (a.iso g).monotone ((c.pair_mem_conditionOrder rp rq).1 rows)
    · intro y hy
      obtain ⟨hy, x, hx, edge⟩ := (mem_relationImage _ J _ y).1 hy
      exact (mem_relationImage _ J _ y).2 ⟨hy, x, assignments hx, edge⟩

end PartitionPilot.Forcing



end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Forcing_GroundSharedConditionalNames
attribute [-instance] _root_.OAI.PartitionPilot.Forcing.GroundMainPrefix.withTopSmall
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PartitionPilot.Forcing

section
open SetRealization SetFormula
universe u

namespace SetFormula

def sharedConditionFormula {n : Nat} (phi : SetFormula n) (i : Fin n) :
    SetFormula (n + 1) :=
  .conj (reindex Fin.succ phi) (.mem 0 i.succ)

end SetFormula

namespace Name
variable {P : Type u} [Preorder P] [OrderTop P] {s : Presentation P}

noncomputable def sharedConditionName (D : NameDomain s) {n : Nat}
    (phi : SetFormula n) (env : Assignment D n) (i : Fin n)
    (T : ZFSet.{u}) (valid : ∀ z ∈ T, IsName s z) : Name s :=
  separationName D (sharedConditionFormula phi i) env (familySet ⊤ T valid)

end Name
end

namespace Name
open SetRealization SetFormula
universe u
variable {P : Type u} [Preorder P] [OrderTop P] {s : Presentation P}

noncomputable def refinementConditionNames (D : NameDomain s)
    (env : Assignment D 4) (T : Fin 3 → ZFSet.{u})
    (valid : ∀ i, ∀ z ∈ T i, IsName s z) : Fin 3 → Name s :=
  fun i => sharedConditionName D BoundedFormula.refinementValidityFormula.toFormula
    env i.castSucc (T i) (valid i)

end Name

end PartitionPilot.Forcing

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Forcing_PreparedWitnessCertificateGraphs
attribute [-instance] _root_.OAI.PartitionPilot.Forcing.GroundMainPrefix.withTopSmall
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PartitionPilot.Forcing
open SetFormula
universe u

noncomputable def preparedWitnessCertificateGraph (stages Q K E : ZFSet.{u}) : ZFSet.{u} :=
  let tail := ZFSet.prod K E
  let output := ZFSet.prod Q tail
  let L := ZFSet.prod stages output
  relationCompose L tail K
    (relationCompose L output tail (productSecond stages output) (productSecond Q tail))
    (productFirst K E)

end PartitionPilot.Forcing

end

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Forcing_GroundMainFinalStructuralCommonSupportInduction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open scoped ZFSet


section

namespace PartitionPilot.Forcing.TransitiveGround
open SetRealization SetFormula
universe u
variable (M : TransitiveGround.{u}) {G P : Type u} [Group G] [PartialOrder P]
variable (a : PosetAction G P) (s : Presentation P) (t : Presentation G)
variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
variable (unions : Realize M.sets SetFormula.union Fin.elim0)
variable (powers : Realize M.sets powerSet Fin.elim0)
variable (separation : SeparationSchema M.sets) (collection : CollectionSchema M.sets)
variable (carrier : s.carrier ∈ M.sets) (order : s.conditionOrder ∈ M.sets)
variable (group : t.carrier ∈ M.sets) (action : a.actionGraph s t ∈ M.sets)
variable (maps : a.conditionMapFamily s t ∈ M.sets)
include pairing unions powers separation collection carrier order group action maps

noncomputable def rectangleParameters (p : P) (x y : Name s) (g₁ g₂ : G) : Fin 10 → ZFSet.{u} :=
  extend (s.encode p) (extend x.val (extend y.val (extend (a.act s g₁ x).val
    (extend (a.act s g₂ x).val (extend s.carrier (extend s.conditionOrder
      (extend t.carrier (extend (a.actionGraph s t) (extend (a.conditionMapFamily s t) Fin.elim0)))))))))

end PartitionPilot.Forcing.TransitiveGround



end


end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Forcing_GroundSelectedOrbitNameFamilies
attribute [-instance] _root_.OAI.PartitionPilot.Forcing.GroundMainPrefix.withTopSmall
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open scoped ZFSet




namespace PartitionPilot.Forcing
namespace TransitiveGround
open SetRealization SetFormula
universe u
variable (M : TransitiveGround.{u}) {G P : Type u} [Group G] [PartialOrder P]
variable (a : PosetAction G P) (s : Presentation P) (t : Presentation G)

noncomputable def selectedImageDefinition (separation : SeparationSchema M.sets) :
    GroundDefinableFunction M (fun env : Fin 3 → ZFSet.{u} => relationImage (env 0) (env 1) (env 2)) where
  formula := (BoundedFormula.relationImageEqualityFormula 0 1 2 3).toFormula
  closed := fun _ members => M.relationImage_mem separation (members 0) (members 1) (members 2)
  correct := by
    intro env members z hz
    rw [BoundedFormula.realize_toFormula M _ _ (Fin.cases hz members),
      BoundedFormula.truth_relationImageEqualityFormula]
    rfl

noncomputable def jointCodeDefinition
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0) :
    GroundDefinableFunction M (fun env : Fin 3 → ZFSet.{u} => orderedPairNameCode (env 0) (env 1) (env 2)) where
  formula := orderedPairNameCodeFormula 0 2 3 1
  closed := fun _ members => M.orderedPairNameCode_mem pairing (members 0) (members 1) (members 2)
  correct := fun _ members _ hz => M.realize_orderedPairNameCodeFormula pairing 0 2 3 1 _ (Fin.cases hz members)

end TransitiveGround
end PartitionPilot.Forcing

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Geometry_GroundMainFinalStructuralCompression
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open scoped ZFSet


namespace PartitionPilot.Forcing
open SetFormula SetRealization
universe u

noncomputable def insertionUsedNodes
    (rowNodes columns row I T A nodes anchors : ZFSet.{u}) : ZFSet.{u} :=
  rowUsedRows rowNodes columns (natSetCode 2) row ∪
    relationImage (assignmentIndices I T A) nodes anchors

end PartitionPilot.Forcing



end OAI
end


