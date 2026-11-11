-- Prove2me | Definitions.Def_OAIQ253P002
-- name    : OAIQ253P002
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-11T05:46:41.261402+00:00
-- url     : https://prove2.me/theorems/f9e6c6c2-1a71-460a-b47f-2db5a3a6b40a
-- title:
--   Definitions bundle OAIQ253P002 of the split of OpenAI, The Partition Principle does not imply Choice
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.PartitionPilot.Forcing.TransitiveGround.exists_model_partitionPrinciple_without_choice`, carved from OpenAI's openai/math development (OpenAI, *The Partition Principle does not imply Choice*, OpenAI Math Release, September 24, 2026, result family 244, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 947 declarations of OpenAI's Lean: 406 definitions, 23 inductive types or structures and 518 theorems. The definitions and types are `OAI.PartitionPilot.Forcing.BoundedFormula.activePreparationFormula`, `OAI.PartitionPilot.Forcing.BoundedFormula.eligibleTaskEntryFormula`, `OAI.PartitionPilot.Forcing.BoundedFormula.eligibleTaskFormula`, `OAI.PartitionPilot.Forcing.BoundedFormula.enumerationGraphEntryAt`, `OAI.PartitionPilot.Forcing.BoundedFormula.exFairStateFields`, `OAI.PartitionPilot.Forcing.BoundedFormula.exLinkedCoverageFields`, `OAI.PartitionPilot.Forcing.BoundedFormula.exMainLimitConeFields`, `OAI.PartitionPilot.Forcing.BoundedFormula.exMainLimitImageFields`, `OAI.PartitionPilot.Forcing.BoundedFormula.exMainLimitStageFields`, `OAI.PartitionPilot.Forcing.BoundedFormula.externalCosetEntryFormula`, `OAI.PartitionPilot.Forcing.BoundedFormula.externalCosetSupportFormula`, `OAI.PartitionPilot.Forcing.BoundedFormula.externalFlatCoordinateFormula`, `OAI.PartitionPilot.Forcing.BoundedFormula.externalFlatPlacementEntryFormula`, `OAI.PartitionPilot.Forcing.BoundedFormula.externalFlatStepEntryFormula`, `OAI.PartitionPilot.Forcing.BoundedFormula.externalFlatStepFormula`, `OAI.PartitionPilot.Forcing.BoundedFormula.externalFlatTileStepFormula`, `OAI.PartitionPilot.Forcing.BoundedFormula.externalFlatVertexWordFormula`, `OAI.PartitionPilot.Forcing.BoundedFormula.externalGeneratorSymbolEntryFormula`, `OAI.PartitionPilot.Forcing.BoundedFormula.externalRectangleFormula`, `OAI.PartitionPilot.Forcing.BoundedFormula.externalRectangleTupleFormula`, `OAI.PartitionPilot.Forcing.BoundedFormula.externalRectanglesEntryFormula`, `OAI.PartitionPilot.Forcing.BoundedFormula.externalRequestOverlapEntryFormula`, `OAI.PartitionPilot.Forcing.BoundedFormula.externalRequestOverlapFormula`, `OAI.PartitionPilot.Forcing.BoundedFormula.externalRequestOverlapForwardFormula`, `OAI.PartitionPilot.Forcing.BoundedFormula.externalSlotCopyEntryFormula`, `OAI.PartitionPilot.Forcing.BoundedFormula.externalStarSupportEntryFormula`, `OAI.PartitionPilot.Forcing.BoundedFormula.externalSymbolInverseEntryFormula`, `OAI.PartitionPilot.Forcing.BoundedFormula.externalSymbolInverseFormula`, `OAI.PartitionPilot.Forcing.BoundedFormula.externalTileSlotSupportFormula`, `OAI.PartitionPilot.Forcing.BoundedFormula.externalTileSupportFormula`, `OAI.PartitionPilot.Forcing.BoundedFormula.externalWordAtomicFormula`, `OAI.PartitionPilot.Forcing.BoundedFormula.externalWordStepEntryFormula`, `OAI.PartitionPilot.Forcing.BoundedFormula.externalWordStepFormula`, `OAI.PartitionPilot.Forcing.BoundedFormula.fairPreparationStateFormula`, `OAI.PartitionPilot.Forcing.BoundedFormula.fairPreparationStepFormula`, `OAI.PartitionPilot.Forcing.BoundedFormula.fairStepFieldsFormula`, `OAI.PartitionPilot.Forcing.BoundedFormula.finitePathClosureEntryFormula`, `OAI.PartitionPilot.Forcing.BoundedFormula.finiteRelationPathFormula`, `OAI.PartitionPilot.Forcing.BoundedFormula.finiteWordAppendEntryFormula`, `OAI.PartitionPilot.Forcing.BoundedFormula.finiteWordAppendFormula` and 389 more.
--
--   **Sources.** They come from these modules of lean/OAI/SetTheory, in whole or in part: `PartitionPrinciple_Definability_BatchAttachmentRealization`, `PartitionPrinciple_Definability_BatchGraphSetFormulas`, `PartitionPrinciple_Definability_BoundedAtomicEquality`, `PartitionPrinciple_Definability_BoundedRelationImageEquality`, `PartitionPrinciple_Definability_CodedBatchDecoding`, `PartitionPrinciple_Definability_CodedInjectiveCones`, `PartitionPrinciple_Definability_CodedLayerRestrictions`, `PartitionPrinciple_Definability_CodedTemplateShadowLaws`, `PartitionPrinciple_Definability_CompressionExternalStepRealization`, `PartitionPrinciple_Definability_CountableSetFormulas`, `PartitionPrinciple_Definability_DepthSlotCodes`, `PartitionPrinciple_Definability_EqualityStepSyntax`, `PartitionPrinciple_Definability_ExternalColumnCodes`, `PartitionPrinciple_Definability_ExternalGroupOperationGraphs`, `PartitionPrinciple_Definability_ExternalSlotCopyGraphs`, `PartitionPrinciple_Definability_ExternalWordRewriteFormulas`, `PartitionPrinciple_Definability_FiniteWordOperationFormulas`, `PartitionPrinciple_Definability_FixedTopCodes`, `PartitionPrinciple_Definability_FlatLimitConditionFormulas`, `PartitionPrinciple_Definability_ForcingHistoryOutputFormulas`, `PartitionPrinciple_Definability_GreedyAntichainStepFormulas`, `PartitionPrinciple_Definability_GroundAssignmentClassGraphs`, `PartitionPrinciple_Definability_GroundBatchAttachmentGraphs`, `PartitionPrinciple_Definability_GroundBelowFunctionGraphs`, `PartitionPrinciple_Definability_GroundBelowIndexedCarriers`, `PartitionPrinciple_Definability_GroundBelowRelationSpaces`, `PartitionPrinciple_Definability_GroundBoundedExternalBirths`, `PartitionPrinciple_Definability_GroundDepthSlotCodes`, `PartitionPrinciple_Definability_GroundExternalRequestSetRecognition`, `PartitionPrinciple_Definability_GroundFlatCopyGraphs`, `PartitionPrinciple_Definability_GroundLiftedCompressionFormulas`, `PartitionPrinciple_Definability_GroundLiftedRowTupleProvenance`, `PartitionPrinciple_Definability_GroundPackedRefinementFormulaData`, `PartitionPrinciple_Definability_GroundPairCompositions`, `PartitionPrinciple_Definability_GroundPartialFunctionSpaces`, `PartitionPrinciple_Definability_GroundPowerImageGraphs`, `PartitionPrinciple_Definability_GroundPushFilterFamilyFormulas`, `PartitionPrinciple_Definability_GroundRationalCodes`, `PartitionPrinciple_Definability_GroundRecursiveActionFormulas`, `PartitionPrinciple_Definability_GroundRegularFormulas`, `PartitionPrinciple_Definability_IndexedSubstructureCodes`, `PartitionPrinciple_Definability_IndexedValueLiftCodes`, `PartitionPrinciple_Definability_InitialMainAlgebraCodes`, `PartitionPrinciple_Definability_LeastSlotOwnerCodes`, `PartitionPrinciple_Definability_LiftedCompressionFormulas`, `PartitionPrinciple_Definability_LinkedMainTransitionRawCodes`, `PartitionPrinciple_Definability_MainLimitCoverageFormulas`, `PartitionPrinciple_Definability_MainPrefixValidityFormulas`, `PartitionPrinciple_Definability_MapFamilyApplicationGraphs`, `PartitionPrinciple_Definability_NameSupportFormulas`, `PartitionPrinciple_Definability_NatUnionCodes`, `PartitionPrinciple_Definability_NaturalSetCodes`, `PartitionPrinciple_Definability_NonemptyTupleFields`, `PartitionPrinciple_Definability_PairPushFilterFamilies`, `PartitionPrinciple_Definability_ParentSupportCodes`, `PartitionPrinciple_Definability_PresentedGroupCodes`, `PartitionPrinciple_Definability_PreservedMainPrefixHistoryFormulas`, `PartitionPrinciple_Definability_PrincipalSupportFormulas`, `PartitionPrinciple_Definability_RecursiveActionRealization`, `PartitionPrinciple_Definability_RefinementDataHistoryEntryFormulas`, `PartitionPrinciple_Definability_RefinementValidityCodes`, `PartitionPrinciple_Definability_SeparationFulfillmentCodes`, `PartitionPrinciple_Definability_SmallFunctionActionFormulas`, `PartitionPrinciple_Definability_StrictLexHeightFormulas`, `PartitionPrinciple_Definability_TaggedGrowthLayerFormulas`, `PartitionPrinciple_Definability_TaggedSumPresentations`, `PartitionPrinciple_Definability_TaskCapFamilyCodes`, `PartitionPrinciple_Definability_TaskRepresentativeCodes`, `PartitionPrinciple_Definability_TaskTransportFormulas`, `PartitionPrinciple_Definability_VisibilityProfileFormulas`, `PartitionPrinciple_Forcing_ActionPostcompositionCodes`, `PartitionPrinciple_Forcing_CodedDenseOrders`, `PartitionPrinciple_Forcing_CodedRecursiveTaskActions`, `PartitionPrinciple_Forcing_ConditionQuantifiers`, `PartitionPrinciple_Forcing_FinitePrincipalNameSupports`, `PartitionPrinciple_Forcing_ForcingHistoryTestDecomposition`, `PartitionPrinciple_Forcing_GroundFixedTopStep`, `PartitionPrinciple_Forcing_GroundMainFinalStructuralCommonSupportInduction`, `PartitionPrinciple_Forcing_GroundOutsideRowNames`, `PartitionPrinciple_Forcing_GroundProductActions`, `PartitionPrinciple_Forcing_GroundProductSizeWitnesses`, `PartitionPrinciple_Forcing_GroundPushFilters`, `PartitionPrinciple_Forcing_GroundRecursiveActions`, `PartitionPrinciple_Forcing_GroundRepresentedDomainConditions`, `PartitionPrinciple_Forcing_GroundRowAssignmentActions`, `PartitionPrinciple_Forcing_GroundRowGenerics`, `PartitionPrinciple_Forcing_GroundSizeWitnesses`, `PartitionPrinciple_Forcing_GroundSmallFunctionPermutations`, `PartitionPrinciple_Forcing_GroundStoredPreparedFamilyActions`, `PartitionPrinciple_Forcing_GroundUnionSizeWitnesses`, `PartitionPrinciple_Forcing_GroundVaryingFamilyEvaluation`, `PartitionPrinciple_Forcing_InitialRecursiveActionAgreement`, `PartitionPrinciple_Forcing_NameRenameSteps`, `PartitionPrinciple_Forcing_OwnerBirthLayerTransport`, `PartitionPrinciple_Forcing_RecursiveNextTaskActions`, `PartitionPrinciple_Forcing_RefinementAssignmentLabelNames`, `PartitionPrinciple_Forcing_SmallCodedMeetActions`, `PartitionPrinciple_Forcing_UniformGroundNames`, `PartitionPrinciple_Forcing_UniformGroundSizeWitnesses`, `PartitionPrinciple_Geometry_CompressionExternalTileOverlaps`, `PartitionPrinciple_Geometry_CompressionUnionBaseFilling`, `PartitionPrinciple_Geometry_DecodedMeetMaps`, `PartitionPrinciple_Geometry_ExternalOwnerCoordinateLaws`, `PartitionPrinciple_Geometry_FiniteWordOperations`, `PartitionPrinciple_Geometry_FixedCompressionSeeds`, `PartitionPrinciple_Geometry_GroundAttachmentEmbeddings`, `PartitionPrinciple_Geometry_GroundBatchAttachment`, `PartitionPrinciple_Geometry_GroundBatchEmbeddingRecognition`, `PartitionPrinciple_Geometry_GroundBatchHeightGraphs`, `PartitionPrinciple_Geometry_GroundBelowExternalPoints`, `PartitionPrinciple_Geometry_GroundBelowInitialCompression`, `PartitionPrinciple_Geometry_GroundCodedBinaryHeights`, `PartitionPrinciple_Geometry_GroundCompressionHeightSteps`, `PartitionPrinciple_Geometry_GroundCompressionOrigins`, `PartitionPrinciple_Geometry_GroundCompressionStampBounds`, `PartitionPrinciple_Geometry_GroundCompressionStarIncidence`, `PartitionPrinciple_Geometry_GroundContainmentOrders`, `PartitionPrinciple_Geometry_GroundExternalAlphabetInversion`, `PartitionPrinciple_Geometry_GroundExternalGenerators`, `PartitionPrinciple_Geometry_GroundExternalLocalHeightSelection`, `PartitionPrinciple_Geometry_GroundExternalRequestOverlaps`, `PartitionPrinciple_Geometry_GroundExternalRewriteSteps`, `PartitionPrinciple_Geometry_GroundExternalTileSlotSupports`, `PartitionPrinciple_Geometry_GroundFairPreparationMonotonicity`, `PartitionPrinciple_Geometry_GroundFinalInsertionExceptions`, `PartitionPrinciple_Geometry_GroundFiniteWordLaws`, `PartitionPrinciple_Geometry_GroundHeightPushforward`, `PartitionPrinciple_Geometry_GroundIndexedClassInclusions`, `PartitionPrinciple_Geometry_GroundIndexedMixedOperationLifts`, `PartitionPrinciple_Geometry_GroundIndexedOperationLifts`, `PartitionPrinciple_Geometry_GroundInitialCompressionOrigin`, `PartitionPrinciple_Geometry_GroundLiftedCompressionGraphs`, `PartitionPrinciple_Geometry_GroundMainFinalSeparatedActors`, `PartitionPrinciple_Geometry_GroundMeetGeneratorSteps`, `PartitionPrinciple_Geometry_GroundPreparationFamilyImages`, `PartitionPrinciple_Geometry_GroundSingleAttachment`, `PartitionPrinciple_Geometry_GroundTaskRepresentativeRecognition`, `PartitionPrinciple_Geometry_GroundTileStarIncidence`, `PartitionPrinciple_Geometry_GroundVisibilitySupportIncidence`, `PartitionPrinciple_Geometry_GrowthLayerSourceCongruence`, `PartitionPrinciple_Geometry_HeightColumnBoundLaws`, `PartitionPrinciple_Geometry_InitialCompressionAccounting`, `PartitionPrinciple_Geometry_LiftedCompressionEmbeddings`, `PartitionPrinciple_Geometry_LiftedCompressionFunctions`, `PartitionPrinciple_Geometry_RectangleFulfillmentAtBound`, `PartitionPrinciple_Geometry_RepresentativeIndexSteps`, `PartitionPrinciple_Geometry_SeparationTileCodes`, `PartitionPrinciple_Geometry_TemplateHeightRangeCodes`, `PartitionPrinciple_Geometry_TileStarIncomingCodes`, `PartitionPrinciple_Geometry_UniformAtomicEquality`, `PartitionPrinciple_Models_GroundCoherentHeightChoices`, `PartitionPrinciple_Models_GroundExternalWordQuotient`, `PartitionPrinciple_Models_GroundInjectionRestrictions`, `PartitionPrinciple_Models_GroundQuotientBinaryOperations`, `PartitionPrinciple_Models_GroundSuccessorInjections`, `PartitionPrinciple_Transfinite_ExternalChronologyStageLaws`, `PartitionPrinciple_Transfinite_GroundBatchBirths`, `PartitionPrinciple_Transfinite_GroundChronologyPairs`, `PartitionPrinciple_Transfinite_GroundCompressionBirthData`, `PartitionPrinciple_Transfinite_GroundCountableFunctionClosure`, `PartitionPrinciple_Transfinite_GroundCountableLayerCodes`, `PartitionPrinciple_Transfinite_GroundCountableProducts`, `PartitionPrinciple_Transfinite_GroundInitialCompressionHistory`, `PartitionPrinciple_Transfinite_GroundInvariantSuccessors`, `PartitionPrinciple_Transfinite_GroundLinkedMainStageCodeLaws`, `PartitionPrinciple_Transfinite_GroundMainPrefixDecoding`, `PartitionPrinciple_Transfinite_GroundMainPrefixLimitGroupLaws`, `PartitionPrinciple_Transfinite_GroundMainStageCandidates`, `PartitionPrinciple_Transfinite_GroundMainStageFromCodes`, `PartitionPrinciple_Transfinite_GroundNaturalRecursion`, `PartitionPrinciple_Transfinite_GroundOrdinalOrderCodes`, `PartitionPrinciple_Transfinite_GroundSerializedChronologyTimeEquality`, `PartitionPrinciple_Transfinite_GroundStageOneOrder`, `PartitionPrinciple_Transfinite_GroundStandardInaccessible`, `PartitionPrinciple_Transfinite_GroundStrongLimitPowers`, `PartitionPrinciple_Transfinite_GroundStructuralHistoryTestUnions`, `PartitionPrinciple_Transfinite_GroundTaskBearingSuccessorDecoding`, `PartitionPrinciple_Transfinite_NonzeroLimitOrdinalCodes`, `PartitionPrinciple_Transfinite_OwnerBirthLayers`, `PartitionPrinciple_Transfinite_RecursiveLiftAgreement`, `PartitionPrinciple_Transfinite_RecursiveNextMapInputs`, `PartitionPrinciple_Transfinite_RecursiveStateFieldEnvironments`, `PartitionPrinciple_Transfinite_RefinementHistoryPrefixLevels`, `PartitionPrinciple_Transfinite_SerializedChronologyCodes`, `PartitionPrinciple_Transfinite_SmallTileHeightInputs`, `PartitionPrinciple_Transfinite_StageOneDataBoundLaws`.
--
--   **Imports.** It imports the published bundle `Def_PartitionPrinciple`; the bundles `OAIQ253P000` and `OAIQ253P001` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ253P004` and `OAIQ253P005`.
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
import Definitions.Def_OAIQ253P000
import Definitions.Def_OAIQ253P001

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Definability_CountableSetFormulas
attribute [-instance] _root_.OAI.PartitionPilot.Forcing.GroundMainPrefix.withTopSmall
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace PartitionPilot.Forcing



namespace SetFormula

universe u

theorem extend_liftIndex {n m : Nat} {A : Type u} (f : Fin n → Fin m)
    (x : A) (env : Fin m → A) :
    (fun i => extend x env (liftIndex f i)) = extend x (fun i => env (f i)) := by
  funext i
  refine Fin.cases ?_ (fun j => ?_) i <;> rfl

def reindex : {n m : Nat} → (Fin n → Fin m) → SetFormula n → SetFormula m
  | _, _, f, .equal i j => .equal (f i) (f j)
  | _, _, f, .mem i j => .mem (f i) (f j)
  | _, _, f, .neg φ => .neg (reindex f φ)
  | _, _, f, .conj φ ψ => .conj (reindex f φ) (reindex f ψ)
  | _, _, f, .all φ => .all (reindex (liftIndex f) φ)

end SetFormula



end PartitionPilot.Forcing

end OAI
end

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

theorem pair_mem_graphRestriction {A f x y : ZFSet.{u}} :
    ZFSet.pair x y ∈ graphRestriction A f ↔ ZFSet.pair x y ∈ f ∧ x ∈ A := by
  constructor
  · intro h
    exact ⟨(ZFSet.mem_sep.1 h).1, (ZFSet.pair_mem_prod.1 (ZFSet.mem_sep.1 h).2).1⟩
  · rintro ⟨entry, hx⟩
    exact ZFSet.mem_sep.2 ⟨entry, ZFSet.pair_mem_prod.2
      ⟨hx, pair_second_mem_doubleUnion entry⟩⟩

theorem mem_graphRestriction {A f z : ZFSet.{u}} :
    z ∈ graphRestriction A f ↔ ∃ x ∈ A, ∃ y, z = ZFSet.pair x y ∧ ZFSet.pair x y ∈ f := by
  constructor
  · intro h
    obtain ⟨x, hx, y, _, rfl⟩ := ZFSet.mem_prod.1 (ZFSet.mem_sep.1 h).2
    exact ⟨x, hx, y, rfl, (ZFSet.mem_sep.1 h).1⟩
  · rintro ⟨x, hx, y, rfl, entry⟩
    exact pair_mem_graphRestriction.2 ⟨entry, hx⟩

namespace FunctionGraphOn

theorem restrict {A B f : ZFSet.{u}} (h : FunctionGraphOn A f) (subset : B ⊆ A) :
    FunctionGraphOn B (graphRestriction B f) := by
  refine ⟨⋃₀ ⋃₀ f, ?_, ?_⟩
  · intro z hz
    exact (ZFSet.mem_sep.1 hz).2
  · intro x hx
    obtain ⟨y, entry⟩ := h.total (subset hx)
    refine ⟨y, pair_mem_graphRestriction.2 ⟨entry, hx⟩, ?_⟩
    intro z hz
    exact h.unique (pair_mem_graphRestriction.1 hz).1 entry

theorem restriction_eq {A f : ZFSet.{u}} (h : FunctionGraphOn A f) :
    graphRestriction A f = f := by
  apply ZFSet.ext
  intro z
  constructor
  · exact fun hz => graphRestriction_subset A f hz
  · intro hz
    exact ZFSet.mem_sep.2 ⟨hz, h.to_isFunc.1 hz⟩

theorem eq_of_agree {A f g : ZFSet.{u}} (hf : FunctionGraphOn A f)
    (hg : FunctionGraphOn A g)
    (agree : ∀ x y z, ZFSet.pair x y ∈ f → ZFSet.pair x z ∈ g → y = z) : f = g := by
  apply ZFSet.ext
  intro z
  constructor
  · intro hz
    obtain ⟨x, hx, y, _, rfl⟩ := ZFSet.mem_prod.1 (hf.to_isFunc.1 hz)
    obtain ⟨w, hw⟩ := hg.total hx
    exact (agree x y w hz hw).symm ▸ hw
  · intro hz
    obtain ⟨x, hx, y, _, rfl⟩ := ZFSet.mem_prod.1 (hg.to_isFunc.1 hz)
    obtain ⟨w, hw⟩ := hf.total hx
    exact agree x w y hw hz ▸ hw

theorem insert {A f x : ZFSet.{u}} (h : FunctionGraphOn A f) (fresh : x ∉ A)
    (y : ZFSet.{u}) : FunctionGraphOn (Insert.insert x A) (Insert.insert (ZFSet.pair x y) f) := by
  classical
  refine ⟨Insert.insert y (⋃₀ ⋃₀ f), ?_, ?_⟩
  · intro z hz
    rcases ZFSet.mem_insert_iff.1 hz with rfl | hz
    · exact ZFSet.pair_mem_prod.2
        ⟨ZFSet.mem_insert_iff.2 (Or.inl rfl), ZFSet.mem_insert_iff.2 (Or.inl rfl)⟩
    · obtain ⟨a, ha, b, hb, rfl⟩ := ZFSet.mem_prod.1 (h.to_isFunc.1 hz)
      exact ZFSet.pair_mem_prod.2
        ⟨ZFSet.mem_insert_iff.2 (Or.inr ha), ZFSet.mem_insert_iff.2 (Or.inr hb)⟩
  · intro a ha
    rcases ZFSet.mem_insert_iff.1 ha with rfl | ha
    · refine ⟨y, ZFSet.mem_insert_iff.2 (Or.inl rfl), ?_⟩
      intro b hb
      rcases ZFSet.mem_insert_iff.1 hb with eq | hb
      · exact (ZFSet.pair_inj.1 eq).2
      · exact False.elim (fresh (h.pair_source hb))
    · obtain ⟨b, entry⟩ := h.total ha
      refine ⟨b, ZFSet.mem_insert_iff.2 (Or.inr entry), ?_⟩
      intro c hc
      rcases ZFSet.mem_insert_iff.1 hc with eq | hc
      · exact False.elim (fresh ((ZFSet.pair_inj.1 eq).1 ▸ ha))
      · exact h.unique hc entry

end FunctionGraphOn

end PartitionPilot.Forcing



end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Definability_NaturalSetCodes
attribute [-instance] _root_.OAI.PartitionPilot.Forcing.GroundMainPrefix.withTopSmall
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section



namespace PartitionPilot.Forcing

universe u

theorem natSetCode_zero : natSetCode 0 = (∅ : ZFSet.{u}) := rfl

end PartitionPilot.Forcing

end

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Definability_PresentedGroupCodes
attribute [-instance] _root_.OAI.PartitionPilot.Forcing.GroundMainPrefix.withTopSmall
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI



namespace PartitionPilot.Forcing.BoundedFormula

open SetFormula SetRealization
universe u

def ordinalFormula {n} (x : Fin n) : BoundedFormula n :=
  .conj (setTransitiveFormula x) (.allMem x (setTransitiveFormula 0))

theorem truth_ordinalFormula {n} (x : Fin n) (env : Fin n → ZFSet.{u}) :
    Truth (ordinalFormula x) env ↔ ∃ o : Ordinal.{u}, env x = ordinalCode o := by
  simp only [ordinalFormula, Truth, truth_setTransitiveFormula]
  exact ordinalSetProperty_iff (env x)

theorem realize_ordinalFormula (M : TransitiveGround.{u}) {n}
    (x : Fin n) (env : Fin n → ZFSet.{u}) (members : ∀ i, env i ∈ M.sets) :
    Realize M.sets (ordinalFormula x).toFormula env ↔ ∃ o : Ordinal.{u}, env x = ordinalCode o :=
  (realize_toFormula M _ env members).trans (truth_ordinalFormula x env)

end PartitionPilot.Forcing.BoundedFormula



section

namespace PartitionPilot.Forcing.BoundedFormula

open SetFormula
universe u

theorem truth_functionFormula {n} (a b f : Fin n) (env : Fin n → ZFSet.{u}) :
    Truth (functionFormula a b f) env ↔ ZFSet.IsFunc (env a) (env b) (env f) := by
  simp only [functionFormula, Truth, truth_relationBetweenFormula, truth_exMem,
    truth_pairMembershipFormula, truth_imp]
  constructor
  · rintro ⟨shape, total⟩
    refine ⟨shape, ?_⟩
    intro x hx
    obtain ⟨y, _, pair, unique⟩ := total x hx
    refine ⟨y, pair, ?_⟩
    intro z rel
    exact unique z (ZFSet.pair_mem_prod.1 (shape rel)).2 rel
  · rintro ⟨shape, total⟩
    refine ⟨shape, ?_⟩
    intro x hx
    obtain ⟨y, rel, unique⟩ := total x hx
    exact ⟨y, (ZFSet.pair_mem_prod.1 (shape rel)).2, rel, fun z _ hz => unique z hz⟩

end PartitionPilot.Forcing.BoundedFormula

end


namespace PartitionPilot.Forcing.BoundedFormula

open SetFormula
universe u

theorem truth_nestedActionTripleFormula {n} (z g a b c d : Fin n)
    (env : Fin n → ZFSet.{u}) :
    Truth (nestedActionTripleFormula z g a b c d) env ↔
      env z = ZFSet.pair (ZFSet.pair (env g) (ZFSet.pair (env a) (env b)))
        (ZFSet.pair (env c) (env d)) := by
  simp only [nestedActionTripleFormula, truth_exMem, Truth, truth_orderedPairFormula]
  change (∃ s ∈ env z, ∃ x ∈ s, ∃ t ∈ env z, ∃ y ∈ t,
    env z = ZFSet.pair x y ∧ y = ZFSet.pair (env c) (env d) ∧
      ∃ w ∈ x, ∃ v ∈ w, x = ZFSet.pair (env g) v ∧ v = ZFSet.pair (env a) (env b)) ↔ _
  constructor
  · rintro ⟨_, _, x, _, _, _, y, _, outer, hy, _, _, v, _, hx, hv⟩
    rw [outer, hy, hx, hv]
  · intro equal
    let v := ZFSet.pair (env a) (env b)
    let x := ZFSet.pair (env g) v
    let y := ZFSet.pair (env c) (env d)
    refine ⟨{x}, ?_, x, ZFSet.mem_singleton.2 rfl, {x, y}, ?_, y,
      ZFSet.mem_pair.2 (Or.inr rfl), equal, rfl, {env g, v},
      ZFSet.mem_pair.2 (Or.inr rfl), v, ZFSet.mem_pair.2 (Or.inr rfl), rfl, rfl⟩
    · rw [equal]
      exact ZFSet.mem_pair.2 (Or.inl rfl)
    · rw [equal]
      exact ZFSet.mem_pair.2 (Or.inr rfl)






end PartitionPilot.Forcing.BoundedFormula



namespace PartitionPilot.Forcing

universe u

namespace BoundedFormula

open SetFormula

def groupIdentityFormula {n} (g m e : Fin n) : BoundedFormula n :=
  .allMem g (.conj (tripleMembershipFormula e.succ 0 0 m.succ)
    (tripleMembershipFormula 0 e.succ 0 m.succ))

def groupInverseFormula {n} (g m i e : Fin n) : BoundedFormula n :=
  .allMem g (.allMem g.succ (imp (pairMembershipFormula 1 0 i.succ.succ)
    (tripleMembershipFormula 0 1 e.succ.succ m.succ.succ)))

def groupAssociativeFormula {n} (g m : Fin n) : BoundedFormula n :=
  .allMem g (.allMem g.succ (.allMem g.succ.succ (.allMem g.succ.succ.succ
    (.allMem g.succ.succ.succ.succ (.allMem g.succ.succ.succ.succ.succ
      (imp (.conj (tripleMembershipFormula 5 4 2 m.succ.succ.succ.succ.succ.succ)
        (.conj (tripleMembershipFormula 4 3 1 m.succ.succ.succ.succ.succ.succ)
          (tripleMembershipFormula 2 3 0 m.succ.succ.succ.succ.succ.succ)))
        (tripleMembershipFormula 5 1 0 m.succ.succ.succ.succ.succ.succ)))))))

def groupFormula {n} (g m i e : Fin n) : BoundedFormula n :=
  .conj (binaryFunctionFormula g m) (.conj (functionFormula g g i)
    (.conj (.mem e g) (.conj (groupIdentityFormula g m e)
      (.conj (groupInverseFormula g m i e) (groupAssociativeFormula g m)))))

end BoundedFormula

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


section

namespace PartitionPilot.Forcing.TransitiveGround

open SetFormula
universe u
variable (M : TransitiveGround.{u})

theorem groundPower_mem (powers : Realize M.sets powerSet Fin.elim0)
    {B : ZFSet.{u}} (hB : B ∈ M.sets) : M.groundPower B ∈ M.sets := by
  obtain ⟨W, hW, spec⟩ := M.power_witness powers hB
  have eq : W = M.groundPower B := by
    apply ZFSet.ext
    intro p
    rw [M.mem_groundPower]
    exact ⟨fun hp => ⟨M.transitive hW hp, (spec p (M.transitive hW hp)).1 hp⟩,
      fun ⟨hp, subset⟩ => (spec p hp).2 subset⟩
  exact eq ▸ hW

theorem groundRelations_mem
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    {A B : ZFSet.{u}} (hA : A ∈ M.sets) (hB : B ∈ M.sets) : M.groundRelations A B ∈ M.sets :=
  M.groundPower_mem powers (M.prod_mem pairing unions powers separation hA hB)

end PartitionPilot.Forcing.TransitiveGround

end


namespace PartitionPilot.Forcing

universe u

namespace BoundedFormula

open SetFormula

theorem truth_partialFunctionFormula {n} (x y p : Fin n) (env : Fin n → ZFSet.{u}) :
    Truth (partialFunctionFormula x y p) env ↔ PartialFunctionCode (env x) (env y) (env p) := by
  simp only [partialFunctionFormula, Truth, truth_relationBetweenFormula, truth_imp, truth_pairMembershipFormula]
  constructor
  · rintro ⟨shape, unique⟩
    refine ⟨shape, ?_⟩
    intro a b c hb hc
    have ab := ZFSet.pair_mem_prod.1 (shape hb)
    have ac := ZFSet.pair_mem_prod.1 (shape hc)
    exact unique a ab.1 b ab.2 c ac.2 ⟨hb, hc⟩
  · intro h
    exact ⟨h.shape, fun a _ b _ c _ ⟨hb, hc⟩ => h.unique a b c hb hc⟩

end BoundedFormula

end PartitionPilot.Forcing



namespace PartitionPilot.Forcing
open SetRealization SetFormula
universe u
namespace BoundedFormula

theorem truth_familySetEntryFormula {n} (z T one : Fin n) (env : Fin n → ZFSet.{u}) :
    Truth (familySetEntryFormula z T one) env ↔ env z ∈ ZFSet.prod (env T) {env one} := by
  rw [familySetEntryFormula, truth_exMem]
  simp only [truth_orderedPairFormula]
  change (∃ x ∈ env T, env z = ZFSet.pair x (env one)) ↔ _
  constructor
  · rintro ⟨x, hx, equal⟩
    rw [equal]
    exact ZFSet.pair_mem_prod.2 ⟨hx, ZFSet.mem_singleton.2 rfl⟩
  · intro member
    obtain ⟨x, hx, y, hy, equal⟩ := ZFSet.mem_prod.1 member
    have same := ZFSet.mem_singleton.1 hy
    rw [same] at equal
    exact ⟨x, hx, equal⟩

end BoundedFormula

end PartitionPilot.Forcing



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

namespace BoundedFormula

open SetFormula

theorem truth_injectionFormula {n} (d c f : Fin n) (env : Fin n → ZFSet.{u}) :
    Truth (injectionFormula d c f) env ↔ InjectionCode (env d) (env c) (env f) := by
  simp only [injectionFormula, Truth, truth_functionFormula, truth_imp, truth_pairMembershipFormula]
  constructor
  · rintro ⟨function, injective⟩
    refine ⟨function, ?_⟩
    intro x y z hx hy
    have xz := ZFSet.pair_mem_prod.1 (function.1 hx)
    have yz := ZFSet.pair_mem_prod.1 (function.1 hy)
    exact injective x xz.1 y yz.1 z xz.2 ⟨hx, hy⟩
  · intro h
    exact ⟨h.function, fun x _ y _ z _ ⟨hx, hy⟩ => h.injective x y z hx hy⟩

end BoundedFormula

end PartitionPilot.Forcing

end

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Models_GroundInjectionRestrictions
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

theorem injection_restriction_mem (separation : SeparationSchema M.sets)
    {Q N f : ZFSet.{u}} (hQ : Q ∈ M.sets) (hN : N ∈ M.sets) (hf : f ∈ M.sets) :
    ZFSet.sep (fun z => z ∈ ZFSet.prod Q N) f ∈ M.sets := by
  let params := extend Q (extend N Fin.elim0)
  have selected := M.separation_mem separation (BoundedFormula.productElementFormula 0 1 2).toFormula
    params (Fin.cases hQ (Fin.cases hN (fun j => Fin.elim0 j))) hf
  have eq : ZFSet.sep (fun z => Realize M.sets
      (BoundedFormula.productElementFormula 0 1 2).toFormula (extend z params)) f =
        ZFSet.sep (fun z => z ∈ ZFSet.prod Q N) f := by
    apply ZFSet.ext
    intro z
    rw [ZFSet.mem_sep, ZFSet.mem_sep]
    constructor
    · rintro ⟨hz, rel⟩
      exact ⟨hz, (BoundedFormula.truth_productElementFormula 0 1 2 _).1
        ((BoundedFormula.realize_toFormula M _ _ (Fin.cases (M.transitive hf hz)
          (Fin.cases hQ (Fin.cases hN (fun j => Fin.elim0 j))))).1 rel)⟩
    · rintro ⟨hz, rel⟩
      exact ⟨hz, (BoundedFormula.realize_toFormula M _ _ (Fin.cases (M.transitive hf hz)
        (Fin.cases hQ (Fin.cases hN (fun j => Fin.elim0 j))))).2
          ((BoundedFormula.truth_productElementFormula 0 1 2 _).2 rel)⟩
  exact eq ▸ selected

theorem groundEmbeddable_restrict (separation : SeparationSchema M.sets)
    {D Q N : ZFSet.{u}} (hQ : Q ∈ M.sets) (hN : N ∈ M.sets) (subset : Q ⊆ D)
    (small : M.groundEmbeddable D N) : M.groundEmbeddable Q N := by
  obtain ⟨f, hf, code⟩ := small
  exact ⟨ZFSet.sep (fun z => z ∈ ZFSet.prod Q N) f,
    M.injection_restriction_mem separation hQ hN hf, code.restrict subset⟩

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

namespace BoundedFormula

open SetFormula

theorem truth_nonemptyTupleFormula (k : Nat) {n : Nat} (z : Fin n)
    (fields : Fin (k + 1) → Fin n) (env : Fin n → ZFSet.{u}) :
    Truth (nonemptyTupleFormula k z fields) env ↔
      env z = nonemptyTupleCode k (fun i => env (fields i)) := by
  induction k generalizing n with
  | zero => rfl
  | succ k ih =>
    simp only [nonemptyTupleFormula, truth_exMem, Truth, truth_orderedPairFormula, ih]
    change (∃ a ∈ env z, ∃ b ∈ a, env z = ZFSet.pair (env (fields 0)) b ∧
      b = nonemptyTupleCode k (fun i => env (fields i.succ))) ↔ _
    constructor
    · rintro ⟨_, _, b, _, outer, tail⟩
      rw [outer, tail]
      rfl
    · intro equal
      let tail := nonemptyTupleCode k (fun i => env (fields i.succ))
      have outer : env z = ZFSet.pair (env (fields 0)) tail := equal
      refine ⟨{env (fields 0), tail}, ?_, tail, ZFSet.mem_pair.2 (Or.inr rfl), outer, rfl⟩
      rw [outer]
      exact ZFSet.mem_pair.2 (Or.inr rfl)

end BoundedFormula

end PartitionPilot.Forcing



namespace PartitionPilot.Forcing.BoundedFormula
open SetFormula
universe u

theorem truth_reindex {n m} (f : Fin n → Fin m) (φ : BoundedFormula n)
    (env : Fin m → ZFSet.{u}) :
    Truth (reindex f φ) env ↔ Truth φ (fun i => env (f i)) := by
  induction φ generalizing m with
  | equal i j => rfl
  | mem i j => rfl
  | neg φ ih => exact not_congr (ih f env)
  | conj φ ψ ihφ ihψ => exact and_congr (ihφ f env) (ihψ f env)
  | allMem b φ ih =>
    change (∀ x ∈ env (f b), Truth (reindex (liftIndex f) φ) (extend x env)) ↔ _
    apply forall_congr'
    intro x
    apply forall_congr'
    intro _
    rw [ih, extend_liftIndex]

theorem truth_exPairFields {n} (z : Fin n) (body : BoundedFormula (n + 2))
    (env : Fin n → ZFSet.{u}) :
    Truth (exPairFields z body) env ↔
      ∃ x y, env z = ZFSet.pair x y ∧ Truth body (extend y (extend x env)) := by
  simp only [exPairFields, truth_exMem, Truth, truth_orderedPairFormula, truth_reindex]
  have rearrange (a x b y : ZFSet.{u}) :
      (fun i => extend y (extend b (extend x (extend a env)))
        (Fin.cases 0 (Fin.cases 2 (fun j => j.succ.succ.succ.succ)) i)) =
        extend y (extend x env) := by
    funext i
    refine Fin.cases ?_ (fun j => Fin.cases ?_ (fun k => ?_) j) i <;> rfl
  simp only [rearrange]
  change (∃ a ∈ env z, ∃ x ∈ a, ∃ b ∈ env z, ∃ y ∈ b,
    env z = ZFSet.pair x y ∧ Truth body (extend y (extend x env))) ↔ _
  constructor
  · rintro ⟨a, _, x, _, b, _, y, _, equal, holds⟩
    exact ⟨x, y, equal, holds⟩
  · rintro ⟨x, y, equal, holds⟩
    have both : ({x, y} : ZFSet.{u}) ∈ env z := by
      rw [equal]
      exact ZFSet.mem_pair.2 (Or.inr rfl)
    exact ⟨{x,y}, both, x, ZFSet.mem_pair.2 (Or.inl rfl),
      {x,y}, both, y, ZFSet.mem_pair.2 (Or.inr rfl), equal, holds⟩

def tupleShapeFormula : (k : Nat) → {n : Nat} → Fin n → BoundedFormula n
  | 0, _, z => .equal z z
  | k + 1, _, z => exPairFields z (tupleShapeFormula k 0)

theorem truth_tupleShapeFormula (k : Nat) {n} (z : Fin n) (env : Fin n → ZFSet.{u}) :
    Truth (tupleShapeFormula k z) env ↔ ∃ fields, env z = nonemptyTupleCode k fields := by
  induction k generalizing n with
  | zero =>
    change env z = env z ↔ ∃ fields : Fin 1 → ZFSet.{u}, env z = fields 0
    exact ⟨fun _ => ⟨fun _ => env z, rfl⟩, fun _ => rfl⟩
  | succ k ih =>
    rw [tupleShapeFormula, truth_exPairFields]
    constructor
    · rintro ⟨x, y, equal, shape⟩
      obtain ⟨fields, tail⟩ := (ih 0 (extend y (extend x env))).1 shape
      refine ⟨Fin.cases x fields, ?_⟩
      change env z = ZFSet.pair x (nonemptyTupleCode k fields)
      exact equal.trans (congrArg (ZFSet.pair x) tail)
    · rintro ⟨fields, equal⟩
      exact ⟨fields 0, nonemptyTupleCode k (fun i => fields i.succ), equal,
        (ih 0 _).2 ⟨fun i => fields i.succ, rfl⟩⟩

end PartitionPilot.Forcing.BoundedFormula



namespace PartitionPilot.Forcing
universe u

noncomputable def refinementIndexCode (level C E U Rf Rc : ZFSet.{u}) : ZFSet.{u} :=
  nonemptyTupleCode 5 ![level, C, E, U, Rf, Rc]

namespace BoundedFormula

def refinementIndexFormula {n : Nat} (z level C E U Rf Rc : Fin n) : BoundedFormula n :=
  nonemptyTupleFormula 5 z ![level, C, E, U, Rf, Rc]

theorem truth_refinementIndexFormula {n : Nat} (z level C E U Rf Rc : Fin n)
    (env : Fin n → ZFSet.{u}) :
    Truth (refinementIndexFormula z level C E U Rf Rc) env ↔
      env z = refinementIndexCode (env level) (env C) (env E) (env U) (env Rf) (env Rc) := by
  rw [refinementIndexFormula, truth_nonemptyTupleFormula]
  rfl

end BoundedFormula

end PartitionPilot.Forcing



namespace PartitionPilot.Forcing
open SetFormula
open scoped ZFSet
universe u

theorem nonemptyTupleCode_field_mem_bound (k : Nat) (fields : Fin (k + 1) → ZFSet.{u})
    {B : ZFSet.{u}} (member : nonemptyTupleCode k fields ∈ B) :
    ∀ j, fields j ∈ tupleFieldBound k B := by
  induction k generalizing B with
  | zero => exact Fin.cases member (fun j => Fin.elim0 j)
  | succ k ih =>
    have pair : ZFSet.pair (fields 0) (nonemptyTupleCode k (fun j => fields j.succ)) ∈ B := member
    exact Fin.cases (ZFSet.mem_union.2 (Or.inl (pair_first_mem_doubleUnion pair)))
      (fun j => ZFSet.mem_union.2 (Or.inr (ih _ (pair_second_mem_doubleUnion pair) j)))

namespace BoundedFormula
noncomputable def tupleFieldFormula : (k : Nat) → {n : Nat} → Fin n → Fin n → Fin (k + 1) → BoundedFormula n
  | 0, _, z, y, _ => .equal y z
  | k + 1, _, z, y, j => exPairFields z
      (Fin.cases (.conj (.equal y.succ.succ 1) (tupleShapeFormula k 0))
        (fun i => tupleFieldFormula k 0 y.succ.succ i) j)

theorem truth_tupleFieldFormula (k : Nat) {n : Nat} (z y : Fin n) (j : Fin (k + 1))
    (env : Fin n → ZFSet.{u}) :
    Truth (tupleFieldFormula k z y j) env ↔
      ∃ fields : Fin (k + 1) → ZFSet.{u}, env z = nonemptyTupleCode k fields ∧ env y = fields j := by
  induction k generalizing n with
  | zero =>
    change env y = env z ↔ ∃ fields : Fin 1 → ZFSet.{u}, env z = fields 0 ∧ env y = fields j
    constructor
    · intro equal
      exact ⟨fun _ => env z, rfl, equal⟩
    · rintro ⟨fields, first, second⟩
      have eq : j = 0 := Fin.cases rfl (fun i => Fin.elim0 i) j
      exact (eq ▸ second).trans first.symm
  | succ k ih =>
    rw [tupleFieldFormula, truth_exPairFields]
    refine Fin.cases ?_ (fun i => ?_) j
    · simp only [Fin.cases_zero, Truth, truth_tupleShapeFormula]
      constructor
      · rintro ⟨head, tail, pair, value, fields, tuple⟩
        let all : Fin (k + 2) → ZFSet.{u} := Fin.cases head fields
        refine ⟨all, ?_, ?_⟩
        · change env z = ZFSet.pair head (nonemptyTupleCode k fields)
          exact pair.trans (congrArg (ZFSet.pair head) tuple)
        · exact value
      · rintro ⟨fields, pair, value⟩
        exact ⟨fields 0, nonemptyTupleCode k (fun i => fields i.succ), pair,
          value, fun i => fields i.succ, rfl⟩
    · simp only [Fin.cases_succ, ih]
      constructor
      · rintro ⟨head, tail, pair, fields, tuple, value⟩
        let all : Fin (k + 2) → ZFSet.{u} := Fin.cases head fields
        refine ⟨all, ?_, ?_⟩
        · change env z = ZFSet.pair head (nonemptyTupleCode k fields)
          exact pair.trans (congrArg (ZFSet.pair head) tuple)
        · exact value
      · rintro ⟨fields, pair, value⟩
        exact ⟨fields 0, nonemptyTupleCode k (fun i => fields i.succ), pair,
          fun i => fields i.succ, rfl, value⟩

end BoundedFormula

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

universe u

theorem relationImage_restrict (D B r : ZFSet.{u}) :
    relationImage D B (ZFSet.sep (fun z => z ∈ ZFSet.prod D B) r) = relationImage D B r := by
  apply ZFSet.ext
  intro y
  rw [mem_relationImage, mem_relationImage]
  constructor
  · rintro ⟨hy, x, hx, rel⟩
    exact ⟨hy, x, hx, (ZFSet.mem_sep.1 rel).1⟩
  · rintro ⟨hy, x, hx, rel⟩
    exact ⟨hy, x, hx, ZFSet.mem_sep.2 ⟨rel, ZFSet.pair_mem_prod.2 ⟨hx, hy⟩⟩⟩

namespace InjectionCode

theorem converse_image {A B r : ZFSet.{u}} (h : InjectionCode A B r) :
    InjectionCode (relationImage A B r) A (relationConverse A B r) := by
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · intro z hz
    obtain ⟨x, hx, y, hy, eq, rel⟩ := (mem_relationConverse A B r z).1 hz
    exact eq.symm ▸ ZFSet.pair_mem_prod.2
      ⟨(mem_relationImage A B r y).2 ⟨hy, x, hx, rel⟩, hx⟩
  · intro y hy
    obtain ⟨hyB, x, hx, rel⟩ := (mem_relationImage A B r y).1 hy
    refine ⟨x, (pair_mem_relationConverse A B r x y).2 ⟨hx, hyB, rel⟩, ?_⟩
    intro z hz
    exact h.injective z x y ((pair_mem_relationConverse A B r z y).1 hz).2.2 rel
  · intro x y z hx hy
    have zx := (pair_mem_relationConverse A B r z x).1 hx
    have zy := (pair_mem_relationConverse A B r z y).1 hy
    obtain ⟨w, _, unique⟩ := h.function.2 z zx.1
    exact (unique x zx.2.2).trans (unique y zy.2.2).symm

end InjectionCode

end PartitionPilot.Forcing



section

namespace PartitionPilot.Forcing.BoundedFormula

open SetFormula
universe u

theorem truth_imageMemberFormula {n} (y d r : Fin n) (env : Fin n → ZFSet.{u}) :
    Truth (imageMemberFormula y d r) env ↔ ∃ x ∈ env d, ZFSet.pair x (env y) ∈ env r := by
  simp only [imageMemberFormula, truth_exMem, truth_pairMembershipFormula]
  rfl

theorem truth_converseEntryFormula {n} (z a b r : Fin n) (env : Fin n → ZFSet.{u}) :
    Truth (converseEntryFormula z a b r) env ↔ ∃ x ∈ env a, ∃ y ∈ env b,
      env z = ZFSet.pair y x ∧ ZFSet.pair x y ∈ env r := by
  simp only [converseEntryFormula, truth_exMem, Truth,
    truth_orderedPairFormula, truth_pairMembershipFormula]
  rfl

theorem truth_composeEntryFormula {n} (z a b c r f : Fin n) (env : Fin n → ZFSet.{u}) :
    Truth (composeEntryFormula z a b c r f) env ↔ ∃ x ∈ env a, ∃ y ∈ env b, ∃ w ∈ env c,
      env z = ZFSet.pair x w ∧ ZFSet.pair x y ∈ env r ∧ ZFSet.pair y w ∈ env f := by
  simp only [composeEntryFormula, truth_exMem, Truth,
    truth_orderedPairFormula, truth_pairMembershipFormula]
  rfl

end PartitionPilot.Forcing.BoundedFormula

namespace PartitionPilot.Forcing.TransitiveGround

open SetFormula
universe u
variable (M : TransitiveGround.{u})

theorem relationImage_mem (separation : SeparationSchema M.sets)
    {D B r : ZFSet.{u}} (hD : D ∈ M.sets) (hB : B ∈ M.sets) (hr : r ∈ M.sets) :
    relationImage D B r ∈ M.sets := by
  let params := extend D (extend r Fin.elim0)
  have selected := M.bounded_separation_mem separation (BoundedFormula.imageMemberFormula 0 1 2)
    params (Fin.cases hD (Fin.cases hr (fun i => Fin.elim0 i))) hB
  have eq : ZFSet.sep (fun z => BoundedFormula.Truth (BoundedFormula.imageMemberFormula 0 1 2)
      (extend z params)) B = relationImage D B r := by
    apply ZFSet.ext
    intro z
    rw [ZFSet.mem_sep, mem_relationImage]
    exact and_congr Iff.rfl (BoundedFormula.truth_imageMemberFormula 0 1 2 _)
  exact eq ▸ selected

theorem relationConverse_mem
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    {A B r : ZFSet.{u}} (hA : A ∈ M.sets) (hB : B ∈ M.sets) (hr : r ∈ M.sets) :
    relationConverse A B r ∈ M.sets := by
  let params := extend A (extend B (extend r Fin.elim0))
  have selected := M.bounded_separation_mem separation (BoundedFormula.converseEntryFormula 0 1 2 3)
    params (Fin.cases hA (Fin.cases hB (Fin.cases hr (fun i => Fin.elim0 i))))
    (M.prod_mem pairing unions powers separation hB hA)
  have eq : ZFSet.sep (fun z => BoundedFormula.Truth (BoundedFormula.converseEntryFormula 0 1 2 3)
      (extend z params)) (ZFSet.prod B A) = relationConverse A B r := by
    apply ZFSet.ext
    intro z
    rw [ZFSet.mem_sep, relationConverse, ZFSet.mem_sep]
    exact and_congr Iff.rfl (BoundedFormula.truth_converseEntryFormula 0 1 2 3 _)
  exact eq ▸ selected

theorem relationCompose_mem
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    {A B C r f : ZFSet.{u}} (hA : A ∈ M.sets) (hB : B ∈ M.sets) (hC : C ∈ M.sets)
    (hr : r ∈ M.sets) (hf : f ∈ M.sets) : relationCompose A B C r f ∈ M.sets := by
  let params := extend A (extend B (extend C (extend r (extend f Fin.elim0))))
  have selected := M.bounded_separation_mem separation (BoundedFormula.composeEntryFormula 0 1 2 3 4 5)
    params (Fin.cases hA (Fin.cases hB (Fin.cases hC (Fin.cases hr
      (Fin.cases hf (fun i => Fin.elim0 i)))))) (M.prod_mem pairing unions powers separation hA hC)
  have eq : ZFSet.sep (fun z => BoundedFormula.Truth (BoundedFormula.composeEntryFormula 0 1 2 3 4 5)
      (extend z params)) (ZFSet.prod A C) = relationCompose A B C r f := by
    apply ZFSet.ext
    intro z
    rw [ZFSet.mem_sep, relationCompose, ZFSet.mem_sep]
    exact and_congr Iff.rfl (BoundedFormula.truth_composeEntryFormula 0 1 2 3 4 5 _)
  exact eq ▸ selected

theorem groundEmbeddable_image
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    {A B D N r : ZFSet.{u}} (hD : D ∈ M.sets) (hB : B ∈ M.sets) (hN : N ∈ M.sets)
    (hr : r ∈ M.sets) (code : InjectionCode A B r) (subset : D ⊆ A)
    (small : M.groundEmbeddable D N) : M.groundEmbeddable (relationImage D B r) N := by
  obtain ⟨f, hf, fcode⟩ := small
  let rD := ZFSet.sep (fun z => z ∈ ZFSet.prod D B) r
  have hrD := M.injection_restriction_mem separation hD hB hr
  have image := M.relationImage_mem separation hD hB hrD
  have inverse := M.relationConverse_mem pairing unions powers separation hD hB hrD
  have witness := M.relationCompose_mem pairing unions powers separation image hD hN inverse hf
  rw [← relationImage_restrict D B r]
  exact ⟨relationCompose (relationImage D B rD) D N (relationConverse D B rD) f,
    witness, (code.restrict subset).converse_image.compose fcode⟩

end PartitionPilot.Forcing.TransitiveGround

end



namespace PartitionPilot.Forcing
open SetFormula
universe u

namespace BoundedFormula

def flatCopyOrderEntryFormula {n} (z E U Q classifier r : Fin n) : BoundedFormula n :=
  exMem Q (exMem Q.succ (.conj (orderedPairFormula z.succ.succ 1 0)
    (exMem E.succ.succ (exMem U.succ.succ.succ (exMem U.succ.succ.succ.succ
      (.conj (pairMembershipFormula 1 0 r.succ.succ.succ.succ.succ)
        (.conj (tripleMembershipFormula 2 1 4 classifier.succ.succ.succ.succ.succ)
          (tripleMembershipFormula 2 0 3 classifier.succ.succ.succ.succ.succ))))))))

theorem truth_flatCopyOrderEntryFormula {n} (z E U Q classifier r : Fin n)
    (env : Fin n → ZFSet.{u}) :
    Truth (flatCopyOrderEntryFormula z E U Q classifier r) env ↔
      env z ∈ flatCopyOrderGraph (env E) (env U) (env Q) (env classifier) (env r) := by
  simp only [flatCopyOrderEntryFormula, truth_exMem, Truth, truth_orderedPairFormula,
    truth_pairMembershipFormula, truth_tripleMembershipFormula, mem_flatCopyOrderGraph]
  rfl

def flatCopyActionEntryFormula {n} (z E U Q classifier m : Fin n) : BoundedFormula n :=
  exMem E (exMem Q.succ (exMem Q.succ.succ (.conj (orderedTripleFormula z.succ.succ.succ 2 1 0)
    (exMem E.succ.succ.succ (exMem E.succ.succ.succ.succ (exMem U.succ.succ.succ.succ.succ
      (.conj (tripleMembershipFormula 5 2 1 m.succ.succ.succ.succ.succ.succ)
        (.conj (tripleMembershipFormula 2 0 4 classifier.succ.succ.succ.succ.succ.succ)
          (tripleMembershipFormula 1 0 3 classifier.succ.succ.succ.succ.succ.succ)))))))))

theorem truth_flatCopyActionEntryFormula {n} (z E U Q classifier m : Fin n)
    (env : Fin n → ZFSet.{u}) :
    Truth (flatCopyActionEntryFormula z E U Q classifier m) env ↔
      env z ∈ flatCopyActionGraph (env E) (env U) (env Q) (env classifier) (env m) := by
  simp only [flatCopyActionEntryFormula, truth_exMem, Truth, truth_orderedTripleFormula,
    truth_tripleMembershipFormula, mem_flatCopyActionGraph]
  rfl

end BoundedFormula





end PartitionPilot.Forcing



namespace PartitionPilot.Forcing
open SetFormula
open scoped ZFSet
universe u

noncomputable def functionGraphRange (A f : ZFSet.{u}) : ZFSet.{u} :=
  relationImage A (⋃₀ ⋃₀ f) f

theorem mem_functionGraphRange (A f y : ZFSet.{u}) :
    y ∈ functionGraphRange A f ↔ ∃ x ∈ A, ZFSet.pair x y ∈ f := by
  rw [functionGraphRange, mem_relationImage]
  exact ⟨And.right, fun h => ⟨pair_second_mem_doubleUnion h.choose_spec.2, h⟩⟩

end PartitionPilot.Forcing



end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Definability_GroundPairCompositions
attribute [-instance] _root_.OAI.PartitionPilot.Forcing.GroundMainPrefix.withTopSmall
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open scoped ZFSet


namespace PartitionPilot.Forcing.FunctionGraphOn

universe u
variable {I f : ZFSet.{u}}

theorem value_mem (h : FunctionGraphOn I f) (M : TransitiveGround.{u})
    (hf : f ∈ M.sets) (i : {i : ZFSet.{u} // i ∈ I}) : h.value i ∈ M.sets :=
  M.pair_right (M.transitive hf (h.value_entry i))





noncomputable def totalValue (function : FunctionGraphOn I f) (i : ZFSet.{u}) : ZFSet.{u} := by
  classical
  exact if hi : i ∈ I then function.value ⟨i, hi⟩ else ∅

theorem totalValue_entry (function : FunctionGraphOn I f) {i : ZFSet.{u}} (hi : i ∈ I) :
    ZFSet.pair i (function.totalValue i) ∈ f := by
  rw [totalValue, dite_eq_left hi]
  exact function.value_entry ⟨i, hi⟩

theorem totalValue_eq_of_entry (function : FunctionGraphOn I f) {i y : ZFSet.{u}}
    (entry : ZFSet.pair i y ∈ f) : function.totalValue i = y :=
  function.unique (function.totalValue_entry (function.pair_source entry)) entry

theorem totalValue_outside (function : FunctionGraphOn I f) {i : ZFSet.{u}} (hi : i ∉ I) :
    function.totalValue i = ∅ := by rw [totalValue, dite_eq_right hi]

theorem totalValue_ground (function : FunctionGraphOn I f) (M : TransitiveGround.{u})
    (hf : f ∈ M.sets) (i : ZFSet.{u}) : function.totalValue i ∈ M.sets := by
  classical
  by_cases hi : i ∈ I
  · exact M.pair_right (M.transitive hf (function.totalValue_entry hi))
  · rw [function.totalValue_outside hi]
    exact M.empty_mem ⟨f, hf⟩

end PartitionPilot.Forcing.FunctionGraphOn



namespace PartitionPilot.Forcing

open SetRealization
universe u

noncomputable def productFirst (A B : ZFSet.{u}) : ZFSet.{u} :=
  ((SetMembers.presentation A).product (SetMembers.presentation B)).graph (SetMembers.presentation A) Prod.fst

noncomputable def productSecond (A B : ZFSet.{u}) : ZFSet.{u} :=
  ((SetMembers.presentation A).product (SetMembers.presentation B)).graph (SetMembers.presentation B) Prod.snd

theorem mem_productFirst (A B z : ZFSet.{u}) : z ∈ productFirst A B ↔
    ∃ x ∈ A, ∃ y ∈ B, z = ZFSet.pair (ZFSet.pair x y) x := by
  rw [productFirst, Presentation.mem_graph]
  constructor
  · rintro ⟨⟨x, y⟩, eq⟩
    exact ⟨SetMembers.raw x, SetMembers.raw_mem x, SetMembers.raw y, SetMembers.raw_mem y, eq.symm⟩
  · rintro ⟨x, hx, y, hy, eq⟩
    refine ⟨(SetMembers.ofMem x hx, SetMembers.ofMem y hy), ?_⟩
    change ZFSet.pair (ZFSet.pair (SetMembers.raw _) (SetMembers.raw _)) (SetMembers.raw _) = z
    rw [SetMembers.raw_ofMem, SetMembers.raw_ofMem]
    exact eq.symm

theorem mem_productSecond (A B z : ZFSet.{u}) : z ∈ productSecond A B ↔
    ∃ x ∈ A, ∃ y ∈ B, z = ZFSet.pair (ZFSet.pair x y) y := by
  rw [productSecond, Presentation.mem_graph]
  constructor
  · rintro ⟨⟨x, y⟩, eq⟩
    exact ⟨SetMembers.raw x, SetMembers.raw_mem x, SetMembers.raw y, SetMembers.raw_mem y, eq.symm⟩
  · rintro ⟨x, hx, y, hy, eq⟩
    refine ⟨(SetMembers.ofMem x hx, SetMembers.ofMem y hy), ?_⟩
    change ZFSet.pair (ZFSet.pair (SetMembers.raw _) (SetMembers.raw _)) (SetMembers.raw _) = z
    rw [SetMembers.raw_ofMem, SetMembers.raw_ofMem]
    exact eq.symm

theorem productFirst_function (A B : ZFSet.{u}) : ZFSet.IsFunc (ZFSet.prod A B) A (productFirst A B) :=
  ((SetMembers.presentation A).product (SetMembers.presentation B)).graph_isFunc (SetMembers.presentation A) Prod.fst

theorem productSecond_function (A B : ZFSet.{u}) : ZFSet.IsFunc (ZFSet.prod A B) B (productSecond A B) :=
  ((SetMembers.presentation A).product (SetMembers.presentation B)).graph_isFunc (SetMembers.presentation B) Prod.snd

namespace BoundedFormula

open SetFormula

def productFirstEntryFormula {n} (z a b : Fin n) : BoundedFormula n :=
  exMem a (exMem b.succ (orderedTripleFormula z.succ.succ 1 0 1))

def productSecondEntryFormula {n} (z a b : Fin n) : BoundedFormula n :=
  exMem a (exMem b.succ (orderedTripleFormula z.succ.succ 1 0 0))

theorem truth_productFirstEntryFormula {n} (z a b : Fin n) (env : Fin n → ZFSet.{u}) :
    Truth (productFirstEntryFormula z a b) env ↔ env z ∈ productFirst (env a) (env b) := by
  simp only [productFirstEntryFormula, truth_exMem, truth_orderedTripleFormula, mem_productFirst]
  rfl

theorem truth_productSecondEntryFormula {n} (z a b : Fin n) (env : Fin n → ZFSet.{u}) :
    Truth (productSecondEntryFormula z a b) env ↔ env z ∈ productSecond (env a) (env b) := by
  simp only [productSecondEntryFormula, truth_exMem, truth_orderedTripleFormula, mem_productSecond]
  rfl

end BoundedFormula

namespace TransitiveGround

open SetFormula
variable (M : TransitiveGround.{u})

theorem productFirst_mem
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    {A B : ZFSet.{u}} (hA : A ∈ M.sets) (hB : B ∈ M.sets) : productFirst A B ∈ M.sets := by
  let params := extend A (extend B Fin.elim0)
  have selected := M.bounded_separation_mem separation (BoundedFormula.productFirstEntryFormula 0 1 2)
    params (Fin.cases hA (Fin.cases hB (fun i => Fin.elim0 i)))
    (M.prod_mem pairing unions powers separation (M.prod_mem pairing unions powers separation hA hB) hA)
  have eq : ZFSet.sep (fun z => BoundedFormula.Truth (BoundedFormula.productFirstEntryFormula 0 1 2)
      (extend z params)) (ZFSet.prod (ZFSet.prod A B) A) = productFirst A B := by
    apply ZFSet.ext
    intro z
    rw [ZFSet.mem_sep, BoundedFormula.truth_productFirstEntryFormula]
    exact ⟨And.right, fun hz => ⟨(productFirst_function A B).1 hz, hz⟩⟩
  exact eq ▸ selected

theorem productSecond_mem
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    {A B : ZFSet.{u}} (hA : A ∈ M.sets) (hB : B ∈ M.sets) : productSecond A B ∈ M.sets := by
  let params := extend A (extend B Fin.elim0)
  have selected := M.bounded_separation_mem separation (BoundedFormula.productSecondEntryFormula 0 1 2)
    params (Fin.cases hA (Fin.cases hB (fun i => Fin.elim0 i)))
    (M.prod_mem pairing unions powers separation (M.prod_mem pairing unions powers separation hA hB) hB)
  have eq : ZFSet.sep (fun z => BoundedFormula.Truth (BoundedFormula.productSecondEntryFormula 0 1 2)
      (extend z params)) (ZFSet.prod (ZFSet.prod A B) B) = productSecond A B := by
    apply ZFSet.ext
    intro z
    rw [ZFSet.mem_sep, BoundedFormula.truth_productSecondEntryFormula]
    exact ⟨And.right, fun hz => ⟨(productSecond_function A B).1 hz, hz⟩⟩
  exact eq ▸ selected

end TransitiveGround

end PartitionPilot.Forcing



namespace PartitionPilot.Forcing

universe u

theorem pair_mem_pairCompositionFamily (K I J B D L Es Ss W i j c : ZFSet.{u}) :
    ZFSet.pair (ZFSet.pair i j) c ∈ pairCompositionFamily K I J B D L Es Ss W ↔
      ZFSet.pair i j ∈ K ∧ i ∈ I ∧ j ∈ J ∧ c ∈ W ∧
        ∃ ell f, ZFSet.pair j ell ∈ Es ∧ ZFSet.pair i f ∈ Ss ∧ c = relationCompose B D L ell f := by
  constructor
  · intro entry
    obtain ⟨_, a, ha, b, hb, ell, _, f, _, c', hc', equal, hk, first, second, output⟩ :=
      ZFSet.mem_sep.1 entry
    obtain ⟨indices, rfl⟩ := ZFSet.pair_inj.1 equal
    obtain ⟨rfl, rfl⟩ := ZFSet.pair_inj.1 indices
    exact ⟨hk, ha, hb, hc', ell, f, first, second, output⟩
  · rintro ⟨hk, hi, hj, hc, ell, f, first, second, output⟩
    exact ZFSet.mem_sep.2 ⟨ZFSet.pair_mem_prod.2 ⟨hk, hc⟩,
      i, hi, j, hj, ell, pair_second_mem_doubleUnion first,
      f, pair_second_mem_doubleUnion second, c, hc, rfl, hk, first, second, output⟩

theorem pairCompositionFamily_entry_iff {K I J B D L Es Ss W i j ell f c : ZFSet.{u}}
    (bases : FunctionGraphOn J Es) (maps : FunctionGraphOn I Ss)
    (first : ZFSet.pair j ell ∈ Es) (second : ZFSet.pair i f ∈ Ss) :
    ZFSet.pair (ZFSet.pair i j) c ∈ pairCompositionFamily K I J B D L Es Ss W ↔
      ZFSet.pair i j ∈ K ∧ c ∈ W ∧ c = relationCompose B D L ell f := by
  rw [pair_mem_pairCompositionFamily]
  constructor
  · rintro ⟨hk, _, _, hc, ell', f', left, right, equal⟩
    have ellEq := bases.unique left first
    have fEq := maps.unique right second
    exact ⟨hk, hc, ellEq ▸ fEq ▸ equal⟩
  · rintro ⟨hk, hc, equal⟩
    exact ⟨hk, maps.pair_source second, bases.pair_source first, hc, ell, f, first, second, equal⟩

theorem pairCompositionFamily_function {K I J B D L Es Ss W : ZFSet.{u}}
    (bases : FunctionGraphOn J Es) (maps : FunctionGraphOn I Ss) (subset : K ⊆ ZFSet.prod I J)
    (bounded : ∀ i ∈ I, ∀ j ∈ J, ∀ ell f, ZFSet.pair j ell ∈ Es → ZFSet.pair i f ∈ Ss →
      relationCompose B D L ell f ∈ W) :
    ZFSet.IsFunc K W (pairCompositionFamily K I J B D L Es Ss W) := by
  refine ⟨fun _ hz => (ZFSet.mem_sep.1 hz).1, ?_⟩
  intro k hk
  obtain ⟨i, hi, j, hj, rfl⟩ := ZFSet.mem_prod.1 (subset hk)
  obtain ⟨ell, first⟩ := bases.total hj
  obtain ⟨f, second⟩ := maps.total hi
  refine ⟨relationCompose B D L ell f,
    (pairCompositionFamily_entry_iff bases maps first second).2
      ⟨hk, bounded i hi j hj ell f first second, rfl⟩, ?_⟩
  intro c entry
  exact ((pairCompositionFamily_entry_iff bases maps first second).1 entry).2.2

namespace BoundedFormula

open SetFormula

theorem truth_compositionGraphFormula {n} (f B D L ell s : Fin n) (env : Fin n → ZFSet.{u}) :
    Truth (compositionGraphFormula f B D L ell s) env ↔
      env f = relationCompose (env B) (env D) (env L) (env ell) (env s) := by
  simp only [compositionGraphFormula, Truth, truth_composeEntryFormula, truth_imp,
    truth_pairMembershipFormula]
  constructor
  · rintro ⟨sound, complete⟩
    apply ZFSet.ext
    intro z
    rw [mem_relationCompose]
    refine ⟨sound z, ?_⟩
    rintro ⟨x, hx, y, hy, w, hw, rfl, first, second⟩
    exact complete x hx y hy w hw ⟨first, second⟩
  · intro equal
    refine ⟨fun z hz => (mem_relationCompose _ _ _ _ _ z).1 (equal ▸ hz), ?_⟩
    intro x hx y hy w hw entries
    change ZFSet.pair x w ∈ env f
    rw [equal]
    exact (pair_mem_relationCompose _ _ _ _ _ x w).2 ⟨hx, hw, y, hy, entries⟩

def pairCompositionEntryFormula {n} (z K I J B D L Es Ss W U V : Fin n) : BoundedFormula n :=
  let lift (i : Fin n) := i.succ.succ.succ.succ.succ
  exMem I (exMem J.succ (exMem U.succ.succ (exMem V.succ.succ.succ (exMem W.succ.succ.succ.succ
    (.conj (orderedTripleFormula (lift z) 4 3 0)
      (.conj (pairMembershipFormula 4 3 (lift K))
        (.conj (pairMembershipFormula 3 2 (lift Es))
          (.conj (pairMembershipFormula 4 1 (lift Ss))
            (compositionGraphFormula 0 (lift B) (lift D) (lift L) 2 1)))))))))

theorem truth_pairCompositionEntryFormula {n} (z K I J B D L Es Ss W U V : Fin n)
    (env : Fin n → ZFSet.{u}) :
    Truth (pairCompositionEntryFormula z K I J B D L Es Ss W U V) env ↔
      ∃ i ∈ env I, ∃ j ∈ env J, ∃ ell ∈ env U, ∃ f ∈ env V, ∃ c ∈ env W,
        env z = ZFSet.pair (ZFSet.pair i j) c ∧ ZFSet.pair i j ∈ env K ∧
          ZFSet.pair j ell ∈ env Es ∧ ZFSet.pair i f ∈ env Ss ∧
            c = relationCompose (env B) (env D) (env L) ell f := by
  simp only [pairCompositionEntryFormula, truth_exMem, Truth, truth_orderedTripleFormula,
    truth_pairMembershipFormula, truth_compositionGraphFormula]
  rfl

end BoundedFormula

end PartitionPilot.Forcing



namespace PartitionPilot.Forcing.TransitiveGround

open SetFormula
universe u
variable (M : TransitiveGround.{u})

theorem pairCompositionFamily_mem
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    {K I J B D L Es Ss W : ZFSet.{u}} (hK : K ∈ M.sets) (hI : I ∈ M.sets)
    (hJ : J ∈ M.sets) (hB : B ∈ M.sets) (hD : D ∈ M.sets) (hL : L ∈ M.sets)
    (hEs : Es ∈ M.sets) (hSs : Ss ∈ M.sets) (hW : W ∈ M.sets) :
    pairCompositionFamily K I J B D L Es Ss W ∈ M.sets := by
  have hU := M.union_mem unions (M.union_mem unions hEs)
  have hV := M.union_mem unions (M.union_mem unions hSs)
  let params := extend K (extend I (extend J (extend B (extend D (extend L
    (extend Es (extend Ss (extend W (extend (⋃₀ ⋃₀ Es) (extend (⋃₀ ⋃₀ Ss) Fin.elim0))))))))))
  have selected := M.bounded_separation_mem separation
    (BoundedFormula.pairCompositionEntryFormula 0 1 2 3 4 5 6 7 8 9 10 11) params
    (Fin.cases hK (Fin.cases hI (Fin.cases hJ (Fin.cases hB (Fin.cases hD (Fin.cases hL
      (Fin.cases hEs (Fin.cases hSs (Fin.cases hW (Fin.cases hU (Fin.cases hV (fun i => Fin.elim0 i))))))))))))
    (M.prod_mem pairing unions powers separation hK hW)
  have equal : ZFSet.sep (fun z => BoundedFormula.Truth
      (BoundedFormula.pairCompositionEntryFormula 0 1 2 3 4 5 6 7 8 9 10 11) (extend z params))
      (ZFSet.prod K W) = pairCompositionFamily K I J B D L Es Ss W := by
    apply ZFSet.ext
    intro z
    rw [ZFSet.mem_sep, pairCompositionFamily, ZFSet.mem_sep]
    exact and_congr Iff.rfl (BoundedFormula.truth_pairCompositionEntryFormula 0 1 2 3 4 5 6 7 8 9 10 11 _)
  exact equal ▸ selected

noncomputable def groundPairCompositions (K I J B D L Es Ss : ZFSet.{u}) : ZFSet.{u} :=
  pairCompositionFamily K I J B D L Es Ss (M.groundRelations B L)

theorem groundPairCompositions_spec
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    {K I J B D L Es Ss : ZFSet.{u}} (hK : K ∈ M.sets) (hI : I ∈ M.sets)
    (hJ : J ∈ M.sets) (hB : B ∈ M.sets) (hD : D ∈ M.sets) (hL : L ∈ M.sets)
    (hEs : Es ∈ M.sets) (hSs : Ss ∈ M.sets)
    (bases : FunctionGraphOn J Es) (maps : FunctionGraphOn I Ss) (subset : K ⊆ ZFSet.prod I J) :
    M.groundPairCompositions K I J B D L Es Ss ∈ M.sets ∧
      ZFSet.IsFunc K (M.groundRelations B L) (M.groundPairCompositions K I J B D L Es Ss) ∧
      ∀ i j ell f c, ZFSet.pair j ell ∈ Es → ZFSet.pair i f ∈ Ss →
        (ZFSet.pair (ZFSet.pair i j) c ∈ M.groundPairCompositions K I J B D L Es Ss ↔
          ZFSet.pair i j ∈ K ∧ c = relationCompose B D L ell f) := by
  have bounded (i j ell f : ZFSet.{u}) (first : ZFSet.pair j ell ∈ Es)
      (second : ZFSet.pair i f ∈ Ss) : relationCompose B D L ell f ∈ M.groundRelations B L :=
    (M.mem_groundRelations B L _).2
      ⟨M.relationCompose_mem pairing unions powers separation hB hD hL
        (M.pair_right (M.transitive hEs first)) (M.pair_right (M.transitive hSs second)),
        fun _ hz => (ZFSet.mem_sep.1 hz).1⟩
  refine ⟨M.pairCompositionFamily_mem pairing unions powers separation hK hI hJ hB hD hL hEs hSs
    (M.groundRelations_mem pairing unions powers separation hB hL),
    pairCompositionFamily_function bases maps subset (fun i _ j _ ell f first second => bounded i j ell f first second), ?_⟩
  intro i j ell f c first second
  rw [groundPairCompositions, pairCompositionFamily_entry_iff bases maps first second]
  constructor
  · exact fun h => ⟨h.1, h.2.2⟩
  · rintro ⟨hk, rfl⟩
    exact ⟨hk, bounded i j ell f first second, rfl⟩

end PartitionPilot.Forcing.TransitiveGround

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


namespace PartitionPilot.Forcing.BoundedFormula

open SetFormula
universe u

theorem truth_orderedRightTripleFormula {n} (w x c q : Fin n)
    (env : Fin n → ZFSet.{u}) :
    Truth (orderedRightTripleFormula w x c q) env ↔
      env w = ZFSet.pair (env x) (ZFSet.pair (env c) (env q)) := by
  simp only [orderedRightTripleFormula, truth_exMem, Truth, truth_orderedPairFormula]
  change (∃ a ∈ env w, ∃ b ∈ a, b = ZFSet.pair (env c) (env q) ∧
    env w = ZFSet.pair (env x) b) ↔ _
  constructor
  · rintro ⟨_, _, _, _, rfl, equal⟩
    exact equal
  · intro equal
    refine ⟨{env x, ZFSet.pair (env c) (env q)}, ?_, ZFSet.pair (env c) (env q),
      ZFSet.mem_pair.2 (Or.inr rfl), rfl, equal⟩
    rw [equal]
    exact ZFSet.mem_pair.2 (Or.inr rfl)

theorem truth_rightTripleMembershipFormula {n} (x c q f : Fin n)
    (env : Fin n → ZFSet.{u}) :
    Truth (rightTripleMembershipFormula x c q f) env ↔
      ZFSet.pair (env x) (ZFSet.pair (env c) (env q)) ∈ env f := by
  simp only [rightTripleMembershipFormula, truth_exMem, truth_orderedRightTripleFormula]
  change (∃ w ∈ env f, w = ZFSet.pair (env x) (ZFSet.pair (env c) (env q))) ↔ _
  constructor
  · rintro ⟨w, hw, heq⟩
    exact heq ▸ hw
  · intro hw
    exact ⟨_, hw, rfl⟩

end PartitionPilot.Forcing.BoundedFormula



namespace PartitionPilot.Forcing

open scoped ZFSet

universe u

namespace BoundedFormula

open SetFormula

theorem truth_nonemptyFormula {n} (x : Fin n) (env : Fin n → ZFSet.{u}) :
    Truth (nonemptyFormula x) env ↔ (env x).Nonempty := by
  simp only [nonemptyFormula, truth_exMem, Truth]
  exact ⟨fun ⟨y, hy, _⟩ => ⟨y, hy⟩, fun ⟨y, hy⟩ => ⟨y, hy, True.intro⟩⟩

theorem truth_choiceFunctionFormula {n} (a f : Fin n) (env : Fin n → ZFSet.{u}) :
    Truth (choiceFunctionFormula a f) env ↔ ChoiceFunctionCode (env a) (env f) := by
  simp only [choiceFunctionFormula, Truth, truth_exMem, truth_orderedPairFormula,
    truth_pairMembershipFormula, truth_imp]
  change ((∀ z ∈ env f, ∃ x ∈ env a, ∃ y ∈ x, z = ZFSet.pair x y) ∧
    ∀ x ∈ env a, ∃ y ∈ x, ZFSet.pair x y ∈ env f ∧
      ∀ z ∈ x, ZFSet.pair x z ∈ env f → z = y) ↔ _
  constructor
  · rintro ⟨shape, total⟩
    have chosen : ∀ x y, ZFSet.pair x y ∈ env f → y ∈ x := by
      intro x y rel
      obtain ⟨x', _, y', hy', eq⟩ := shape _ rel
      obtain ⟨rfl, rfl⟩ := ZFSet.pair_inj.1 eq
      exact hy'
    refine ⟨⟨?_, ?_⟩, chosen⟩
    · intro z hz
      obtain ⟨x, hx, y, hy, rfl⟩ := shape z hz
      exact ZFSet.pair_mem_prod.2 ⟨hx, ZFSet.mem_sUnion.2 ⟨x, hx, hy⟩⟩
    · intro x hx
      obtain ⟨y, _, rel, unique⟩ := total x hx
      exact ⟨y, rel, fun z hz => unique z (chosen x z hz) hz⟩
  · intro h
    refine ⟨?_, ?_⟩
    · intro z hz
      obtain ⟨x, hx, y, _, eq⟩ := ZFSet.mem_prod.1 (h.function.1 hz)
      exact ⟨x, hx, y, h.chosen x y (eq ▸ hz), eq⟩
    · intro x hx
      obtain ⟨y, rel, unique⟩ := h.function.2 x hx
      exact ⟨y, h.chosen x y rel, rel, fun z _ hz => unique z hz⟩

end BoundedFormula


namespace TransitiveGround

open SetFormula
variable (M : TransitiveGround.{u})

theorem choice_witness (choice : Realize M.sets SetFormula.choice Fin.elim0)
    {A : ZFSet.{u}} (hA : A ∈ M.sets) (nonempty : ∀ x ∈ A, x.Nonempty) :
    ∃ f ∈ M.sets, ChoiceFunctionCode A f := by
  have selected := (realize_imp M.sets _ _ _).1 (choice A hA)
  have premise : Realize M.sets
      (BoundedFormula.allMem 0 (BoundedFormula.nonemptyFormula 0)).toFormula (extend A Fin.elim0) := by
    apply (BoundedFormula.realize_toFormula M _ _ (Fin.cases hA (fun i => Fin.elim0 i))).2
    intro x hx
    exact (BoundedFormula.truth_nonemptyFormula 0 _).2 (nonempty x hx)
  obtain ⟨f, hf, rel⟩ := (realize_ex M.sets _ _).1 (selected premise)
  exact ⟨f, hf, (BoundedFormula.truth_choiceFunctionFormula 1 0 _).1
    ((BoundedFormula.realize_toFormula M _ _ (Fin.cases hf (Fin.cases hA (fun i => Fin.elim0 i)))).1 rel)⟩

end TransitiveGround

end PartitionPilot.Forcing



namespace PartitionPilot.Forcing

universe u

namespace BoundedFormula

open SetFormula

theorem truth_fiberFormula {n} (f x b r : Fin n) (env : Fin n → ZFSet.{u}) :
    Truth (fiberFormula f x b r) env ↔ env f = relationFiber (env b) (env r) (env x) := by
  simp only [fiberFormula, Truth, truth_imp, truth_pairMembershipFormula]
  change ((∀ y ∈ env f, y ∈ env b) ∧ ∀ y ∈ env b,
    (y ∈ env f → ZFSet.pair (env x) y ∈ env r) ∧ (ZFSet.pair (env x) y ∈ env r → y ∈ env f)) ↔ _
  constructor
  · rintro ⟨subset, spec⟩
    apply ZFSet.ext
    intro y
    rw [mem_relationFiber]
    exact ⟨fun hy => ⟨subset y hy, (spec y (subset y hy)).1 hy⟩,
      fun ⟨hy, rel⟩ => (spec y hy).2 rel⟩
  · intro eq
    rw [eq]
    exact ⟨fun _ hy => (ZFSet.mem_sep.1 hy).1,
      fun y hy => ⟨fun rel => (ZFSet.mem_sep.1 rel).2, fun rel => ZFSet.mem_sep.2 ⟨hy, rel⟩⟩⟩

theorem truth_choiceUniformEntryFormula {n} (z a b r f c : Fin n) (env : Fin n → ZFSet.{u}) :
    Truth (choiceUniformEntryFormula z a b r f c) env ↔
      ∃ x ∈ env a, ∃ y ∈ env b, env z = ZFSet.pair x y ∧
        relationFiber (env b) (env r) x ∈ env f ∧ ZFSet.pair (relationFiber (env b) (env r) x) y ∈ env c := by
  simp only [choiceUniformEntryFormula, truth_exMem, Truth,
    truth_orderedPairFormula, truth_fiberFormula, truth_pairMembershipFormula]
  change (∃ x ∈ env a, ∃ y ∈ env b, ∃ F ∈ env f, env z = ZFSet.pair x y ∧
    F = relationFiber (env b) (env r) x ∧ ZFSet.pair F y ∈ env c) ↔ _
  constructor
  · rintro ⟨x, hx, y, hy, F, hF, eq, rfl, rel⟩
    exact ⟨x, hx, y, hy, eq, hF, rel⟩
  · rintro ⟨x, hx, y, hy, eq, hF, rel⟩
    exact ⟨x, hx, y, hy, relationFiber (env b) (env r) x, hF, eq, rfl, rel⟩

end BoundedFormula

namespace TransitiveGround

open SetFormula
variable (M : TransitiveGround.{u})

theorem relationFiber_mem (separation : SeparationSchema M.sets) {B r x : ZFSet.{u}}
    (hB : B ∈ M.sets) (hr : r ∈ M.sets) (hx : x ∈ M.sets) : relationFiber B r x ∈ M.sets := by
  let params := extend x (extend r Fin.elim0)
  have selected := M.bounded_separation_mem separation (BoundedFormula.pairMembershipFormula 1 0 2)
    params (Fin.cases hx (Fin.cases hr (fun i => Fin.elim0 i))) hB
  have eq : ZFSet.sep (fun y => BoundedFormula.Truth (BoundedFormula.pairMembershipFormula 1 0 2)
      (extend y params)) B = relationFiber B r x := by
    apply ZFSet.ext
    intro y
    rw [ZFSet.mem_sep, mem_relationFiber]
    exact and_congr Iff.rfl (BoundedFormula.truth_pairMembershipFormula 1 0 2 _)
  exact eq ▸ selected

theorem mem_nonemptyGroundSubsets (B F : ZFSet.{u}) :
    F ∈ M.nonemptyGroundSubsets B ↔ F ∈ M.sets ∧ F ⊆ B ∧ F.Nonempty := by
  rw [nonemptyGroundSubsets, ZFSet.mem_sep, M.mem_groundPower]
  exact and_assoc

theorem nonemptyGroundSubsets_mem (powers : Realize M.sets powerSet Fin.elim0)
    (separation : SeparationSchema M.sets) {B : ZFSet.{u}} (hB : B ∈ M.sets) :
    M.nonemptyGroundSubsets B ∈ M.sets := by
  have selected := M.bounded_separation_mem separation (BoundedFormula.nonemptyFormula 0)
    Fin.elim0 (fun i => Fin.elim0 i) (M.groundPower_mem powers hB)
  have eq : ZFSet.sep (fun F => BoundedFormula.Truth (BoundedFormula.nonemptyFormula 0)
      (extend F Fin.elim0)) (M.groundPower B) = M.nonemptyGroundSubsets B := by
    apply ZFSet.ext
    intro F
    rw [ZFSet.mem_sep, nonemptyGroundSubsets, ZFSet.mem_sep]
    exact and_congr Iff.rfl (BoundedFormula.truth_nonemptyFormula 0 _)
  exact eq ▸ selected

theorem choiceUniformGraph_mem
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    {A B r F c : ZFSet.{u}} (hA : A ∈ M.sets) (hB : B ∈ M.sets)
    (hr : r ∈ M.sets) (hF : F ∈ M.sets) (hc : c ∈ M.sets) : choiceUniformGraph A B r F c ∈ M.sets := by
  let params := extend A (extend B (extend r (extend F (extend c Fin.elim0))))
  have selected := M.bounded_separation_mem separation (BoundedFormula.choiceUniformEntryFormula 0 1 2 3 4 5)
    params (Fin.cases hA (Fin.cases hB (Fin.cases hr (Fin.cases hF (Fin.cases hc (fun i => Fin.elim0 i))))))
    (M.prod_mem pairing unions powers separation hA hB)
  have eq : ZFSet.sep (fun z => BoundedFormula.Truth (BoundedFormula.choiceUniformEntryFormula 0 1 2 3 4 5)
      (extend z params)) (ZFSet.prod A B) = choiceUniformGraph A B r F c := by
    apply ZFSet.ext
    intro z
    rw [ZFSet.mem_sep, choiceUniformGraph, ZFSet.mem_sep]
    exact and_congr Iff.rfl (BoundedFormula.truth_choiceUniformEntryFormula 0 1 2 3 4 5 _)
  exact eq ▸ selected

theorem uniformize_relation
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (choice : Realize M.sets SetFormula.choice Fin.elim0)
    {A B r : ZFSet.{u}} (hA : A ∈ M.sets) (hB : B ∈ M.sets) (hr : r ∈ M.sets)
    (total : ∀ x ∈ A, ∃ y ∈ B, ZFSet.pair x y ∈ r) :
    ∃ f ∈ M.sets, ZFSet.IsFunc A B f ∧ f ⊆ r := by
  have family := M.nonemptyGroundSubsets_mem powers separation hB
  obtain ⟨c, hc, code⟩ := M.choice_witness choice family
    (fun F hF => ((M.mem_nonemptyGroundSubsets B F).1 hF).2.2)
  have fibers (x : ZFSet.{u}) (hx : x ∈ A) : relationFiber B r x ∈ M.nonemptyGroundSubsets B := by
    obtain ⟨y, hy, rel⟩ := total x hx
    exact (M.mem_nonemptyGroundSubsets B _).2
      ⟨M.relationFiber_mem separation hB hr (M.transitive hA hx), fun _ hz => (ZFSet.mem_sep.1 hz).1,
        y, (mem_relationFiber B r x y).2 ⟨hy, rel⟩⟩
  exact ⟨choiceUniformGraph A B r (M.nonemptyGroundSubsets B) c,
    M.choiceUniformGraph_mem pairing unions powers separation hA hB hr family hc,
    choiceUniformGraph_function code fibers⟩

end TransitiveGround

end PartitionPilot.Forcing



namespace PartitionPilot.Forcing
open SetFormula
universe u

namespace BoundedFormula
def relationFiberFamilyEntryFormula {n} (z I W B R : Fin n) : BoundedFormula n :=
  exMem I (exMem W.succ (.conj (orderedPairFormula z.succ.succ 1 0)
    (fiberFormula 0 1 B.succ.succ R.succ.succ)))

theorem truth_relationFiberFamilyEntryFormula {n} (z I W B R : Fin n)
    (env : Fin n → ZFSet.{u}) :
    Truth (relationFiberFamilyEntryFormula z I W B R) env ↔
      ∃ i ∈ env I, ∃ f ∈ env W, env z = ZFSet.pair i f ∧
        f = relationFiber (env B) (env R) i := by
  simp only [relationFiberFamilyEntryFormula, truth_exMem, Truth,
    truth_orderedPairFormula, truth_fiberFormula]
  rfl
end BoundedFormula

namespace BoundedFormula

def externalCosetSupportFormula {n} (E U C classifier copies zero v y : Fin n) : BoundedFormula n :=
  exMem C (exMem E.succ (exMem U.succ.succ
    (.conj (orderedPairFormula v.succ.succ.succ zero.succ.succ.succ 2)
      (.conj (pairMembershipFormula 1 2 classifier.succ.succ.succ)
        (tripleMembershipFormula 1 0 y.succ.succ.succ copies.succ.succ.succ)))))

theorem truth_externalCosetSupportFormula {n} (E U C classifier copies zero v y : Fin n) (env : Fin n → ZFSet.{u}) :
    Truth (externalCosetSupportFormula E U C classifier copies zero v y) env ↔
      ExternalCosetSupport (env E) (env U) (env C) (env classifier) (env copies) (env zero) (env v) (env y) := by
  simp only [externalCosetSupportFormula, truth_exMem, Truth, truth_orderedPairFormula,
    truth_pairMembershipFormula, truth_tripleMembershipFormula, ExternalCosetSupport]
  rfl

def externalTileSupportFormula {n} (E Q Requests localPoints action first v y : Fin n) : BoundedFormula n :=
  exMem E (exMem Requests.succ (exMem Q.succ.succ
    (.conj (orderedRightTripleFormula v.succ.succ.succ first.succ.succ.succ 2 1)
      (.conj (pairMembershipFormula 1 0 localPoints.succ.succ.succ)
        (tripleMembershipFormula 2 0 y.succ.succ.succ action.succ.succ.succ)))))

theorem truth_externalTileSupportFormula {n} (E Q Requests localPoints action first v y : Fin n) (env : Fin n → ZFSet.{u}) :
    Truth (externalTileSupportFormula E Q Requests localPoints action first v y) env ↔
      ExternalTileSupport (env E) (env Q) (env Requests) (env localPoints) (env action) (env first) (env v) (env y) := by
  simp only [externalTileSupportFormula, truth_exMem, Truth, truth_orderedRightTripleFormula,
    truth_pairMembershipFormula, truth_tripleMembershipFormula, ExternalTileSupport]
  rfl

def externalStarSupportEntryFormula {n} (z V Q E U C Requests classifier copies localPoints action zero first : Fin n) : BoundedFormula n :=
  exMem V (exMem Q.succ (.conj (orderedPairFormula z.succ.succ 1 0)
    (.disj (externalCosetSupportFormula E.succ.succ U.succ.succ C.succ.succ
      classifier.succ.succ copies.succ.succ zero.succ.succ 1 0)
      (externalTileSupportFormula E.succ.succ Q.succ.succ Requests.succ.succ
        localPoints.succ.succ action.succ.succ first.succ.succ 1 0))))

theorem truth_externalStarSupportEntryFormula {n} (z V Q E U C Requests classifier copies localPoints action zero first : Fin n)
    (env : Fin n → ZFSet.{u}) :
    Truth (externalStarSupportEntryFormula z V Q E U C Requests classifier copies localPoints action zero first) env ↔
      env z ∈ externalStarSupportGraph (env V) (env Q) (env E) (env U) (env C) (env Requests)
        (env classifier) (env copies) (env localPoints) (env action) (env zero) (env first) := by
  simp only [externalStarSupportEntryFormula, truth_exMem, Truth, truth_disj, truth_orderedPairFormula,
    truth_externalCosetSupportFormula, truth_externalTileSupportFormula, externalStarSupportGraph, ZFSet.mem_sep]
  refine ⟨fun body => ⟨?_, body⟩, And.right⟩
  obtain ⟨v, hv, y, hy, equal, _⟩ := body
  change env z = ZFSet.pair v y at equal
  rw [equal]
  exact ZFSet.pair_mem_prod.2 ⟨hv, hy⟩
end BoundedFormula

end PartitionPilot.Forcing

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Definability_MapFamilyApplicationGraphs
attribute [-instance] _root_.OAI.PartitionPilot.Forcing.GroundMainPrefix.withTopSmall
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace PartitionPilot.Forcing

section

universe u

theorem indexedRelationSection_subset (B C R i : ZFSet.{u}) :
    indexedRelationSection B C R i ⊆ ZFSet.prod B C :=
  fun _ hz => (ZFSet.mem_sep.1 hz).1

theorem mem_indexedRelationSection (B C R i z : ZFSet.{u}) :
    z ∈ indexedRelationSection B C R i ↔ ∃ q ∈ B, ∃ y ∈ C,
      z = ZFSet.pair q y ∧ ZFSet.pair (ZFSet.pair i q) y ∈ R := by
  constructor
  · intro hz
    exact (ZFSet.mem_sep.1 hz).2
  · rintro ⟨q, hq, y, hy, rfl, entry⟩
    exact ZFSet.mem_sep.2 ⟨ZFSet.pair_mem_prod.2 ⟨hq, hy⟩, q, hq, y, hy, rfl, entry⟩

theorem pair_mem_indexedRelationSection (B C R i q y : ZFSet.{u}) :
    ZFSet.pair q y ∈ indexedRelationSection B C R i ↔
      q ∈ B ∧ y ∈ C ∧ ZFSet.pair (ZFSet.pair i q) y ∈ R := by
  rw [mem_indexedRelationSection]
  constructor
  · rintro ⟨q', hq, y', hy, equal, entry⟩
    obtain ⟨rfl, rfl⟩ := ZFSet.pair_inj.1 equal
    exact ⟨hq, hy, entry⟩
  · rintro ⟨hq, hy, entry⟩
    exact ⟨q, hq, y, hy, rfl, entry⟩






namespace BoundedFormula

open SetFormula

def indexedRelationSectionEntryFormula {n} (z i b c r : Fin n) : BoundedFormula n :=
  exMem b (exMem c.succ (.conj (orderedPairFormula z.succ.succ 1 0)
    (tripleMembershipFormula i.succ.succ 1 0 r.succ.succ)))

theorem truth_indexedRelationSectionEntryFormula {n} (z i b c r : Fin n)
    (env : Fin n → ZFSet.{u}) :
    Truth (indexedRelationSectionEntryFormula z i b c r) env ↔
      env z ∈ indexedRelationSection (env b) (env c) (env r) (env i) := by
  simp only [indexedRelationSectionEntryFormula, truth_exMem, Truth,
    truth_orderedPairFormula, truth_tripleMembershipFormula, mem_indexedRelationSection]
  rfl

def indexedRelationSectionFormula {n} (f i b c r : Fin n) : BoundedFormula n :=
  .conj (.allMem f (indexedRelationSectionEntryFormula 0 i.succ b.succ c.succ r.succ))
    (.allMem b (.allMem c.succ
      (imp (tripleMembershipFormula i.succ.succ 1 0 r.succ.succ)
        (pairMembershipFormula 1 0 f.succ.succ))))

theorem truth_indexedRelationSectionFormula {n} (f i b c r : Fin n)
    (env : Fin n → ZFSet.{u}) :
    Truth (indexedRelationSectionFormula f i b c r) env ↔
      env f = indexedRelationSection (env b) (env c) (env r) (env i) := by
  simp only [indexedRelationSectionFormula, Truth, truth_indexedRelationSectionEntryFormula,
    truth_imp, truth_tripleMembershipFormula, truth_pairMembershipFormula]
  constructor
  · rintro ⟨subset, complete⟩
    apply ZFSet.ext
    intro z
    refine ⟨subset z, ?_⟩
    intro hz
    obtain ⟨q, hq, y, hy, rfl, entry⟩ := (mem_indexedRelationSection _ _ _ _ z).1 hz
    exact complete q hq y hy entry
  · intro equal
    refine ⟨fun _ hz => equal ▸ hz, ?_⟩
    intro q hq y hy entry
    change ZFSet.pair q y ∈ env f
    rw [equal]
    exact (pair_mem_indexedRelationSection _ _ _ _ q y).2 ⟨hq, hy, entry⟩

def indexedRelationFamilyEntryFormula {n} (z domain bound b c r : Fin n) : BoundedFormula n :=
  exMem domain (exMem bound.succ (.conj (orderedPairFormula z.succ.succ 1 0)
    (indexedRelationSectionFormula 0 1 b.succ.succ c.succ.succ r.succ.succ)))

theorem truth_indexedRelationFamilyEntryFormula {n} (z domain bound b c r : Fin n)
    (env : Fin n → ZFSet.{u}) :
    Truth (indexedRelationFamilyEntryFormula z domain bound b c r) env ↔
      ∃ i ∈ env domain, ∃ f ∈ env bound, env z = ZFSet.pair i f ∧
        f = indexedRelationSection (env b) (env c) (env r) i := by
  simp only [indexedRelationFamilyEntryFormula, truth_exMem, Truth,
    truth_orderedPairFormula, truth_indexedRelationSectionFormula]
  rfl

end BoundedFormula

namespace TransitiveGround

open SetFormula
variable (M : TransitiveGround.{u})

theorem indexedRelationSection_mem
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    {B C R i : ZFSet.{u}} (hB : B ∈ M.sets) (hC : C ∈ M.sets)
    (hR : R ∈ M.sets) (hi : i ∈ M.sets) : indexedRelationSection B C R i ∈ M.sets := by
  let params := extend i (extend B (extend C (extend R Fin.elim0)))
  have selected := M.bounded_separation_mem separation
    (BoundedFormula.indexedRelationSectionEntryFormula 0 1 2 3 4) params
    (Fin.cases hi (Fin.cases hB (Fin.cases hC (Fin.cases hR (fun j => Fin.elim0 j)))))
    (M.prod_mem pairing unions powers separation hB hC)
  have equal : ZFSet.sep (fun z => BoundedFormula.Truth
      (BoundedFormula.indexedRelationSectionEntryFormula 0 1 2 3 4) (extend z params))
      (ZFSet.prod B C) = indexedRelationSection B C R i := by
    apply ZFSet.ext
    intro z
    rw [ZFSet.mem_sep, BoundedFormula.truth_indexedRelationSectionEntryFormula]
    exact ⟨And.right, fun hz => ⟨indexedRelationSection_subset B C R i hz, hz⟩⟩
  exact equal ▸ selected

theorem pair_mem_indexedRelationSections (I B C R i f : ZFSet.{u}) :
    ZFSet.pair i f ∈ M.indexedRelationSections I B C R ↔
      i ∈ I ∧ f ∈ M.groundRelations B C ∧ f = indexedRelationSection B C R i := by
  rw [indexedRelationSections, ZFSet.mem_sep, ZFSet.pair_mem_prod]
  constructor
  · rintro ⟨⟨hi, hf⟩, j, _, g, _, equal, sectionEq⟩
    obtain ⟨rfl, rfl⟩ := ZFSet.pair_inj.1 equal
    exact ⟨hi, hf, sectionEq⟩
  · rintro ⟨hi, hf, sectionEq⟩
    exact ⟨⟨hi, hf⟩, i, hi, f, hf, rfl, sectionEq⟩

theorem indexedRelationSections_mem
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    {I B C R : ZFSet.{u}} (hI : I ∈ M.sets) (hB : B ∈ M.sets)
    (hC : C ∈ M.sets) (hR : R ∈ M.sets) : M.indexedRelationSections I B C R ∈ M.sets := by
  have bound := M.groundRelations_mem pairing unions powers separation hB hC
  let params := extend I (extend (M.groundRelations B C) (extend B (extend C (extend R Fin.elim0))))
  have selected := M.bounded_separation_mem separation
    (BoundedFormula.indexedRelationFamilyEntryFormula 0 1 2 3 4 5) params
    (Fin.cases hI (Fin.cases bound (Fin.cases hB (Fin.cases hC
      (Fin.cases hR (fun j => Fin.elim0 j))))))
    (M.prod_mem pairing unions powers separation hI bound)
  have equal : ZFSet.sep (fun z => BoundedFormula.Truth
      (BoundedFormula.indexedRelationFamilyEntryFormula 0 1 2 3 4 5) (extend z params))
      (ZFSet.prod I (M.groundRelations B C)) = M.indexedRelationSections I B C R := by
    apply ZFSet.ext
    intro z
    rw [ZFSet.mem_sep, indexedRelationSections, ZFSet.mem_sep]
    exact and_congr Iff.rfl (BoundedFormula.truth_indexedRelationFamilyEntryFormula 0 1 2 3 4 5 _)
  exact equal ▸ selected

theorem indexedRelationSections_function
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    {I B C R : ZFSet.{u}} (hI : I ∈ M.sets) (hB : B ∈ M.sets)
    (hC : C ∈ M.sets) (hR : R ∈ M.sets) :
    ZFSet.IsFunc I (M.groundRelations B C) (M.indexedRelationSections I B C R) := by
  refine ⟨fun _ hz => (ZFSet.mem_sep.1 hz).1, ?_⟩
  intro i hi
  have sectionBound := (M.mem_groundRelations B C (indexedRelationSection B C R i)).2
    ⟨M.indexedRelationSection_mem pairing unions powers separation hB hC hR (M.transitive hI hi),
      indexedRelationSection_subset B C R i⟩
  exact ⟨indexedRelationSection B C R i,
    (M.pair_mem_indexedRelationSections I B C R i _).2 ⟨hi, sectionBound, rfl⟩,
    fun f hf => ((M.pair_mem_indexedRelationSections I B C R i f).1 hf).2.2⟩

theorem indexedRelationSections_spec
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    {I B C R : ZFSet.{u}} (hI : I ∈ M.sets) (hB : B ∈ M.sets)
    (hC : C ∈ M.sets) (hR : R ∈ M.sets) :
    M.indexedRelationSections I B C R ∈ M.sets ∧
      ZFSet.IsFunc I (M.groundRelations B C) (M.indexedRelationSections I B C R) ∧
      ∀ i f, ZFSet.pair i f ∈ M.indexedRelationSections I B C R ↔
        i ∈ I ∧ f = indexedRelationSection B C R i := by
  have func := M.indexedRelationSections_function pairing unions powers separation hI hB hC hR
  refine ⟨M.indexedRelationSections_mem pairing unions powers separation hI hB hC hR, func, ?_⟩
  intro i f
  constructor
  · intro entry
    have parts := (M.pair_mem_indexedRelationSections I B C R i f).1 entry
    exact ⟨parts.1, parts.2.2⟩
  · rintro ⟨hi, rfl⟩
    obtain ⟨g, entry, _⟩ := func.2 i hi
    have equal := ((M.pair_mem_indexedRelationSections I B C R i g).1 entry).2.2
    exact equal ▸ entry

end TransitiveGround

end



open SetFormula
universe u

theorem pair_mem_indexedCarrierLabels (T U A i x : ZFSet.{u}) :
    ZFSet.pair i x ∈ indexedCarrierLabels T U A ↔
      i ∈ T ∧ x ∈ U ∧ ∃ X, ZFSet.pair i X ∈ A ∧ x ∈ X := by
  rw [mem_indexedCarrierLabels]
  constructor
  · rintro ⟨j, hj, X, _, y, hy, hu, equal, entry⟩
    obtain ⟨rfl, rfl⟩ := ZFSet.pair_inj.1 equal
    exact ⟨hj, hu, X, entry, hy⟩
  · rintro ⟨hi, hu, X, entry, hx⟩
    exact ⟨i, hi, X, pair_second_mem_doubleUnion entry, x, hx, hu, rfl, entry⟩

theorem pair_mem_indexedCarrierLabels_of_entry {T U A i X x : ZFSet.{u}}
    (family : FunctionGraphOn T A) (entry : ZFSet.pair i X ∈ A) (bound : X ⊆ U) :
    ZFSet.pair i x ∈ indexedCarrierLabels T U A ↔ x ∈ X := by
  rw [pair_mem_indexedCarrierLabels]
  constructor
  · rintro ⟨_, _, Y, other, hx⟩
    exact (family.unique other entry) ▸ hx
  · intro hx
    exact ⟨family.pair_source entry, bound hx, X, entry, hx⟩

namespace BoundedFormula

theorem truth_indexedCarrierLabelFormula {n} (z T U A V : Fin n)
    (env : Fin n → ZFSet.{u}) (bound : env V = ZFSet.sUnion (ZFSet.sUnion (env A))) :
    Truth (indexedCarrierLabelFormula z T U A V) env ↔
      env z ∈ indexedCarrierLabels (env T) (env U) (env A) := by
  simp only [indexedCarrierLabelFormula, truth_exMem, Truth,
    truth_orderedPairFormula, truth_pairMembershipFormula]
  change (∃ i ∈ env T, ∃ X ∈ env V, ∃ x ∈ X,
    x ∈ env U ∧ env z = ZFSet.pair i x ∧ ZFSet.pair i X ∈ env A) ↔ _
  rw [bound, mem_indexedCarrierLabels]

end BoundedFormula

namespace TransitiveGround
variable (M : TransitiveGround.{u})

theorem indexedCarrierLabels_mem
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    {T U A : ZFSet.{u}} (hT : T ∈ M.sets) (hU : U ∈ M.sets) (hA : A ∈ M.sets) :
    indexedCarrierLabels T U A ∈ M.sets := by
  have hV := M.union_mem unions (M.union_mem unions hA)
  let params := extend T (extend U (extend A (extend (ZFSet.sUnion (ZFSet.sUnion A)) Fin.elim0)))
  have selected := M.bounded_separation_mem separation
    (BoundedFormula.indexedCarrierLabelFormula 0 1 2 3 4) params
    (Fin.cases hT (Fin.cases hU (Fin.cases hA (Fin.cases hV (fun j => Fin.elim0 j)))))
    (M.prod_mem pairing unions powers separation hT hU)
  have equal : ZFSet.sep (fun z => BoundedFormula.Truth
      (BoundedFormula.indexedCarrierLabelFormula 0 1 2 3 4) (extend z params))
      (ZFSet.prod T U) = indexedCarrierLabels T U A := by
    apply ZFSet.ext
    intro z
    rw [ZFSet.mem_sep, BoundedFormula.truth_indexedCarrierLabelFormula 0 1 2 3 4 _ rfl]
    exact ⟨And.right, fun hz => ⟨indexedCarrierLabels_subset T U A hz, hz⟩⟩
  exact equal ▸ selected

end TransitiveGround





namespace BoundedFormula

def mapFamilyApplicationEntryFormula {n} (z I P Q B family : Fin n) : BoundedFormula n :=
  exMem I (exMem P.succ (exMem Q.succ.succ (exMem B.succ.succ.succ
    (.conj (orderedTripleFormula z.succ.succ.succ.succ 3 2 1)
      (.conj (pairMembershipFormula 3 0 family.succ.succ.succ.succ)
        (pairMembershipFormula 2 1 0))))))

end BoundedFormula


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



namespace PartitionPilot.SetRealization.Presentation

universe u
variable {P : Type u} [Preorder P] (s : Presentation P)

noncomputable def conditionOrder : ZFSet.{u} := (s.product s).subset (fun z => z.1 ≤ z.2)

theorem pair_mem_conditionOrder (p q : P) :
    ZFSet.pair (s.encode p) (s.encode q) ∈ s.conditionOrder ↔ p ≤ q :=
  (s.product s).encode_mem_subset (fun z => z.1 ≤ z.2) (p, q)

end PartitionPilot.SetRealization.Presentation

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



namespace PartitionPilot.Forcing

universe u

namespace BoundedFormula

open SetFormula

def reverseInclusionEntryFormula {n} (z q : Fin n) : BoundedFormula n :=
  exMem q (exMem q.succ (.conj (orderedPairFormula z.succ.succ 1 0) (subsetFormula 0 1)))

theorem truth_subsetFormula {n} (a b : Fin n) (env : Fin n → ZFSet.{u}) :
    Truth (subsetFormula a b) env ↔ env a ⊆ env b := Iff.rfl

theorem truth_reverseInclusionEntryFormula {n} (z q : Fin n) (env : Fin n → ZFSet.{u}) :
    Truth (reverseInclusionEntryFormula z q) env ↔ env z ∈ reverseInclusionCode (env q) := by
  simp only [reverseInclusionEntryFormula, truth_exMem, Truth, truth_orderedPairFormula, truth_subsetFormula]
  exact (mem_reverseInclusionCode (env q) (env z)).symm

end BoundedFormula

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


section

namespace PartitionPilot.SetRealization.Presentation

open Forcing
universe u
variable {A B : Type u} (s : Presentation A) (t : Presentation B)

theorem graph_injection (f : A → B) (injective : Function.Injective f) :
    InjectionCode s.carrier t.carrier (s.graph t f) := by
  have function := s.graph_isFunc t f
  refine ⟨function, ?_⟩
  intro x y z hx hy
  obtain ⟨a, rfl⟩ := (s.mem_carrier x).1 (ZFSet.pair_mem_prod.1 (function.1 hx)).1
  obtain ⟨b, rfl⟩ := (s.mem_carrier y).1 (ZFSet.pair_mem_prod.1 (function.1 hy)).1
  obtain ⟨c, rfl⟩ := (t.mem_carrier z).1 (ZFSet.pair_mem_prod.1 (function.1 hx)).2
  exact congrArg s.encode (injective
    (((s.pair_mem_graph t f a c).1 hx).trans ((s.pair_mem_graph t f b c).1 hy).symm))

end PartitionPilot.SetRealization.Presentation

namespace PartitionPilot.Forcing

open SetRealization
universe u
variable {X Y : Type u} (s : Presentation X) (t : Presentation Y)

noncomputable def entryPermutationGraph (e : X ≃ X) : ZFSet.{u} :=
  (s.product t).graph (s.product t) (fun xy => (e xy.1, xy.2))

end PartitionPilot.Forcing



namespace PartitionPilot.Forcing.BoundedFormula

open SetFormula SetRealization
universe u

theorem truth_entryTransportFormula {n} (a b r x y : Fin n) (env : Fin n → ZFSet.{u}) :
    Truth (entryTransportFormula a b r x y) env ↔
      ∃ i ∈ env x, ∃ j ∈ env x, ∃ v ∈ env y,
        env a = ZFSet.pair i v ∧ env b = ZFSet.pair j v ∧ ZFSet.pair i j ∈ env r := by
  simp only [entryTransportFormula, truth_exMem, Truth,
    truth_orderedPairFormula, truth_pairMembershipFormula]
  rfl

theorem truth_entryPermutationFormula {n} (z r x y c : Fin n) (env : Fin n → ZFSet.{u}) :
    Truth (entryPermutationFormula z r x y c) env ↔
      ∃ a ∈ env c, ∃ b ∈ env c, env z = ZFSet.pair a b ∧
        ∃ i ∈ env x, ∃ j ∈ env x, ∃ v ∈ env y,
          a = ZFSet.pair i v ∧ b = ZFSet.pair j v ∧ ZFSet.pair i j ∈ env r := by
  simp only [entryPermutationFormula, truth_exMem, Truth,
    truth_orderedPairFormula, truth_entryTransportFormula]
  rfl

theorem entryPermutation_correct {X Y : Type u} (s : Presentation X) (t : Presentation Y)
    (e : X ≃ X) (z : ZFSet.{u}) :
    Truth (entryPermutationFormula 0 1 2 3 4)
      (extend z (extend (s.graph s e) (extend s.carrier (extend t.carrier
        (extend (ZFSet.prod s.carrier t.carrier) Fin.elim0))))) ↔ z ∈ entryPermutationGraph s t e := by
  rw [truth_entryPermutationFormula]
  change (∃ a ∈ ZFSet.prod s.carrier t.carrier, ∃ b ∈ ZFSet.prod s.carrier t.carrier,
    z = ZFSet.pair a b ∧ ∃ i ∈ s.carrier, ∃ j ∈ s.carrier, ∃ v ∈ t.carrier,
      a = ZFSet.pair i v ∧ b = ZFSet.pair j v ∧ ZFSet.pair i j ∈ s.graph s e) ↔ _
  constructor
  · rintro ⟨a, _, b, _, rfl, i, hi, j, hj, v, hv, rfl, rfl, rel⟩
    obtain ⟨x, rfl⟩ := (s.mem_carrier i).1 hi
    obtain ⟨x', rfl⟩ := (s.mem_carrier j).1 hj
    obtain ⟨y, rfl⟩ := (t.mem_carrier v).1 hv
    exact ((s.product t).pair_mem_graph (s.product t) _ (x, y) (x', y)).2
      (Prod.ext ((s.pair_mem_graph s e x x').1 rel) rfl)
  · intro hz
    obtain ⟨⟨x, y⟩, eq⟩ := ((s.product t).mem_graph (s.product t) _ z).1 hz
    exact ⟨ZFSet.pair (s.encode x) (t.encode y), (s.product t).encode_mem (x, y),
      ZFSet.pair (s.encode (e x)) (t.encode y), (s.product t).encode_mem (e x, y), eq.symm,
      s.encode x, s.encode_mem x, s.encode (e x), s.encode_mem (e x), t.encode y, t.encode_mem y,
      rfl, rfl, (s.pair_mem_graph s e x (e x)).2 rfl⟩

end PartitionPilot.Forcing.BoundedFormula

end


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

namespace BoundedFormula

theorem truth_chronologyPairFormula {n} (z T : Fin n) (env : Fin n → ZFSet.{u}) :
    Truth (chronologyPairFormula z T) env ↔ env z ∈ chronologyPairs (env T) := by
  simp only [chronologyPairFormula, truth_exMem, Truth, truth_orderedPairFormula,
    truth_disj, mem_chronologyPairs]
  rfl

end BoundedFormula

end PartitionPilot.Forcing

end

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Definability_CodedInjectiveCones
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

namespace BoundedFormula

def graphCompositionFormula {n} (f g h : Fin n) : BoundedFormula n :=
  .allMem f (.allMem 0 (.allMem 0 (.allMem 2 (.allMem 0
    (imp (orderedPairFormula 4 2 0)
      (graphFiberEqualityFormula 0 2 g.succ.succ.succ.succ.succ h.succ.succ.succ.succ.succ))))))

end BoundedFormula

end



section
open SetRealization SetFormula
universe u

noncomputable def identityFunctionGraph (A : ZFSet.{u}) : ZFSet.{u} :=
  (SetMembers.presentation A).graph (SetMembers.presentation A) id

theorem mem_identityFunctionGraph (A z : ZFSet.{u}) :
    z ∈ identityFunctionGraph A ↔ ∃ x ∈ A, z = ZFSet.pair x x := by
  constructor
  · intro hz
    obtain ⟨x, eq⟩ := ((SetMembers.presentation A).mem_graph (SetMembers.presentation A) id z).1 hz
    exact ⟨SetMembers.raw x, SetMembers.raw_mem x, eq.symm⟩
  · rintro ⟨x, hx, rfl⟩
    have entry := ((SetMembers.presentation A).pair_mem_graph (SetMembers.presentation A) id (SetMembers.ofMem x hx) (SetMembers.ofMem x hx)).2 rfl
    change ZFSet.pair (SetMembers.raw (SetMembers.ofMem x hx)) (SetMembers.raw (SetMembers.ofMem x hx)) ∈ identityFunctionGraph A at entry
    simpa only [SetMembers.raw_ofMem] using entry

theorem pair_mem_identityFunctionGraph (A x y : ZFSet.{u}) :
    ZFSet.pair x y ∈ identityFunctionGraph A ↔ x = y ∧ x ∈ A := by
  rw [mem_identityFunctionGraph]
  constructor
  · rintro ⟨z, hz, equal⟩
    obtain ⟨rfl, rfl⟩ := ZFSet.pair_inj.1 equal
    exact ⟨rfl, hz⟩
  · rintro ⟨rfl, hx⟩
    exact ⟨x, hx, rfl⟩

theorem identityFunctionGraph_injection (A : ZFSet.{u}) : InjectionCode A A (identityFunctionGraph A) :=
  (SetMembers.presentation A).graph_injection (SetMembers.presentation A) id (fun _ _ h => h)

namespace TransitiveGround
variable (M : TransitiveGround.{u})

theorem identityFunctionGraph_mem
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    {A : ZFSet.{u}} (hA : A ∈ M.sets) : identityFunctionGraph A ∈ M.sets := by
  let phi : BoundedFormula 2 := .exMem 1 (BoundedFormula.orderedPairFormula 1 0 0)
  have truth (z : ZFSet.{u}) : BoundedFormula.Truth phi (extend z (extend A Fin.elim0)) ↔
      z ∈ identityFunctionGraph A := by
    simp only [phi, BoundedFormula.truth_exMem, BoundedFormula.truth_orderedPairFormula,
      extend, Fin.cases_zero]
    exact (mem_identityFunctionGraph A z).symm
  have equal : ZFSet.sep (fun z => BoundedFormula.Truth phi (extend z (extend A Fin.elim0))) (ZFSet.prod A A) =
      identityFunctionGraph A := by
    apply ZFSet.ext
    intro z
    rw [ZFSet.mem_sep, truth]
    exact ⟨And.right, fun hz => ⟨(identityFunctionGraph_injection A).function.1 hz, hz⟩⟩
  rw [← equal]
  exact M.bounded_separation_mem separation phi (extend A Fin.elim0)
    (Fin.cases hA (fun i => Fin.elim0 i)) (M.prod_mem pairing unions powers separation hA hA)

end TransitiveGround

end



section
universe u v

structure CodedDirectSystem (I : Type v) [Preorder I] where
  carrier : I → ZFSet.{u}
  map : ∀ {i j : I}, i ≤ j → ZFSet.{u}
  injection : ∀ {i j : I} (before : i ≤ j), InjectionCode (carrier i) (carrier j) (map before)
  identity : ∀ i, map (le_refl i) = identityFunctionGraph (carrier i)
  composition : ∀ {i j k : I} (first : i ≤ j) (second : j ≤ k),
    map (le_trans first second) = relationCompose (carrier i) (carrier j) (carrier k) (map first) (map second)
  common_upper : ∀ i j : I, ∃ k, i ≤ k ∧ j ≤ k

namespace CodedDirectSystem
variable {I : Type v} [Preorder I] (system : CodedDirectSystem.{u} I)

def Related (i : I) (x : ZFSet.{u}) (j : I) (y : ZFSet.{u}) : Prop :=
  ∃ k, ∃ first : i ≤ k, ∃ second : j ≤ k, ∃ z,
    ZFSet.pair x z ∈ system.map first ∧ ZFSet.pair y z ∈ system.map second

theorem map_entry_bounds {i j : I} (before : i ≤ j) {x y : ZFSet.{u}}
    (entry : ZFSet.pair x y ∈ system.map before) :
    x ∈ system.carrier i ∧ y ∈ system.carrier j :=
  ZFSet.pair_mem_prod.1 ((system.injection before).function.1 entry)

theorem map_entry_total {i j : I} (before : i ≤ j) {x : ZFSet.{u}}
    (member : x ∈ system.carrier i) : ∃ y, ZFSet.pair x y ∈ system.map before := by
  obtain ⟨y, entry, _⟩ := (system.injection before).function.2 x member
  exact ⟨y, entry⟩

theorem map_identity_entry {i : I} {x : ZFSet.{u}} (member : x ∈ system.carrier i) :
    ZFSet.pair x x ∈ system.map (le_refl i) := by
  rw [system.identity]
  exact (pair_mem_identityFunctionGraph _ _ _).2 ⟨rfl, member⟩

theorem map_comp_entry {i j k : I} (first : i ≤ j) (second : j ≤ k) {x y z : ZFSet.{u}}
    (xy : ZFSet.pair x y ∈ system.map first) (yz : ZFSet.pair y z ∈ system.map second) :
    ZFSet.pair x z ∈ system.map (le_trans first second) := by
  rw [system.composition first second]
  exact (pair_mem_relationCompose _ _ _ _ _ _ _).2
    ⟨(system.map_entry_bounds first xy).1, (system.map_entry_bounds second yz).2,
      y, (system.map_entry_bounds first xy).2, xy, yz⟩

end CodedDirectSystem

end



section
universe u

theorem GraphDiagonalCode.eq_identityFunctionGraph {A B f : ZFSet.{u}}
    (diagonal : GraphDiagonalCode f) (function : ZFSet.IsFunc A B f) :
    f = identityFunctionGraph A := by
  apply ZFSet.ext
  intro z
  constructor
  · intro hz
    obtain ⟨x, hx, y, _, rfl⟩ := ZFSet.mem_prod.1 (function.1 hz)
    exact (pair_mem_identityFunctionGraph A x y).2 ⟨diagonal x y hz, hx⟩
  · intro hz
    obtain ⟨x, hx, rfl⟩ := (mem_identityFunctionGraph A z).1 hz
    obtain ⟨v, entry, _⟩ := function.2 x hx
    have same : v = x := (diagonal x v entry).symm
    exact same ▸ entry

end



section
universe u v

structure CodedDirectPresentation {I : Type v} [Small.{u} I] [Preorder I]
    (system : CodedDirectSystem.{u} I) (T U A F : ZFSet.{u}) where
  key : I → ZFSet.{u}
  key_injective : Function.Injective key
  key_range : ZFSet.range key = T
  key_order : ∀ i j, i ≤ j ↔ key i = key j ∨ key i ∈ key j
  carrier_function : FunctionGraphOn T A
  carrier_entry : ∀ i, ZFSet.pair (key i) (system.carrier i) ∈ A
  map_function : FunctionGraphOn (chronologyPairs T) F
  map_entry : ∀ {i j} (before : i ≤ j), ZFSet.pair (ZFSet.pair (key j) (key i)) (system.map before) ∈ F
  carrier_bound : ∀ i, system.carrier i ⊆ U

namespace CodedDirectPresentation
variable {I : Type v} [Small.{u} I] [Preorder I] {system : CodedDirectSystem.{u} I}
variable {T U A F : ZFSet.{u}} (p : CodedDirectPresentation system T U A F)

theorem key_mem (i : I) : p.key i ∈ T := by
  have member : p.key i ∈ ZFSet.range p.key := ZFSet.mem_range.2 ⟨i, rfl⟩
  simpa only [p.key_range] using member

theorem exists_key {j : ZFSet.{u}} (member : j ∈ T) : ∃ i, p.key i = j :=
  ZFSet.mem_range.1 (p.key_range.symm ▸ member)

theorem label_mem (i : I) (x : ZFSet.{u}) :
    ZFSet.pair (p.key i) x ∈ indexedCarrierLabels T U A ↔ x ∈ system.carrier i :=
  pair_mem_indexedCarrierLabels_of_entry p.carrier_function (p.carrier_entry i) (p.carrier_bound i)

theorem label_cases {z : ZFSet.{u}} (member : z ∈ indexedCarrierLabels T U A) :
    ∃ i x, x ∈ system.carrier i ∧ z = ZFSet.pair (p.key i) x := by
  obtain ⟨j, hj, X, _, x, hx, _, rfl, entry⟩ := (mem_indexedCarrierLabels T U A z).1 member
  obtain ⟨i, rfl⟩ := p.exists_key hj
  have equal := p.carrier_function.unique entry (p.carrier_entry i)
  exact ⟨i, x, equal ▸ hx, rfl⟩

theorem map_lookup {i j : I} {f : ZFSet.{u}}
    (entry : ZFSet.pair (ZFSet.pair (p.key j) (p.key i)) f ∈ F) :
    ∃ before : i ≤ j, f = system.map before := by
  have ordered := (pair_mem_chronologyPairs T (p.key j) (p.key i)).1
    (p.map_function.pair_source entry)
  have before := (p.key_order i j).2 ordered.2.2
  exact ⟨before, p.map_function.unique entry (p.map_entry before)⟩

end CodedDirectPresentation

end



namespace CodedDirectSystem
universe u v
variable {I : Type v} [Preorder I] (system : CodedDirectSystem.{u} I)

theorem related_refl {i : I} {x : ZFSet.{u}} (member : x ∈ system.carrier i) :
    system.Related i x i x :=
  ⟨i, le_rfl, le_rfl, x, system.map_identity_entry member, system.map_identity_entry member⟩

theorem related_symm {i j : I} {x y : ZFSet.{u}} (related : system.Related i x j y) :
    system.Related j y i x := by
  obtain ⟨k, first, second, z, xz, yz⟩ := related
  exact ⟨k, second, first, z, yz, xz⟩

theorem related_trans {i j k : I} {x y z : ZFSet.{u}}
    (first : system.Related i x j y) (second : system.Related j y k z) :
    system.Related i x k z := by
  obtain ⟨a, ia, ja, v, xv, yv⟩ := first
  obtain ⟨b, jb, kb, w, yw, zw⟩ := second
  obtain ⟨c, ac, bc⟩ := system.common_upper a b
  obtain ⟨v', vv'⟩ := system.map_entry_total ac (system.map_entry_bounds ia xv).2
  obtain ⟨w', ww'⟩ := system.map_entry_total bc (system.map_entry_bounds jb yw).2
  have yv' := system.map_comp_entry ja ac yv vv'
  have yw' := system.map_comp_entry jb bc yw ww'
  have equal : v' = w' :=
    (show FunctionGraphOn (system.carrier j) (system.map (le_trans ja ac)) from
      ⟨system.carrier c, (system.injection (le_trans ja ac)).function⟩).unique yv' yw'
  refine ⟨c, le_trans ia ac, le_trans kb bc, v', system.map_comp_entry ia ac xv vv', ?_⟩
  exact equal.symm ▸ system.map_comp_entry kb bc zw ww'

theorem related_same_iff {i : I} {x y : ZFSet.{u}} :
    system.Related i x i y ↔ x = y ∧ x ∈ system.carrier i := by
  constructor
  · rintro ⟨k, first, second, z, xz, yz⟩
    exact ⟨(system.injection first).injective x y z xz yz, (system.map_entry_bounds first xz).1⟩
  · rintro ⟨rfl, member⟩
    exact system.related_refl member

theorem related_same_iff_eq {i : I} {x y : ZFSet.{u}} (member : x ∈ system.carrier i) :
    system.Related i x i y ↔ x = y := by
  rw [system.related_same_iff]
  exact and_iff_left member

theorem related_of_entry {i j : I} (before : i ≤ j) {x y : ZFSet.{u}}
    (entry : ZFSet.pair x y ∈ system.map before) : system.Related i x j y :=
  ⟨j, before, le_rfl, y, entry, system.map_identity_entry (system.map_entry_bounds before entry).2⟩

theorem related_map_left_iff {i j k : I} (before : i ≤ j) {x y z : ZFSet.{u}}
    (entry : ZFSet.pair x y ∈ system.map before) :
    system.Related i x k z ↔ system.Related j y k z := by
  have step := system.related_of_entry before entry
  exact ⟨fun related => system.related_trans (system.related_symm step) related,
    fun related => system.related_trans step related⟩

theorem related_map_right_iff {i j k : I} (before : i ≤ j) {x y z : ZFSet.{u}}
    (entry : ZFSet.pair x y ∈ system.map before) :
    system.Related k z i x ↔ system.Related k z j y := by
  have step := system.related_of_entry before entry
  exact ⟨fun related => system.related_trans related step,
    fun related => system.related_trans related (system.related_symm step)⟩

theorem related_iff_common_images {i j k : I} (first : i ≤ k) (second : j ≤ k)
    {x y v w : ZFSet.{u}} (xv : ZFSet.pair x v ∈ system.map first)
    (yw : ZFSet.pair y w ∈ system.map second) :
    system.Related i x j y ↔ v = w := by
  rw [system.related_map_left_iff first xv, system.related_map_right_iff second yw]
  exact system.related_same_iff_eq (system.map_entry_bounds first xv).2

end CodedDirectSystem



end PartitionPilot.Forcing

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

namespace PartitionPilot.Forcing.SetFormula

universe u

def atomicApplication {k m : Nat} (E : SetFormula (k + 3))
    (params : Fin k → Fin m) (p x y : Fin m) : SetFormula m :=
  reindex (extend p (extend x (extend y params))) E

def membershipFormula {k m : Nat} (E : SetFormula (k + 3)) (c o : Fin k)
    (params : Fin k → Fin m) (p σ τ : Fin m) : SetFormula m :=
  allConditions (params c) <|
    imp (pairMembershipFormula 0 p.succ (params o).succ) <|
    exConditions (params c).succ <| ex <|
    exConditions (params c).succ.succ.succ <|
    .conj (pairMembershipFormula 1 0 τ.succ.succ.succ.succ) <|
    .conj (pairMembershipFormula 2 3 (params o).succ.succ.succ.succ) <|
    .conj (pairMembershipFormula 2 0 (params o).succ.succ.succ.succ) <|
    atomicApplication E (fun j => (params j).succ.succ.succ.succ) 2 σ.succ.succ.succ.succ 1

end PartitionPilot.Forcing.SetFormula



namespace PartitionPilot.Forcing.SetFormula

def swapEquality {k : Nat} (E : SetFormula (k + 3)) : SetFormula (k + 3) :=
  atomicApplication E (fun j => j.succ.succ.succ) 0 2 1

def matchingDirectionFormula {k m : Nat} (E : SetFormula (k + 3)) (c o : Fin k)
    (params : Fin k → Fin m) (p σ τ : Fin m) : SetFormula m :=
  .all <| allConditions (params c).succ <|
    imp (pairMembershipFormula 1 0 σ.succ.succ) <|
    allConditions (params c).succ.succ <|
    imp (.conj (pairMembershipFormula 0 p.succ.succ.succ (params o).succ.succ.succ)
      (pairMembershipFormula 0 1 (params o).succ.succ.succ)) <|
    membershipFormula E c o (fun j => (params j).succ.succ.succ) 0 2 τ.succ.succ.succ

def equalityStepFormula {k m : Nat} (E : SetFormula (k + 3)) (c o : Fin k)
    (params : Fin k → Fin m) (p σ τ : Fin m) : SetFormula m :=
  .conj (matchingDirectionFormula E c o params p σ τ)
    (matchingDirectionFormula (swapEquality E) c o params p τ σ)

end PartitionPilot.Forcing.SetFormula

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

namespace PartitionPilot.Forcing.SetFormula

def equalityStateFormula : SetFormula 4 :=
  exConditions 2 <| ex <| ex <|
    .conj (orderedTripleFormula 3 2 1 0)
      (equalityStepFormula codedRelationFormula 1 2 (fun j => j.succ.succ.succ.succ) 2 1 0)

end PartitionPilot.Forcing.SetFormula

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

namespace PartitionPilot.Forcing.SetFormula

def equalityCertificateFormula : SetFormula 3 := postfixedFormula equalityStateFormula

end PartitionPilot.Forcing.SetFormula

end



namespace PartitionPilot.Forcing.SetFormula

universe u v

def uniformEqualityFormula : SetFormula 5 :=
  ex (.conj (atomicApplication equalityCertificateFormula Fin.elim0 0 4 5)
    (tripleMembershipFormula 1 2 3 0))

def liftedEqualityFormula {k : Nat} (c o : Fin k) : SetFormula (k + 3) :=
  atomicApplication uniformEqualityFormula
    (extend c.succ.succ.succ (extend o.succ.succ.succ Fin.elim0)) 0 1 2

end PartitionPilot.Forcing.SetFormula

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Forcing_UniformGroundNames
attribute [-instance] _root_.OAI.PartitionPilot.Forcing.GroundMainPrefix.withTopSmall
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI



namespace PartitionPilot.Forcing.SetFormula

universe u

def domainApplication {k m : Nat} (N : SetFormula (k + 1))
    (params : Fin k → Fin m) (x : Fin m) : SetFormula m := reindex (extend x params) N

def forcingTranslation {k : Nat} (A : ForcingPrimitives k) :
    {n m : Nat} → SetFormula n → (Fin k → Fin m) → Fin m → (Fin n → Fin m) → SetFormula m
  | _, _, .equal i j, params, p, names => atomicApplication A.equality params p (names i) (names j)
  | _, _, .mem i j, params, p, names =>
      membershipFormula A.equality A.carrier A.order params p (names i) (names j)
  | _, _, .neg φ, params, p, names =>
      allConditions (params A.carrier) <|
        imp (pairMembershipFormula 0 p.succ (params A.order).succ) <|
        .neg (forcingTranslation A φ (fun j => (params j).succ) 0 (fun i => (names i).succ))
  | _, _, .conj φ ψ, params, p, names =>
      .conj (forcingTranslation A φ params p names) (forcingTranslation A ψ params p names)
  | _, _, .all φ, params, p, names =>
      .all <| imp (domainApplication A.domain (fun j => (params j).succ) 0) <|
        forcingTranslation A φ (fun j => (params j).succ) p.succ
          (extend 0 (fun i => (names i).succ))

end PartitionPilot.Forcing.SetFormula



section

namespace PartitionPilot.Forcing.SetFormula

def withGroundEquality {k : Nat} (c o : Fin k) (N : SetFormula (k + 1)) : ForcingPrimitives k where
  carrier := c
  order := o
  equality := liftedEqualityFormula c o
  domain := N

end PartitionPilot.Forcing.SetFormula

end


namespace PartitionPilot.Forcing.SetFormula

def uniformNameFormula : SetFormula 2 :=
  ex (.conj (domainApplication nameCertificateFormula (extend 2 Fin.elim0) 0) (.mem 1 0))

def liftedNameFormula {k : Nat} (c : Fin k) : SetFormula (k + 1) :=
  domainApplication uniformNameFormula (extend c.succ Fin.elim0) 0

end PartitionPilot.Forcing.SetFormula

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

def ordinaryGroundPrimitives {k : Nat} (c o : Fin k) : ForcingPrimitives k :=
  withGroundEquality c o (liftedNameFormula c)

end PartitionPilot.Forcing.SetFormula

end


end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Definability_SeparationFulfillmentCodes
attribute [-instance] _root_.OAI.PartitionPilot.Forcing.GroundMainPrefix.withTopSmall
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace PartitionPilot.Forcing

namespace BoundedFormula

open SetFormula
universe u

def productRelationFormula {n} (a b c f : Fin n) : BoundedFormula n :=
  .allMem f (exMem a.succ (exMem b.succ.succ
    (exMem c.succ.succ.succ (orderedTripleFormula 3 2 1 0))))

def productFunctionFormula {n} (a b c f : Fin n) : BoundedFormula n :=
  .conj (productRelationFormula a b c f) (.allMem a (.allMem b.succ
    (exMem c.succ.succ (.conj (tripleMembershipFormula 2 1 0 f.succ.succ.succ)
      (.allMem c.succ.succ.succ (imp
        (tripleMembershipFormula 3 2 0 f.succ.succ.succ.succ) (.equal 0 1)))))))

end BoundedFormula




universe u

namespace BoundedFormula

open SetFormula

def posetActionFormula {n} (g p m e r a : Fin n) : BoundedFormula n :=
  .conj (productFunctionFormula g p p a) (.conj (actionOneFormula p e a)
    (.conj (actionMulFormula g p m a) (actionMonotoneFormula g p r a)))

end BoundedFormula

namespace BoundedFormula

def separationActorFormula {n} (P r Q R ν A e W k : Fin n) : BoundedFormula n :=
  .allMem Q (imp (pairMembershipFormula W.succ 0 e.succ)
    (.conj
      (.allMem Q.succ (imp (pairMembershipFormula 0 1 R.succ.succ)
        (tripleMembershipFormula k.succ.succ 0 0 A.succ.succ)))
      (.allMem P.succ (.allMem P.succ.succ (.allMem Q.succ.succ.succ
        (.allMem Q.succ.succ.succ.succ (.allMem Q.succ.succ.succ.succ.succ
          (imp (pairMembershipFormula W.succ.succ.succ.succ.succ.succ 4 r.succ.succ.succ.succ.succ.succ)
            (imp (pairMembershipFormula W.succ.succ.succ.succ.succ.succ 3 r.succ.succ.succ.succ.succ.succ)
              (imp (pairMembershipFormula 4 2 e.succ.succ.succ.succ.succ.succ)
                (imp (pairMembershipFormula 3 1 e.succ.succ.succ.succ.succ.succ)
                  (imp (tripleMembershipFormula k.succ.succ.succ.succ.succ.succ 2 0 A.succ.succ.succ.succ.succ.succ)
                    (tripleMembershipFormula 0 1 5 ν.succ.succ.succ.succ.succ.succ)))))))))))))

def separationFulfillmentFormula {n} (P r Q R ν H A e : Fin n) : BoundedFormula n :=
  .allMem P (.exMem H.succ (separationActorFormula P.succ.succ r.succ.succ Q.succ.succ
    R.succ.succ ν.succ.succ A.succ.succ e.succ.succ 1 0))

end BoundedFormula


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

namespace PartitionPilot.Forcing.PosetActionCode

open SetRealization
universe u
variable {G P m i e R A : ZFSet.{u}} (h : PosetActionCode G P m e R A)

noncomputable def act (g : SetMembers G) (p : SetMembers P) : SetMembers P :=
  ((SetMembers.presentation G).product (SetMembers.presentation P)).decodeFunction
    (SetMembers.presentation P) A h.function (g, p)

theorem act_mem (g : SetMembers G) (p : SetMembers P) :
    ZFSet.pair (ZFSet.pair (SetMembers.raw g) (SetMembers.raw p)) (SetMembers.raw (h.act g p)) ∈ A :=
  ((SetMembers.presentation G).product (SetMembers.presentation P)).decodeFunction_mem
    (SetMembers.presentation P) A h.function (g, p)

theorem act_eq_iff (g : SetMembers G) (p q : SetMembers P) : h.act g p = q ↔
    ZFSet.pair (ZFSet.pair (SetMembers.raw g) (SetMembers.raw p)) (SetMembers.raw q) ∈ A :=
  ((SetMembers.presentation G).product (SetMembers.presentation P)).decodeFunction_iff
    (SetMembers.presentation P) A h.function (g, p) q

theorem act_one (group : GroupCode G m i e) (p : SetMembers P) :
    letI _decodedGroup := group.toGroup
    h.act 1 p = p := by
  let decodedGroup := group.toGroup
  apply (h.act_eq_iff _ _ _).2
  change ZFSet.pair (ZFSet.pair (SetMembers.raw group.one) (SetMembers.raw p)) (SetMembers.raw p) ∈ A
  rw [group.raw_one]
  exact h.one _ (SetMembers.raw_mem p)

theorem act_mul (group : GroupCode G m i e) (g j : SetMembers G) (p : SetMembers P) :
    letI _decodedGroup := group.toGroup
    h.act (g * j) p = h.act g (h.act j p) := by
  let decodedGroup := group.toGroup
  apply (h.act_eq_iff _ _ _).2
  exact h.mul _ (SetMembers.raw_mem g) _ (SetMembers.raw_mem j) _ (SetMembers.raw_mem (g * j))
    _ (SetMembers.raw_mem p) _ (SetMembers.raw_mem (h.act j p)) _ (SetMembers.raw_mem (h.act g (h.act j p)))
    (group.mul_mem g j) (h.act_mem j p) (h.act_mem g (h.act j p))

theorem act_inv_left (group : GroupCode G m i e) (g : SetMembers G) (p : SetMembers P) :
    letI _decodedGroup := group.toGroup
    h.act g⁻¹ (h.act g p) = p := by
  let decodedGroup := group.toGroup
  rw [← h.act_mul group, inv_mul_cancel, h.act_one group]

theorem act_inv_right (group : GroupCode G m i e) (g : SetMembers G) (p : SetMembers P) :
    letI _decodedGroup := group.toGroup
    h.act g (h.act g⁻¹ p) = p := by
  let decodedGroup := group.toGroup
  rw [← h.act_mul group, mul_inv_cancel, h.act_one group]

theorem act_monotone (order : PartialOrderCode P R) (g : SetMembers G) :
    letI _decodedOrder := order.toPartialOrder
    Monotone (h.act g) := by
  let decodedOrder := order.toPartialOrder
  intro p q pq
  exact h.monotone _ (SetMembers.raw_mem g) _ (SetMembers.raw_mem p) _ (SetMembers.raw_mem q)
    _ (SetMembers.raw_mem (h.act g p)) _ (SetMembers.raw_mem (h.act g q))
    (h.act_mem g p) (h.act_mem g q) pq

theorem act_le_iff (group : GroupCode G m i e) (order : PartialOrderCode P R)
    (g : SetMembers G) (p q : SetMembers P) :
    letI _decodedGroup := group.toGroup
    letI _decodedOrder := order.toPartialOrder
    h.act g p ≤ h.act g q ↔ p ≤ q := by
  let decodedGroup := group.toGroup
  let decodedOrder := order.toPartialOrder
  constructor
  · intro le
    have back := h.act_monotone order g⁻¹ le
    simpa only [h.act_inv_left group] using back
  · exact fun le => h.act_monotone order g le

end PartitionPilot.Forcing.PosetActionCode

end


section

namespace PartitionPilot.Forcing.BoundedFormula

open SetFormula
universe u

theorem truth_actionRestrictionEntryFormula {n} (z g p : Fin n) (env : Fin n → ZFSet.{u}) :
    Truth (actionRestrictionEntryFormula z g p) env ↔
      ∃ h ∈ env g, ∃ x ∈ env p, ∃ y ∈ env p,
        env z = ZFSet.pair (ZFSet.pair h x) y := by
  simp only [actionRestrictionEntryFormula, truth_exMem, truth_orderedTripleFormula]
  rfl

end PartitionPilot.Forcing.BoundedFormula

end


namespace PartitionPilot.Forcing.PosetAction

open SetRealization
universe u
variable {G I : Type u} [Group G] [PartialOrder I]

noncomputable def productColumns (a : PosetAction G I) (C : Type u) [PartialOrder C] :
    PosetAction G (I × C) where
  iso g := {
    toFun := fun x => (a.iso g x.1, x.2)
    invFun := fun x => ((a.iso g).symm x.1, x.2)
    left_inv := fun x => Prod.ext ((a.iso g).symm_apply_apply x.1) rfl
    right_inv := fun x => Prod.ext ((a.iso g).apply_symm_apply x.1) rfl
    map_rel_iff' := by
      intro x y
      exact and_congr (a.iso g).map_rel_iff Iff.rfl }
  one x := Prod.ext (a.one x.1) rfl
  mul g h x := Prod.ext (a.mul g h x.1) rfl

theorem mem_productColumns_actionGraph {C : Type u} [PartialOrder C]
    (a : PosetAction G I) (s : Presentation I) (c : Presentation C) (t : Presentation G)
    (z : ZFSet.{u}) :
    z ∈ (a.productColumns C).actionGraph (s.product c) t ↔ ∃ g i k,
      z = ZFSet.pair (ZFSet.pair (t.encode g) (ZFSet.pair (s.encode i) (c.encode k)))
        (ZFSet.pair (s.encode (a.iso g i)) (c.encode k)) := by
  rw [actionGraph, Presentation.mem_graph]
  constructor
  · rintro ⟨⟨g, i, k⟩, eq⟩
    exact ⟨g, i, k, eq.symm⟩
  · rintro ⟨g, i, k, eq⟩
    exact ⟨(g, i, k), eq.symm⟩

end PartitionPilot.Forcing.PosetAction

namespace PartitionPilot.Forcing.BoundedFormula

open SetFormula SetRealization
universe u

def productColumnsEntryFormula {n} (z g i c q a : Fin n) : BoundedFormula n :=
  exMem g (exMem i.succ (exMem i.succ.succ (exMem c.succ.succ.succ
    (exMem q.succ.succ.succ.succ (exMem q.succ.succ.succ.succ.succ
      (.conj (orderedPairFormula 1 4 2)
        (.conj (orderedPairFormula 0 3 2)
          (.conj (orderedTripleFormula z.succ.succ.succ.succ.succ.succ 5 1 0)
            (tripleMembershipFormula 5 4 3 a.succ.succ.succ.succ.succ.succ)))))))))

theorem truth_productColumnsEntryFormula {n} (z g i c q a : Fin n)
    (env : Fin n → ZFSet.{u}) :
    Truth (productColumnsEntryFormula z g i c q a) env ↔
      ∃ h ∈ env g, ∃ x ∈ env i, ∃ y ∈ env i, ∃ k ∈ env c,
        ∃ v ∈ env q, ∃ w ∈ env q,
          v = ZFSet.pair x k ∧ w = ZFSet.pair y k ∧
          env z = ZFSet.pair (ZFSet.pair h v) w ∧
          ZFSet.pair (ZFSet.pair h x) y ∈ env a := by
  simp only [productColumnsEntryFormula, truth_exMem, Truth, truth_orderedPairFormula,
    truth_orderedTripleFormula, truth_tripleMembershipFormula]
  rfl

theorem productColumnsEntry_correct {G I C : Type u} [Group G] [PartialOrder I] [PartialOrder C]
    (a : PosetAction G I) (s : Presentation I) (c : Presentation C) (t : Presentation G)
    (z : ZFSet.{u}) :
    Truth (productColumnsEntryFormula 0 1 2 3 4 5)
      (extend z (extend t.carrier (extend s.carrier (extend c.carrier
        (extend (s.product c).carrier (extend (a.actionGraph s t) Fin.elim0)))))) ↔
      z ∈ (a.productColumns C).actionGraph (s.product c) t := by
  rw [truth_productColumnsEntryFormula]
  constructor
  · rintro ⟨g, hg, i, hi, j, hj, k, hk, x, _, y, _, xeq, yeq, eq, rel⟩
    obtain ⟨g, rfl⟩ := (t.mem_carrier g).1 hg
    obtain ⟨i, rfl⟩ := (s.mem_carrier i).1 hi
    obtain ⟨j, rfl⟩ := (s.mem_carrier j).1 hj
    obtain ⟨k, rfl⟩ := (c.mem_carrier k).1 hk
    subst x
    subst y
    change z = ZFSet.pair (ZFSet.pair (t.encode g) (ZFSet.pair (s.encode i) (c.encode k)))
      (ZFSet.pair (s.encode j) (c.encode k)) at eq
    rw [eq]
    exact ((a.productColumns C).triple_mem_actionGraph (s.product c) t g (i, k) (j, k)).2
      (Prod.ext ((a.triple_mem_actionGraph s t g i j).1 rel) rfl)
  · intro member
    obtain ⟨g, i, k, eq⟩ := (a.mem_productColumns_actionGraph s c t z).1 member
    exact ⟨t.encode g, t.encode_mem g, s.encode i, s.encode_mem i,
      s.encode (a.iso g i), s.encode_mem _, c.encode k, c.encode_mem k,
      (s.product c).encode (i, k), (s.product c).encode_mem _,
      (s.product c).encode (a.iso g i, k), (s.product c).encode_mem _, rfl, rfl, eq,
      (a.triple_mem_actionGraph s t g i (a.iso g i)).2 rfl⟩

end PartitionPilot.Forcing.BoundedFormula

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

noncomputable def supportBasisCode (b : Presentation I) (t : Presentation G)
    (K : I → Subgroup G) : ZFSet.{u} := (b.product t).subset (fun z => z.2 ∈ K z.1)

end PartitionPilot.Forcing



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

theorem point_inv_right (g : G) (x : I) : a.iso g (a.iso g⁻¹ x) = x := by
  rw [← a.mul, mul_inv_cancel, a.one]

def principalFix (C : I) : Subgroup G where
  carrier := {g | ∀ x, x ≤ C → a.iso g x = x}
  one_mem' := fun x _ => a.one x
  mul_mem' {g h} hg hh x lower := by rw [a.mul, hh x lower, hg x lower]
  inv_mem' {g} hg x lower := by
    apply (a.iso g).injective
    exact (a.point_inv_right g x).trans (hg x lower).symm

end PartitionPilot.Forcing.PosetAction



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


namespace PartitionPilot.Forcing.BoundedFormula

open SetFormula
universe u

theorem truth_ordinalImagePairFormula {k} (m n a f : Fin k) (env : Fin k → ZFSet.{u}) :
    Truth (ordinalImagePairFormula m n a f) env ↔
      ∃ x ∈ env a, ∃ y ∈ env a, ZFSet.pair x (env m) ∈ env f ∧
        ZFSet.pair y (env n) ∈ env f ∧ (x = y ∨ x ∈ y) := by
  simp only [ordinalImagePairFormula, truth_exMem, Truth, truth_pairMembershipFormula, truth_disj]
  rfl

theorem truth_ordinalImageEntryFormula {k} (z a n f : Fin k) (env : Fin k → ZFSet.{u}) :
    Truth (ordinalImageEntryFormula z a n f) env ↔
      env z ∈ ordinalImageOrder (env a) (env n) (env f) := by
  simp only [ordinalImageEntryFormula, truth_exMem, Truth, truth_orderedPairFormula,
    truth_ordinalImagePairFormula]
  exact (mem_ordinalImageOrder (env a) (env n) (env f) (env z)).symm

theorem truth_ordinalImageFormula {k} (r a n f : Fin k) (env : Fin k → ZFSet.{u}) :
    Truth (ordinalImageFormula r a n f) env ↔
      env r = ordinalImageOrder (env a) (env n) (env f) := by
  simp only [ordinalImageFormula, Truth, truth_ordinalImageEntryFormula,
    truth_imp, truth_ordinalImagePairFormula, truth_pairMembershipFormula]
  change ((∀ z ∈ env r, z ∈ ordinalImageOrder (env a) (env n) (env f)) ∧
    ∀ m ∈ env n, ∀ v ∈ env n,
      (∃ x ∈ env a, ∃ y ∈ env a, ZFSet.pair x m ∈ env f ∧
        ZFSet.pair y v ∈ env f ∧ (x = y ∨ x ∈ y)) → ZFSet.pair m v ∈ env r) ↔ _
  constructor
  · rintro ⟨subset, covers⟩
    apply ZFSet.ext
    intro z
    constructor
    · exact subset z
    · intro hz
      obtain ⟨m, hm, n, hn, eq, witnesses⟩ := (mem_ordinalImageOrder _ _ _ z).1 hz
      exact eq.symm ▸ covers m hm n hn witnesses
  · intro eq
    refine ⟨fun _ hz => eq ▸ hz, ?_⟩
    intro m hm n hn witnesses
    rw [eq]
    exact (mem_ordinalImageOrder _ _ _ _).2 ⟨m, hm, n, hn, rfl, witnesses⟩

end PartitionPilot.Forcing.BoundedFormula

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Models_GroundSuccessorInjections
attribute [-instance] _root_.OAI.PartitionPilot.Forcing.GroundMainPrefix.withTopSmall
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace PartitionPilot.Forcing

universe u

theorem shiftedInjectionGraph_no_zero (D f x : ZFSet.{u}) :
    ZFSet.pair x ∅ ∉ shiftedInjectionGraph D f := by
  intro rel
  obtain ⟨_, n, _, eq, _⟩ := (pair_mem_shiftedInjectionGraph D f x ∅).1 rel
  exact setSuccessor_ne_empty n eq.symm

namespace InjectionCode

theorem shift {D f : ZFSet.{u}} (h : InjectionCode D ZFSet.omega f) :
    InjectionCode D ZFSet.omega (shiftedInjectionGraph D f) := by
  refine ⟨⟨fun _ hz => (ZFSet.mem_sep.1 hz).1, ?_⟩, ?_⟩
  · intro x hx
    obtain ⟨n, rel, unique⟩ := h.function.2 x hx
    have hn := (ZFSet.pair_mem_prod.1 (h.function.1 rel)).2
    refine ⟨insert n n, (pair_mem_shiftedInjectionGraph D f x _).2 ⟨hx, n, hn, rfl, rel⟩, ?_⟩
    intro y hy
    obtain ⟨_, m, _, eq, hm⟩ := (pair_mem_shiftedInjectionGraph D f x y).1 hy
    rw [eq, unique m hm]
  · intro x y z hx hy
    obtain ⟨_, n, _, zn, xn⟩ := (pair_mem_shiftedInjectionGraph D f x z).1 hx
    obtain ⟨_, m, _, zm, ym⟩ := (pair_mem_shiftedInjectionGraph D f y z).1 hy
    have eq := setSuccessor_injective (zn.symm.trans zm)
    exact h.injective x y m (eq ▸ xn) ym

end InjectionCode

namespace InjectionCode

theorem adjoin_fresh {D f a : ZFSet.{u}} (h : InjectionCode D ZFSet.omega f) (fresh : a ∉ D) :
    InjectionCode (insert a D) ZFSet.omega (adjoinInjectionGraph D f a) := by
  have shifted := h.shift
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · intro z hz
    rcases ZFSet.mem_insert_iff.1 hz with rfl | hz
    · exact ZFSet.pair_mem_prod.2 ⟨ZFSet.mem_insert a D, ZFSet.omega_zero⟩
    · obtain ⟨x, hx, y, hy, rfl⟩ := ZFSet.mem_prod.1 (shifted.function.1 hz)
      exact ZFSet.pair_mem_prod.2 ⟨ZFSet.mem_insert_of_mem a hx, hy⟩
  · intro x hx
    rcases ZFSet.mem_insert_iff.1 hx with eq | hx
    · subst x
      refine ⟨∅, (pair_mem_adjoinInjectionGraph D f a a ∅).2 (Or.inl ⟨rfl, rfl⟩), ?_⟩
      intro y hy
      rcases (pair_mem_adjoinInjectionGraph D f a a y).1 hy with eq | rel
      · exact eq.2
      · exact False.elim (fresh ((pair_mem_shiftedInjectionGraph D f a y).1 rel).1)
    · obtain ⟨y, rel, unique⟩ := shifted.function.2 x hx
      refine ⟨y, (pair_mem_adjoinInjectionGraph D f a x y).2 (Or.inr rel), ?_⟩
      intro z hz
      rcases (pair_mem_adjoinInjectionGraph D f a x z).1 hz with eq | rel
      · exact False.elim (fresh (eq.1 ▸ hx))
      · exact unique z rel
  · intro x y z hx hy
    rcases (pair_mem_adjoinInjectionGraph D f a x z).1 hx with eqx | shiftx
    · rcases (pair_mem_adjoinInjectionGraph D f a y z).1 hy with eqy | shifty
      · exact eqx.1.trans eqy.1.symm
      · rw [eqx.2] at shifty
        exact False.elim (shiftedInjectionGraph_no_zero D f y shifty)
    · rcases (pair_mem_adjoinInjectionGraph D f a y z).1 hy with eqy | shifty
      · rw [eqy.2] at shiftx
        exact False.elim (shiftedInjectionGraph_no_zero D f x shiftx)
      · exact shifted.injective x y z shiftx shifty

end InjectionCode

end PartitionPilot.Forcing



namespace PartitionPilot.Forcing.BoundedFormula

open SetFormula
universe u

def shiftedInjectionEntryFormula {n} (z d o f : Fin n) : BoundedFormula n :=
  exMem d (exMem o.succ (exMem o.succ.succ
    (.conj (successorFormula 0 1)
      (.conj (orderedPairFormula z.succ.succ.succ 2 0)
        (pairMembershipFormula 2 1 f.succ.succ.succ)))))

theorem truth_shiftedInjectionEntryFormula {n} (z d o f : Fin n)
    (env : Fin n → ZFSet.{u}) (omega : env o = ZFSet.omega) :
    Truth (shiftedInjectionEntryFormula z d o f) env ↔
      ∃ x ∈ env d, ∃ m ∈ ZFSet.omega,
        env z = ZFSet.pair x (insert m m) ∧ ZFSet.pair x m ∈ env f := by
  simp only [shiftedInjectionEntryFormula, truth_exMem, Truth,
    truth_successorFormula, truth_orderedPairFormula, truth_pairMembershipFormula]
  change (∃ x ∈ env d, ∃ m ∈ env o, ∃ k ∈ env o,
    k = insert m m ∧ env z = ZFSet.pair x k ∧ ZFSet.pair x m ∈ env f) ↔ _
  rw [omega]
  constructor
  · rintro ⟨x, hx, m, hm, k, _, rfl, eq, rel⟩
    exact ⟨x, hx, m, hm, eq, rel⟩
  · rintro ⟨x, hx, m, hm, eq, rel⟩
    exact ⟨x, hx, m, hm, insert m m, ZFSet.omega_succ hm, rfl, eq, rel⟩

end PartitionPilot.Forcing.BoundedFormula

namespace PartitionPilot.Forcing.TransitiveGround

open SetFormula
universe u
variable (M : TransitiveGround.{u})

theorem shiftedInjectionGraph_mem
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (infinite : Realize M.sets infinity Fin.elim0)
    {D f : ZFSet.{u}} (hD : D ∈ M.sets) (hf : f ∈ M.sets) :
    shiftedInjectionGraph D f ∈ M.sets := by
  have hO := M.omega_mem separation infinite
  have bound := M.prod_mem pairing unions powers separation hD hO
  let params := extend D (extend ZFSet.omega (extend f Fin.elim0))
  have members : ∀ i, params i ∈ M.sets :=
    Fin.cases hD (Fin.cases hO (Fin.cases hf (fun i => Fin.elim0 i)))
  have selected := M.separation_mem separation
    (BoundedFormula.shiftedInjectionEntryFormula 0 1 2 3).toFormula params members bound
  have eq : ZFSet.sep (fun z => Realize M.sets
      (BoundedFormula.shiftedInjectionEntryFormula 0 1 2 3).toFormula (extend z params))
      (ZFSet.prod D ZFSet.omega) = shiftedInjectionGraph D f := by
    apply ZFSet.ext
    intro z
    rw [ZFSet.mem_sep, shiftedInjectionGraph, ZFSet.mem_sep]
    apply and_congr_right
    intro hz
    exact (BoundedFormula.realize_toFormula M _ _
      (Fin.cases (M.transitive bound hz) members)).trans
        (BoundedFormula.truth_shiftedInjectionEntryFormula 0 1 2 3 (extend z params) rfl)
  exact eq ▸ selected

theorem adjoinInjectionGraph_mem
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (infinite : Realize M.sets infinity Fin.elim0)
    {D f a : ZFSet.{u}} (hD : D ∈ M.sets) (hf : f ∈ M.sets) (ha : a ∈ M.sets) :
    adjoinInjectionGraph D f a ∈ M.sets :=
  M.insert_mem pairing unions
    (M.orderedPair_mem pairing ha (M.empty_mem ⟨a, ha⟩))
    (M.shiftedInjectionGraph_mem pairing unions powers separation infinite hD hf)

theorem groundEmbeddable_insert
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (infinite : Realize M.sets infinity Fin.elim0)
    {D a : ZFSet.{u}} (hD : D ∈ M.sets) (ha : a ∈ M.sets)
    (small : M.groundEmbeddable D ZFSet.omega) :
    M.groundEmbeddable (insert a D) ZFSet.omega := by
  classical
  by_cases member : a ∈ D
  · have eq : insert a D = D := by
      apply ZFSet.ext
      intro z
      rw [ZFSet.mem_insert_iff]
      exact ⟨fun h => h.elim (fun eq => eq.symm ▸ member) id, Or.inr⟩
    exact eq.symm ▸ small
  · obtain ⟨f, hf, code⟩ := small
    exact ⟨adjoinInjectionGraph D f a,
      M.adjoinInjectionGraph_mem pairing unions powers separation infinite hD hf ha,
      code.adjoin_fresh member⟩

end PartitionPilot.Forcing.TransitiveGround

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

def externalSignCode (b : Bool) : ZFSet.{u} := natSetCode (if b then 1 else 0)

def externalActorSymbol (g : ZFSet.{u}) : ZFSet.{u} := ZFSet.pair (natSetCode 0) g

def externalLetterSymbol (s : ZFSet.{u}) (b : Bool) : ZFSet.{u} :=
  ZFSet.pair (natSetCode 1) (ZFSet.pair s (externalSignCode b))

def externalGeneratorAlphabet (G S : ZFSet.{u}) : ZFSet.{u} :=
  ZFSet.prod {natSetCode 0} G ∪ ZFSet.prod {natSetCode 1} (ZFSet.prod S (natSetCode 2))






namespace BoundedFormula

theorem truth_finiteWordFormula {n} (omega alphabet graph : Fin n)
    (env : Fin n → ZFSet.{u}) :
    Truth (finiteWordFormula omega alphabet graph) env ↔
      ∃ N ∈ env omega, ZFSet.IsFunc N (env alphabet) (env graph) := by
  simp only [finiteWordFormula, truth_exMem, truth_functionFormula]
  rfl

end BoundedFormula

theorem finiteWord_domain_unique {m n : Nat} {A B f : ZFSet.{u}}
    (first : ZFSet.IsFunc (natSetCode m) A f)
    (second : ZFSet.IsFunc (natSetCode n) B f) : m = n := by
  apply natSetCode_injective
  apply ZFSet.ext
  intro x
  constructor
  · intro hx
    obtain ⟨y, entry, _⟩ := first.2 x hx
    exact (ZFSet.pair_mem_prod.1 (second.1 entry)).1
  · intro hx
    obtain ⟨y, entry, _⟩ := second.2 x hx
    exact (ZFSet.pair_mem_prod.1 (first.1 entry)).1

end PartitionPilot.Forcing


namespace PartitionPilot.Forcing
open SetRealization SetFormula
universe u

def taggedSumCarrier (A B : ZFSet.{u}) : ZFSet.{u} :=
  ZFSet.prod {natSetCode 0} A ∪ ZFSet.prod {natSetCode 1} B

end PartitionPilot.Forcing

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Forcing_CodedDenseOrders
attribute [-instance] _root_.OAI.PartitionPilot.Forcing.GroundMainPrefix.withTopSmall
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace PartitionPilot.Forcing

open Compression.RecursiveMaps
universe u

def StrictLinearOrderCode.toLinearHeightOrder {D r : ZFSet.{u}} (code : StrictLinearOrderCode D r) :
    LinearHeightOrder {x : ZFSet.{u} // x ∈ D} where
  lt x y := ZFSet.pair x.val y.val ∈ r
  irrefl x := code.irrefl x.val x.property
  trans {x y z} := code.trans x.val y.val z.val
  compare x y := (code.compare x.val x.property y.val y.property).imp id
    (fun h => h.imp (fun equal => Subtype.ext equal) id)

def DenseOrderCode.toDenseHeightOrder {D r : ZFSet.{u}} (code : DenseOrderCode D r) :
    DenseHeightOrder {x : ZFSet.{u} // x ∈ D} where
  toLinearHeightOrder := code.toStrictLinearOrderCode.toLinearHeightOrder
  between x y lower := by
    obtain ⟨z, hz, left, right⟩ := code.between x.val y.val lower
    exact ⟨⟨z, hz⟩, left, right⟩

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

section
universe u

theorem stageOneAssignment_mem_assignments (I T t u w : ZFSet.{u}) :
    stageOneAssignment t u w ∈ stageOneAssignments I T ↔
      t ∈ I ∧ u ∈ T ∧ w ∈ T := by
  simp only [stageOneAssignment, stageOneAssignments, ZFSet.pair_mem_prod]

theorem mem_stageOneAssignments (I T z : ZFSet.{u}) :
    z ∈ stageOneAssignments I T ↔
      ∃ t ∈ I, ∃ u ∈ T, ∃ w ∈ T, z = stageOneAssignment t u w := by
  constructor
  · intro member
    obtain ⟨t, ht, rest, hr, rfl⟩ := ZFSet.mem_prod.1 member
    obtain ⟨u, hu, w, hw, rfl⟩ := ZFSet.mem_prod.1 hr
    exact ⟨t, ht, u, hu, w, hw, rfl⟩
  · rintro ⟨t, ht, u, hu, w, hw, rfl⟩
    exact (stageOneAssignment_mem_assignments I T t u w).2 ⟨ht, hu, hw⟩

namespace BoundedFormula

theorem truth_stageOneAssignmentFormula {n : Nat} (z t u w : Fin n)
    (env : Fin n → ZFSet.{u}) :
    Truth (stageOneAssignmentFormula z t u w) env ↔
      env z = stageOneAssignment (env t) (env u) (env w) :=
  truth_nonemptyTupleFormula 2 z ![t, u, w] env

end BoundedFormula

end

section
open SetRealization SetFormula
universe u

namespace BoundedFormula

def stageOneDataBoundEntryFormula {n} (z A I T S L mu X r anchors tuples : Fin n) : BoundedFormula n :=
  let lift (j : Fin n) := j.succ.succ.succ.succ.succ.succ.succ.succ
  exMem A (exMem L.succ (exMem I.succ.succ (exMem T.succ.succ.succ
    (exMem T.succ.succ.succ.succ (exMem L.succ.succ.succ.succ.succ
      (exMem S.succ.succ.succ.succ.succ.succ (exMem S.succ.succ.succ.succ.succ.succ.succ
        (.conj (orderedPairFormula (lift z) 7 6)
          (.conj (stageOneAssignmentFormula 7 5 4 3)
            (.conj (pairMembershipFormula 5 2 (lift anchors))
              (.conj (pairMembershipFormula 2 6 (lift r))
                (.conj (pairMembershipFormula 1 4 (lift tuples))
                  (.conj (pairMembershipFormula 0 3 (lift tuples))
                    (.conj (rowPositionBoundFormula (lift mu) (lift X) (lift r) 1 6)
                      (rowPositionBoundFormula (lift mu) (lift X) (lift r) 0 6)))))))))))))))

end BoundedFormula

end

open SetRealization
universe u

end PartitionPilot.Forcing

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Forcing_RefinementAssignmentLabelNames
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

def refinementClassEntryFormula : SetFormula 7 :=
  ex (ex (ex (.conj (.mem 2 4) (.conj (.mem 1 7)
    (.conj (orderedPairFormula 3 2 1)
      (.conj (orderedPairNameCodeFormula 0 2 6 9)
        (forcingTranslation (ordinaryGroundPrimitives 0 1) (.mem 0 1)
          ![7, 8] 1 ![0, 5])))))))

end SetFormula

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

noncomputable def natAddGraph : ZFSet.{u} :=
  (natPresentation.product natPresentation).graph natPresentation
    (fun n => ⟨n.1.down + n.2.down⟩)

noncomputable def natMulGraph : ZFSet.{u} :=
  (natPresentation.product natPresentation).graph natPresentation
    (fun n => ⟨n.1.down * n.2.down⟩)

theorem pair_mem_natAddGraph (a b c : Nat) :
    ZFSet.pair (ZFSet.pair (natSetCode a) (natSetCode b)) (natSetCode c) ∈
      natAddGraph.{u} ↔ c = a + b := by
  change ZFSet.pair ((natPresentation.product natPresentation).encode (⟨a⟩, ⟨b⟩))
    (natPresentation.encode ⟨c⟩) ∈ (natPresentation.product natPresentation).graph
      natPresentation (fun n => ⟨n.1.down + n.2.down⟩) ↔ _
  rw [Presentation.pair_mem_graph]
  exact ⟨fun h => (congrArg ULift.down h).symm, fun h => ULift.ext _ _ h.symm⟩

end PartitionPilot.Forcing

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Geometry_FiniteWordOperations
attribute [-instance] _root_.OAI.PartitionPilot.Forcing.GroundMainPrefix.withTopSmall
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace PartitionPilot.Forcing
open SetRealization
universe u

theorem FiniteWordAppendCode.unique {A f g h h' : ZFSet.{u}}
    (first : FiniteWordAppendCode A ZFSet.omega natAddGraph f g h)
    (second : FiniteWordAppendCode A ZFSet.omega natAddGraph f g h') : h = h' := by
  obtain ⟨m, hm, n, hn, p, hp, fm, gn, funH, sum, entries⟩ := first
  obtain ⟨m', hm', n', hn', p', hp', fm', gn', funH', sum', entries'⟩ := second
  obtain ⟨m, rfl⟩ := (mem_omega_iff_natSetCode _).1 hm
  obtain ⟨n, rfl⟩ := (mem_omega_iff_natSetCode _).1 hn
  obtain ⟨p, rfl⟩ := (mem_omega_iff_natSetCode _).1 hp
  obtain ⟨m', rfl⟩ := (mem_omega_iff_natSetCode _).1 hm'
  obtain ⟨n', rfl⟩ := (mem_omega_iff_natSetCode _).1 hn'
  obtain ⟨p', rfl⟩ := (mem_omega_iff_natSetCode _).1 hp'
  have mEqual := finiteWord_domain_unique fm' fm
  have nEqual := finiteWord_domain_unique gn' gn
  subst m' n'
  have pEqual := ((pair_mem_natAddGraph _ _ _).1 sum').trans ((pair_mem_natAddGraph _ _ _).1 sum).symm
  subst p'
  apply ZFSet.ext
  intro z
  constructor
  · intro hz
    obtain ⟨i, hi, a, ha, rfl⟩ := ZFSet.mem_prod.1 (funH.1 hz)
    exact (entries' i hi a ha).2 ((entries i hi a ha).1 hz)
  · intro hz
    obtain ⟨i, hi, a, ha, rfl⟩ := ZFSet.mem_prod.1 (funH'.1 hz)
    exact (entries i hi a ha).2 ((entries' i hi a ha).1 hz)

end PartitionPilot.Forcing

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Definability_FiniteWordOperationFormulas
attribute [-instance] _root_.OAI.PartitionPilot.Forcing.GroundMainPrefix.withTopSmall
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace PartitionPilot.Forcing.BoundedFormula
open SetFormula
universe u

def finiteWordAppendFormula {k} (a omega add f g h : Fin k) : BoundedFormula k :=
  exMem omega (exMem omega.succ (exMem omega.succ.succ
    (.conj (functionFormula 2 a.succ.succ.succ f.succ.succ.succ)
      (.conj (functionFormula 1 a.succ.succ.succ g.succ.succ.succ)
        (.conj (functionFormula 0 a.succ.succ.succ h.succ.succ.succ)
          (.conj (tripleMembershipFormula 2 1 0 add.succ.succ.succ)
            (.allMem 0 (.allMem a.succ.succ.succ.succ
              (let left := pairMembershipFormula 1 0 h.succ.succ.succ.succ.succ
               let right := disj (pairMembershipFormula 1 0 f.succ.succ.succ.succ.succ)
                 (exMem 3 (.conj (tripleMembershipFormula 5 0 2 add.succ.succ.succ.succ.succ.succ)
                   (pairMembershipFormula 0 1 g.succ.succ.succ.succ.succ.succ)))
               .conj (imp left right) (imp right left))))))))))

def finiteWordReverseFormula {k} (a omega add f h : Fin k) : BoundedFormula k :=
  exMem omega (.conj (functionFormula 0 a.succ f.succ)
    (.conj (functionFormula 0 a.succ h.succ)
      (.allMem 0 (.allMem a.succ.succ
        (let left := pairMembershipFormula 1 0 h.succ.succ.succ
         let right := exMem 2 (exMem 3
           (.conj (tripleMembershipFormula 3 1 0 add.succ.succ.succ.succ.succ)
             (.conj (successorFormula 4 0) (pairMembershipFormula 1 2 f.succ.succ.succ.succ.succ))))
         .conj (imp left right) (imp right left))))))

end PartitionPilot.Forcing.BoundedFormula

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Geometry_GroundExternalAlphabetInversion
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

def ExternalSymbolInverseEntry (G S inv x y : ZFSet.{u}) : Prop :=
  (∃ g ∈ G, ∃ h ∈ G, x = externalActorSymbol g ∧ y = externalActorSymbol h ∧
    ZFSet.pair g h ∈ inv) ∨
  ∃ s ∈ S, ∃ b : Bool, x = externalLetterSymbol s b ∧ y = externalLetterSymbol s (!b)

end PartitionPilot.Forcing



namespace PartitionPilot.Forcing

open SetFormula
universe u

namespace BoundedFormula

def externalSymbolInverseFormula {n} (x y G S inv zero one : Fin n) : BoundedFormula n :=
  disj
    (exMem G (exMem G.succ
      (.conj (orderedPairFormula x.succ.succ zero.succ.succ 1)
        (.conj (orderedPairFormula y.succ.succ zero.succ.succ 0)
          (pairMembershipFormula 1 0 inv.succ.succ)))))
    (exMem S (disj
      (.conj (orderedRightTripleFormula x.succ one.succ 0 zero.succ)
        (orderedRightTripleFormula y.succ one.succ 0 one.succ))
      (.conj (orderedRightTripleFormula x.succ one.succ 0 one.succ)
        (orderedRightTripleFormula y.succ one.succ 0 zero.succ))))

def externalSymbolInverseEntryFormula {n} (z alphabet G S inv zero one : Fin n) :
    BoundedFormula n :=
  exMem alphabet (exMem alphabet.succ
    (.conj (orderedPairFormula z.succ.succ 1 0)
      (externalSymbolInverseFormula 1 0 G.succ.succ S.succ.succ inv.succ.succ
        zero.succ.succ one.succ.succ)))

end BoundedFormula

end PartitionPilot.Forcing

end

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

namespace PartitionPilot.Forcing.BoundedFormula

open SetFormula
universe u

def iterationTraceFormula {k} (n d b step base t zero : Fin k) : BoundedFormula k :=
  .conj (functionFormula d b t) (.conj (pairMembershipFormula zero base t)
    (.allMem n (.allMem d.succ (.allMem b.succ.succ (.allMem b.succ.succ.succ
      (imp (.conj (successorFormula 2 3) (.conj (pairMembershipFormula 3 1 t.succ.succ.succ.succ)
        (pairMembershipFormula 2 0 t.succ.succ.succ.succ)))
        (pairMembershipFormula 1 0 step.succ.succ.succ.succ)))))))

theorem truth_iterationTraceFormula {k} (n d b step base t zero : Fin k)
    (env : Fin k → ZFSet.{u}) (hzero : env zero = ∅) :
    Truth (iterationTraceFormula n d b step base t zero) env ↔
      IterationTraceCode (env n) (env d) (env b) (env step) (env base) (env t) := by
  simp only [iterationTraceFormula, Truth, truth_functionFormula, truth_pairMembershipFormula,
    truth_imp, truth_successorFormula]
  change (ZFSet.IsFunc (env d) (env b) (env t) ∧ ZFSet.pair (env zero) (env base) ∈ env t ∧
    ∀ i ∈ env n, ∀ j ∈ env d, ∀ x ∈ env b, ∀ y ∈ env b,
      (j = insert i i ∧ ZFSet.pair i x ∈ env t ∧ ZFSet.pair j y ∈ env t) →
        ZFSet.pair x y ∈ env step) ↔ _
  rw [hzero]
  exact ⟨fun ⟨func, seed, next⟩ => ⟨func, seed,
    fun i hi j hj x hx y hy succ prev after => next i hi j hj x hx y hy ⟨succ, prev, after⟩⟩,
    fun trace => ⟨trace.function, trace.seed,
      fun i hi j hj x hx y hy h => trace.next i hi j hj x hx y hy h.1 h.2.1 h.2.2⟩⟩

def iterationEntryFormula {k} (z w b step base traces zero : Fin k) : BoundedFormula k :=
  exMem w (exMem b.succ (exMem w.succ.succ (exMem traces.succ.succ.succ
    (.conj (orderedPairFormula z.succ.succ.succ.succ 3 2)
      (.conj (successorFormula 1 3)
        (.conj (iterationTraceFormula 3 1 b.succ.succ.succ.succ step.succ.succ.succ.succ
          base.succ.succ.succ.succ 0 zero.succ.succ.succ.succ)
          (pairMembershipFormula 3 2 0)))))))

theorem truth_iterationEntryFormula {k} (z w b step base traces zero : Fin k)
    (env : Fin k → ZFSet.{u}) (hzero : env zero = ∅) :
    Truth (iterationEntryFormula z w b step base traces zero) env ↔
      ∃ n ∈ env w, ∃ y ∈ env b, ∃ d ∈ env w, ∃ t ∈ env traces,
        env z = ZFSet.pair n y ∧ d = insert n n ∧
          IterationTraceCode n d (env b) (env step) (env base) t ∧ ZFSet.pair n y ∈ t := by
  simp only [iterationEntryFormula, truth_exMem, Truth, truth_orderedPairFormula,
    truth_successorFormula, truth_pairMembershipFormula]
  apply exists_congr
  intro n
  apply and_congr_right
  intro _
  apply exists_congr
  intro y
  apply and_congr_right
  intro _
  apply exists_congr
  intro d
  apply and_congr_right
  intro _
  apply exists_congr
  intro t
  apply and_congr_right
  intro _
  exact and_congr Iff.rfl (and_congr Iff.rfl (and_congr
    (truth_iterationTraceFormula _ _ _ _ _ _ _ _ (by exact hzero)) Iff.rfl))

end PartitionPilot.Forcing.BoundedFormula

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

namespace PartitionPilot.Forcing.BoundedFormula

open SetFormula
universe u

def natSuccessorEntryFormula {k} (z w : Fin k) : BoundedFormula k :=
  exMem w (exMem w.succ (.conj (orderedPairFormula z.succ.succ 1 0)
    (successorFormula 0 1)))

theorem truth_natSuccessorEntryFormula {k} (z w : Fin k) (env : Fin k → ZFSet.{u}) :
    Truth (natSuccessorEntryFormula z w) env ↔
      ∃ a ∈ env w, ∃ b ∈ env w, env z = ZFSet.pair a b ∧ b = insert a a := by
  simp only [natSuccessorEntryFormula, truth_exMem, Truth, truth_orderedPairFormula,
    truth_successorFormula]
  rfl

def natAddEntryFormula {k} (z w step traces zero : Fin k) : BoundedFormula k :=
  exMem w (exMem w.succ (exMem w.succ.succ (exMem w.succ.succ.succ
    (exMem traces.succ.succ.succ.succ
      (.conj (orderedTripleFormula z.succ.succ.succ.succ.succ 4 3 2)
        (.conj (successorFormula 1 3)
          (.conj (iterationTraceFormula 3 1 w.succ.succ.succ.succ.succ
            step.succ.succ.succ.succ.succ 4 0 zero.succ.succ.succ.succ.succ)
            (pairMembershipFormula 3 2 0))))))))

theorem truth_natAddEntryFormula {k} (z w step traces zero : Fin k)
    (env : Fin k → ZFSet.{u}) (hzero : env zero = ∅) :
    Truth (natAddEntryFormula z w step traces zero) env ↔
      ∃ a ∈ env w, ∃ b ∈ env w, ∃ c ∈ env w, ∃ d ∈ env w, ∃ t ∈ env traces,
        env z = ZFSet.pair (ZFSet.pair a b) c ∧ d = insert b b ∧
          IterationTraceCode b d (env w) (env step) a t ∧ ZFSet.pair b c ∈ t := by
  simp only [natAddEntryFormula, truth_exMem, Truth, truth_orderedTripleFormula,
    truth_successorFormula, truth_pairMembershipFormula]
  apply exists_congr
  intro a
  apply and_congr_right
  intro _
  apply exists_congr
  intro b
  apply and_congr_right
  intro _
  apply exists_congr
  intro c
  apply and_congr_right
  intro _
  apply exists_congr
  intro d
  apply and_congr_right
  intro _
  apply exists_congr
  intro t
  apply and_congr_right
  intro _
  exact and_congr Iff.rfl (and_congr Iff.rfl (and_congr
    (truth_iterationTraceFormula _ _ _ _ _ _ _ _ (by exact hzero)) Iff.rfl))

def natMulEntryFormula {k} (z w family traces zero : Fin k) : BoundedFormula k :=
  exMem w (exMem w.succ (exMem w.succ.succ (exMem w.succ.succ.succ
    (exMem traces.succ.succ.succ.succ (exMem traces.succ.succ.succ.succ.succ
      (.conj (orderedTripleFormula z.succ.succ.succ.succ.succ.succ 5 4 3)
        (.conj (successorFormula 2 4)
          (.conj (pairMembershipFormula 5 0 family.succ.succ.succ.succ.succ.succ)
            (.conj (iterationTraceFormula 4 2 w.succ.succ.succ.succ.succ.succ
              0 zero.succ.succ.succ.succ.succ.succ 1 zero.succ.succ.succ.succ.succ.succ)
              (pairMembershipFormula 4 3 1))))))))))

theorem truth_natMulEntryFormula {k} (z w family traces zero : Fin k)
    (env : Fin k → ZFSet.{u}) (hzero : env zero = ∅) :
    Truth (natMulEntryFormula z w family traces zero) env ↔
      ∃ a ∈ env w, ∃ b ∈ env w, ∃ c ∈ env w, ∃ d ∈ env w,
      ∃ t ∈ env traces, ∃ step ∈ env traces,
        env z = ZFSet.pair (ZFSet.pair a b) c ∧ d = insert b b ∧
          ZFSet.pair a step ∈ env family ∧
            IterationTraceCode b d (env w) step ∅ t ∧ ZFSet.pair b c ∈ t := by
  simp only [natMulEntryFormula, truth_exMem, Truth, truth_orderedTripleFormula,
    truth_successorFormula, truth_pairMembershipFormula]
  apply exists_congr
  intro a
  apply and_congr_right
  intro _
  apply exists_congr
  intro b
  apply and_congr_right
  intro _
  apply exists_congr
  intro c
  apply and_congr_right
  intro _
  apply exists_congr
  intro d
  apply and_congr_right
  intro _
  apply exists_congr
  intro t
  apply and_congr_right
  intro _
  apply exists_congr
  intro step
  apply and_congr_right
  intro _
  apply and_congr_right
  intro _
  apply and_congr_right
  intro _
  apply and_congr_right
  intro _
  have correct := truth_iterationTraceFormula 4 2 w.succ.succ.succ.succ.succ.succ
    0 zero.succ.succ.succ.succ.succ.succ 1 zero.succ.succ.succ.succ.succ.succ
    (extend step (extend t (extend d (extend c (extend b (extend a env)))))) (by exact hzero)
  constructor
  · rintro ⟨h, entry⟩
    have trace := correct.1 h
    change IterationTraceCode b d (env w) step (env zero) t at trace
    exact ⟨by simpa only [hzero] using trace, entry⟩
  · rintro ⟨trace, entry⟩
    refine ⟨correct.2 ?_, entry⟩
    change IterationTraceCode b d (env w) step (env zero) t
    simpa only [hzero] using trace

end PartitionPilot.Forcing.BoundedFormula

end


namespace PartitionPilot.Forcing
open SetRealization SetFormula
universe u





namespace BoundedFormula

def finiteWordAppendEntryFormula {n} (z words alphabet omega add : Fin n) : BoundedFormula n :=
  exMem words (exMem words.succ (exMem words.succ.succ
    (.conj (orderedTripleFormula z.succ.succ.succ 2 1 0)
      (finiteWordAppendFormula alphabet.succ.succ.succ omega.succ.succ.succ
        add.succ.succ.succ 2 1 0))))

def finiteWordReverseEntryFormula {n} (z words alphabet omega add : Fin n) : BoundedFormula n :=
  exMem words (exMem words.succ
    (.conj (orderedPairFormula z.succ.succ 1 0)
      (finiteWordReverseFormula alphabet.succ.succ omega.succ.succ add.succ.succ 1 0)))

end BoundedFormula

namespace TransitiveGround
variable (M : TransitiveGround.{u})

noncomputable def finiteWordAppendGraph (A : ZFSet.{u}) : ZFSet.{u} :=
  ZFSet.sep (fun z => ∃ f ∈ M.finiteWords A, ∃ g ∈ M.finiteWords A,
    ∃ h ∈ M.finiteWords A, z = ZFSet.pair (ZFSet.pair f g) h ∧
      FiniteWordAppendCode A ZFSet.omega natAddGraph f g h)
    (ZFSet.prod (ZFSet.prod (M.finiteWords A) (M.finiteWords A)) (M.finiteWords A))

end TransitiveGround






end PartitionPilot.Forcing



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

open Compression.RecursiveMaps.RationalHeights
universe u

namespace BoundedFormula

open SetFormula

def positiveMagnitudeFormula {n} (code magnitude add : Fin n) : BoundedFormula n :=
  tripleMembershipFormula magnitude magnitude code add

def negativeMagnitudeFormula {n} (code magnitude W add one : Fin n) : BoundedFormula n :=
  exMem W (exMem W.succ
    (.conj (tripleMembershipFormula 1 one.succ.succ magnitude.succ.succ add.succ.succ)
      (.conj (tripleMembershipFormula 1 1 0 add.succ.succ)
        (tripleMembershipFormula 0 one.succ.succ code.succ.succ add.succ.succ))))

def fractionComparisonFormula {n} (strict : Bool) (a ad b bd W add mul one : Fin n) : BoundedFormula n :=
  let lift (i : Fin n) : Fin (n + 4) := i.succ.succ.succ.succ
  exMem W (exMem W.succ (exMem W.succ.succ (exMem W.succ.succ.succ
    (.conj (tripleMembershipFormula 3 (lift bd) 1 (lift mul))
      (.conj (tripleMembershipFormula 2 (lift ad) 0 (lift mul))
        (disj
          (.conj (positiveMagnitudeFormula (lift a) 3 (lift add))
            (.conj (positiveMagnitudeFormula (lift b) 2 (lift add))
              (if strict then .mem 1 0 else .equal 1 0)))
          (disj
            (.conj (negativeMagnitudeFormula (lift a) 3 (lift W) (lift add) (lift one))
              (.conj (negativeMagnitudeFormula (lift b) 2 (lift W) (lift add) (lift one))
                (if strict then .mem 0 1 else .equal 1 0)))
            (if strict then
              .conj (negativeMagnitudeFormula (lift a) 3 (lift W) (lift add) (lift one))
                (positiveMagnitudeFormula (lift b) 2 (lift add))
              else .neg (.equal 0 0)))))))))

end BoundedFormula

end



section

open SetRealization
universe u

theorem gridStepCode_nat (a b c d : Nat) :
    GridStepCode (natSetCode a : ZFSet.{u}) (natSetCode b) (natSetCode c) (natSetCode d) ↔
      gridStep (a, b) = (c, d) := by
  have successor (m n : Nat) : (natSetCode m : ZFSet.{u}) = insert (natSetCode n) (natSetCode n) ↔
      m = n + 1 := by
    rw [← natSetCode_succ]
    exact natSetCode_injective.eq_iff
  have zero (m : Nat) : (natSetCode m : ZFSet.{u}) = ∅ ↔ m = 0 := by
    rw [← natSetCode_zero]
    exact natSetCode_injective.eq_iff
  rw [GridStepCode, gridStep_eq_iff]
  simp only [successor, zero, natSetCode_injective.eq_iff, natSetCode_mem_iff]

namespace BoundedFormula

open SetFormula

def gridStepFormula {n} (a b c d : Fin n) : BoundedFormula n :=
  disj (.conj (successorFormula c a) (.conj (.mem c b) (.equal d b)))
    (disj (.conj (successorFormula b a) (.conj (.equal c b) (emptyFormula d)))
      (disj (.conj (.mem b a) (.conj (.equal c a) (successorFormula d b)))
        (.conj (.equal a b) (.conj (emptyFormula c) (successorFormula d a)))))

theorem truth_gridStepFormula {n} (a b c d : Fin n) (env : Fin n → ZFSet.{u}) :
    Truth (gridStepFormula a b c d) env ↔ GridStepCode (env a) (env b) (env c) (env d) := by
  simp only [gridStepFormula, truth_disj, Truth, truth_successorFormula, truth_emptyFormula]
  rfl

def gridTransitionFormula {n} (x y w : Fin n) : BoundedFormula n :=
  exMem w (exMem w.succ (exMem w.succ.succ (exMem w.succ.succ.succ
    (.conj (orderedPairFormula x.succ.succ.succ.succ 3 2)
      (.conj (orderedPairFormula y.succ.succ.succ.succ 1 0) (gridStepFormula 3 2 1 0))))))

theorem truth_gridTransitionFormula {n} (x y w : Fin n) (env : Fin n → ZFSet.{u}) :
    Truth (gridTransitionFormula x y w) env ↔
      ∃ a ∈ env w, ∃ b ∈ env w, ∃ c ∈ env w, ∃ d ∈ env w,
        env x = ZFSet.pair a b ∧ env y = ZFSet.pair c d ∧ GridStepCode a b c d := by
  simp only [gridTransitionFormula, truth_exMem, Truth, truth_orderedPairFormula, truth_gridStepFormula]
  rfl

def gridEntryFormula {n} (z w s : Fin n) : BoundedFormula n :=
  exMem s (exMem s.succ (.conj (orderedPairFormula z.succ.succ 1 0)
    (gridTransitionFormula 1 0 w.succ.succ)))

theorem truth_gridEntryFormula {n} (z w s : Fin n) (env : Fin n → ZFSet.{u}) :
    Truth (gridEntryFormula z w s) env ↔
      ∃ x ∈ env s, ∃ y ∈ env s, env z = ZFSet.pair x y ∧
        ∃ a ∈ env w, ∃ b ∈ env w, ∃ c ∈ env w, ∃ d ∈ env w,
          x = ZFSet.pair a b ∧ y = ZFSet.pair c d ∧ GridStepCode a b c d := by
  simp only [gridEntryFormula, truth_exMem, Truth, truth_orderedPairFormula, truth_gridTransitionFormula]
  rfl

theorem gridEntry_correct (z : ZFSet.{u}) :
    Truth (gridEntryFormula 0 1 2) (extend z (extend ZFSet.omega
      (extend (ZFSet.prod ZFSet.omega ZFSet.omega) Fin.elim0))) ↔
      z ∈ (natPresentation.product natPresentation).graph
        (natPresentation.product natPresentation) liftedGridStep := by
  rw [truth_gridEntryFormula]
  change (∃ x ∈ ZFSet.prod ZFSet.omega ZFSet.omega, ∃ y ∈ ZFSet.prod ZFSet.omega ZFSet.omega,
    z = ZFSet.pair x y ∧ ∃ a ∈ ZFSet.omega, ∃ b ∈ ZFSet.omega, ∃ c ∈ ZFSet.omega, ∃ d ∈ ZFSet.omega,
      x = ZFSet.pair a b ∧ y = ZFSet.pair c d ∧ GridStepCode a b c d) ↔ _
  constructor
  · rintro ⟨x, _, y, _, rfl, a, ha, b, hb, c, hc, d, hd, rfl, rfl, code⟩
    obtain ⟨a, rfl⟩ := (mem_omega_iff_natSetCode a).1 ha
    obtain ⟨b, rfl⟩ := (mem_omega_iff_natSetCode b).1 hb
    obtain ⟨c, rfl⟩ := (mem_omega_iff_natSetCode c).1 hc
    obtain ⟨d, rfl⟩ := (mem_omega_iff_natSetCode d).1 hd
    have step := (gridStepCode_nat a b c d).1 code
    apply ((natPresentation.product natPresentation).pair_mem_graph
      (natPresentation.product natPresentation) liftedGridStep (⟨a⟩, ⟨b⟩) (⟨c⟩, ⟨d⟩)).2
    exact Prod.ext (ULift.ext _ _ (congrArg Prod.fst step)) (ULift.ext _ _ (congrArg Prod.snd step))
  · intro hz
    obtain ⟨p, eq⟩ := ((natPresentation.product natPresentation).mem_graph
      (natPresentation.product natPresentation) liftedGridStep z).1 hz
    let q := liftedGridStep p
    exact ⟨(natPresentation.product natPresentation).encode p,
      (natPresentation.product natPresentation).encode_mem p,
      (natPresentation.product natPresentation).encode q,
      (natPresentation.product natPresentation).encode_mem q, eq.symm,
      natSetCode p.1.down, natSetCode_mem_omega _, natSetCode p.2.down, natSetCode_mem_omega _,
      natSetCode q.1.down, natSetCode_mem_omega _, natSetCode q.2.down, natSetCode_mem_omega _,
      rfl, rfl, (gridStepCode_nat _ _ _ _).2 rfl⟩

end BoundedFormula

end



section

open Compression.RecursiveMaps.RationalHeights
universe u

namespace BoundedFormula

open SetFormula

def fractionGraphFormula (strict : Bool) : BoundedFormula 6 :=
  exMem 1 (exMem 2 (.conj (orderedPairFormula 2 1 0)
    (exMem 4 (exMem 5 (exMem 6 (exMem 7
      (.conj (orderedPairFormula 5 3 2)
        (.conj (orderedPairFormula 4 1 0)
          (fractionComparisonFormula strict 3 2 1 0 8 9 10 11)))))))))

end BoundedFormula

end



end PartitionPilot.Forcing

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

namespace BoundedFormula

open SetFormula

theorem truth_sizeWitnessEntryFormula {k} (z r w n : Fin k) (env : Fin k → ZFSet.{u}) :
    Truth (sizeWitnessEntryFormula z r w n) env ↔
      ∃ p ∈ env r, ∃ f ∈ env w, env z = ZFSet.pair p f ∧ InjectionCode p (env n) f := by
  simp only [sizeWitnessEntryFormula, truth_exMem, Truth, truth_orderedPairFormula, truth_injectionFormula]
  rfl

end BoundedFormula

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

namespace BoundedFormula

open SetFormula

def indexedSizeEntryFormula {k} (z u r w n g f : Fin k) : BoundedFormula k :=
  exMem u (exMem n.succ (exMem n.succ.succ (exMem r.succ.succ.succ (exMem w.succ.succ.succ.succ
    (.conj (orderedTripleFormula z.succ.succ.succ.succ.succ 3 2 4)
      (.conj (pairMembershipFormula 3 1 g.succ.succ.succ.succ.succ)
        (.conj (pairMembershipFormula 1 0 f.succ.succ.succ.succ.succ)
          (pairMembershipFormula 4 2 0))))))))

theorem truth_indexedSizeEntryFormula {k} (z u r w n g f : Fin k) (env : Fin k → ZFSet.{u}) :
    Truth (indexedSizeEntryFormula z u r w n g f) env ↔
      ∃ x ∈ env u, ∃ i ∈ env n, ∃ j ∈ env n, ∃ p ∈ env r, ∃ h ∈ env w,
        env z = ZFSet.pair (ZFSet.pair i j) x ∧ ZFSet.pair i p ∈ env g ∧
          ZFSet.pair p h ∈ env f ∧ ZFSet.pair x j ∈ h := by
  simp only [indexedSizeEntryFormula, truth_exMem, Truth, truth_orderedTripleFormula,
    truth_pairMembershipFormula]
  rfl

end BoundedFormula

namespace TransitiveGround

open SetFormula
variable (M : TransitiveGround.{u})

theorem groundEmbeddable_of_partial_surjection
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (choice : Realize M.sets SetFormula.choice Fin.elim0)
    {A B r : ZFSet.{u}} (hA : A ∈ M.sets) (hB : B ∈ M.sets) (hr : r ∈ M.sets)
    (code : PartialFunctionCode A B r) (onto : ∀ y ∈ B, ∃ x ∈ A, ZFSet.pair x y ∈ r) :
    M.groundEmbeddable B A := by
  have inverse := M.relationConverse_mem pairing unions powers separation hA hB hr
  have total (y : ZFSet.{u}) (hy : y ∈ B) : ∃ x ∈ A, ZFSet.pair y x ∈ relationConverse A B r := by
    obtain ⟨x, hx, rel⟩ := onto y hy
    exact ⟨x, hx, (pair_mem_relationConverse A B r x y).2 ⟨hx, hy, rel⟩⟩
  obtain ⟨f, hf, func, selected⟩ := M.uniformize_relation pairing unions powers separation choice hB hA inverse total
  exact ⟨f, hf, func, fun x y z hx hy => code.unique z x y
    ((pair_mem_relationConverse A B r z x).1 (selected hx)).2.2
    ((pair_mem_relationConverse A B r z y).1 (selected hy)).2.2⟩

end TransitiveGround





theorem unionSizeRelation_partial {U R W D F : ZFSet.{u}}
    (family : ZFSet.IsFunc R W F)
    (codes : ∀ A f, ZFSet.pair A f ∈ F → InjectionCode A D f) :
    PartialFunctionCode (ZFSet.prod R D) U (unionSizeRelation U R W D F) := by
  refine ⟨fun _ entry => (ZFSet.mem_sep.1 entry).1, ?_⟩
  intro v x y first second
  obtain ⟨_, A, hA, k, _, va, f, _, selected, value⟩ :=
    (pair_mem_unionSizeRelation U R W D F v x).1 first
  obtain ⟨_, B, _, l, _, vb, g, _, selected', value'⟩ :=
    (pair_mem_unionSizeRelation U R W D F v y).1 second
  obtain ⟨sameA, sameK⟩ := ZFSet.pair_inj.1 (va.symm.trans vb)
  subst B
  subst l
  obtain ⟨_, _, unique⟩ := family.2 A hA
  have sameF := (unique f selected).trans (unique g selected').symm
  subst g
  exact (codes A f selected).injective x y k value value'

namespace BoundedFormula
open SetFormula

def unionSizeEntryFormula {n} (z u r w d f : Fin n) : BoundedFormula n :=
  exMem u (exMem r.succ (exMem d.succ.succ (exMem w.succ.succ.succ
    (.conj (orderedTripleFormula z.succ.succ.succ.succ 2 1 3)
      (.conj (pairMembershipFormula 2 0 f.succ.succ.succ.succ)
        (pairMembershipFormula 3 1 0))))))

theorem truth_unionSizeEntryFormula {n} (z u r w d f : Fin n) (env : Fin n → ZFSet.{u}) :
    Truth (unionSizeEntryFormula z u r w d f) env ↔
      ∃ x ∈ env u, ∃ A ∈ env r, ∃ k ∈ env d, ∃ h ∈ env w,
        env z = ZFSet.pair (ZFSet.pair A k) x ∧
          ZFSet.pair A h ∈ env f ∧ ZFSet.pair x k ∈ h := by
  simp only [unionSizeEntryFormula, truth_exMem, Truth, truth_orderedTripleFormula,
    truth_pairMembershipFormula]
  rfl

end BoundedFormula

namespace TransitiveGround
open SetFormula
variable (M : TransitiveGround.{u})

theorem unionSizeRelation_mem
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    {U R W D F : ZFSet.{u}} (hU : U ∈ M.sets) (hR : R ∈ M.sets)
    (hW : W ∈ M.sets) (hD : D ∈ M.sets) (hF : F ∈ M.sets) :
    unionSizeRelation U R W D F ∈ M.sets := by
  let params := extend U (extend R (extend W (extend D (extend F Fin.elim0))))
  have selected := M.bounded_separation_mem separation (BoundedFormula.unionSizeEntryFormula 0 1 2 3 4 5)
    params (Fin.cases hU (Fin.cases hR (Fin.cases hW (Fin.cases hD (Fin.cases hF (fun i => Fin.elim0 i))))))
    (M.prod_mem pairing unions powers separation (M.prod_mem pairing unions powers separation hR hD) hU)
  have equal : ZFSet.sep (fun z => BoundedFormula.Truth
      (BoundedFormula.unionSizeEntryFormula 0 1 2 3 4 5) (extend z params))
      (ZFSet.prod (ZFSet.prod R D) U) = unionSizeRelation U R W D F := by
    apply ZFSet.ext
    intro z
    rw [ZFSet.mem_sep, unionSizeRelation, ZFSet.mem_sep]
    exact and_congr Iff.rfl (BoundedFormula.truth_unionSizeEntryFormula 0 1 2 3 4 5 _)
  exact equal ▸ selected

end TransitiveGround






noncomputable def defaultInverse (R N f d : ZFSet.{u}) : ZFSet.{u} :=
  relationConverse R N f ∪
    ZFSet.prod (ZFSet.sep (fun n => n ∉ relationImage R N f) N) {d}

theorem pair_mem_defaultInverse (R N f d n p : ZFSet.{u}) :
    ZFSet.pair n p ∈ defaultInverse R N f d ↔
      (p ∈ R ∧ n ∈ N ∧ ZFSet.pair p n ∈ f) ∨
      (n ∈ N ∧ n ∉ relationImage R N f ∧ p = d) := by
  simp only [defaultInverse, ZFSet.mem_union, pair_mem_relationConverse,
    ZFSet.pair_mem_prod, ZFSet.mem_sep, ZFSet.mem_singleton, and_assoc]

theorem defaultInverse_isFunc {R N f d : ZFSet.{u}}
    (code : InjectionCode R N f) (hd : d ∈ R) :
    ZFSet.IsFunc N R (defaultInverse R N f d) := by
  classical
  refine ⟨?_, ?_⟩
  · intro z hz
    rcases ZFSet.mem_union.1 hz with hz | hz
    · obtain ⟨p, hp, n, hn, rfl, _⟩ := (mem_relationConverse R N f z).1 hz
      exact ZFSet.pair_mem_prod.2 ⟨hn, hp⟩
    · obtain ⟨n, hn, p, hp, rfl⟩ := ZFSet.mem_prod.1 hz
      exact ZFSet.pair_mem_prod.2
        ⟨(ZFSet.mem_sep.1 hn).1, ZFSet.mem_singleton.1 hp ▸ hd⟩
  · intro n hn
    by_cases image : n ∈ relationImage R N f
    · obtain ⟨_, p, hp, hpn⟩ := (mem_relationImage R N f n).1 image
      refine ⟨p, (pair_mem_defaultInverse R N f d n p).2 (Or.inl ⟨hp, hn, hpn⟩), ?_⟩
      intro q hq
      rcases (pair_mem_defaultInverse R N f d n q).1 hq with hq | hq
      · exact code.injective q p n hq.2.2 hpn
      · exact False.elim (hq.2.1 image)
    · refine ⟨d, (pair_mem_defaultInverse R N f d n d).2 (Or.inr ⟨hn, image, rfl⟩), ?_⟩
      intro p hp
      rcases (pair_mem_defaultInverse R N f d n p).1 hp with hp | hp
      · exact False.elim (image ((mem_relationImage R N f n).2 ⟨hn, p, hp.1, hp.2.2⟩))
      · exact hp.2.2

theorem defaultInverse_onto {R N f : ZFSet.{u}}
    (code : InjectionCode R N f) (d : ZFSet.{u}) :
    ∀ p ∈ R, ∃ n ∈ N, ZFSet.pair n p ∈ defaultInverse R N f d := by
  intro p hp
  obtain ⟨n, hpn, _⟩ := code.function.2 p hp
  have hn := (ZFSet.pair_mem_prod.1 (code.function.1 hpn)).2
  exact ⟨n, hn, (pair_mem_defaultInverse R N f d n p).2 (Or.inl ⟨hp, hn, hpn⟩)⟩

namespace TransitiveGround

open SetFormula
variable (M : TransitiveGround.{u})

theorem defaultInverse_mem
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    {R N f d : ZFSet.{u}}
    (hR : R ∈ M.sets) (hN : N ∈ M.sets) (hf : f ∈ M.sets) (hd : d ∈ M.sets) :
    defaultInverse R N f d ∈ M.sets := by
  have image := M.relationImage_mem separation hR hN hf
  have missing : ZFSet.sep (fun n => n ∉ relationImage R N f) N ∈ M.sets :=
    M.bounded_separation_mem separation (.neg (.mem 0 1))
      (extend (relationImage R N f) Fin.elim0) (Fin.cases image (fun i => Fin.elim0 i)) hN
  have singleton : ({d} : ZFSet.{u}) ∈ M.sets := by
    simpa only [ZFSet.pair_eq_singleton] using M.unorderedPair_mem pairing hd hd
  exact M.binary_union_mem pairing unions
    (M.relationConverse_mem pairing unions powers separation hR hN hf)
    (M.prod_mem pairing unions powers separation missing singleton)

theorem groundEmbeddable_enumeration
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    {R N : ZFSet.{u}} (hR : R ∈ M.sets) (hN : N ∈ M.sets)
    (nonempty : R.Nonempty) (small : M.groundEmbeddable R N) :
    ∃ g ∈ M.sets, ZFSet.IsFunc N R g ∧
      ∀ p ∈ R, ∃ n ∈ N, ZFSet.pair n p ∈ g := by
  obtain ⟨d, hd⟩ := nonempty
  obtain ⟨f, hf, code⟩ := small
  exact ⟨defaultInverse R N f d,
    M.defaultInverse_mem pairing unions powers separation hR hN hf (M.transitive hR hd),
    defaultInverse_isFunc code hd, defaultInverse_onto code d⟩

end TransitiveGround

end PartitionPilot.Forcing



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

universe u

theorem functionCode_partial {A B r : ZFSet.{u}} (func : ZFSet.IsFunc A B r) :
    PartialFunctionCode A B r := by
  refine ⟨func.1, ?_⟩
  intro x y z xy xz
  obtain ⟨v, _, unique⟩ := func.2 x (ZFSet.pair_mem_prod.1 (func.1 xy)).1
  exact (unique y xy).trans (unique z xz).symm

namespace TransitiveGround

open SetFormula
variable (M : TransitiveGround.{u})

theorem groundEmbeddable_function_image
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (choice : Realize M.sets SetFormula.choice Fin.elim0)
    {A B D N r : ZFSet.{u}} (hD : D ∈ M.sets) (hB : B ∈ M.sets) (hN : N ∈ M.sets)
    (hr : r ∈ M.sets) (func : ZFSet.IsFunc A B r) (small : M.groundEmbeddable D N) :
    M.groundEmbeddable (relationImage D B r) N := by
  let rD := ZFSet.sep (fun z => z ∈ ZFSet.prod D B) r
  have hrD : rD ∈ M.sets := M.injection_restriction_mem separation hD hB hr
  have image := M.relationImage_mem separation hD hB hr
  have partialCode : PartialFunctionCode D (relationImage D B r) rD := by
    refine ⟨?_, fun x y z xy xz => (functionCode_partial func).unique x y z
      (ZFSet.mem_sep.1 xy).1 (ZFSet.mem_sep.1 xz).1⟩
    intro z hz
    obtain ⟨rel, bound⟩ := ZFSet.mem_sep.1 hz
    obtain ⟨x, hx, y, hy, rfl⟩ := ZFSet.mem_prod.1 bound
    exact ZFSet.pair_mem_prod.2 ⟨hx, (mem_relationImage D B r y).2 ⟨hy, x, hx, rel⟩⟩
  have onto : ∀ y ∈ relationImage D B r, ∃ x ∈ D, ZFSet.pair x y ∈ rD := by
    intro y hy
    obtain ⟨hyB, x, hx, rel⟩ := (mem_relationImage D B r y).1 hy
    exact ⟨x, hx, ZFSet.mem_sep.2 ⟨rel, ZFSet.pair_mem_prod.2 ⟨hx, hyB⟩⟩⟩
  obtain ⟨f, hf, code⟩ := M.groundEmbeddable_of_partial_surjection pairing unions powers separation choice
    hD image hrD partialCode onto
  obtain ⟨g, hg, gcode⟩ := small
  exact ⟨relationCompose (relationImage D B r) D N f g,
    M.relationCompose_mem pairing unions powers separation image hD hN hf hg, code.compose gcode⟩

end TransitiveGround

end PartitionPilot.Forcing



namespace PartitionPilot.Forcing
open SetFormula
universe u

namespace GroundBelow
variable {M N : TransitiveGround.{u}} {A B K L : ZFSet.{u}}

theorem restrict (small : GroundBelow M B K) (separation : SeparationSchema M.sets)
    (hA : A ∈ M.sets) (hK : K ∈ M.sets) (subset : A ⊆ B) : GroundBelow M A K := by
  obtain ⟨β, hβ, witness⟩ := small
  exact ⟨β, hβ, M.groundEmbeddable_restrict separation hA (M.transitive hK hβ) subset witness⟩

theorem of_embeddable (small : GroundBelow M B K)
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (hA : A ∈ M.sets) (hB : B ∈ M.sets) (hK : K ∈ M.sets)
    (embedding : M.groundEmbeddable A B) : GroundBelow M A K := by
  obtain ⟨β, hβ, g, hg, second⟩ := small
  obtain ⟨f, hf, first⟩ := embedding
  exact ⟨β, hβ, relationCompose A B β f g,
    M.relationCompose_mem pairing unions powers separation hA hB (M.transitive hK hβ) hf hg,
    first.compose second⟩

theorem function_image (small : GroundBelow M A K)
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (choice : Realize M.sets SetFormula.choice Fin.elim0)
    {D f : ZFSet.{u}} (hA : A ∈ M.sets) (hB : B ∈ M.sets) (hK : K ∈ M.sets)
    (hf : f ∈ M.sets) (function : ZFSet.IsFunc D B f) :
    GroundBelow M (relationImage A B f) K := by
  obtain ⟨β, hβ, witness⟩ := small
  exact ⟨β, hβ, M.groundEmbeddable_function_image pairing unions powers separation choice
    hA hB (M.transitive hK hβ) hf function witness⟩

end GroundBelow

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



section
universe u

namespace BoundedFormula
open SetFormula

def mainStageFormula {n} (z P r μ G m inv one A bottom top height : Fin n) : BoundedFormula n :=
  nonemptyTupleFormula 10 z (Fin.cases P (Fin.cases r (Fin.cases μ (Fin.cases G (Fin.cases m (Fin.cases inv (Fin.cases one (Fin.cases A (Fin.cases bottom (Fin.cases top (Fin.cases height (Fin.elim0))))))))))))

end BoundedFormula

end



end PartitionPilot.Forcing

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Definability_PairPushFilterFamilies
attribute [-instance] _root_.OAI.PartitionPilot.Forcing.GroundMainPrefix.withTopSmall
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PartitionPilot.Forcing

universe u

theorem MeetEmbeddingCode.order_iff {P L rP rL μP μL S x y x' y' : ZFSet.{u}}
    (embedding : MeetEmbeddingCode P L rP rL μP μL S)
    (source : MeetOrderCode P rP μP) (target : MeetOrderCode L rL μL)
    (first : ZFSet.pair x x' ∈ S) (second : ZFSet.pair y y' ∈ S) :
    ZFSet.pair x' y' ∈ rL ↔ ZFSet.pair x y ∈ rP := by
  refine ⟨?_, fun lower => embedding.monotone x y x' y' lower first second⟩
  intro lower
  have sx := ZFSet.pair_mem_prod.1 (embedding.injection.function.1 first)
  have sy := ZFSet.pair_mem_prod.1 (embedding.injection.function.1 second)
  obtain ⟨z, meetXY, _⟩ := source.operation.2 (ZFSet.pair x y)
    (ZFSet.pair_mem_prod.2 ⟨sx.1, sy.1⟩)
  have hz := (ZFSet.pair_mem_prod.1 (source.operation.1 meetXY)).2
  obtain ⟨z', image, _⟩ := embedding.injection.function.2 z hz
  have hz' := (ZFSet.pair_mem_prod.1 (embedding.injection.function.1 image)).2
  have imageMeet := embedding.map_meet x y z x' y' z' meetXY first second image
  have equalImage : z' = x' := target.order.antisymm z' hz' x' sx.2
    (target.lower_left x' y' z' imageMeet)
    (target.greatest x' y' z' x' sx.2 imageMeet (target.order.refl x' sx.2) lower)
  have equal : z = x := embedding.injection.injective z x x' (equalImage ▸ image) first
  exact equal ▸ source.lower_right x y z meetXY

theorem meetFilter_pushFilter {P L rP rL μP μL S F : ZFSet.{u}}
    (source : MeetOrderCode P rP μP) (target : MeetOrderCode L rL μL)
    (embedding : MeetEmbeddingCode P L rP rL μP μL S)
    (filter : MeetFilterCode P rP μP F) :
    MeetFilterCode L rL μL (pushFilterCode L rL S F) where
  subset := pushFilterCode_subset L rL S F
  nonempty := by
    obtain ⟨f, hf⟩ := filter.nonempty
    obtain ⟨z, image, _⟩ := embedding.injection.function.2 f (filter.subset hf)
    have hz := (ZFSet.pair_mem_prod.1 (embedding.injection.function.1 image)).2
    exact ⟨z, (mem_pushFilterCode L rL S F z).2
      ⟨hz, f, hf, z, hz, image, target.order.refl z hz⟩⟩
  upward := by
    intro x hx y hy lower
    obtain ⟨hxL, f, hf, z, hz, image, below⟩ := (mem_pushFilterCode L rL S F x).1 hx
    exact (mem_pushFilterCode L rL S F y).2
      ⟨hy, f, hf, z, hz, image, target.order.trans z hz x hxL y hy below lower⟩
  closed_meet := by
    intro x hx y hy z meetXY
    obtain ⟨hxL, f, hf, f', hf', first, belowX⟩ := (mem_pushFilterCode L rL S F x).1 hx
    obtain ⟨hyL, g, hg, g', hg', second, belowY⟩ := (mem_pushFilterCode L rL S F y).1 hy
    have hz := (ZFSet.pair_mem_prod.1 (target.operation.1 meetXY)).2
    obtain ⟨h, meetFG, _⟩ := source.operation.2 (ZFSet.pair f g)
      (ZFSet.pair_mem_prod.2 ⟨filter.subset hf, filter.subset hg⟩)
    have hhF := filter.closed_meet f hf g hg h meetFG
    obtain ⟨h', image, _⟩ := embedding.injection.function.2 h (filter.subset hhF)
    have hh' := (ZFSet.pair_mem_prod.1 (embedding.injection.function.1 image)).2
    have imageMeet := embedding.map_meet f g h f' g' h' meetFG first second image
    have left := target.order.trans h' hh' f' hf' x hxL
      (target.lower_left f' g' h' imageMeet) belowX
    have right := target.order.trans h' hh' g' hg' y hyL
      (target.lower_right f' g' h' imageMeet) belowY
    exact (mem_pushFilterCode L rL S F z).2
      ⟨hz, h, hhF, h', hh', image, target.greatest x y z h' hh' meetXY left right⟩

theorem pushFilter_lower_bound {P L rP rL μP μL S F e e' y : ZFSet.{u}}
    (target : MeetOrderCode L rL μL) (embedding : MeetEmbeddingCode P L rP rL μP μL S)
    (lower : ∀ f ∈ F, ZFSet.pair e f ∈ rP) (entry : ZFSet.pair e e' ∈ S)
    (positive : y ∈ pushFilterCode L rL S F) : ZFSet.pair e' y ∈ rL := by
  obtain ⟨hy, f, hf, z, hz, image, below⟩ := (mem_pushFilterCode L rL S F y).1 positive
  have he' := (ZFSet.pair_mem_prod.1 (embedding.injection.function.1 entry)).2
  exact target.order.trans e' he' z hz y hy
    (embedding.monotone e f e' z (lower f hf) entry image) below

theorem pair_mem_pairPushFilterFamily (K I J L rL Ss Fs B i j V : ZFSet.{u}) :
    ZFSet.pair (ZFSet.pair i j) V ∈ pairPushFilterFamily K I J L rL Ss Fs B ↔
      ZFSet.pair i j ∈ K ∧ V ∈ B ∧ i ∈ I ∧ j ∈ J ∧ ∃ S F,
        ZFSet.pair i S ∈ Ss ∧ ZFSet.pair j F ∈ Fs ∧ V = pushFilterCode L rL S F := by
  rw [pairPushFilterFamily, ZFSet.mem_sep, ZFSet.pair_mem_prod]
  constructor
  · rintro ⟨⟨hk, hV⟩, i', hi, j', hj, S, _, F, _, V', _, equal, eS, eF, value⟩
    obtain ⟨pairEq, rfl⟩ := ZFSet.pair_inj.1 equal
    obtain ⟨rfl, rfl⟩ := ZFSet.pair_inj.1 pairEq
    exact ⟨hk, hV, hi, hj, S, F, eS, eF, value⟩
  · rintro ⟨hk, hV, hi, hj, S, F, eS, eF, value⟩
    exact ⟨⟨hk, hV⟩, i, hi, j, hj, S, pair_second_mem_doubleUnion eS,
      F, pair_second_mem_doubleUnion eF, V, hV, rfl, eS, eF, value⟩

theorem pairPushFilterFamily_entry_iff {K I J L rL Ss Fs B i j S F V : ZFSet.{u}}
    (maps : FunctionGraphOn I Ss) (filters : FunctionGraphOn J Fs)
    (mapEntry : ZFSet.pair i S ∈ Ss) (filterEntry : ZFSet.pair j F ∈ Fs) :
    ZFSet.pair (ZFSet.pair i j) V ∈ pairPushFilterFamily K I J L rL Ss Fs B ↔
      ZFSet.pair i j ∈ K ∧ V ∈ B ∧ V = pushFilterCode L rL S F := by
  rw [pair_mem_pairPushFilterFamily]
  constructor
  · rintro ⟨hk, hV, _, _, S', F', eS, eF, value⟩
    exact ⟨hk, hV, maps.unique eS mapEntry ▸ filters.unique eF filterEntry ▸ value⟩
  · rintro ⟨hk, hV, value⟩
    exact ⟨hk, hV, maps.pair_source mapEntry, filters.pair_source filterEntry,
      S, F, mapEntry, filterEntry, value⟩

theorem pairPushFilterFamily_function {K I J L rL Ss Fs B : ZFSet.{u}}
    (subset : K ⊆ ZFSet.prod I J) (maps : FunctionGraphOn I Ss) (filters : FunctionGraphOn J Fs)
    (bounds : ∀ i ∈ I, ∀ j ∈ J, ∀ S F,
      ZFSet.pair i S ∈ Ss → ZFSet.pair j F ∈ Fs → pushFilterCode L rL S F ∈ B) :
    ZFSet.IsFunc K B (pairPushFilterFamily K I J L rL Ss Fs B) := by
  refine ⟨fun _ hz => (ZFSet.mem_sep.1 hz).1, ?_⟩
  intro k hk
  obtain ⟨i, hi, j, hj, rfl⟩ := ZFSet.mem_prod.1 (subset hk)
  obtain ⟨S, eS⟩ := maps.total hi
  obtain ⟨F, eF⟩ := filters.total hj
  exact ⟨pushFilterCode L rL S F,
    (pairPushFilterFamily_entry_iff maps filters eS eF).2 ⟨hk, bounds i hi j hj S F eS eF, rfl⟩,
    fun V hV => ((pairPushFilterFamily_entry_iff maps filters eS eF).1 hV).2.2⟩

end PartitionPilot.Forcing

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Geometry_GroundAttachmentEmbeddings
attribute [-instance] _root_.OAI.PartitionPilot.Forcing.GroundMainPrefix.withTopSmall
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace PartitionPilot.Forcing




universe u






namespace BoundedFormula

open SetFormula

theorem truth_attachmentOldEmbeddingEntryFormula {n} (z p : Fin n)
    (env : Fin n → ZFSet.{u}) :
    Truth (attachmentOldEmbeddingEntryFormula z p) env ↔
      ∃ x ∈ env p, env z = ZFSet.pair x x := by
  simp only [attachmentOldEmbeddingEntryFormula, truth_exMem, truth_orderedPairFormula]
  rfl

end BoundedFormula

namespace TransitiveGround

open SetFormula
variable (M : TransitiveGround.{u})

theorem attachmentOldEmbeddingGraph_mem
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    {P : ZFSet.{u}} (hP : P ∈ M.sets) : attachmentOldEmbeddingGraph P ∈ M.sets := by
  let params := extend P Fin.elim0
  have selected := M.bounded_separation_mem separation
    (BoundedFormula.attachmentOldEmbeddingEntryFormula 0 1) params
    (Fin.cases hP (fun i => Fin.elim0 i))
    (M.prod_mem pairing unions powers separation hP hP)
  have eq : ZFSet.sep (fun z => BoundedFormula.Truth
      (BoundedFormula.attachmentOldEmbeddingEntryFormula 0 1) (extend z params))
      (ZFSet.prod P P) = attachmentOldEmbeddingGraph P := by
    apply ZFSet.ext
    intro z
    rw [attachmentOldEmbeddingGraph, ZFSet.mem_sep, ZFSet.mem_sep]
    exact and_congr Iff.rfl (BoundedFormula.truth_attachmentOldEmbeddingEntryFormula 0 1 _)
  exact eq ▸ selected

end TransitiveGround


end PartitionPilot.Forcing

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Definability_FixedTopCodes
attribute [-instance] _root_.OAI.PartitionPilot.Forcing.GroundMainPrefix.withTopSmall
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PartitionPilot.Forcing

universe u

namespace MeetOrderCode

theorem pair_iff {L r μ x y z : ZFSet.{u}} (code : MeetOrderCode L r μ) :
    ZFSet.pair (ZFSet.pair x y) z ∈ μ ↔
      x ∈ L ∧ y ∈ L ∧ z ∈ L ∧ GreatestLowerBoundCode L r x y z := by
  constructor
  · intro h
    have shape := ZFSet.pair_mem_prod.1 (code.operation.1 h)
    have domain := ZFSet.pair_mem_prod.1 shape.1
    exact ⟨domain.1, domain.2, shape.2, code.lower_left x y z h,
      code.lower_right x y z h, fun w hw => code.greatest x y z w hw h⟩
  · rintro ⟨hx, hy, hz, h⟩
    obtain ⟨w, hw, _⟩ := code.operation.2 (ZFSet.pair x y) (ZFSet.pair_mem_prod.2 ⟨hx, hy⟩)
    have wL := (ZFSet.pair_mem_prod.1 (code.operation.1 hw)).2
    have glb : GreatestLowerBoundCode L r x y w :=
      ⟨code.lower_left x y w hw, code.lower_right x y w hw,
        fun a ha => code.greatest x y w a ha hw⟩
    have eq := GreatestLowerBoundCode.unique code.order hz wL h glb
    exact eq.symm ▸ hw

end MeetOrderCode

noncomputable def fixedTopMeet (P r : ZFSet.{u}) : ZFSet.{u} :=
  canonicalMeetGraph (fixedTopCarrier P) (fixedTopOrder P r)

end PartitionPilot.Forcing

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Geometry_SeparationTileCodes
attribute [-instance] _root_.OAI.PartitionPilot.Forcing.GroundMainPrefix.withTopSmall
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace PartitionPilot.Forcing

universe u

namespace BoundedFormula
open SetFormula

theorem truth_codedAttachmentFreshLeFormula {n} (x y p inside shadow upper : Fin n)
    (env : Fin n → ZFSet.{u}) :
    Truth (codedAttachmentFreshLeFormula x y p inside shadow upper) env ↔
      codedAttachmentFreshLe (env p) (env inside) (env shadow) (env upper) (env x) (env y) := by
  simp only [codedAttachmentFreshLeFormula, truth_disj, truth_exMem, Truth,
    truth_pairMembershipFormula]
  rfl

theorem truth_codedAttachmentLeFormula {n} (x y p nset r inside shadow upper : Fin n)
    (env : Fin n → ZFSet.{u}) :
    Truth (codedAttachmentLeFormula x y p nset r inside shadow upper) env ↔
      codedAttachmentLe (env p) (env nset) (env r) (env inside) (env shadow)
        (env upper) (env x) (env y) := by
  simp only [codedAttachmentLeFormula, attachmentOldNewFormula, truth_disj, truth_exMem,
    Truth, truth_pairMembershipFormula, truth_orderedPairFormula, truth_codedAttachmentFreshLeFormula]
  rfl

theorem truth_codedAttachmentOrderEntryFormula {n} (z l p nset r inside shadow upper : Fin n)
    (env : Fin n → ZFSet.{u}) :
    Truth (codedAttachmentOrderEntryFormula z l p nset r inside shadow upper) env ↔
      ∃ x ∈ env l, ∃ y ∈ env l, env z = ZFSet.pair x y ∧
        codedAttachmentLe (env p) (env nset) (env r) (env inside) (env shadow) (env upper) x y := by
  simp only [codedAttachmentOrderEntryFormula, truth_exMem, Truth,
    truth_orderedPairFormula, truth_codedAttachmentLeFormula]
  rfl

end BoundedFormula

end PartitionPilot.Forcing



namespace PartitionPilot.Forcing

universe u

namespace BoundedFormula

open SetFormula

theorem truth_greatestLowerBoundFormula {n} (l r x y z : Fin n)
    (env : Fin n → ZFSet.{u}) :
    Truth (greatestLowerBoundFormula l r x y z) env ↔
      GreatestLowerBoundCode (env l) (env r) (env x) (env y) (env z) := by
  simp only [greatestLowerBoundFormula, Truth, truth_imp,
    truth_pairMembershipFormula, GreatestLowerBoundCode]
  rfl

theorem truth_canonicalMeetEntryFormula {n} (v l r : Fin n)
    (env : Fin n → ZFSet.{u}) :
    Truth (canonicalMeetEntryFormula v l r) env ↔
      env v ∈ canonicalMeetGraph (env l) (env r) := by
  simp only [canonicalMeetEntryFormula, truth_exMem, Truth,
    truth_orderedTripleFormula, truth_greatestLowerBoundFormula, mem_canonicalMeetGraph]
  rfl

end BoundedFormula

namespace TransitiveGround

open SetFormula

theorem canonicalMeetGraph_mem (M : TransitiveGround.{u})
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    {L r : ZFSet.{u}} (hL : L ∈ M.sets) (hr : r ∈ M.sets) :
    canonicalMeetGraph L r ∈ M.sets := by
  let params := extend L (extend r Fin.elim0)
  have selected := M.bounded_separation_mem separation
    (BoundedFormula.canonicalMeetEntryFormula 0 1 2) params
    (Fin.cases hL (Fin.cases hr (fun i => Fin.elim0 i)))
    (M.prod_mem pairing unions powers separation
      (M.prod_mem pairing unions powers separation hL hL) hL)
  have eq : ZFSet.sep (fun v => BoundedFormula.Truth
      (BoundedFormula.canonicalMeetEntryFormula 0 1 2) (extend v params))
      (ZFSet.prod (ZFSet.prod L L) L) = canonicalMeetGraph L r := by
    apply ZFSet.ext
    intro v
    rw [ZFSet.mem_sep, BoundedFormula.truth_canonicalMeetEntryFormula]
    exact ⟨And.right, fun hv => ⟨canonicalMeetGraph_subset L r hv, hv⟩⟩
  exact eq ▸ selected

end TransitiveGround

end PartitionPilot.Forcing



end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Geometry_GroundSingleAttachment
attribute [-instance] _root_.OAI.PartitionPilot.Forcing.GroundMainPrefix.withTopSmall
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI



namespace PartitionPilot.Forcing.SingleAttachmentInputs

universe u

theorem pushforward
    {P Q L rP rQ rL μP μQ μL ell F a e S e' : ZFSet.{u}}
    (d : SingleAttachmentInputs P Q rP rQ μP μQ ell F a e)
    (target : MeetOrderCode L rL μL)
    (embedding : MeetEmbeddingCode P L rP rL μP μL S)
    (separator : ZFSet.pair e e' ∈ S) :
    SingleAttachmentInputs L Q rL rQ μL μQ
      (relationCompose (attachmentIdeal Q rQ a) P L ell S)
      (pushFilterCode L rL S F) a e' where
  oldOrder := target
  templateOrder := d.templateOrder
  anchor_mem := d.anchor_mem
  base_function := relationCompose_function_of_subset d.base_function embedding.injection.function
    (fun _ hx => hx)
  base_order := by
    intro x y x' y' first second
    obtain ⟨_, _, u, _, xu, ux'⟩ := (pair_mem_relationCompose _ _ _ _ _ _ _).1 first
    obtain ⟨_, _, v, _, yv, vy'⟩ := (pair_mem_relationCompose _ _ _ _ _ _ _).1 second
    exact (embedding.order_iff d.oldOrder target ux' vy').trans (d.base_order x y u v xu yv)
  base_meet := by
    intro x y z x' y' z' meetXYZ first second third
    obtain ⟨_, _, u, _, xu, ux'⟩ := (pair_mem_relationCompose _ _ _ _ _ _ _).1 first
    obtain ⟨_, _, v, _, yv, vy'⟩ := (pair_mem_relationCompose _ _ _ _ _ _ _).1 second
    obtain ⟨_, _, w, _, zw, wz'⟩ := (pair_mem_relationCompose _ _ _ _ _ _ _).1 third
    exact embedding.map_meet u v w x' y' z'
      (d.base_meet x y z u v w meetXYZ xu yv zw) ux' vy' wz'
  filter := meetFilter_pushFilter d.oldOrder target embedding d.filter
  separator_mem := (ZFSet.pair_mem_prod.1 (embedding.injection.function.1 separator)).2
  base_le_separator := by
    intro b entry
    obtain ⟨_, _, c, _, base, image⟩ := (pair_mem_relationCompose _ _ _ _ _ _ _).1 entry
    exact embedding.monotone c e b e' (d.base_le_separator c base) image separator
  separator_not_le_base := by
    intro b entry lower
    obtain ⟨_, _, c, _, base, image⟩ := (pair_mem_relationCompose _ _ _ _ _ _ _).1 entry
    exact d.separator_not_le_base c base ((embedding.order_iff d.oldOrder target separator image).1 lower)
  separator_le_upper := by
    intro y positive
    exact pushFilter_lower_bound target embedding d.separator_le_upper separator positive

end PartitionPilot.Forcing.SingleAttachmentInputs



end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Geometry_TemplateHeightRangeCodes
attribute [-instance] _root_.OAI.PartitionPilot.Forcing.GroundMainPrefix.withTopSmall
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open scoped ZFSet

namespace PartitionPilot.Forcing

universe u

namespace BoundedFormula

open SetFormula

def heightImageEquationFormula {n} (R Q B h : Fin n) : BoundedFormula n :=
  .conj (.allMem R (.conj (.mem 0 B.succ) (imageMemberFormula 0 Q.succ h.succ)))
    (.allMem B (imp (imageMemberFormula 0 Q.succ h.succ) (.mem 0 R.succ)))

def heightOrderEquationFormula {n} (r R s : Fin n) : BoundedFormula n :=
  .conj (.allMem r (.conj (.mem 0 s.succ) (productElementFormula 0 R.succ R.succ)))
    (.allMem s (imp (productElementFormula 0 R.succ R.succ) (.mem 0 r.succ)))

def heightImageCandidateFormula {n} (Qs Bs Hs i R qb bb hb : Fin n) : BoundedFormula n :=
  let lift (j : Fin n) := j.succ.succ.succ
  exMem qb (exMem bb.succ (exMem hb.succ.succ
    (.conj (pairMembershipFormula (lift i) 2 (lift Qs))
      (.conj (pairMembershipFormula (lift i) 1 (lift Bs))
        (.conj (pairMembershipFormula (lift i) 0 (lift Hs))
          (heightImageEquationFormula (lift R) 2 1 0))))))

def heightOrderCandidateFormula {n} (Rs brs i r rb sb : Fin n) : BoundedFormula n :=
  exMem rb (exMem sb.succ
    (.conj (pairMembershipFormula i.succ.succ 1 Rs.succ.succ)
      (.conj (pairMembershipFormula i.succ.succ 0 brs.succ.succ)
        (heightOrderEquationFormula r.succ.succ 1 0))))

def heightImageFamilyEntryFormula {n} (z I W Qs Bs Hs qb bb hb : Fin n) : BoundedFormula n :=
  exMem I (exMem W.succ (.conj (orderedPairFormula z.succ.succ 1 0)
    (heightImageCandidateFormula Qs.succ.succ Bs.succ.succ Hs.succ.succ 1 0
      qb.succ.succ bb.succ.succ hb.succ.succ)))

def heightOrderFamilyEntryFormula {n} (z I W Rs brs rb sb : Fin n) : BoundedFormula n :=
  exMem I (exMem W.succ (.conj (orderedPairFormula z.succ.succ 1 0)
    (heightOrderCandidateFormula Rs.succ.succ brs.succ.succ 1 0 rb.succ.succ sb.succ.succ)))

end BoundedFormula

end PartitionPilot.Forcing

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Definability_GroundBatchAttachmentGraphs
attribute [-instance] _root_.OAI.PartitionPilot.Forcing.GroundMainPrefix.withTopSmall
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PartitionPilot.Forcing

universe u

namespace BoundedFormula

open SetFormula

theorem truth_batchShadowGraphFormula (env : Fin 11 → ZFSet.{u}) :
    Truth batchShadowGraphFormula env ↔
      ∃ i ∈ env 1, ∃ Q ∈ env 7, ∃ μ ∈ env 8, ∃ a ∈ env 9, ∃ ell ∈ env 10,
        ∃ q ∈ Q, ∃ p ∈ env 2, env 0 = ZFSet.pair (ZFSet.pair i q) p ∧
          ZFSet.pair i Q ∈ env 3 ∧ ZFSet.pair i μ ∈ env 4 ∧
          ZFSet.pair i a ∈ env 5 ∧ ZFSet.pair i ell ∈ env 6 ∧
          ∃ c ∈ Q, ZFSet.pair (ZFSet.pair q a) c ∈ μ ∧ ZFSet.pair c p ∈ ell := by
  simp only [batchShadowGraphFormula, truth_exMem, Truth, truth_orderedTripleFormula,
    truth_pairMembershipFormula, truth_tripleMembershipFormula]
  rfl

end BoundedFormula

namespace TransitiveGround

open SetFormula
variable (M : TransitiveGround.{u})

theorem batchAttachmentShadowGraph_mem
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    {I P Qs μs As Es : ZFSet.{u}} (hI : I ∈ M.sets) (hP : P ∈ M.sets)
    (hQs : Qs ∈ M.sets) (hμs : μs ∈ M.sets) (hAs : As ∈ M.sets) (hEs : Es ∈ M.sets) :
    batchAttachmentShadowGraph I P Qs μs As Es ∈ M.sets := by
  have doubleUnion {x : ZFSet.{u}} (hx : x ∈ M.sets) : ZFSet.sUnion (ZFSet.sUnion x) ∈ M.sets :=
    M.union_mem unions (M.union_mem unions hx)
  let params := extend I (extend P (extend Qs (extend μs (extend As (extend Es
    (extend (ZFSet.sUnion (ZFSet.sUnion Qs)) (extend (ZFSet.sUnion (ZFSet.sUnion μs))
      (extend (ZFSet.sUnion (ZFSet.sUnion As)) (extend (ZFSet.sUnion (ZFSet.sUnion Es)) Fin.elim0)))))))))
  have selected := M.bounded_separation_mem separation BoundedFormula.batchShadowGraphFormula params
    (Fin.cases hI (Fin.cases hP (Fin.cases hQs (Fin.cases hμs (Fin.cases hAs (Fin.cases hEs
      (Fin.cases (doubleUnion hQs) (Fin.cases (doubleUnion hμs)
        (Fin.cases (doubleUnion hAs) (Fin.cases (doubleUnion hEs) (fun j => Fin.elim0 j)))))))))))
    (M.prod_mem pairing unions powers separation
      (M.indexedAttachmentDomain_mem pairing unions powers separation hI hQs) hP)
  have equal : ZFSet.sep (fun z => BoundedFormula.Truth BoundedFormula.batchShadowGraphFormula
      (extend z params)) (ZFSet.prod (indexedAttachmentDomain I Qs) P) =
        batchAttachmentShadowGraph I P Qs μs As Es := by
    apply ZFSet.ext
    intro z
    rw [batchAttachmentShadowGraph, ZFSet.mem_sep, ZFSet.mem_sep]
    exact and_congr Iff.rfl (BoundedFormula.truth_batchShadowGraphFormula _)
  exact equal ▸ selected

end TransitiveGround

end PartitionPilot.Forcing

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Definability_BatchAttachmentRealization
attribute [-instance] _root_.OAI.PartitionPilot.Forcing.GroundMainPrefix.withTopSmall
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace PartitionPilot.Forcing

section
universe u v w

namespace CodedTemplateAttachment
variable {J : Type v} {P r μ N inside shadow upper : ZFSet.{u}}
variable {old : MeetOrderCode P r μ} {b : Attachment.Templates.{u+1,w,v} old.toMeetOrder J}
variable (d : CodedTemplateAttachment old b N inside shadow upper)

theorem encode_injective : Function.Injective d.encode := by
  intro x y eq
  cases x with
  | inl p =>
    cases y with
    | inl s => exact congrArg Sum.inl (Subtype.ext eq)
    | inr q =>
      change p.val = ZFSet.pair P (d.freshCode q) at eq
      exact False.elim (pair_tag_not_mem P (d.freshCode q) (eq ▸ p.property))
  | inr q =>
    cases y with
    | inl p =>
      change ZFSet.pair P (d.freshCode q) = p.val at eq
      exact False.elim (pair_tag_not_mem P (d.freshCode q) (eq.symm ▸ p.property))
    | inr t => exact congrArg Sum.inr (d.fresh_injective (ZFSet.pair_inj.1 eq).2)

end CodedTemplateAttachment

end




universe u

namespace BoundedFormula

open SetFormula

theorem truth_pairOfPairsFormula {n} (z a b c d : Fin n) (env : Fin n → ZFSet.{u}) :
    Truth (pairOfPairsFormula z a b c d) env ↔
      env z = ZFSet.pair (ZFSet.pair (env a) (env b)) (ZFSet.pair (env c) (env d)) := by
  simp only [pairOfPairsFormula, truth_exMem, Truth, truth_orderedPairFormula]
  change (∃ u ∈ env z, ∃ x ∈ u, ∃ v ∈ env z, ∃ y ∈ v,
    x = ZFSet.pair (env a) (env b) ∧ y = ZFSet.pair (env c) (env d) ∧ env z = ZFSet.pair x y) ↔ _
  constructor
  · rintro ⟨_, _, x, _, _, _, y, _, rfl, rfl, eq⟩
    exact eq
  · intro eq
    refine ⟨{ZFSet.pair (env a) (env b)}, ?_, ZFSet.pair (env a) (env b),
      ZFSet.mem_singleton.2 rfl, {ZFSet.pair (env a) (env b), ZFSet.pair (env c) (env d)},
      ?_, ZFSet.pair (env c) (env d), ZFSet.mem_pair.2 (Or.inr rfl), rfl, rfl, eq⟩
    · rw [eq]
      exact ZFSet.mem_pair.2 (Or.inl rfl)
    · rw [eq]
      exact ZFSet.mem_pair.2 (Or.inr rfl)

theorem truth_batchAttachmentInsideEntryFormula {n} (z i qs rs qb rb : Fin n)
    (env : Fin n → ZFSet.{u}) :
    Truth (batchAttachmentInsideEntryFormula z i qs rs qb rb) env ↔
      ∃ j ∈ env i, ∃ Q ∈ env qb, ∃ r ∈ env rb, ∃ q ∈ Q, ∃ t ∈ Q,
        env z = ZFSet.pair (ZFSet.pair j q) (ZFSet.pair j t) ∧
          ZFSet.pair j Q ∈ env qs ∧ ZFSet.pair j r ∈ env rs ∧ ZFSet.pair q t ∈ r := by
  simp only [batchAttachmentInsideEntryFormula, truth_exMem, Truth,
    truth_pairOfPairsFormula, truth_pairMembershipFormula]
  rfl

theorem truth_batchAttachmentUpperEntryFormula {n} (z i p qs fs qb fb : Fin n)
    (env : Fin n → ZFSet.{u}) :
    Truth (batchAttachmentUpperEntryFormula z i p qs fs qb fb) env ↔
      ∃ j ∈ env i, ∃ Q ∈ env qb, ∃ F ∈ env fb, ∃ q ∈ Q, ∃ v ∈ env p,
        env z = ZFSet.pair (ZFSet.pair j q) v ∧
          ZFSet.pair j Q ∈ env qs ∧ ZFSet.pair j F ∈ env fs ∧ v ∈ F := by
  simp only [batchAttachmentUpperEntryFormula, truth_exMem, Truth,
    truth_orderedTripleFormula, truth_pairMembershipFormula]
  rfl

end BoundedFormula

namespace TransitiveGround

open SetFormula
variable (M : TransitiveGround.{u})

theorem batchAttachmentInsideGraph_mem
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    {I Qs rs : ZFSet.{u}} (hI : I ∈ M.sets) (hQs : Qs ∈ M.sets) (hrs : rs ∈ M.sets) :
    batchAttachmentInsideGraph I Qs rs ∈ M.sets := by
  have qBound := M.union_mem unions (M.union_mem unions hQs)
  have rBound := M.union_mem unions (M.union_mem unions hrs)
  have domain := M.indexedAttachmentDomain_mem pairing unions powers separation hI hQs
  let params := extend I (extend Qs (extend rs
    (extend (ZFSet.sUnion (ZFSet.sUnion Qs)) (extend (ZFSet.sUnion (ZFSet.sUnion rs)) Fin.elim0))))
  have selected := M.bounded_separation_mem separation
    (BoundedFormula.batchAttachmentInsideEntryFormula 0 1 2 3 4 5) params
    (Fin.cases hI (Fin.cases hQs (Fin.cases hrs (Fin.cases qBound
      (Fin.cases rBound (fun j => Fin.elim0 j))))))
    (M.prod_mem pairing unions powers separation domain domain)
  have eq : ZFSet.sep (fun z => BoundedFormula.Truth
      (BoundedFormula.batchAttachmentInsideEntryFormula 0 1 2 3 4 5) (extend z params))
      (ZFSet.prod (indexedAttachmentDomain I Qs) (indexedAttachmentDomain I Qs)) =
      batchAttachmentInsideGraph I Qs rs := by
    apply ZFSet.ext
    intro z
    rw [batchAttachmentInsideGraph, ZFSet.mem_sep, ZFSet.mem_sep]
    exact and_congr Iff.rfl (BoundedFormula.truth_batchAttachmentInsideEntryFormula 0 1 2 3 4 5 _)
  exact eq ▸ selected

theorem batchAttachmentUpperGraph_mem
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    {I P Qs Fs : ZFSet.{u}} (hI : I ∈ M.sets) (hP : P ∈ M.sets)
    (hQs : Qs ∈ M.sets) (hFs : Fs ∈ M.sets) : batchAttachmentUpperGraph I P Qs Fs ∈ M.sets := by
  have qBound := M.union_mem unions (M.union_mem unions hQs)
  have fBound := M.union_mem unions (M.union_mem unions hFs)
  have domain := M.indexedAttachmentDomain_mem pairing unions powers separation hI hQs
  let params := extend I (extend P (extend Qs (extend Fs
    (extend (ZFSet.sUnion (ZFSet.sUnion Qs)) (extend (ZFSet.sUnion (ZFSet.sUnion Fs)) Fin.elim0)))))
  have selected := M.bounded_separation_mem separation
    (BoundedFormula.batchAttachmentUpperEntryFormula 0 1 2 3 4 5 6) params
    (Fin.cases hI (Fin.cases hP (Fin.cases hQs (Fin.cases hFs (Fin.cases qBound
      (Fin.cases fBound (fun j => Fin.elim0 j)))))))
    (M.prod_mem pairing unions powers separation domain hP)
  have eq : ZFSet.sep (fun z => BoundedFormula.Truth
      (BoundedFormula.batchAttachmentUpperEntryFormula 0 1 2 3 4 5 6) (extend z params))
      (ZFSet.prod (indexedAttachmentDomain I Qs) P) = batchAttachmentUpperGraph I P Qs Fs := by
    apply ZFSet.ext
    intro z
    rw [batchAttachmentUpperGraph, ZFSet.mem_sep, ZFSet.mem_sep]
    exact and_congr Iff.rfl (BoundedFormula.truth_batchAttachmentUpperEntryFormula 0 1 2 3 4 5 6 _)
  exact eq ▸ selected

end TransitiveGround


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

namespace TransitiveGround
open SetFormula
universe u
variable (M : TransitiveGround.{u})

theorem codedAttachmentOrder_mem
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    {P N r inside shadow upper : ZFSet.{u}}
    (hP : P ∈ M.sets) (hN : N ∈ M.sets) (hr : r ∈ M.sets)
    (hi : inside ∈ M.sets) (hs : shadow ∈ M.sets) (hu : upper ∈ M.sets) :
    codedAttachmentOrder P N r inside shadow upper ∈ M.sets := by
  let L := taggedExtension P N
  have hL := M.taggedExtension_mem pairing unions powers separation hP hN
  let params := extend L (extend P (extend N (extend r (extend inside
    (extend shadow (extend upper Fin.elim0))))))
  have selected := M.bounded_separation_mem separation
    (BoundedFormula.codedAttachmentOrderEntryFormula 0 1 2 3 4 5 6 7) params
    (Fin.cases hL (Fin.cases hP (Fin.cases hN (Fin.cases hr (Fin.cases hi
      (Fin.cases hs (Fin.cases hu (fun i => Fin.elim0 i))))))))
    (M.prod_mem pairing unions powers separation hL hL)
  have eq : ZFSet.sep (fun z => BoundedFormula.Truth
      (BoundedFormula.codedAttachmentOrderEntryFormula 0 1 2 3 4 5 6 7)
      (extend z params)) (ZFSet.prod L L) = codedAttachmentOrder P N r inside shadow upper := by
    apply ZFSet.ext
    intro z
    rw [ZFSet.mem_sep, codedAttachmentOrder, ZFSet.mem_sep]
    exact and_congr Iff.rfl (BoundedFormula.truth_codedAttachmentOrderEntryFormula 0 1 2 3 4 5 6 7 _)
  exact eq ▸ selected

end TransitiveGround



open SetFormula
universe u

end PartitionPilot.Forcing

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Definability_BoundedRelationImageEquality
attribute [-instance] _root_.OAI.PartitionPilot.Forcing.GroundMainPrefix.withTopSmall
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PartitionPilot.Forcing.BoundedFormula
open SetFormula
universe u

def relationImageEqualityFormula {n} (output domain codomain graph : Fin n) : BoundedFormula n :=
  .conj (.allMem output (.conj (.mem 0 codomain.succ)
    (imageMemberFormula 0 domain.succ graph.succ)))
    (.allMem codomain (imp (imageMemberFormula 0 domain.succ graph.succ) (.mem 0 output.succ)))

theorem truth_relationImageEqualityFormula {n} (output domain codomain graph : Fin n)
    (env : Fin n → ZFSet.{u}) :
    Truth (relationImageEqualityFormula output domain codomain graph) env ↔
      env output = relationImage (env domain) (env codomain) (env graph) := by
  simp only [relationImageEqualityFormula, Truth, truth_imageMemberFormula, truth_imp]
  change ((∀ y ∈ env output, y ∈ env codomain ∧ ∃ x ∈ env domain,
      ZFSet.pair x y ∈ env graph) ∧
    (∀ y ∈ env codomain, (∃ x ∈ env domain, ZFSet.pair x y ∈ env graph) → y ∈ env output)) ↔ _
  constructor
  · rintro ⟨forward, backward⟩
    apply ZFSet.ext
    intro y
    rw [mem_relationImage]
    exact ⟨forward y, fun h => backward y h.1 h.2⟩
  · intro equal
    constructor
    · intro y hy
      exact (mem_relationImage _ _ _ y).1 (equal ▸ hy)
    · intro y hy member
      exact equal ▸ (mem_relationImage _ _ _ y).2 ⟨hy, member⟩

end PartitionPilot.Forcing.BoundedFormula

end

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Definability_CodedBatchDecoding
attribute [-instance] _root_.OAI.PartitionPilot.Forcing.GroundMainPrefix.withTopSmall
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PartitionPilot.Forcing.CodedTemplateAttachment

open Compression.RecursiveMaps
universe u v w
variable {J : Type v} {P r μ N inside shadow upper : ZFSet.{u}}
variable {old : MeetOrderCode P r μ}
variable {b : Attachment.Templates.{u+1,w,v} old.toMeetOrder J}
variable (d : CodedTemplateAttachment old b N inside shadow upper)

noncomputable def decode (x : {x : ZFSet.{u} // x ∈ d.carrier}) : {p : ZFSet.{u} // p ∈ P} ⊕ b.Fresh :=
  Classical.choose (d.encode_surjective x.val x.property)

theorem encode_decode (x : {x : ZFSet.{u} // x ∈ d.carrier}) : d.encode (d.decode x) = x.val :=
  Classical.choose_spec (d.encode_surjective x.val x.property)

theorem decode_encode (x : {p : ZFSet.{u} // p ∈ P} ⊕ b.Fresh) : d.decode ⟨d.encode x, d.encode_mem x⟩ = x :=
  d.encode_injective (d.encode_decode _)

noncomputable def encodingIso : Compression.MeetIso b.extension d.meetOrder.toMeetOrder :=
  isoOfOrder (fun x => ⟨d.encode x, d.encode_mem x⟩) d.decode d.decode_encode
    (fun x => Subtype.ext (d.encode_decode x)) d.le_encode

noncomputable def decodingIso : Compression.MeetIso d.meetOrder.toMeetOrder b.extension :=
  inverseIso d.encodingIso

theorem decodingIso_encode (x : {x : ZFSet.{u} // x ∈ d.carrier}) :
    d.encode (d.decodingIso.toFun x) = x.val := d.encode_decode x

end PartitionPilot.Forcing.CodedTemplateAttachment

end

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Geometry_GrowthLayerSourceCongruence
attribute [-instance] _root_.OAI.PartitionPilot.Forcing.GroundMainPrefix.withTopSmall
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PartitionPilot.Forcing

namespace TransitiveGround

universe u
variable (M N : TransitiveGround.{u})

theorem groundEmbeddable_of_inclusion (includes : M.sets ⊆ N.sets)
    {A B : ZFSet.{u}} (small : M.groundEmbeddable A B) : N.groundEmbeddable A B := by
  obtain ⟨f, hf, injection⟩ := small
  exact ⟨f, includes hf, injection⟩

end TransitiveGround

namespace CodedGrowthLayer

universe u

def of_inclusion {M N : TransitiveGround.{u}}
    {Space sourceOrder sourceMeet : ZFSet.{u} → ZFSet.{u}}
    {L r μ birth t : ZFSet.{u}}
    (layer : CodedGrowthLayer M Space sourceOrder sourceMeet L r μ birth t)
    (includes : M.sets ⊆ N.sets) :
    CodedGrowthLayer N Space sourceOrder sourceMeet L r μ birth t := by
  cases layer with
  | countablePoints D ground small cover =>
    exact .countablePoints D (includes ground)
      (M.groundEmbeddable_of_inclusion N includes small) cover
  | copies I parts groundI small groundParts index e earlier groundCopy embedding cover inCopy =>
    exact .copies I parts (includes groundI)
      (M.groundEmbeddable_of_inclusion N includes small) (includes groundParts)
      index e earlier (fun i hi => includes (groundCopy i hi)) embedding cover inCopy
  | separated I index e earlier groundCopy embedding component cover separated =>
    exact .separated I index e earlier (fun i => includes (groundCopy i))
      embedding component cover separated

def congr_sources_below {M : TransitiveGround.{u}}
    {Space sourceOrder sourceMeet Space' sourceOrder' sourceMeet' : ZFSet.{u} → ZFSet.{u}}
    {L r μ birth t : ZFSet.{u}}
    (layer : CodedGrowthLayer M Space sourceOrder sourceMeet L r μ birth t)
    (spaces : ∀ s ∈ t, Space s = Space' s)
    (orders : ∀ s ∈ t, sourceOrder s = sourceOrder' s)
    (meets : ∀ s ∈ t, sourceMeet s = sourceMeet' s) :
    CodedGrowthLayer M Space' sourceOrder' sourceMeet' L r μ birth t := by
  cases layer with
  | countablePoints D ground small cover =>
    exact .countablePoints D ground small cover
  | copies I parts groundI small groundParts index e earlier groundCopy embedding cover inCopy =>
    refine .copies I parts groundI small groundParts index e earlier groundCopy ?_ cover ?_
    · intro i hi
      simpa only [← spaces (index i) (earlier i hi), ← orders (index i) (earlier i hi),
        ← meets (index i) (earlier i hi)] using embedding i hi
    · intro i hi x hx entry
      simpa only [← spaces (index i) (earlier i hi)] using inCopy i hi x hx entry
  | separated I index e earlier groundCopy embedding component cover separation =>
    refine .separated I index e earlier groundCopy ?_ component ?_ separation
    · intro i
      simpa only [← spaces (index i) (earlier i), ← orders (index i) (earlier i),
        ← meets (index i) (earlier i)] using embedding i
    · intro x
      simpa only [← spaces (index (component x)) (earlier (component x))] using cover x

end CodedGrowthLayer

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

def CodedGrowthLayer.restrictBirth
    {M : TransitiveGround.{u}} {Space sourceOrder sourceMeet : ZFSet.{u} → ZFSet.{u}}
    {L r μ birth t : ZFSet.{u}}
    (layer : CodedGrowthLayer M Space sourceOrder sourceMeet L r μ birth t)
    (meet : MeetOrderCode L r μ) :
    CodedGrowthLayer M Space sourceOrder sourceMeet L r μ (graphRestriction L birth) t := by
  cases layer with
  | countablePoints D ground small cover =>
    exact .countablePoints D ground small
      (fun x hx entry => cover x hx (pair_mem_graphRestriction.1 entry).1)
  | copies I parts groundI small groundParts index e earlier groundCopy embedding cover inCopy =>
    exact .copies I parts groundI small groundParts index e earlier groundCopy embedding
      (fun x hx entry => cover x hx (pair_mem_graphRestriction.1 entry).1) inCopy
  | separated I index e earlier groundCopy embedding component cover separated =>
    let original (x : {x : ZFSet.{u} // x ∈ L ∧ ZFSet.pair x t ∈ graphRestriction L birth}) :
        {x : ZFSet.{u} // x ∈ L ∧ ZFSet.pair x t ∈ birth} :=
      ⟨x.val, x.property.1, (pair_mem_graphRestriction.1 x.property.2).1⟩
    refine .separated I index e earlier groundCopy embedding (fun x => component (original x))
      (fun x => cover (original x)) ?_
    intro x y different
    rcases separated (original x) (original y) different with
      ⟨z, a, entry, born, before⟩ | ⟨z, hz, a, born, before, between⟩
    · exact Or.inl ⟨z, a, entry, pair_mem_graphRestriction.2
        ⟨born, (ZFSet.pair_mem_prod.1 (meet.operation.1 entry)).2⟩, before⟩
    · exact Or.inr ⟨z, hz, a, pair_mem_graphRestriction.2 ⟨born, hz⟩, before, between⟩

end PartitionPilot.Forcing

end

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Definability_CodedTemplateShadowLaws
attribute [-instance] _root_.OAI.PartitionPilot.Forcing.GroundMainPrefix.withTopSmall
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PartitionPilot.Forcing.CodedTemplateAttachment
universe u v w
variable {J : Type v} {P r μ N inside shadow upper : ZFSet.{u}}
variable {old : MeetOrderCode P r μ} {b : Attachment.Templates.{u+1,w,v} old.toMeetOrder J}
variable (d : CodedTemplateAttachment old b N inside shadow upper)

theorem greatest_preserved {T : ZFSet.{u}} (hT : T ∈ P)
    (greatest : ∀ p ∈ P, ZFSet.pair p T ∈ r) :
    ∀ z ∈ d.carrier, ZFSet.pair z T ∈ d.order := by
  intro z hz
  obtain ⟨x, rfl⟩ := d.encode_surjective z hz
  exact (d.le_encode x (.inl ⟨T, hT⟩)).2
    (b.greatest_preserved ⟨T, hT⟩ (fun p => greatest p.val p.property) x)

end PartitionPilot.Forcing.CodedTemplateAttachment

end

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

namespace PosetActionCode

open SetRealization

variable {G P m inv e r A : ZFSet.{u}} (action : PosetActionCode G P m e r A)
include action

theorem raw_order_iff (group : GroupCode G m inv e) (order : PartialOrderCode P r)
    {g x y x' y' : ZFSet.{u}} (hg : g ∈ G)
    (xx' : ZFSet.pair (ZFSet.pair g x) x' ∈ A)
    (yy' : ZFSet.pair (ZFSet.pair g y) y' ∈ A) :
    ZFSet.pair x' y' ∈ r ↔ ZFSet.pair x y ∈ r := by
  have sx := ZFSet.pair_mem_prod.1 (action.function.1 xx')
  have sy := ZFSet.pair_mem_prod.1 (action.function.1 yy')
  have hx := (ZFSet.pair_mem_prod.1 sx.1).2
  have hy := (ZFSet.pair_mem_prod.1 sy.1).2
  let actor : SetMembers G := SetMembers.ofMem g hg
  let X : SetMembers P := SetMembers.ofMem x hx
  let Y : SetMembers P := SetMembers.ofMem y hy
  have eqX : action.act actor X = SetMembers.ofMem x' sx.2 := by
    apply (action.act_eq_iff actor X _).2
    simpa only [actor, X, SetMembers.raw_ofMem] using xx'
  have eqY : action.act actor Y = SetMembers.ofMem y' sy.2 := by
    apply (action.act_eq_iff actor Y _).2
    simpa only [actor, Y, SetMembers.raw_ofMem] using yy'
  have law := action.act_le_iff group order actor X Y
  rw [eqX, eqY] at law
  change (ZFSet.pair (SetMembers.raw (SetMembers.ofMem x' sx.2))
      (SetMembers.raw (SetMembers.ofMem y' sy.2)) ∈ r ↔
    ZFSet.pair (SetMembers.raw X) (SetMembers.raw Y) ∈ r) at law
  simpa only [X, Y, SetMembers.raw_ofMem] using law

theorem raw_preimage (group : GroupCode G m inv e) {g y : ZFSet.{u}}
    (hg : g ∈ G) (hy : y ∈ P) :
    ∃ x ∈ P, ZFSet.pair (ZFSet.pair g x) y ∈ A := by
  let := group.toGroup
  let actor : SetMembers G := SetMembers.ofMem g hg
  let Y : SetMembers P := SetMembers.ofMem y hy
  let X := action.act actor⁻¹ Y
  refine ⟨SetMembers.raw X, SetMembers.raw_mem X, ?_⟩
  simpa only [actor, Y, SetMembers.raw_ofMem] using
    (action.act_eq_iff actor X Y).1 (action.act_inv_right group actor Y)

theorem raw_map_meet {meetGraph : ZFSet.{u}}
    (group : GroupCode G m inv e) (meet : MeetOrderCode P r meetGraph)
    {g x y z x' y' z' : ZFSet.{u}} (hg : g ∈ G)
    (xyz : ZFSet.pair (ZFSet.pair x y) z ∈ meetGraph)
    (xx' : ZFSet.pair (ZFSet.pair g x) x' ∈ A)
    (yy' : ZFSet.pair (ZFSet.pair g y) y' ∈ A)
    (zz' : ZFSet.pair (ZFSet.pair g z) z' ∈ A) :
    ZFSet.pair (ZFSet.pair x' y') z' ∈ meetGraph := by
  have hx' := (ZFSet.pair_mem_prod.1 (action.function.1 xx')).2
  have hy' := (ZFSet.pair_mem_prod.1 (action.function.1 yy')).2
  have hz' := (ZFSet.pair_mem_prod.1 (action.function.1 zz')).2
  apply meet.pair_iff.2
  refine ⟨hx', hy', hz',
    (action.raw_order_iff group meet.order hg zz' xx').2 (meet.lower_left x y z xyz),
    (action.raw_order_iff group meet.order hg zz' yy').2 (meet.lower_right x y z xyz), ?_⟩
  intro w hw wx' wy'
  obtain ⟨v, hv, vw⟩ := action.raw_preimage group hg hw
  exact (action.raw_order_iff group meet.order hg vw zz').2
    (meet.greatest x y z v hv xyz
      ((action.raw_order_iff group meet.order hg vw xx').1 wx')
      ((action.raw_order_iff group meet.order hg vw yy').1 wy'))

end PosetActionCode

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

noncomputable def value (x : {x : ZFSet.{u} // x ∈ P}) :
    {y : ZFSet.{u} // y ∈ L} :=
  let graph : FunctionGraphOn P S := ⟨L, embedding.injection.function⟩
  ⟨graph.value x, (ZFSet.pair_mem_prod.1
    (embedding.injection.function.1 (graph.value_entry x))).2⟩

theorem value_entry (x : {x : ZFSet.{u} // x ∈ P}) :
    ZFSet.pair x.val (embedding.value x).val ∈ S :=
  (show FunctionGraphOn P S from ⟨L, embedding.injection.function⟩).value_entry x

noncomputable def toMeetEmbedding (source : MeetOrderCode P rP μP)
    (target : MeetOrderCode L rL μL) :
    MeetEmbedding source.toMeetOrder target.toMeetOrder where
  toFun := embedding.value
  le_iff x y := embedding.order_iff source target
    (embedding.value_entry x) (embedding.value_entry y)
  map_meet x y := by
    apply Subtype.ext
    exact (show FunctionGraphOn (ZFSet.prod L L) μL from
      ⟨L, target.operation⟩).unique
      (embedding.map_meet _ _ _ _ _ _ (source.toMeetOrder_meet_entry x y)
        (embedding.value_entry x) (embedding.value_entry y)
        (embedding.value_entry (source.toMeetOrder.meet x y)))
      (target.toMeetOrder_meet_entry (embedding.value x) (embedding.value y))

theorem toMeetEmbedding_entry (source : MeetOrderCode P rP μP)
    (target : MeetOrderCode L rL μL) (x : {x : ZFSet.{u} // x ∈ P}) :
    ZFSet.pair x.val ((embedding.toMeetEmbedding source target).toFun x).val ∈ S :=
  embedding.value_entry x

end MeetEmbeddingCode

namespace PosetActionCode

variable {G P m inv e r μ A : ZFSet.{u}}
variable (action : PosetActionCode G P m e r A)

noncomputable def rawAct (g : {g : ZFSet.{u} // g ∈ G})
    (x : {x : ZFSet.{u} // x ∈ P}) : {y : ZFSet.{u} // y ∈ P} :=
  let graph : FunctionGraphOn (ZFSet.prod G P) A := ⟨P, action.function⟩
  let input := (⟨ZFSet.pair g.val x.val,
    ZFSet.pair_mem_prod.2 ⟨g.property, x.property⟩⟩ :
      {z : ZFSet.{u} // z ∈ ZFSet.prod G P})
  ⟨graph.value input, (ZFSet.pair_mem_prod.1
    (action.function.1 (graph.value_entry input))).2⟩

theorem rawAct_entry (g : {g : ZFSet.{u} // g ∈ G})
    (x : {x : ZFSet.{u} // x ∈ P}) :
    ZFSet.pair (ZFSet.pair g.val x.val) (action.rawAct g x).val ∈ A :=
  (show FunctionGraphOn (ZFSet.prod G P) A from ⟨P, action.function⟩).value_entry
    ⟨ZFSet.pair g.val x.val, ZFSet.pair_mem_prod.2 ⟨g.property, x.property⟩⟩

theorem rawAct_eq_iff (g : {g : ZFSet.{u} // g ∈ G})
    (x y : {x : ZFSet.{u} // x ∈ P}) :
    action.rawAct g x = y ↔ ZFSet.pair (ZFSet.pair g.val x.val) y.val ∈ A := by
  constructor
  · intro equal
    exact equal ▸ action.rawAct_entry g x
  · intro entry
    exact Subtype.ext ((show FunctionGraphOn (ZFSet.prod G P) A from
      ⟨P, action.function⟩).unique (action.rawAct_entry g x) entry)

theorem rawAct_injective (group : GroupCode G m inv e) (order : PartialOrderCode P r)
    (g : {g : ZFSet.{u} // g ∈ G}) : Function.Injective (action.rawAct g) := by
  intro x y equal
  have lower : ZFSet.pair (action.rawAct g x).val (action.rawAct g y).val ∈ r := by
    rw [equal]
    exact order.refl _ (action.rawAct g y).property
  have back : ZFSet.pair (action.rawAct g y).val (action.rawAct g x).val ∈ r := by
    rw [equal]
    exact order.refl _ (action.rawAct g y).property
  exact Subtype.ext (order.antisymm x.val x.property y.val y.property
    ((action.raw_order_iff group order g.property
      (action.rawAct_entry g x) (action.rawAct_entry g y)).1 lower)
    ((action.raw_order_iff group order g.property
      (action.rawAct_entry g y) (action.rawAct_entry g x)).1 back))

theorem rawAct_surjective (group : GroupCode G m inv e)
    (g : {g : ZFSet.{u} // g ∈ G}) : Function.Surjective (action.rawAct g) := by
  intro y
  obtain ⟨x, hx, entry⟩ := action.raw_preimage group g.property y.property
  exact ⟨⟨x, hx⟩, (action.rawAct_eq_iff g ⟨x, hx⟩ y).2 entry⟩

noncomputable def toMeetIso (group : GroupCode G m inv e) (meet : MeetOrderCode P r μ)
    (g : {g : ZFSet.{u} // g ∈ G}) :
    Compression.MeetIso meet.toMeetOrder meet.toMeetOrder where
  toFun := action.rawAct g
  le_iff x y := action.raw_order_iff group meet.order g.property
    (action.rawAct_entry g x) (action.rawAct_entry g y)
  map_meet x y := by
    apply Subtype.ext
    exact (show FunctionGraphOn (ZFSet.prod P P) μ from ⟨P, meet.operation⟩).unique
      (action.raw_map_meet group meet g.property (meet.toMeetOrder_meet_entry x y)
        (action.rawAct_entry g x) (action.rawAct_entry g y)
        (action.rawAct_entry g (meet.toMeetOrder.meet x y)))
      (meet.toMeetOrder_meet_entry (action.rawAct g x) (action.rawAct g y))
  inverse y := Classical.choose (action.rawAct_surjective group g y)
  left_inverse x := action.rawAct_injective group meet.order g
    (Classical.choose_spec (action.rawAct_surjective group g (action.rawAct g x)))
  right_inverse y := Classical.choose_spec (action.rawAct_surjective group g y)

theorem toMeetIso_entry (group : GroupCode G m inv e) (meet : MeetOrderCode P r μ)
    (g : {g : ZFSet.{u} // g ∈ G}) (x : {x : ZFSet.{u} // x ∈ P}) :
    ZFSet.pair (ZFSet.pair g.val x.val)
      ((action.toMeetIso group meet g).toFun x).val ∈ A := action.rawAct_entry g x

end PosetActionCode

end PartitionPilot.Forcing

end

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Definability_GroundPowerImageGraphs
attribute [-instance] _root_.OAI.PartitionPilot.Forcing.GroundMainPrefix.withTopSmall
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PartitionPilot.Forcing
universe u

namespace InjectionCode

theorem relationImage_inj {A B f X Y : ZFSet.{u}} (injection : InjectionCode A B f)
    (hX : X ⊆ A) (hY : Y ⊆ A) :
    relationImage X B f = relationImage Y B f ↔ X = Y := by
  constructor
  · intro equal
    have forward {V W : ZFSet.{u}} (hV : V ⊆ A)
        (same : relationImage V B f = relationImage W B f) : V ⊆ W := by
      intro x hx
      obtain ⟨y, entry, _⟩ := injection.function.2 x (hV hx)
      have hy := (ZFSet.pair_mem_prod.1 (injection.function.1 entry)).2
      have image := (mem_relationImage V B f y).2 ⟨hy, x, hx, entry⟩
      rw [same] at image
      obtain ⟨_, z, hz, other⟩ := (mem_relationImage W B f y).1 image
      exact (injection.injective z x y other entry) ▸ hz
    exact ZFSet.ext (fun _ => ⟨fun hx => forward hX equal hx, fun hy => forward hY equal.symm hy⟩)
  · rintro rfl
    rfl

end InjectionCode

namespace BoundedFormula
open SetFormula

def imageSetFormula {n} (y x b f : Fin n) : BoundedFormula n :=
  .conj (.allMem y (.conj (.mem 0 b.succ) (imageMemberFormula 0 x.succ f.succ)))
    (.allMem b (imp (imageMemberFormula 0 x.succ f.succ) (.mem 0 y.succ)))

theorem truth_imageSetFormula {n} (y x b f : Fin n) (env : Fin n → ZFSet.{u}) :
    Truth (imageSetFormula y x b f) env ↔ env y = relationImage (env x) (env b) (env f) := by
  simp only [imageSetFormula, Truth, truth_imageMemberFormula, truth_imp]
  change ((∀ z ∈ env y, z ∈ env b ∧ ∃ w ∈ env x, ZFSet.pair w z ∈ env f) ∧
    ∀ z ∈ env b, (∃ w ∈ env x, ZFSet.pair w z ∈ env f) → z ∈ env y) ↔ _
  constructor
  · rintro ⟨forward, backward⟩
    apply ZFSet.ext
    intro z
    rw [mem_relationImage]
    exact ⟨forward z, fun hz => backward z hz.1 hz.2⟩
  · intro equal
    rw [equal]
    exact ⟨fun z hz => (mem_relationImage _ _ _ z).1 hz,
      fun z hz image => (mem_relationImage _ _ _ z).2 ⟨hz, image⟩⟩

def powerImageEntryFormula {n} (z pa pb b f : Fin n) : BoundedFormula n :=
  exMem pa (exMem pb.succ (.conj (orderedPairFormula z.succ.succ 1 0)
    (imageSetFormula 0 1 b.succ.succ f.succ.succ)))

theorem truth_powerImageEntryFormula {n} (z pa pb b f : Fin n) (env : Fin n → ZFSet.{u}) :
    Truth (powerImageEntryFormula z pa pb b f) env ↔
      ∃ X ∈ env pa, ∃ Y ∈ env pb, env z = ZFSet.pair X Y ∧
        Y = relationImage X (env b) (env f) := by
  simp only [powerImageEntryFormula, truth_exMem, Truth, truth_orderedPairFormula, truth_imageSetFormula]
  rfl

end BoundedFormula

namespace TransitiveGround
open SetFormula
variable (M : TransitiveGround.{u})

noncomputable def groundPowerImageGraph (A B f : ZFSet.{u}) : ZFSet.{u} :=
  ZFSet.sep (fun z => ∃ X ∈ M.groundPower A, ∃ Y ∈ M.groundPower B,
    z = ZFSet.pair X Y ∧ Y = relationImage X B f)
    (ZFSet.prod (M.groundPower A) (M.groundPower B))

theorem mem_groundPowerImageGraph (A B f z : ZFSet.{u}) :
    z ∈ M.groundPowerImageGraph A B f ↔
      ∃ X ∈ M.groundPower A, ∃ Y ∈ M.groundPower B,
        z = ZFSet.pair X Y ∧ Y = relationImage X B f := by
  rw [groundPowerImageGraph, ZFSet.mem_sep]
  constructor
  · exact And.right
  · rintro ⟨X, hX, Y, hY, rfl, equal⟩
    exact ⟨ZFSet.pair_mem_prod.2 ⟨hX, hY⟩, X, hX, Y, hY, rfl, equal⟩

theorem pair_mem_groundPowerImageGraph (A B f X Y : ZFSet.{u}) :
    ZFSet.pair X Y ∈ M.groundPowerImageGraph A B f ↔
      X ∈ M.groundPower A ∧ Y ∈ M.groundPower B ∧ Y = relationImage X B f := by
  rw [M.mem_groundPowerImageGraph]
  constructor
  · rintro ⟨V, hV, W, hW, equal, image⟩
    obtain ⟨rfl, rfl⟩ := ZFSet.pair_inj.1 equal
    exact ⟨hV, hW, image⟩
  · rintro ⟨hX, hY, image⟩
    exact ⟨X, hX, Y, hY, rfl, image⟩

theorem groundPowerImageGraph_mem
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    {A B f : ZFSet.{u}} (hA : A ∈ M.sets) (hB : B ∈ M.sets) (hf : f ∈ M.sets) :
    M.groundPowerImageGraph A B f ∈ M.sets := by
  have hPA := M.groundPower_mem powers hA
  have hPB := M.groundPower_mem powers hB
  let params := extend (M.groundPower A) (extend (M.groundPower B) (extend B (extend f Fin.elim0)))
  have selected := M.bounded_separation_mem separation (BoundedFormula.powerImageEntryFormula 0 1 2 3 4)
    params (Fin.cases hPA (Fin.cases hPB (Fin.cases hB (Fin.cases hf (fun i => Fin.elim0 i)))))
    (M.prod_mem pairing unions powers separation hPA hPB)
  have equal : ZFSet.sep (fun z => BoundedFormula.Truth (BoundedFormula.powerImageEntryFormula 0 1 2 3 4)
      (extend z params)) (ZFSet.prod (M.groundPower A) (M.groundPower B)) =
      M.groundPowerImageGraph A B f := by
    apply ZFSet.ext
    intro z
    rw [ZFSet.mem_sep, groundPowerImageGraph, ZFSet.mem_sep, BoundedFormula.truth_powerImageEntryFormula]
    rfl
  exact equal ▸ selected

theorem groundPowerImageGraph_entry_iff (separation : SeparationSchema M.sets)
    {A B f : ZFSet.{u}} (hB : B ∈ M.sets) (hf : f ∈ M.sets) (X Y : ZFSet.{u}) :
    ZFSet.pair X Y ∈ M.groundPowerImageGraph A B f ↔
      X ∈ M.groundPower A ∧ Y = relationImage X B f := by
  rw [M.pair_mem_groundPowerImageGraph]
  constructor
  · exact fun entry => ⟨entry.1, entry.2.2⟩
  · rintro ⟨hX, rfl⟩
    exact ⟨hX, (M.mem_groundPower B _).2
      ⟨M.relationImage_mem separation ((M.mem_groundPower A X).1 hX).1 hB hf,
        fun _ h => ((mem_relationImage _ _ _ _).1 h).1⟩, rfl⟩

theorem groundPowerImageGraph_function (separation : SeparationSchema M.sets)
    {A B f : ZFSet.{u}} (hB : B ∈ M.sets) (hf : f ∈ M.sets) :
    ZFSet.IsFunc (M.groundPower A) (M.groundPower B) (M.groundPowerImageGraph A B f) := by
  refine ⟨fun _ hz => (ZFSet.mem_sep.1 hz).1, ?_⟩
  intro X hX
  refine ⟨relationImage X B f, (M.groundPowerImageGraph_entry_iff separation hB hf _ _).2 ⟨hX, rfl⟩, ?_⟩
  intro Y entry
  exact ((M.groundPowerImageGraph_entry_iff separation hB hf _ _).1 entry).2

theorem groundPowerImageGraph_injection (separation : SeparationSchema M.sets)
    {A B f : ZFSet.{u}} (hB : B ∈ M.sets) (hf : f ∈ M.sets) (injection : InjectionCode A B f) :
    InjectionCode (M.groundPower A) (M.groundPower B) (M.groundPowerImageGraph A B f) := by
  refine ⟨M.groundPowerImageGraph_function separation hB hf, ?_⟩
  intro X Y Z first second
  obtain ⟨hX, _, imageX⟩ := (M.pair_mem_groundPowerImageGraph _ _ _ _ _).1 first
  obtain ⟨hY, _, imageY⟩ := (M.pair_mem_groundPowerImageGraph _ _ _ _ _).1 second
  exact (injection.relationImage_inj ((M.mem_groundPower _ _).1 hX).2
    ((M.mem_groundPower _ _).1 hY).2).1 (imageX.symm.trans imageY)

end TransitiveGround
end PartitionPilot.Forcing

end

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Transfinite_GroundStrongLimitPowers
attribute [-instance] _root_.OAI.PartitionPilot.Forcing.GroundMainPrefix.withTopSmall
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PartitionPilot.Forcing
universe u

def GroundStrongLimit (M : TransitiveGround.{u}) (K : ZFSet.{u}) : Prop :=
  ∀ α ∈ K, GroundBelow M (M.groundPower α) K

end PartitionPilot.Forcing



namespace PartitionPilot.Forcing
open SetFormula
universe u

namespace TransitiveGround
variable (M : TransitiveGround.{u})

theorem groundEmbeddable_power
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    {A B : ZFSet.{u}} (hA : A ∈ M.sets) (hB : B ∈ M.sets) (embedding : M.groundEmbeddable A B) :
    M.groundEmbeddable (M.groundPower A) (M.groundPower B) := by
  obtain ⟨f, hf, injection⟩ := embedding
  exact ⟨M.groundPowerImageGraph A B f,
    M.groundPowerImageGraph_mem pairing unions powers separation hA hB hf,
    M.groundPowerImageGraph_injection separation hB hf injection⟩

end TransitiveGround

namespace GroundStrongLimit
variable {M : TransitiveGround.{u}} {K : ZFSet.{u}} (strong : GroundStrongLimit M K)

include strong in
theorem power_closed
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    {A : ZFSet.{u}} (hA : A ∈ M.sets) (hK : K ∈ M.sets) (small : GroundBelow M A K) :
    GroundBelow M (M.groundPower A) K := by
  obtain ⟨α, hα, embedding⟩ := small
  have hAlpha := M.transitive hK hα
  exact (strong α hα).of_embeddable pairing unions powers separation
    (M.groundPower_mem powers hA) (M.groundPower_mem powers hAlpha) hK
    (M.groundEmbeddable_power pairing unions powers separation hA hAlpha embedding)

end GroundStrongLimit
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

def GroundRegular (M : TransitiveGround.{u}) (K : ZFSet.{u}) : Prop :=
  ∀ α ∈ K, ∀ f ∈ M.sets, ZFSet.IsFunc α K f →
    ∃ δ ∈ K, ∀ x y, ZFSet.pair x y ∈ f → y ∈ δ

namespace GroundRegular
variable {M : TransitiveGround.{u}} {K : ZFSet.{u}} (regular : GroundRegular M K)
variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
variable (unions : Realize M.sets SetFormula.union Fin.elim0)
variable (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
include regular pairing unions powers separation

theorem bound_small_domain {R f : ZFSet.{u}}
    (hR : R ∈ M.sets) (hK : K ∈ M.sets) (hf : f ∈ M.sets)
    (small : GroundBelow M R K) (function : ZFSet.IsFunc R K f) :
    ∃ δ ∈ K, ∀ x y, ZFSet.pair x y ∈ f → y ∈ δ := by
  classical
  obtain ⟨α, hα, small⟩ := small
  by_cases nonempty : R.Nonempty
  · obtain ⟨g, hg, enumeration, onto⟩ := M.groundEmbeddable_enumeration
      pairing unions powers separation hR (M.transitive hK hα) nonempty small
    have composite := M.relationCompose_mem pairing unions powers separation
      (M.transitive hK hα) hR hK hg hf
    have code := relationCompose_function_of_subset enumeration function (fun _ h => h)
    obtain ⟨δ, hδ, bounded⟩ := regular α hα (relationCompose α R K g f) composite code
    refine ⟨δ, hδ, ?_⟩
    intro x y entry
    obtain ⟨hx, hy⟩ := ZFSet.pair_mem_prod.1 (function.1 entry)
    obtain ⟨a, ha, ax⟩ := onto x hx
    exact bounded a y ((pair_mem_relationCompose α R K g f a y).2 ⟨ha, hy, x, hx, ax, entry⟩)
  · exact ⟨α, hα, fun x _ entry => False.elim
      (nonempty ⟨x, (ZFSet.pair_mem_prod.1 (function.1 entry)).1⟩)⟩

theorem bound_paired {R W F : ZFSet.{u}}
    (hR : R ∈ M.sets) (hK : K ∈ M.sets) (hW : W ∈ M.sets) (hF : F ∈ M.sets)
    (small : GroundBelow M R K) (family : ZFSet.IsFunc R (ZFSet.prod K W) F) :
    ∃ δ ∈ K, ∀ A β f, ZFSet.pair A (ZFSet.pair β f) ∈ F → β ∈ δ := by
  have ground := M.relationCompose_mem pairing unions powers separation hR
    (M.prod_mem pairing unions powers separation hK hW) hK hF
    (M.productFirst_mem pairing unions powers separation hK hW)
  have code := relationCompose_function_of_subset family (productFirst_function K W) (fun _ h => h)
  obtain ⟨δ, hδ, bounded⟩ := regular.bound_small_domain pairing unions powers separation hR hK ground small code
  refine ⟨δ, hδ, ?_⟩
  intro A β f entry
  obtain ⟨hA, hPair⟩ := ZFSet.pair_mem_prod.1 (family.1 entry)
  obtain ⟨hβ, hf⟩ := ZFSet.pair_mem_prod.1 hPair
  exact bounded A β ((pair_mem_relationCompose R (ZFSet.prod K W) K F (productFirst K W) A β).2
    ⟨hA, hβ, ZFSet.pair β f, hPair, entry, (mem_productFirst K W _).2 ⟨β, hβ, f, hf, rfl⟩⟩)

end GroundRegular

end

open SetFormula SetRealization
universe u

end PartitionPilot.Forcing

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Geometry_GroundCompressionStampBounds
attribute [-instance] _root_.OAI.PartitionPilot.Forcing.GroundMainPrefix.withTopSmall
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace PartitionPilot.Forcing
universe u

structure CompressionStampCode (base stamps limit : ZFSet.{u}) : Prop where
  function : ZFSet.IsFunc ZFSet.omega limit stamps
  entries : ∀ n y, ZFSet.pair (natSetCode n) y ∈ stamps ↔ y = compressionStamp base n
  union : NatUnionCode (compressionStamp base) limit
  ordinal : ordinalSetProperty limit

namespace CompressionStampCode
variable {base stamps limit : ZFSet.{u}} (code : CompressionStampCode base stamps limit)
include code

theorem stamp_mem_limit (n : Nat) : compressionStamp base n ∈ limit :=
  code.union.subset (n + 1) ((compressionStamp_mem_iff base n (n + 1)).2 (Nat.lt_succ_self n))

theorem stamp_ne_limit (n : Nat) : compressionStamp base n ≠ limit := by
  intro equal
  exact ZFSet.mem_irrefl limit (equal ▸ code.stamp_mem_limit n)

theorem base_mem_limit : base ∈ limit := code.union.subset 0 (compressionStamp_base_mem base 0)

end CompressionStampCode





namespace CompressionStampCode
variable {base stamps limit : ZFSet.{u}} (code : CompressionStampCode base stamps limit)
include code

theorem mem_limit_iff (s : ZFSet.{u}) :
    s ∈ limit ↔ s ∈ base ∨ s = base ∨ ∃ n, s = compressionStamp base n := by
  constructor
  · intro member
    obtain ⟨n, before⟩ := (code.union s).1 member
    rcases (mem_compressionStamp_iff base s n).1 before with old | same | ⟨m, _, equal⟩
    · exact Or.inl old
    · exact Or.inr (Or.inl same)
    · exact Or.inr (Or.inr ⟨m, equal⟩)
  · rintro (old | same | ⟨n, equal⟩)
    · exact code.union.subset 0 (compressionStamp_old_mem (Or.inl old) 0)
    · exact same ▸ code.base_mem_limit
    · exact equal ▸ code.stamp_mem_limit n

end CompressionStampCode

end PartitionPilot.Forcing



namespace PartitionPilot.Forcing
open scoped ZFSet
universe u

namespace FunctionGraphOn
variable {family : ZFSet.{u}}

noncomputable def natValue (function : FunctionGraphOn ZFSet.omega family) (n : Nat) : ZFSet.{u} :=
  function.value ⟨natSetCode n, natSetCode_mem_omega n⟩

theorem natValue_entry (function : FunctionGraphOn ZFSet.omega family) (n : Nat) :
    ZFSet.pair (natSetCode n) (function.natValue n) ∈ family :=
  function.value_entry ⟨natSetCode n, natSetCode_mem_omega n⟩

end FunctionGraphOn

end PartitionPilot.Forcing



end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Geometry_GroundBatchAttachment
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

theorem batchAttachment_ground_codes
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    {P rP μP I Qs rs μs As Es Fs Ss : ZFSet.{u}}
    (d : AttachmentBatchInputs P rP μP I Qs rs μs As Es Fs Ss)
    (hP : P ∈ M.sets) (hrP : rP ∈ M.sets) (hI : I ∈ M.sets)
    (hQs : Qs ∈ M.sets) (hrs : rs ∈ M.sets) (hμs : μs ∈ M.sets)
    (hAs : As ∈ M.sets) (hEs : Es ∈ M.sets) (hFs : Fs ∈ M.sets) :
    d.batchCarrier ∈ M.sets ∧ d.batchOrder ∈ M.sets ∧ d.batchMeetGraph ∈ M.sets ∧
      batchAttachmentShadowGraph I P Qs μs As Es ∈ M.sets ∧
      batchAttachmentTemplateGraph I P Qs rs As Es ∈ M.sets ∧
      attachmentOldEmbeddingGraph P ∈ M.sets := by
  have hN := M.indexedAttachmentFresh_mem pairing unions powers separation hI hQs hrs hAs
  have hL := M.taggedExtension_mem pairing unions powers separation hP hN
  have inside := M.batchAttachmentInsideGraph_mem pairing unions powers separation hI hQs hrs
  have shadow := M.batchAttachmentShadowGraph_mem pairing unions powers separation hI hP hQs hμs hAs hEs
  have upper := M.batchAttachmentUpperGraph_mem pairing unions powers separation hI hP hQs hFs
  have order := M.codedAttachmentOrder_mem pairing unions powers separation hP hN hrP inside shadow upper
  exact ⟨hL, order, M.canonicalMeetGraph_mem pairing unions powers separation hL order,
    shadow, M.batchAttachmentTemplateGraph_mem pairing unions powers separation hI hP hQs hrs hAs hEs,
    M.attachmentOldEmbeddingGraph_mem pairing unions powers separation hP⟩

end PartitionPilot.Forcing.TransitiveGround

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Forcing_SmallCodedMeetActions
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

namespace MeetOrderCode

variable {P r μ : ZFSet.{u}} (code : MeetOrderCode P r μ)

noncomputable def smallMeet (x y : SetMembers P) : SetMembers P :=
  ((SetMembers.presentation P).product (SetMembers.presentation P)).decodeFunction
    (SetMembers.presentation P) μ code.operation (x, y)

theorem smallMeet_entry (x y : SetMembers P) :
    ZFSet.pair (ZFSet.pair (SetMembers.raw x) (SetMembers.raw y))
      (SetMembers.raw (code.smallMeet x y)) ∈ μ :=
  ((SetMembers.presentation P).product (SetMembers.presentation P)).decodeFunction_mem
    (SetMembers.presentation P) μ code.operation (x, y)

theorem smallMeet_eq_iff (x y z : SetMembers P) :
    code.smallMeet x y = z ↔ ZFSet.pair (ZFSet.pair (SetMembers.raw x) (SetMembers.raw y))
      (SetMembers.raw z) ∈ μ :=
  ((SetMembers.presentation P).product (SetMembers.presentation P)).decodeFunction_iff
    (SetMembers.presentation P) μ code.operation (x, y) z

noncomputable def toSmallMeetOrder : MeetOrder (SetMembers P) where
  le x y := ZFSet.pair (SetMembers.raw x) (SetMembers.raw y) ∈ r
  meet := code.smallMeet
  refl x := code.order.refl _ (SetMembers.raw_mem x)
  trans {x y z} := code.order.trans _ (SetMembers.raw_mem x) _ (SetMembers.raw_mem y)
    _ (SetMembers.raw_mem z)
  antisymm {x y} xy yx := SetMembers.raw_injective P
    (code.order.antisymm _ (SetMembers.raw_mem x) _ (SetMembers.raw_mem y) xy yx)
  meet_le_left x y := code.lower_left _ _ _ (code.smallMeet_entry x y)
  meet_le_right x y := code.lower_right _ _ _ (code.smallMeet_entry x y)
  le_meet {x y z} := code.greatest _ _ _ _ (SetMembers.raw_mem x) (code.smallMeet_entry y z)

end MeetOrderCode

namespace PosetActionCode

variable {G P m inv one r μ A : ZFSet.{u}} (action : PosetActionCode G P m one r A)

noncomputable def toSmallMeetIso (group : GroupCode G m inv one) (meet : MeetOrderCode P r μ)
    (g : SetMembers G) : Compression.MeetIso meet.toSmallMeetOrder meet.toSmallMeetOrder := by
  letI := group.toGroup
  exact {
    toFun := action.act g
    le_iff := fun x y => action.raw_order_iff group meet.order (SetMembers.raw_mem g)
      (action.act_mem g x) (action.act_mem g y)
    map_meet := fun x y => by
      symm
      apply (meet.smallMeet_eq_iff _ _ _).2
      exact action.raw_map_meet group meet (SetMembers.raw_mem g) (meet.smallMeet_entry x y)
        (action.act_mem g x) (action.act_mem g y) (action.act_mem g (meet.smallMeet x y))
    inverse := action.act g⁻¹
    left_inverse := action.act_inv_left group g
    right_inverse := action.act_inv_right group g }

end PosetActionCode

end PartitionPilot.Forcing

end

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Geometry_GroundFinalInsertionExceptions
attribute [-instance] _root_.OAI.PartitionPilot.Forcing.GroundMainPrefix.withTopSmall
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI



namespace PartitionPilot.Forcing.FinalInsertionFamiliesCode
open SetRealization
universe u
variable {Labels P G r μ A c e d F caps actors : ZFSet.{u}}

noncomputable def decodedCaps
    (family : FinalInsertionFamiliesCode Labels P G r μ A c e d F caps actors) :
    SetMembers Labels → SetMembers P :=
  (SetMembers.presentation Labels).decodeFunction (SetMembers.presentation P)
    caps family.cap_injection.function

noncomputable def decodedActors
    (family : FinalInsertionFamiliesCode Labels P G r μ A c e d F caps actors) :
    SetMembers Labels → SetMembers G :=
  (SetMembers.presentation Labels).decodeFunction (SetMembers.presentation G)
    actors family.actor_injection.function

end PartitionPilot.Forcing.FinalInsertionFamiliesCode



end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Forcing_GroundPushFilters
attribute [-instance] _root_.OAI.PartitionPilot.Forcing.GroundMainPrefix.withTopSmall
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PartitionPilot.Forcing

universe u

namespace BoundedFormula

theorem truth_pushFilterMemberFormula {n} (y L r S F : Fin n) (env : Fin n → ZFSet.{u}) :
    Truth (pushFilterMemberFormula y L r S F) env ↔
      env y ∈ pushFilterCode (env L) (env r) (env S) (env F) := by
  simp only [pushFilterMemberFormula, Truth, truth_exMem,
    truth_pairMembershipFormula, mem_pushFilterCode]
  rfl

theorem truth_pushFilterFormula {n} (V L r S F : Fin n) (env : Fin n → ZFSet.{u}) :
    Truth (pushFilterFormula V L r S F) env ↔
      env V = pushFilterCode (env L) (env r) (env S) (env F) := by
  simp only [pushFilterFormula, Truth, truth_imp, truth_pushFilterMemberFormula]
  constructor
  · rintro ⟨sound, complete⟩
    apply ZFSet.ext
    intro y
    exact ⟨sound y, fun hy => complete y (pushFilterCode_subset _ _ _ _ hy) hy⟩
  · intro equal
    refine ⟨fun y hy => equal ▸ hy, ?_⟩
    intro y _ hy
    change y ∈ env V
    exact equal.symm ▸ hy

end BoundedFormula

namespace TransitiveGround

open SetFormula
variable (M : TransitiveGround.{u})

theorem pushFilterCode_mem (separation : SeparationSchema M.sets)
    {L r S F : ZFSet.{u}} (hL : L ∈ M.sets) (hr : r ∈ M.sets)
    (hS : S ∈ M.sets) (hF : F ∈ M.sets) : pushFilterCode L r S F ∈ M.sets := by
  let params := extend L (extend r (extend S (extend F Fin.elim0)))
  have selected := M.bounded_separation_mem separation
    (BoundedFormula.pushFilterMemberFormula 0 1 2 3 4) params
    (Fin.cases hL (Fin.cases hr (Fin.cases hS (Fin.cases hF (fun i => Fin.elim0 i))))) hL
  have equal : ZFSet.sep (fun y => BoundedFormula.Truth
      (BoundedFormula.pushFilterMemberFormula 0 1 2 3 4) (extend y params)) L =
      pushFilterCode L r S F := by
    apply ZFSet.ext
    intro y
    rw [ZFSet.mem_sep, BoundedFormula.truth_pushFilterMemberFormula]
    exact ⟨And.right, fun hy => ⟨pushFilterCode_subset L r S F hy, hy⟩⟩
  exact equal ▸ selected

end TransitiveGround

end PartitionPilot.Forcing

end

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

open scoped ZFSet

universe u

namespace BoundedFormula

def pairPushFilterEntryFormula {n} (z I J L r Ss Fs B SB FB : Fin n) : BoundedFormula n :=
  exMem I (exMem J.succ (exMem SB.succ.succ (exMem FB.succ.succ.succ
    (exMem B.succ.succ.succ.succ
      (.conj (orderedTripleFormula z.succ.succ.succ.succ.succ 4 3 0)
        (.conj (pairMembershipFormula 4 2 Ss.succ.succ.succ.succ.succ)
          (.conj (pairMembershipFormula 3 1 Fs.succ.succ.succ.succ.succ)
            (pushFilterFormula 0 L.succ.succ.succ.succ.succ r.succ.succ.succ.succ.succ 2 1))))))))

theorem truth_pairPushFilterEntryFormula {n} (z I J L r Ss Fs B SB FB : Fin n)
    (env : Fin n → ZFSet.{u}) :
    Truth (pairPushFilterEntryFormula z I J L r Ss Fs B SB FB) env ↔
      ∃ i ∈ env I, ∃ j ∈ env J, ∃ S ∈ env SB, ∃ F ∈ env FB, ∃ V ∈ env B,
        env z = ZFSet.pair (ZFSet.pair i j) V ∧ ZFSet.pair i S ∈ env Ss ∧
          ZFSet.pair j F ∈ env Fs ∧ V = pushFilterCode (env L) (env r) S F := by
  simp only [pairPushFilterEntryFormula, truth_exMem, Truth,
    truth_orderedTripleFormula, truth_pairMembershipFormula, truth_pushFilterFormula]
  rfl

end BoundedFormula

namespace TransitiveGround

open SetFormula
variable (M : TransitiveGround.{u})

theorem pairPushFilterFamily_mem
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    {K I J L rL Ss Fs B : ZFSet.{u}} (hK : K ∈ M.sets) (hI : I ∈ M.sets)
    (hJ : J ∈ M.sets) (hL : L ∈ M.sets) (hrL : rL ∈ M.sets)
    (hSs : Ss ∈ M.sets) (hFs : Fs ∈ M.sets) (hB : B ∈ M.sets) :
    pairPushFilterFamily K I J L rL Ss Fs B ∈ M.sets := by
  have hSB := M.union_mem unions (M.union_mem unions hSs)
  have hFB := M.union_mem unions (M.union_mem unions hFs)
  let params := extend I (extend J (extend L (extend rL (extend Ss (extend Fs
    (extend B (extend (⋃₀ ⋃₀ Ss) (extend (⋃₀ ⋃₀ Fs) Fin.elim0))))))))
  have selected := M.bounded_separation_mem separation
    (BoundedFormula.pairPushFilterEntryFormula 0 1 2 3 4 5 6 7 8 9) params
    (Fin.cases hI (Fin.cases hJ (Fin.cases hL (Fin.cases hrL (Fin.cases hSs
      (Fin.cases hFs (Fin.cases hB (Fin.cases hSB (Fin.cases hFB (fun i => Fin.elim0 i))))))))))
    (M.prod_mem pairing unions powers separation hK hB)
  have equal : ZFSet.sep (fun z => BoundedFormula.Truth
      (BoundedFormula.pairPushFilterEntryFormula 0 1 2 3 4 5 6 7 8 9) (extend z params))
      (ZFSet.prod K B) = pairPushFilterFamily K I J L rL Ss Fs B := by
    apply ZFSet.ext
    intro z
    rw [ZFSet.mem_sep, pairPushFilterFamily, ZFSet.mem_sep]
    exact and_congr Iff.rfl (BoundedFormula.truth_pairPushFilterEntryFormula 0 1 2 3 4 5 6 7 8 9 _)
  exact equal ▸ selected

noncomputable def groundPairPushFilters (K I J L rL Ss Fs : ZFSet.{u}) : ZFSet.{u} :=
  pairPushFilterFamily K I J L rL Ss Fs (M.groundPower L)

theorem groundPairPushFilters_spec
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    {K I J L rL Ss Fs : ZFSet.{u}} (hK : K ∈ M.sets) (hI : I ∈ M.sets)
    (hJ : J ∈ M.sets) (hL : L ∈ M.sets) (hrL : rL ∈ M.sets)
    (hSs : Ss ∈ M.sets) (hFs : Fs ∈ M.sets)
    (maps : FunctionGraphOn I Ss) (filters : FunctionGraphOn J Fs) (subset : K ⊆ ZFSet.prod I J) :
    M.groundPairPushFilters K I J L rL Ss Fs ∈ M.sets ∧
      ZFSet.IsFunc K (M.groundPower L) (M.groundPairPushFilters K I J L rL Ss Fs) ∧
      ∀ i j S F V, ZFSet.pair i S ∈ Ss → ZFSet.pair j F ∈ Fs →
        (ZFSet.pair (ZFSet.pair i j) V ∈ M.groundPairPushFilters K I J L rL Ss Fs ↔
          ZFSet.pair i j ∈ K ∧ V = pushFilterCode L rL S F) := by
  have bounded (i j S F : ZFSet.{u}) (mapEntry : ZFSet.pair i S ∈ Ss)
      (filterEntry : ZFSet.pair j F ∈ Fs) : pushFilterCode L rL S F ∈ M.groundPower L :=
    (M.mem_groundPower L _).2
      ⟨M.pushFilterCode_mem separation hL hrL
        (M.pair_right (M.transitive hSs mapEntry)) (M.pair_right (M.transitive hFs filterEntry)),
        pushFilterCode_subset L rL S F⟩
  refine ⟨M.pairPushFilterFamily_mem pairing unions powers separation hK hI hJ hL hrL hSs hFs
    (M.groundPower_mem powers hL),
    pairPushFilterFamily_function subset maps filters
      (fun i _ j _ S F mapEntry filterEntry => bounded i j S F mapEntry filterEntry), ?_⟩
  intro i j S F V mapEntry filterEntry
  rw [groundPairPushFilters, pairPushFilterFamily_entry_iff maps filters mapEntry filterEntry]
  constructor
  · exact fun h => ⟨h.1, h.2.2⟩
  · rintro ⟨hk, rfl⟩
    exact ⟨hk, bounded i j S F mapEntry filterEntry, rfl⟩

end TransitiveGround

end PartitionPilot.Forcing



end

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Definability_ExternalWordRewriteFormulas
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

def wordSingleton (a : ZFSet.{u}) : ZFSet.{u} := {ZFSet.pair (natSetCode 0) a}

def wordDouble (a b : ZFSet.{u}) : ZFSet.{u} :=
  {ZFSet.pair (natSetCode 0) a, ZFSet.pair (natSetCode 1) b}

def ExternalWordAtomicCode (G S m one l r : ZFSet.{u}) : Prop :=
  (one ∈ G ∧ l = wordSingleton (externalActorSymbol one) ∧ r = ∅) ∨
  (∃ g ∈ G, ∃ h ∈ G, ∃ k ∈ G, ZFSet.pair (ZFSet.pair g h) k ∈ m ∧
    l = wordDouble (externalActorSymbol g) (externalActorSymbol h) ∧
    r = wordSingleton (externalActorSymbol k)) ∨
  (∃ s ∈ S, (l = wordDouble (externalLetterSymbol s false) (externalLetterSymbol s true) ∨
    l = wordDouble (externalLetterSymbol s true) (externalLetterSymbol s false)) ∧ r = ∅)

def ExternalWordStepCode (W append G S m one f g : ZFSet.{u}) : Prop :=
  ∃ pre ∈ W, ∃ post ∈ W, ∃ l ∈ W, ∃ r ∈ W, ∃ pl ∈ W, ∃ pr ∈ W,
    ExternalWordAtomicCode G S m one l r ∧
    ZFSet.pair (ZFSet.pair pre l) pl ∈ append ∧
    ZFSet.pair (ZFSet.pair pre r) pr ∈ append ∧
    ((ZFSet.pair (ZFSet.pair pl post) f ∈ append ∧
        ZFSet.pair (ZFSet.pair pr post) g ∈ append) ∨
      (ZFSet.pair (ZFSet.pair pl post) g ∈ append ∧
        ZFSet.pair (ZFSet.pair pr post) f ∈ append))

theorem ExternalWordStepCode.symm {W append G S m one f g : ZFSet.{u}}
    (step : ExternalWordStepCode W append G S m one f g) :
    ExternalWordStepCode W append G S m one g f := by
  obtain ⟨pre, hp, post, hq, l, hl, r, hr, pl, hpl, pr, hpr, atomic, left, right, direction⟩ := step
  exact ⟨pre, hp, post, hq, l, hl, r, hr, pl, hpl, pr, hpr, atomic, left, right, direction.symm⟩

end PartitionPilot.Forcing



namespace PartitionPilot.Forcing.BoundedFormula
open SetFormula
universe u

def signedDoubleWordFormula {n} (w zero unit s a b : Fin n) : BoundedFormula n :=
  exMem w (exMem w.succ
    (.conj (nonemptyTupleFormula 3 1
      (Fin.cases zero.succ.succ (Fin.cases unit.succ.succ
        (Fin.cases s.succ.succ (Fin.cases a.succ.succ Fin.elim0)))))
      (.conj (nonemptyTupleFormula 3 0
        (Fin.cases unit.succ.succ (Fin.cases unit.succ.succ
          (Fin.cases s.succ.succ (Fin.cases b.succ.succ Fin.elim0)))))
        (unorderedPairFormula w.succ.succ 1 0))))

def externalWordAtomicFormula {n} (zero unit G S m one l r : Fin n) : BoundedFormula n :=
  disj (.conj (.mem one G) (.conj (actorSingletonWordFormula l zero one) (emptyFormula r)))
    (disj (exMem G (exMem G.succ (exMem G.succ.succ
      (.conj (tripleMembershipFormula 2 1 0 m.succ.succ.succ)
        (.conj (actorDoubleWordFormula l.succ.succ.succ zero.succ.succ.succ unit.succ.succ.succ 2 1)
          (actorSingletonWordFormula r.succ.succ.succ zero.succ.succ.succ 0))))))
      (exMem S (.conj
        (disj (signedDoubleWordFormula l.succ zero.succ unit.succ 0 zero.succ unit.succ)
          (signedDoubleWordFormula l.succ zero.succ unit.succ 0 unit.succ zero.succ)) (emptyFormula r.succ))))

def externalWordStepFormula {n} (W append zero unit G S m one f g : Fin n) : BoundedFormula n :=
  exMem W (exMem W.succ (exMem W.succ.succ (exMem W.succ.succ.succ
    (exMem W.succ.succ.succ.succ (exMem W.succ.succ.succ.succ.succ
      (.conj (externalWordAtomicFormula zero.succ.succ.succ.succ.succ.succ
        unit.succ.succ.succ.succ.succ.succ G.succ.succ.succ.succ.succ.succ
        S.succ.succ.succ.succ.succ.succ m.succ.succ.succ.succ.succ.succ
        one.succ.succ.succ.succ.succ.succ 3 2)
        (.conj (tripleMembershipFormula 5 3 1 append.succ.succ.succ.succ.succ.succ)
          (.conj (tripleMembershipFormula 5 2 0 append.succ.succ.succ.succ.succ.succ)
            (disj (.conj (tripleMembershipFormula 1 4 f.succ.succ.succ.succ.succ.succ append.succ.succ.succ.succ.succ.succ)
              (tripleMembershipFormula 0 4 g.succ.succ.succ.succ.succ.succ append.succ.succ.succ.succ.succ.succ))
              (.conj (tripleMembershipFormula 1 4 g.succ.succ.succ.succ.succ.succ append.succ.succ.succ.succ.succ.succ)
                (tripleMembershipFormula 0 4 f.succ.succ.succ.succ.succ.succ append.succ.succ.succ.succ.succ.succ)))))))))))

end PartitionPilot.Forcing.BoundedFormula

end

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Geometry_GroundExternalRewriteSteps
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

noncomputable def externalWordStepGraph (W append G S m one : ZFSet.{u}) : ZFSet.{u} :=
  ZFSet.sep (fun z => ∃ f ∈ W, ∃ g ∈ W, z = ZFSet.pair f g ∧
    ExternalWordStepCode W append G S m one f g) (ZFSet.prod W W)

namespace BoundedFormula

def externalWordStepEntryFormula {n} (z W append zero unit G S m one : Fin n) : BoundedFormula n :=
  exMem W (exMem W.succ (.conj (orderedPairFormula z.succ.succ 1 0)
    (externalWordStepFormula W.succ.succ append.succ.succ zero.succ.succ unit.succ.succ
      G.succ.succ S.succ.succ m.succ.succ one.succ.succ 1 0)))

end BoundedFormula

namespace TransitiveGround
variable (M : TransitiveGround.{u})

noncomputable def externalWordSteps (G S m one : ZFSet.{u}) : ZFSet.{u} :=
  externalWordStepGraph (M.finiteWords (externalGeneratorAlphabet G S))
    (M.finiteWordAppendGraph (externalGeneratorAlphabet G S)) G S m one

end TransitiveGround

end PartitionPilot.Forcing

end

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Geometry_GroundIndexedClassInclusions
attribute [-instance] _root_.OAI.PartitionPilot.Forcing.GroundMainPrefix.withTopSmall
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace PartitionPilot.Forcing

universe u

namespace BoundedFormula

open SetFormula

theorem truth_equivalenceClassFormula {n} (C A E y : Fin n)
    (env : Fin n → ZFSet.{u}) :
    Truth (equivalenceClassFormula C A E y) env ↔
      env C = equivalenceClass (env A) (env E) (env y) := by
  simp only [equivalenceClassFormula, Truth, truth_imp, truth_pairMembershipFormula]
  change ((∀ x ∈ env C, x ∈ env A) ∧ ∀ x ∈ env A,
    (x ∈ env C → ZFSet.pair x (env y) ∈ env E) ∧
    (ZFSet.pair x (env y) ∈ env E → x ∈ env C)) ↔ _
  constructor
  · rintro ⟨subset, complete⟩
    apply ZFSet.ext
    intro x
    rw [mem_equivalenceClass]
    exact ⟨fun hx => ⟨subset x hx, (complete x (subset x hx)).1 hx⟩,
      fun hx => (complete x hx.1).2 hx.2⟩
  · intro equal
    rw [equal]
    exact ⟨fun _ hx => (mem_equivalenceClass _ _ _ _).1 hx |>.1,
      fun x hx => ⟨fun h => (mem_equivalenceClass _ _ _ x).1 h |>.2,
        fun h => (mem_equivalenceClass _ _ _ x).2 ⟨hx, h⟩⟩⟩

theorem truth_equivalenceClassesFormula {n} (C A E : Fin n)
    (env : Fin n → ZFSet.{u}) :
    Truth (equivalenceClassesFormula C A E) env ↔
      env C ∈ equivalenceClasses (env A) (env E) := by
  simp only [equivalenceClassesFormula, truth_exMem, truth_equivalenceClassFormula,
    mem_equivalenceClasses]
  rfl

theorem truth_equivalenceClassifierEntryFormula {n} (z A E Q : Fin n)
    (env : Fin n → ZFSet.{u}) :
    Truth (equivalenceClassifierEntryFormula z A E Q) env ↔
      ∃ y ∈ env A, ∃ C ∈ env Q,
        env z = ZFSet.pair y C ∧ C = equivalenceClass (env A) (env E) y := by
  simp only [equivalenceClassifierEntryFormula, truth_exMem, Truth,
    truth_orderedPairFormula, truth_equivalenceClassFormula]
  rfl

end BoundedFormula

namespace TransitiveGround

open SetFormula
variable (M : TransitiveGround.{u})

theorem equivalenceClass_mem (separation : SeparationSchema M.sets)
    {A E y : ZFSet.{u}} (hA : A ∈ M.sets) (hE : E ∈ M.sets) (hy : y ∈ M.sets) :
    equivalenceClass A E y ∈ M.sets := by
  let params := extend y (extend E Fin.elim0)
  have selected := M.bounded_separation_mem separation
    (BoundedFormula.pairMembershipFormula 0 1 2) params
    (Fin.cases hy (Fin.cases hE (fun i => Fin.elim0 i))) hA
  have equal : ZFSet.sep (fun x => BoundedFormula.Truth
      (BoundedFormula.pairMembershipFormula 0 1 2) (extend x params)) A =
      equivalenceClass A E y := by
    apply ZFSet.ext
    intro x
    rw [ZFSet.mem_sep, mem_equivalenceClass]
    exact and_congr Iff.rfl (BoundedFormula.truth_pairMembershipFormula 0 1 2 _)
  exact equal ▸ selected

theorem equivalenceClasses_eq_sep_groundPower (separation : SeparationSchema M.sets)
    {A E : ZFSet.{u}} (hA : A ∈ M.sets) (hE : E ∈ M.sets) :
    equivalenceClasses A E = ZFSet.sep
      (fun C => ∃ y ∈ A, C = equivalenceClass A E y) (M.groundPower A) := by
  apply ZFSet.ext
  intro C
  rw [mem_equivalenceClasses, ZFSet.mem_sep, M.mem_groundPower]
  refine ⟨?_, And.right⟩
  rintro ⟨y, hy, rfl⟩
  exact ⟨⟨M.equivalenceClass_mem separation hA hE (M.transitive hA hy),
    equivalenceClass_subset A E y⟩, y, hy, rfl⟩

theorem equivalenceClasses_mem (powers : Realize M.sets powerSet Fin.elim0)
    (separation : SeparationSchema M.sets)
    {A E : ZFSet.{u}} (hA : A ∈ M.sets) (hE : E ∈ M.sets) :
    equivalenceClasses A E ∈ M.sets := by
  let params := extend A (extend E Fin.elim0)
  have selected := M.bounded_separation_mem separation
    (BoundedFormula.equivalenceClassesFormula 0 1 2) params
    (Fin.cases hA (Fin.cases hE (fun i => Fin.elim0 i))) (M.groundPower_mem powers hA)
  have equal : ZFSet.sep (fun C => BoundedFormula.Truth
      (BoundedFormula.equivalenceClassesFormula 0 1 2) (extend C params))
      (M.groundPower A) = equivalenceClasses A E := by
    rw [M.equivalenceClasses_eq_sep_groundPower separation hA hE]
    apply ZFSet.ext
    intro C
    rw [ZFSet.mem_sep, ZFSet.mem_sep]
    exact and_congr Iff.rfl
      ((BoundedFormula.truth_equivalenceClassesFormula 0 1 2 _).trans
        (mem_equivalenceClasses A E C))
  exact equal ▸ selected

end TransitiveGround

end PartitionPilot.Forcing



namespace PartitionPilot.Forcing
open SetFormula
universe u

noncomputable def indexedClassInclusion (U L E i : ZFSet.{u}) : ZFSet.{u} :=
  indexedRelationSection U (equivalenceClasses L E) (equivalenceClassifier L E) i

theorem pair_mem_indexedClassInclusion (U L E i x y : ZFSet.{u}) :
    ZFSet.pair x y ∈ indexedClassInclusion U L E i ↔
      x ∈ U ∧ ZFSet.pair i x ∈ L ∧ y = equivalenceClass L E (ZFSet.pair i x) := by
  rw [indexedClassInclusion, pair_mem_indexedRelationSection, pair_mem_equivalenceClassifier]
  constructor
  · rintro ⟨hu, _, label, equal⟩
    exact ⟨hu, label, equal⟩
  · rintro ⟨hu, label, rfl⟩
    exact ⟨hu, equivalenceClass_mem label, label, rfl⟩

theorem pair_mem_indexedClassInclusion_of_entry {T U A E i X x y : ZFSet.{u}}
    (family : FunctionGraphOn T A) (entry : ZFSet.pair i X ∈ A) (bound : X ⊆ U) :
    ZFSet.pair x y ∈ indexedClassInclusion U (indexedCarrierLabels T U A) E i ↔
      x ∈ X ∧ y = equivalenceClass (indexedCarrierLabels T U A) E (ZFSet.pair i x) := by
  rw [pair_mem_indexedClassInclusion, pair_mem_indexedCarrierLabels_of_entry family entry bound]
  exact ⟨fun h => h.2, fun h => ⟨bound h.1, h⟩⟩

theorem indexedClassInclusion_function {T U A E i X : ZFSet.{u}}
    (family : FunctionGraphOn T A) (entry : ZFSet.pair i X ∈ A) (bound : X ⊆ U) :
    ZFSet.IsFunc X (equivalenceClasses (indexedCarrierLabels T U A) E)
      (indexedClassInclusion U (indexedCarrierLabels T U A) E i) := by
  refine ⟨?_, ?_⟩
  · intro z hz
    obtain ⟨x, _, y, hy, rfl, _⟩ := (mem_indexedRelationSection _ _ _ _ z).1 hz
    exact ZFSet.pair_mem_prod.2
      ⟨((pair_mem_indexedClassInclusion_of_entry family entry bound).1 hz).1, hy⟩
  · intro x hx
    exact ⟨equivalenceClass (indexedCarrierLabels T U A) E (ZFSet.pair i x),
      (pair_mem_indexedClassInclusion_of_entry family entry bound).2 ⟨hx, rfl⟩,
      fun y hy => ((pair_mem_indexedClassInclusion_of_entry family entry bound).1 hy).2⟩

end PartitionPilot.Forcing

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
open SetRealization
universe u

def FiniteRelationPathCode (omega A R x y t : ZFSet.{u}) : Prop :=
  ∃ n ∈ omega, ∃ d ∈ omega, d = insert n n ∧
    IterationTraceCode n d A R x t ∧ ZFSet.pair n y ∈ t

theorem IterationTraceCode.reflTransGen {B : Type u} (s : Presentation B)
    (r : B → B → Prop) {R : ZFSet.{u}}
    (edges : ∀ x y, ZFSet.pair (s.encode x) (s.encode y) ∈ R ↔ r x y)
    {n : Nat} {t : ZFSet.{u}} {x : B}
    (trace : IterationTraceCode (natSetCode n) (natSetCode (n + 1)) s.carrier R
      (s.encode x) t) :
    ∀ k ≤ n, ∀ y, ZFSet.pair (natSetCode k) (s.encode y) ∈ t →
      Relation.ReflTransGen r x y := by
  intro k
  induction k with
  | zero =>
    intro _ y entry
    have same := (show FunctionGraphOn (natSetCode (n + 1)) t from
      ⟨s.carrier, trace.function⟩).unique trace.seed entry
    have equal : x = y := s.injective same
    subst y
    exact .refl
  | succ k ih =>
    intro hk y entry
    have domain := (natSetCode_mem_iff k (n + 1)).2 (by omega)
    obtain ⟨a, prev, _⟩ := trace.function.2 (natSetCode k) domain
    have ha := (ZFSet.pair_mem_prod.1 (trace.function.1 prev)).2
    obtain ⟨b, eq⟩ := (s.mem_carrier a).1 ha
    have previous : ZFSet.pair (natSetCode k) (s.encode b) ∈ t := eq.symm ▸ prev
    have step := trace.next (natSetCode k) ((natSetCode_mem_iff k n).2 (by omega))
      (natSetCode (k + 1)) ((natSetCode_mem_iff _ _).2 (by omega))
      _ (s.encode_mem b) _ (s.encode_mem y) rfl previous entry
    exact (ih (by omega) b previous).tail ((edges b y).1 step)

theorem FiniteRelationPathCode.reflTransGen {B : Type u} (s : Presentation B)
    (r : B → B → Prop) {R : ZFSet.{u}}
    (edges : ∀ x y, ZFSet.pair (s.encode x) (s.encode y) ∈ R ↔ r x y)
    {x y : B} {t : ZFSet.{u}}
    (path : FiniteRelationPathCode ZFSet.omega s.carrier R (s.encode x) (s.encode y) t) :
    Relation.ReflTransGen r x y := by
  obtain ⟨n, hn, d, _, succ, trace, out⟩ := path
  obtain ⟨n, rfl⟩ := (mem_omega_iff_natSetCode n).1 hn
  have dcode : d = natSetCode (n + 1) := succ
  exact (dcode ▸ trace).reflTransGen s r edges n (Nat.le_refl n) y out

end PartitionPilot.Forcing



namespace PartitionPilot.Forcing
open SetRealization SetFormula
universe u

namespace BoundedFormula

def finiteRelationPathFormula {k} (omega A R x y t zero : Fin k) : BoundedFormula k :=
  exMem omega (exMem omega.succ (.conj (successorFormula 0 1)
    (.conj (iterationTraceFormula 1 0 A.succ.succ R.succ.succ x.succ.succ
      t.succ.succ zero.succ.succ) (pairMembershipFormula 1 y.succ.succ t.succ.succ))))

theorem truth_finiteRelationPathFormula {k} (omega A R x y t zero : Fin k)
    (env : Fin k → ZFSet.{u}) (hzero : env zero = ∅) :
    Truth (finiteRelationPathFormula omega A R x y t zero) env ↔
      FiniteRelationPathCode (env omega) (env A) (env R) (env x) (env y) (env t) := by
  simp only [finiteRelationPathFormula, truth_exMem, Truth, truth_successorFormula,
    truth_pairMembershipFormula, FiniteRelationPathCode]
  apply exists_congr
  intro n
  apply and_congr_right
  intro _
  apply exists_congr
  intro d
  apply and_congr_right
  intro _
  exact and_congr Iff.rfl (and_congr
    (truth_iterationTraceFormula _ _ _ _ _ _ _ _ (by exact hzero)) Iff.rfl)

def finitePathClosureEntryFormula {k} (z A R omega paths zero : Fin k) : BoundedFormula k :=
  exMem A (exMem A.succ (exMem paths.succ.succ
    (.conj (orderedPairFormula z.succ.succ.succ 2 1)
      (finiteRelationPathFormula omega.succ.succ.succ A.succ.succ.succ
        R.succ.succ.succ 2 1 0 zero.succ.succ.succ))))

theorem truth_finitePathClosureEntryFormula {k} (z A R omega paths zero : Fin k)
    (env : Fin k → ZFSet.{u}) (hzero : env zero = ∅) :
    Truth (finitePathClosureEntryFormula z A R omega paths zero) env ↔
      ∃ x ∈ env A, ∃ y ∈ env A, ∃ t ∈ env paths,
        env z = ZFSet.pair x y ∧
          FiniteRelationPathCode (env omega) (env A) (env R) x y t := by
  simp only [finitePathClosureEntryFormula, truth_exMem, Truth, truth_orderedPairFormula]
  apply exists_congr
  intro x
  apply and_congr_right
  intro _
  apply exists_congr
  intro y
  apply and_congr_right
  intro _
  apply exists_congr
  intro t
  apply and_congr_right
  intro _
  exact and_congr Iff.rfl
    (truth_finiteRelationPathFormula _ _ _ _ _ _ _ _ (by exact hzero))

end BoundedFormula

namespace TransitiveGround
variable (M : TransitiveGround.{u})

noncomputable def finitePathClosure (A R : ZFSet.{u}) : ZFSet.{u} :=
  ZFSet.sep (fun z => ∃ x ∈ A, ∃ y ∈ A, ∃ t ∈ M.finiteWords A,
    z = ZFSet.pair x y ∧ FiniteRelationPathCode ZFSet.omega A R x y t) (ZFSet.prod A A)

end TransitiveGround

end PartitionPilot.Forcing



namespace PartitionPilot.Forcing
open SetRealization SetFormula
universe u

namespace BoundedFormula

theorem truth_shortestLengthEntryFormula {k} (z A omega lengths : Fin k) (env : Fin k → ZFSet.{u}) :
    Truth (shortestLengthEntryFormula z A omega lengths) env ↔
      ∃ y ∈ env A, ∃ n ∈ env omega, env z = ZFSet.pair y n ∧
        ZFSet.pair n y ∈ env lengths ∧ ∀ j ∈ n, ZFSet.pair j y ∉ env lengths := by
  simp only [shortestLengthEntryFormula, truth_exMem, Truth, truth_orderedPairFormula, truth_pairMembershipFormula]
  rfl
end BoundedFormula

end PartitionPilot.Forcing



end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Models_GroundExternalWordQuotient
attribute [-instance] _root_.OAI.PartitionPilot.Forcing.GroundMainPrefix.withTopSmall
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PartitionPilot.Forcing.ExternalWordRewrite

open PartitionPilot.Compression.RecursiveMaps.CosetGeometry
universe u
variable (J S : Type u) [Group J]

def symbolValue : Alphabet J S → External J S
  | .inl g => old J S g
  | .inr p => signed J S p

def evalWord : FreeMonoid (Alphabet J S) →* External J S := FreeMonoid.lift (symbolValue J S)

theorem atomic_eval {xs ys : List (Alphabet J S)} (h : Atomic xs ys) :
    evalWord J S xs = evalWord J S ys := by
  cases h with
  | old_one => exact (old J S).map_one
  | old_mul g h => exact ((old J S).map_mul g h).symm
  | cancel s b =>
    have cancel : FreeGroup.mk [(s, b), (s, !b)] = (1 : FreeGroup S) :=
      Quot.sound (@FreeGroup.Red.Step.not S [] [] s b)
    change signed J S (s, b) * (signed J S (s, !b) * 1) = 1
    rw [mul_one]
    change free J S (FreeGroup.mk [(s, b)]) * free J S (FreeGroup.mk [(s, !b)]) = 1
    rw [← map_mul, FreeGroup.mul_mk]
    change free J S (FreeGroup.mk [(s, b), (s, !b)]) = 1
    rw [cancel, map_one]

def evalQuotient : WordQuotient J S →* External J S :=
  (congruence J S).lift (evalWord J S)
    (Con.conGen_le.2 (fun _ _ h => atomic_eval J S h))

theorem evalQuotient_mk (xs : List (Alphabet J S)) :
    evalQuotient J S (quotientMap J S xs) = evalWord J S xs := rfl

def fromExternal : External J S →* WordQuotient J S :=
  Monoid.CoprodI.lift (fun b => match b with
    | false => oldClass J S
    | true => freeClass J S)

theorem fromExternal_old (g : J) :
    fromExternal J S (old J S g) = oldClass J S g := rfl

theorem fromExternal_free (x : FreeGroup S) :
    fromExternal J S (free J S x) = freeClass J S x := rfl

theorem fromExternal_evalWord (xs : List (Alphabet J S)) :
    fromExternal J S (evalWord J S xs) = quotientMap J S xs := by
  have hom : (fromExternal J S).comp (evalWord J S) = quotientMap J S := by
    apply FreeMonoid.hom_eq
    intro a
    change fromExternal J S (symbolValue J S a) = quotientMap J S [a]
    cases a with
    | inl g => exact fromExternal_old J S g
    | inr p => exact fromExternal_free J S (FreeGroup.mk [p])
  exact DFunLike.congr_fun hom xs

theorem evalWord_signed_word (xs : List (S × Bool)) :
    evalWord J S (xs.map Sum.inr) = free J S (FreeGroup.mk xs) := by
  induction xs with
  | nil => exact ((free J S).map_one).symm
  | cons p xs ih =>
    have step : evalWord J S ((p :: xs).map Sum.inr) =
        signed J S p * evalWord J S (xs.map Sum.inr) := by
      exact (evalWord J S).map_mul (FreeMonoid.of (.inr p))
        (FreeMonoid.ofList (xs.map Sum.inr))
    rw [step, ih]
    change free J S (FreeGroup.mk [p]) * free J S (FreeGroup.mk xs) =
      free J S (FreeGroup.mk (p :: xs))
    rw [← map_mul, FreeGroup.mul_mk]
    rfl

theorem evalQuotient_fromExternal (x : External J S) :
    evalQuotient J S (fromExternal J S x) = x := by
  induction x using Monoid.CoprodI.induction_on with
  | one => rw [map_one, map_one]
  | of b x =>
    cases b with
    | false =>
      change J at x
      change evalQuotient J S (fromExternal J S (old J S x)) = old J S x
      rw [fromExternal_old]
      change evalWord J S [.inl x] = old J S x
      rfl
    | true =>
      change FreeGroup S at x
      change evalQuotient J S (fromExternal J S (free J S x)) = free J S x
      rw [fromExternal_free]
      induction x using Quot.inductionOn with
      | h xs =>
        change evalQuotient J S (freeClass J S (FreeGroup.mk xs)) = free J S (FreeGroup.mk xs)
        rw [freeClass_mk, evalQuotient_mk]
        exact evalWord_signed_word J S xs
  | mul x y hx hy => simp only [map_mul, hx, hy]

theorem fromExternal_evalQuotient (x : WordQuotient J S) :
    fromExternal J S (evalQuotient J S x) = x := by
  refine Con.induction_on x ?_
  intro xs
  exact fromExternal_evalWord J S xs

def quotientEquiv : WordQuotient J S ≃* External J S where
  toFun := evalQuotient J S
  invFun := fromExternal J S
  left_inv := fromExternal_evalQuotient J S
  right_inv := evalQuotient_fromExternal J S
  map_mul' := (evalQuotient J S).map_mul

theorem evalWord_surjective : Function.Surjective (evalWord J S) := by
  intro x
  obtain ⟨xs, eq⟩ := (Con.mk'_surjective (c := congruence J S)) (fromExternal J S x)
  exact ⟨xs, (congrArg (evalQuotient J S) eq).trans (evalQuotient_fromExternal J S x)⟩

end PartitionPilot.Forcing.ExternalWordRewrite



namespace PartitionPilot.Forcing.TransitiveGround
open SetRealization SetFormula
universe u
variable (M : TransitiveGround.{u})

noncomputable def externalWordEquivalence (G S m one : ZFSet.{u}) : ZFSet.{u} :=
  M.finitePathClosure (M.finiteWords (externalGeneratorAlphabet G S)) (M.externalWordSteps G S m one)

end PartitionPilot.Forcing.TransitiveGround

end

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Models_GroundQuotientBinaryOperations
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

namespace BoundedFormula

def quotientBinaryEntryFormula {n} (z w q classifier op : Fin n) : BoundedFormula n :=
  exMem q (exMem q.succ (exMem q.succ.succ
    (.conj (orderedTripleFormula z.succ.succ.succ 2 1 0)
      (exMem w.succ.succ.succ (exMem w.succ.succ.succ.succ
        (exMem w.succ.succ.succ.succ.succ
          (.conj (pairMembershipFormula 2 5 classifier.succ.succ.succ.succ.succ.succ)
            (.conj (pairMembershipFormula 1 4 classifier.succ.succ.succ.succ.succ.succ)
              (.conj (pairMembershipFormula 0 3 classifier.succ.succ.succ.succ.succ.succ)
                (tripleMembershipFormula 2 1 0 op.succ.succ.succ.succ.succ.succ))))))))))

end BoundedFormula

end PartitionPilot.Forcing

end

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Definability_ExternalGroupOperationGraphs
attribute [-instance] _root_.OAI.PartitionPilot.Forcing.GroundMainPrefix.withTopSmall
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section



namespace PartitionPilot.Forcing.TransitiveGround
open SetRealization SetFormula
open Compression.RecursiveMaps.CosetGeometry
universe u
variable (M : TransitiveGround.{u})

noncomputable def externalGroupCarrier (G S m one : ZFSet.{u}) : ZFSet.{u} :=
  equivalenceClasses (M.finiteWords (externalGeneratorAlphabet G S))
    (M.externalWordEquivalence G S m one)

noncomputable def externalGroupProjection (G S m one : ZFSet.{u}) : ZFSet.{u} :=
  equivalenceClassifier (M.finiteWords (externalGeneratorAlphabet G S))
    (M.externalWordEquivalence G S m one)

noncomputable def externalGroupMultiplication (G S m one : ZFSet.{u}) : ZFSet.{u} :=
  quotientBinaryGraph (M.finiteWords (externalGeneratorAlphabet G S))
    (M.externalGroupCarrier G S m one) (M.externalGroupProjection G S m one)
    (M.finiteWordAppendGraph (externalGeneratorAlphabet G S))

noncomputable def externalGroupIdentity (G S m one : ZFSet.{u}) : ZFSet.{u} :=
  equivalenceClass (M.finiteWords (externalGeneratorAlphabet G S))
    (M.externalWordEquivalence G S m one) ∅

end PartitionPilot.Forcing.TransitiveGround

end

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Geometry_GroundExternalGenerators
attribute [-instance] _root_.OAI.PartitionPilot.Forcing.GroundMainPrefix.withTopSmall
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PartitionPilot.Forcing

open SetRealization SetFormula
universe u

noncomputable def externalActorSymbolGraph (G S : ZFSet.{u}) : ZFSet.{u} :=
  ZFSet.sep (fun z => ∃ g ∈ G, ∃ a ∈ externalGeneratorAlphabet G S,
    z = ZFSet.pair g a ∧ a = externalActorSymbol g)
    (ZFSet.prod G (externalGeneratorAlphabet G S))

noncomputable def externalGeneratorSymbolGraph (G S : ZFSet.{u}) : ZFSet.{u} :=
  ZFSet.sep (fun z => ∃ s ∈ S, ∃ a ∈ externalGeneratorAlphabet G S,
    z = ZFSet.pair s a ∧ a = externalLetterSymbol s true)
    (ZFSet.prod S (externalGeneratorAlphabet G S))

namespace BoundedFormula

def externalGeneratorSymbolEntryFormula {n} (z S alphabet one : Fin n) : BoundedFormula n :=
  exMem S (exMem alphabet.succ (.conj (orderedPairFormula z.succ.succ 1 0)
    (orderedRightTripleFormula 0 one.succ.succ 1 one.succ.succ)))

end BoundedFormula

end PartitionPilot.Forcing

section

namespace PartitionPilot.Forcing

open SetRealization SetFormula
universe u

noncomputable def singletonWordGraph (A W : ZFSet.{u}) : ZFSet.{u} :=
  ZFSet.sep (fun z => ∃ x ∈ A, ∃ w ∈ W, z = ZFSet.pair x w ∧ w = wordSingleton x)
    (ZFSet.prod A W)

end PartitionPilot.Forcing

end

namespace PartitionPilot.Forcing.TransitiveGround

open SetRealization SetFormula
open Compression.RecursiveMaps.CosetGeometry
universe u
variable (M : TransitiveGround.{u})

noncomputable def externalSymbolClasses (G S m one : ZFSet.{u}) : ZFSet.{u} :=
  let alphabet := externalGeneratorAlphabet G S
  let words := M.finiteWords alphabet
  relationCompose alphabet words (M.externalGroupCarrier G S m one)
    (singletonWordGraph alphabet words) (M.externalGroupProjection G S m one)

noncomputable def externalOldInclusion (G S m one : ZFSet.{u}) : ZFSet.{u} :=
  relationCompose G (externalGeneratorAlphabet G S) (M.externalGroupCarrier G S m one)
    (externalActorSymbolGraph G S) (M.externalSymbolClasses G S m one)

noncomputable def externalChildGenerators (G S m one : ZFSet.{u}) : ZFSet.{u} :=
  relationCompose S (externalGeneratorAlphabet G S) (M.externalGroupCarrier G S m one)
    (externalGeneratorSymbolGraph G S) (M.externalSymbolClasses G S m one)

end PartitionPilot.Forcing.TransitiveGround

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Transfinite_GroundCountableLayerCodes
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

namespace CountableLayerCode

def toLayer {M : TransitiveGround.{u}} {L r μ birth t D N injection : ZFSet.{u}}
    (code : CountableLayerCode L birth t D N injection)
    (Space sourceOrder sourceMeet : ZFSet.{u} → ZFSet.{u})
    (hD : D ∈ M.sets) (hInjection : injection ∈ M.sets) (omega : N = ZFSet.omega) :
    CodedGrowthLayer M Space sourceOrder sourceMeet L r μ birth t :=
  .countablePoints D hD ⟨injection, hInjection, omega ▸ code.small⟩ code.cover

end CountableLayerCode

end PartitionPilot.Forcing

end

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
open SetFormula
universe u

def CopyEmbeddingFamilyCode (Qs rs μs L r μ t I Indices Maps : ZFSet.{u}) : Prop :=
  ∀ i ∈ I, ∀ s ∈ t, ∀ e P R V,
    ZFSet.pair i s ∈ Indices → ZFSet.pair i e ∈ Maps →
    ZFSet.pair s P ∈ Qs → ZFSet.pair s R ∈ rs → ZFSet.pair s V ∈ μs →
    MeetEmbeddingCode P L R r V μ e

def CopyImageCoverCode (Qs L t I parts Indices Maps : ZFSet.{u}) : Prop :=
  ∀ i ∈ I, ∀ s ∈ t, ∀ e P, ∀ x ∈ L,
    ZFSet.pair i s ∈ Indices → ZFSet.pair i e ∈ Maps →
    ZFSet.pair s P ∈ Qs → ZFSet.pair i x ∈ parts → x ∈ relationImage P L e





structure CopyLayerCode
    (Qs rs μs L r μ birth t I parts Indices Maps W N injection : ZFSet.{u}) : Prop where
  small : InjectionCode I N injection
  indices : ZFSet.IsFunc I t Indices
  maps : ZFSet.IsFunc I W Maps
  embedding : CopyEmbeddingFamilyCode Qs rs μs L r μ t I Indices Maps
  cover : ∀ x ∈ L, ZFSet.pair x t ∈ birth → ∃ i ∈ I, ZFSet.pair i x ∈ parts
  inCopy : CopyImageCoverCode Qs L t I parts Indices Maps

namespace CopyLayerCode

noncomputable def toLayer
    {M : TransitiveGround.{u}} {Qs rs μs L r μ birth t I parts Indices Maps W N injection : ZFSet.{u}}
    (code : CopyLayerCode Qs rs μs L r μ birth t I parts Indices Maps W N injection)
    (Space sourceOrder sourceMeet : ZFSet.{u} → ZFSet.{u})
    (hI : I ∈ M.sets) (hParts : parts ∈ M.sets) (hMaps : Maps ∈ M.sets)
    (hInjection : injection ∈ M.sets) (omega : N = ZFSet.omega)
    (history : ∀ s ∈ t, ZFSet.pair s (Space s) ∈ Qs ∧
      ZFSet.pair s (sourceOrder s) ∈ rs ∧ ZFSet.pair s (sourceMeet s) ∈ μs) :
    CodedGrowthLayer M Space sourceOrder sourceMeet L r μ birth t := by
  classical
  let indexGraph : FunctionGraphOn I Indices := ⟨t, code.indices⟩
  let mapGraph : FunctionGraphOn I Maps := ⟨W, code.maps⟩
  let index (i : ZFSet.{u}) := if hi : i ∈ I then indexGraph.value ⟨i, hi⟩ else ∅
  let copy (i : ZFSet.{u}) := if hi : i ∈ I then mapGraph.value ⟨i, hi⟩ else ∅
  have indexEntry (i : ZFSet.{u}) (hi : i ∈ I) : ZFSet.pair i (index i) ∈ Indices := by
    simpa only [index, dite_eq_left hi] using indexGraph.value_entry ⟨i, hi⟩
  have copyEntry (i : ZFSet.{u}) (hi : i ∈ I) : ZFSet.pair i (copy i) ∈ Maps := by
    simpa only [copy, dite_eq_left hi] using mapGraph.value_entry ⟨i, hi⟩
  have earlier (i : ZFSet.{u}) (hi : i ∈ I) : index i ∈ t :=
    (ZFSet.pair_mem_prod.1 (code.indices.1 (indexEntry i hi))).2
  refine .copies I parts hI ⟨injection, hInjection, omega ▸ code.small⟩ hParts
    index copy earlier (fun i hi => M.pair_right (M.transitive hMaps (copyEntry i hi)))
    ?_ code.cover ?_
  · intro i hi
    have fields := history (index i) (earlier i hi)
    exact code.embedding i hi (index i) (earlier i hi) (copy i) (Space (index i))
      (sourceOrder (index i)) (sourceMeet (index i)) (indexEntry i hi) (copyEntry i hi)
      fields.1 fields.2.1 fields.2.2
  · intro i hi x hx part
    exact code.inCopy i hi (index i) (earlier i hi) (copy i) (Space (index i)) x hx
      (indexEntry i hi) (copyEntry i hi) (history (index i) (earlier i hi)).1 part

end CopyLayerCode

end PartitionPilot.Forcing



namespace PartitionPilot.Forcing
open SetRealization
universe u

def ComponentImageCoverCode (Qs L t I Components Indices Maps : ZFSet.{u}) : Prop :=
  ∀ i ∈ I, ∀ s ∈ t, ∀ e P, ∀ x ∈ L,
    ZFSet.pair i s ∈ Indices → ZFSet.pair i e ∈ Maps →
    ZFSet.pair s P ∈ Qs → ZFSet.pair x i ∈ Components → x ∈ relationImage P L e

def ComponentSeparationCode (L r μ birth t F I Components : ZFSet.{u}) : Prop :=
  ∀ x ∈ F, ∀ y ∈ F, ∀ i ∈ I, ∀ j ∈ I,
    ZFSet.pair x i ∈ Components → ZFSet.pair y j ∈ Components → i ≠ j →
      OldBridgeCode L r μ birth t x y

structure SeparatedLayerCode
    (Qs rs μs L r μ birth t I Indices Maps W Components F : ZFSet.{u}) : Prop where
  indices : ZFSet.IsFunc I t Indices
  maps : ZFSet.IsFunc I W Maps
  fiber : F = layerBirthFiber L birth t
  components : ZFSet.IsFunc F I Components
  embedding : CopyEmbeddingFamilyCode Qs rs μs L r μ t I Indices Maps
  cover : ComponentImageCoverCode Qs L t I Components Indices Maps
  separated : ComponentSeparationCode L r μ birth t F I Components

end PartitionPilot.Forcing



namespace PartitionPilot.Forcing.BoundedFormula
open SetFormula
universe u

def separatedLayerFormula {n}
    (Qs rs μs L r μ birth t I Indices Maps W Components F QB RB MB : Fin n) :
    BoundedFormula n :=
  .conj (functionFormula I t Indices)
    (.conj (functionFormula I W Maps)
      (.conj (layerBirthFiberFormula F L birth t)
        (.conj (functionFormula F I Components)
          (.conj (copyEmbeddingFamilyFormula Qs rs μs L r μ t I Indices Maps W QB RB MB)
            (.conj (componentImageCoverFormula Qs L t I Components Indices Maps W QB)
              (componentSeparationFormula L r μ birth t F I Components))))))

end PartitionPilot.Forcing.BoundedFormula



namespace PartitionPilot.Forcing
open SetFormula
universe u

noncomputable def countableLayerWitness (D injection : ZFSet.{u}) : ZFSet.{u} :=
  nonemptyTupleCode 2 (Fin.cases (natSetCode 0) (Fin.cases D (fun _ => injection)))

noncomputable def copyLayerWitness (I parts Indices Maps W injection : ZFSet.{u}) : ZFSet.{u} :=
  nonemptyTupleCode 6 (Fin.cases (natSetCode 1) (Fin.cases I (Fin.cases parts
    (Fin.cases Indices (Fin.cases Maps (Fin.cases W (fun _ => injection)))))))

def GrowthLayerWitnessCode (Qs rs μs L r μ birth t N z : ZFSet.{u}) : Prop :=
  (∃ D injection, z = countableLayerWitness D injection ∧ CountableLayerCode L birth t D N injection) ∨
  (∃ I parts Indices Maps W injection, z = copyLayerWitness I parts Indices Maps W injection ∧
    CopyLayerCode Qs rs μs L r μ birth t I parts Indices Maps W N injection) ∨
  (∃ I Indices Maps W Components F, z = separatedLayerWitness I Indices Maps W Components F ∧
    SeparatedLayerCode Qs rs μs L r μ birth t I Indices Maps W Components F)

end PartitionPilot.Forcing



namespace PartitionPilot.Forcing.BoundedFormula
open SetFormula
universe u

def separatedTaggedLayerFormula {n}
    (z tag I Indices Maps W Components F Qs rs μs L r μ birth t QB RB MB : Fin n) :
    BoundedFormula n :=
  .conj (growthTagFormula 2 tag)
    (.conj (nonemptyTupleFormula 6 z (Fin.cases tag (Fin.cases I (Fin.cases Indices
      (Fin.cases Maps (Fin.cases W (Fin.cases Components (fun _ => F))))))))
      (.conj (doubleUnionEquationFormula QB Qs)
        (.conj (doubleUnionEquationFormula RB rs)
          (.conj (doubleUnionEquationFormula MB μs)
            (separatedLayerFormula Qs rs μs L r μ birth t I Indices Maps W Components F QB RB MB)))))

end PartitionPilot.Forcing.BoundedFormula

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

@[instance_reducible]
noncomputable def ordinalMainIndexPreorder {T : ZFSet.{u}} (ordinal : ordinalSetProperty T) :
    Preorder (SetMembers T) where
  le i j := SetMembers.raw i = SetMembers.raw j ∨ SetMembers.raw i ∈ SetMembers.raw j
  le_refl _ := Or.inl rfl
  le_trans i j k first second := by
    rcases first with equal | earlier
    · exact equal.symm ▸ second
    · rcases second with equal | later
      · exact Or.inr (equal ▸ earlier)
      · exact Or.inr (ordinal.2 (SetMembers.raw k) (SetMembers.raw_mem k)
          (SetMembers.raw j) later (SetMembers.raw i) earlier)

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

section

universe u

theorem familyEvaluationGraph_entry_iff {K P L V Ss Es k S e y : ZFSet.{u}}
    (functions : ZFSet.IsFunc K V Ss) (arguments : ZFSet.IsFunc K P Es)
    (ks : ZFSet.pair k S ∈ Ss) (ke : ZFSet.pair k e ∈ Es) :
    ZFSet.pair k y ∈ familyEvaluationGraph K P L V Ss Es ↔
      y ∈ L ∧ ZFSet.pair e y ∈ S := by
  rw [pair_mem_familyEvaluationGraph]
  constructor
  · rintro ⟨_, hy, S', _, e', _, ks', ke', entry⟩
    have eqS := (show FunctionGraphOn K Ss from ⟨V, functions⟩).unique ks' ks
    have eqE := (show FunctionGraphOn K Es from ⟨P, arguments⟩).unique ke' ke
    exact ⟨hy, eqE ▸ eqS ▸ entry⟩
  · rintro ⟨hy, entry⟩
    have hs := ZFSet.pair_mem_prod.1 (functions.1 ks)
    have he := ZFSet.pair_mem_prod.1 (arguments.1 ke)
    exact ⟨hs.1, hy, S, hs.2, e, he.2, ks, ke, entry⟩

theorem familyEvaluationGraph_function {K P L V Ss Es : ZFSet.{u}}
    (functions : ZFSet.IsFunc K V Ss) (arguments : ZFSet.IsFunc K P Es)
    (valid : ∀ k S, ZFSet.pair k S ∈ Ss → ZFSet.IsFunc P L S) :
    ZFSet.IsFunc K L (familyEvaluationGraph K P L V Ss Es) := by
  refine ⟨fun _ hz => (ZFSet.mem_sep.1 hz).1, ?_⟩
  intro k hk
  obtain ⟨S, ks, _⟩ := functions.2 k hk
  obtain ⟨e, ke, _⟩ := arguments.2 k hk
  have function := valid k S ks
  obtain ⟨y, ey, unique⟩ := function.2 e (ZFSet.pair_mem_prod.1 (arguments.1 ke)).2
  refine ⟨y, (familyEvaluationGraph_entry_iff functions arguments ks ke).2
    ⟨(ZFSet.pair_mem_prod.1 (function.1 ey)).2, ey⟩, ?_⟩
  intro z hz
  exact unique z ((familyEvaluationGraph_entry_iff functions arguments ks ke).1 hz).2

namespace BoundedFormula

open SetFormula

theorem truth_familyEvaluationEntryFormula {n} (z k p l v ss es : Fin n)
    (env : Fin n → ZFSet.{u}) :
    Truth (familyEvaluationEntryFormula z k p l v ss es) env ↔
      ∃ i ∈ env k, ∃ S ∈ env v, ∃ e ∈ env p, ∃ y ∈ env l,
        env z = ZFSet.pair i y ∧ ZFSet.pair i S ∈ env ss ∧
          ZFSet.pair i e ∈ env es ∧ ZFSet.pair e y ∈ S := by
  simp only [familyEvaluationEntryFormula, truth_exMem, Truth,
    truth_orderedPairFormula, truth_pairMembershipFormula]
  rfl

end BoundedFormula

namespace TransitiveGround

open SetFormula
variable (M : TransitiveGround.{u})

theorem familyEvaluationGraph_mem
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    {K P L V Ss Es : ZFSet.{u}} (hK : K ∈ M.sets) (hP : P ∈ M.sets)
    (hL : L ∈ M.sets) (hV : V ∈ M.sets) (hSs : Ss ∈ M.sets) (hEs : Es ∈ M.sets) :
    familyEvaluationGraph K P L V Ss Es ∈ M.sets := by
  let params := extend K (extend P (extend L (extend V (extend Ss (extend Es Fin.elim0)))))
  have selected := M.bounded_separation_mem separation
    (BoundedFormula.familyEvaluationEntryFormula 0 1 2 3 4 5 6) params
    (Fin.cases hK (Fin.cases hP (Fin.cases hL (Fin.cases hV (Fin.cases hSs
      (Fin.cases hEs (fun i => Fin.elim0 i)))))))
    (M.prod_mem pairing unions powers separation hK hL)
  have equal : ZFSet.sep (fun z => BoundedFormula.Truth
      (BoundedFormula.familyEvaluationEntryFormula 0 1 2 3 4 5 6) (extend z params))
      (ZFSet.prod K L) = familyEvaluationGraph K P L V Ss Es := by
    apply ZFSet.ext
    intro z
    rw [ZFSet.mem_sep, familyEvaluationGraph, ZFSet.mem_sep]
    exact and_congr Iff.rfl (BoundedFormula.truth_familyEvaluationEntryFormula 0 1 2 3 4 5 6 _)
  exact equal ▸ selected

end TransitiveGround

end

open SetFormula
universe u v

end PartitionPilot.Forcing

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Geometry_LiftedCompressionFunctions
attribute [-instance] _root_.OAI.PartitionPilot.Forcing.GroundMainPrefix.withTopSmall
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PartitionPilot.Forcing

universe u

theorem liftFreshEntry_not_old {D L J B N Sources Fs Reps G A i x y : ZFSet.{u}}
    (entry : liftFreshEntry D L J B N Sources Fs Reps G A i x y) : x ∉ D := by
  obtain ⟨j, _, q, _, _, _, _, _, eq, _⟩ := entry
  rw [eq]
  exact pair_tag_not_mem D (ZFSet.pair j q)

theorem liftOldEntry_iff {I D Maps i S x y : ZFSet.{u}}
    (maps : FunctionGraphOn I Maps) (entry : ZFSet.pair i S ∈ Maps) (hx : x ∈ D) :
    liftOldEntry D Maps i x y ↔ ZFSet.pair x y ∈ S := by
  constructor
  · rintro ⟨_, T, _, iT, xy⟩
    exact maps.unique iT entry ▸ xy
  · intro xy
    exact ⟨hx, S, pair_second_mem_doubleUnion entry, entry, xy⟩

theorem liftedCompressionGraph_old_iff {I J D L C N B Maps Sources Fs Reps G A i S x y : ZFSet.{u}}
    (maps : FunctionGraphOn I Maps) (entry : ZFSet.pair i S ∈ Maps) (hx : x ∈ D) :
    ZFSet.pair (ZFSet.pair i x) y ∈ liftedCompressionGraph I J D L C N B Maps Sources Fs Reps G A ↔
      x ∈ L ∧ y ∈ C ∧ ZFSet.pair x y ∈ S := by
  rw [pair_mem_liftedCompressionGraph]
  constructor
  · rintro ⟨_, hxL, hy, old | fresh⟩
    · exact ⟨hxL, hy, (liftOldEntry_iff maps entry hx).1 old⟩
    · exact False.elim (liftFreshEntry_not_old fresh hx)
  · rintro ⟨hxL, hy, xy⟩
    exact ⟨maps.pair_source entry, hxL, hy, Or.inl ((liftOldEntry_iff maps entry hx).2 xy)⟩

theorem liftFreshEntry_iff {I D L J B N Sources Fs Reps G A i j q a F y : ZFSet.{u}}
    (sources : FunctionGraphOn I Sources) (filters : FunctionGraphOn J Fs)
    (source : ZFSet.pair i a ∈ Sources) (filter : ZFSet.pair j F ∈ Fs)
    (hj : j ∈ J) (hq : q ∈ B) (ha : a ∈ D) (fresh : ZFSet.pair j q ∈ N) :
    liftFreshEntry D L J B N Sources Fs Reps G A i (ZFSet.pair D (ZFSet.pair j q)) y ↔
      ((a ∈ F ∧ ∃ g ∈ G, ZFSet.pair i g ∈ Reps ∧
        ZFSet.pair (ZFSet.pair g (ZFSet.pair D (ZFSet.pair j q))) y ∈ A) ∨
      (a ∉ F ∧ y = ZFSet.pair L (ZFSet.pair (ZFSet.pair i j) q))) := by
  constructor
  · rintro ⟨j', _, q', _, a', _, F', _, eq, _, source', filter', output⟩
    have jq := ZFSet.pair_inj.1 (ZFSet.pair_inj.1 eq).2
    obtain ⟨rfl, rfl⟩ := jq
    have aEq := sources.unique source' source
    have FEq := filters.unique filter' filter
    exact aEq ▸ FEq ▸ output
  · intro output
    exact ⟨j, hj, q, hq, a, ha, F, pair_second_mem_doubleUnion filter,
      rfl, fresh, source, filter, output⟩

theorem liftedCompressionGraph_fresh_iff
    {I J D L C N B Maps Sources Fs Reps G A i j q a F y : ZFSet.{u}}
    (sources : FunctionGraphOn I Sources) (filters : FunctionGraphOn J Fs)
    (source : ZFSet.pair i a ∈ Sources) (filter : ZFSet.pair j F ∈ Fs)
    (hj : j ∈ J) (hq : q ∈ B) (ha : a ∈ D) (fresh : ZFSet.pair j q ∈ N) :
    ZFSet.pair (ZFSet.pair i (ZFSet.pair D (ZFSet.pair j q))) y ∈
      liftedCompressionGraph I J D L C N B Maps Sources Fs Reps G A ↔
      ZFSet.pair D (ZFSet.pair j q) ∈ L ∧ y ∈ C ∧
      ((a ∈ F ∧ ∃ g ∈ G, ZFSet.pair i g ∈ Reps ∧
        ZFSet.pair (ZFSet.pair g (ZFSet.pair D (ZFSet.pair j q))) y ∈ A) ∨
      (a ∉ F ∧ y = ZFSet.pair L (ZFSet.pair (ZFSet.pair i j) q))) := by
  rw [pair_mem_liftedCompressionGraph]
  constructor
  · rintro ⟨_, hx, hy, old | entry⟩
    · exact False.elim (pair_tag_not_mem D (ZFSet.pair j q) old.1)
    · exact ⟨hx, hy, (liftFreshEntry_iff sources filters source filter hj hq ha fresh).1 entry⟩
  · rintro ⟨hx, hy, output⟩
    exact ⟨sources.pair_source source, hx, hy,
      Or.inr ((liftFreshEntry_iff sources filters source filter hj hq ha fresh).2 output)⟩

theorem liftedCompressionGraph_function
    {I J D L C N B Maps Sources Fs Reps G A : ZFSet.{u}}
    (current : L = taggedExtension D N) (freshShape : N ⊆ ZFSet.prod J B)
    (extension : L ⊆ C) (maps : FunctionGraphOn I Maps)
    (valid : ∀ i S, ZFSet.pair i S ∈ Maps → ZFSet.IsFunc D L S)
    (sources : ZFSet.IsFunc I D Sources) (filters : FunctionGraphOn J Fs)
    (reps : ZFSet.IsFunc I G Reps) (action : ZFSet.IsFunc (ZFSet.prod G L) L A)
    (negativeTargets : ∀ i ∈ I, ∀ j ∈ J, ∀ q ∈ B, ∀ a F,
      ZFSet.pair j q ∈ N → ZFSet.pair i a ∈ Sources → ZFSet.pair j F ∈ Fs →
        a ∉ F → ZFSet.pair L (ZFSet.pair (ZFSet.pair i j) q) ∈ C) :
    ZFSet.IsFunc (ZFSet.prod I L) C
      (liftedCompressionGraph I J D L C N B Maps Sources Fs Reps G A) := by
  classical
  refine ⟨fun _ hz => (ZFSet.mem_sep.1 hz).1, ?_⟩
  intro p hp
  obtain ⟨i, hi, x, hxL, rfl⟩ := ZFSet.mem_prod.1 hp
  rcases mem_taggedExtension.1 (current ▸ hxL) with old | ⟨n, hn, rfl⟩
  · obtain ⟨S, mapEntry⟩ := maps.total hi
    obtain ⟨y, entry, unique⟩ := (valid i S mapEntry).2 x old
    have hy := (ZFSet.pair_mem_prod.1 ((valid i S mapEntry).1 entry)).2
    refine ⟨y, (liftedCompressionGraph_old_iff maps mapEntry old).2 ⟨hxL, extension hy, entry⟩, ?_⟩
    intro z hz
    exact unique z ((liftedCompressionGraph_old_iff maps mapEntry old).1 hz).2.2
  · obtain ⟨j, hj, q, hq, rfl⟩ := ZFSet.mem_prod.1 (freshShape hn)
    obtain ⟨a, source, _⟩ := sources.2 i hi
    have ha := (ZFSet.pair_mem_prod.1 (sources.1 source)).2
    obtain ⟨F, filter⟩ := filters.total hj
    have sourceFunc : FunctionGraphOn I Sources := ⟨D, sources⟩
    by_cases positive : a ∈ F
    · obtain ⟨g, representative, _⟩ := reps.2 i hi
      have hg := (ZFSet.pair_mem_prod.1 (reps.1 representative)).2
      obtain ⟨y, entry, unique⟩ := action.2
        (ZFSet.pair g (ZFSet.pair D (ZFSet.pair j q))) (ZFSet.pair_mem_prod.2 ⟨hg, hxL⟩)
      have hy := (ZFSet.pair_mem_prod.1 (action.1 entry)).2
      refine ⟨y, (liftedCompressionGraph_fresh_iff sourceFunc filters source filter hj hq ha hn).2
        ⟨hxL, extension hy, Or.inl ⟨positive, g, hg, representative, entry⟩⟩, ?_⟩
      intro z hz
      rcases ((liftedCompressionGraph_fresh_iff sourceFunc filters source filter hj hq ha hn).1 hz).2.2
          with ⟨_, g', _, representative', entry'⟩ | ⟨negative, _⟩
      · have equal : g' = g := (show FunctionGraphOn I Reps from ⟨G, reps⟩).unique representative' representative
        exact unique z (equal ▸ entry')
      · exact False.elim (negative positive)
    · let y := ZFSet.pair L (ZFSet.pair (ZFSet.pair i j) q)
      have hy : y ∈ C := negativeTargets i hi j hj q hq a F hn source filter positive
      refine ⟨y, (liftedCompressionGraph_fresh_iff sourceFunc filters source filter hj hq ha hn).2
        ⟨hxL, hy, Or.inr ⟨positive, rfl⟩⟩, ?_⟩
      intro z hz
      rcases ((liftedCompressionGraph_fresh_iff sourceFunc filters source filter hj hq ha hn).1 hz).2.2
          with ⟨positive', _⟩ | ⟨_, equal⟩
      · exact False.elim (positive positive')
      · exact equal

theorem indexedRelationSection_function {I L C R i : ZFSet.{u}}
    (function : ZFSet.IsFunc (ZFSet.prod I L) C R) (hi : i ∈ I) :
    ZFSet.IsFunc L C (indexedRelationSection L C R i) := by
  refine ⟨indexedRelationSection_subset L C R i, ?_⟩
  intro x hx
  obtain ⟨y, entry, unique⟩ := function.2 (ZFSet.pair i x) (ZFSet.pair_mem_prod.2 ⟨hi, hx⟩)
  have hy := (ZFSet.pair_mem_prod.1 (function.1 entry)).2
  refine ⟨y, (pair_mem_indexedRelationSection L C R i x y).2 ⟨hx, hy, entry⟩, ?_⟩
  intro z hz
  exact unique z ((pair_mem_indexedRelationSection L C R i x z).1 hz).2.2

end PartitionPilot.Forcing

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Transfinite_RecursiveLiftAgreement
attribute [-instance] _root_.OAI.PartitionPilot.Forcing.GroundMainPrefix.withTopSmall
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace PartitionPilot.Forcing

universe u






namespace BoundedFormula

open SetFormula

theorem truth_recursiveAttachmentIndexFormula {n} (k i j p u a f : Fin n)
    (env : Fin n → ZFSet.{u}) :
    Truth (recursiveAttachmentIndexFormula k i j p u a f) env ↔
      ∃ x ∈ env i, ∃ y ∈ env j, ∃ b ∈ env p, ∃ F ∈ env u,
        env k = ZFSet.pair x y ∧ ZFSet.pair x b ∈ env a ∧
          ZFSet.pair y F ∈ env f ∧ b ∉ F := by
  simp only [recursiveAttachmentIndexFormula, truth_exMem, Truth,
    truth_orderedPairFormula, truth_pairMembershipFormula]
  rfl

theorem truth_pairFieldEntryFormula {n} (left : Bool) (z k i j b h : Fin n)
    (env : Fin n → ZFSet.{u}) :
    Truth (pairFieldEntryFormula left z k i j b h) env ↔
      ∃ t ∈ env k, ∃ x ∈ env i, ∃ y ∈ env j, ∃ v ∈ env b,
        env z = ZFSet.pair t v ∧ t = ZFSet.pair x y ∧
          ZFSet.pair (if left then x else y) v ∈ env h := by
  cases left <;>
    simp only [pairFieldEntryFormula, truth_exMem, Truth,
      truth_orderedPairFormula, truth_pairMembershipFormula, Bool.false_eq_true, ↓reduceIte] <;> rfl

end BoundedFormula

namespace TransitiveGround

open SetFormula
variable (M : TransitiveGround.{u})

theorem recursiveAttachmentIndices_mem
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    {I J P U As Fs : ZFSet.{u}} (hI : I ∈ M.sets) (hJ : J ∈ M.sets)
    (hP : P ∈ M.sets) (hU : U ∈ M.sets) (hAs : As ∈ M.sets) (hFs : Fs ∈ M.sets) :
    recursiveAttachmentIndices I J P U As Fs ∈ M.sets := by
  let params := extend I (extend J (extend P (extend U (extend As (extend Fs Fin.elim0)))))
  have selected := M.bounded_separation_mem separation
    (BoundedFormula.recursiveAttachmentIndexFormula 0 1 2 3 4 5 6) params
    (Fin.cases hI (Fin.cases hJ (Fin.cases hP (Fin.cases hU (Fin.cases hAs
      (Fin.cases hFs (fun i => Fin.elim0 i)))))))
    (M.prod_mem pairing unions powers separation hI hJ)
  have equal : ZFSet.sep (fun z => BoundedFormula.Truth
      (BoundedFormula.recursiveAttachmentIndexFormula 0 1 2 3 4 5 6) (extend z params))
      (ZFSet.prod I J) = recursiveAttachmentIndices I J P U As Fs := by
    apply ZFSet.ext
    intro z
    rw [ZFSet.mem_sep, recursiveAttachmentIndices, ZFSet.mem_sep]
    exact and_congr Iff.rfl (BoundedFormula.truth_recursiveAttachmentIndexFormula 0 1 2 3 4 5 6 _)
  exact equal ▸ selected

theorem pairFieldGraph_mem
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (left : Bool) {I J K B H : ZFSet.{u}} (hI : I ∈ M.sets) (hJ : J ∈ M.sets)
    (hK : K ∈ M.sets) (hB : B ∈ M.sets) (hH : H ∈ M.sets) :
    pairFieldGraph left I J K B H ∈ M.sets := by
  let params := extend K (extend I (extend J (extend B (extend H Fin.elim0))))
  have selected := M.bounded_separation_mem separation
    (BoundedFormula.pairFieldEntryFormula left 0 1 2 3 4 5) params
    (Fin.cases hK (Fin.cases hI (Fin.cases hJ (Fin.cases hB
      (Fin.cases hH (fun i => Fin.elim0 i))))))
    (M.prod_mem pairing unions powers separation hK hB)
  have equal : ZFSet.sep (fun z => BoundedFormula.Truth
      (BoundedFormula.pairFieldEntryFormula left 0 1 2 3 4 5) (extend z params))
      (ZFSet.prod K B) = pairFieldGraph left I J K B H := by
    apply ZFSet.ext
    intro z
    rw [ZFSet.mem_sep, pairFieldGraph, ZFSet.mem_sep]
    exact and_congr Iff.rfl (BoundedFormula.truth_pairFieldEntryFormula left 0 1 2 3 4 5 _)
  exact equal ▸ selected

end TransitiveGround






theorem pairSecondField_entry_iff {I J K H i j x : ZFSet.{u}}
    (hi : i ∈ I) (hj : j ∈ J) :
    ZFSet.pair (ZFSet.pair i j) x ∈ pairSecondField I J K H ↔
      ZFSet.pair i j ∈ K ∧ ZFSet.pair j x ∈ H := by
  rw [pairSecondField, pairFieldGraph_entry_iff false hi hj]
  exact ⟨fun h => ⟨h.1, h.2.2⟩,
    fun h => ⟨h.1, pair_second_mem_doubleUnion h.2, h.2⟩⟩

theorem pairFirstField_entry_iff {I J K H i j x : ZFSet.{u}}
    (hi : i ∈ I) (hj : j ∈ J) :
    ZFSet.pair (ZFSet.pair i j) x ∈ pairFirstField I J K H ↔
      ZFSet.pair i j ∈ K ∧ ZFSet.pair i x ∈ H := by
  rw [pairFirstField, pairFieldGraph_entry_iff true hi hj]
  exact ⟨fun h => ⟨h.1, h.2.2⟩,
    fun h => ⟨h.1, pair_second_mem_doubleUnion h.2, h.2⟩⟩

theorem recursiveSeparatorFamily_function {K I J D L Maps Ss : ZFSet.{u}}
    (subset : K ⊆ ZFSet.prod I J) (maps : FunctionGraphOn I Maps)
    (separators : ZFSet.IsFunc J D Ss)
    (valid : ∀ i S, ZFSet.pair i S ∈ Maps → ZFSet.IsFunc D L S) :
    ZFSet.IsFunc K L (recursiveSeparatorFamily K I J D L Maps Ss) := by
  apply familyEvaluationGraph_function (pairFieldGraph_function true subset maps.to_isFunc)
    (pairFieldGraph_function false subset separators)
  intro k S entry
  obtain ⟨_, _, i, hi, j, hj, rfl, selected⟩ := (pair_mem_pairFieldGraph true _ _ _ _ _ _ _).1 entry
  exact valid i S selected

theorem recursiveSeparatorFamily_entry_iff {K I J D L Maps Ss i j S e y : ZFSet.{u}}
    (subset : K ⊆ ZFSet.prod I J) (maps : FunctionGraphOn I Maps)
    (separators : ZFSet.IsFunc J D Ss) (hk : ZFSet.pair i j ∈ K)
    (mapEntry : ZFSet.pair i S ∈ Maps) (sepEntry : ZFSet.pair j e ∈ Ss) :
    ZFSet.pair (ZFSet.pair i j) y ∈ recursiveSeparatorFamily K I J D L Maps Ss ↔
      y ∈ L ∧ ZFSet.pair e y ∈ S := by
  have shape := ZFSet.pair_mem_prod.1 (subset hk)
  exact familyEvaluationGraph_entry_iff
    (pairFieldGraph_function true subset maps.to_isFunc)
    (pairFieldGraph_function false subset separators)
    ((pairFirstField_entry_iff shape.1 shape.2).2 ⟨hk, mapEntry⟩)
    ((pairFieldGraph_entry_iff false shape.1 shape.2).2
      ⟨hk, (ZFSet.pair_mem_prod.1 (separators.1 sepEntry)).2, sepEntry⟩)

theorem recursiveAttachmentIndices_entry_iff {I J D U Sources Fs i j a F : ZFSet.{u}}
    (sources : ZFSet.IsFunc I D Sources) (filters : ZFSet.IsFunc J U Fs)
    (source : ZFSet.pair i a ∈ Sources) (filter : ZFSet.pair j F ∈ Fs) :
    ZFSet.pair i j ∈ recursiveAttachmentIndices I J D U Sources Fs ↔ a ∉ F := by
  rw [pair_mem_recursiveAttachmentIndices]
  constructor
  · rintro ⟨_, _, b, _, V, _, ib, jV, negative⟩
    have equalA := (show FunctionGraphOn I Sources from ⟨D, sources⟩).unique ib source
    have equalF := (show FunctionGraphOn J Fs from ⟨U, filters⟩).unique jV filter
    exact equalA ▸ equalF ▸ negative
  · intro negative
    have sa := ZFSet.pair_mem_prod.1 (sources.1 source)
    have sf := ZFSet.pair_mem_prod.1 (filters.1 filter)
    exact ⟨sa.1, sf.1, a, sa.2, F, sf.2, source, filter, negative⟩






theorem recursiveFresh_iff {I J K Qs rs As i j q : ZFSet.{u}}
    (hi : i ∈ I) (hj : j ∈ J) :
    ZFSet.pair (ZFSet.pair i j) q ∈ indexedAttachmentFresh K
      (pairSecondField I J K Qs) (pairSecondField I J K rs) (pairSecondField I J K As) ↔
      ZFSet.pair i j ∈ K ∧ ZFSet.pair j q ∈ indexedAttachmentFresh J Qs rs As := by
  rw [pair_mem_indexedAttachmentFresh, pair_mem_indexedAttachmentFresh]
  constructor
  · rintro ⟨hk, Q, r, a, eq, er, ea, hq, fresh⟩
    exact ⟨hk, hj, Q, r, a, ((pairSecondField_entry_iff hi hj).1 eq).2,
      ((pairSecondField_entry_iff hi hj).1 er).2,
      ((pairSecondField_entry_iff hi hj).1 ea).2, hq, fresh⟩
  · rintro ⟨hk, _, Q, r, a, eq, er, ea, hq, fresh⟩
    exact ⟨hk, Q, r, a, (pairSecondField_entry_iff hi hj).2 ⟨hk, eq⟩,
      (pairSecondField_entry_iff hi hj).2 ⟨hk, er⟩,
      (pairSecondField_entry_iff hi hj).2 ⟨hk, ea⟩, hq, fresh⟩

theorem recursiveFresh_shape {I J K Qs rs As z : ZFSet.{u}}
    (subset : K ⊆ ZFSet.prod I J)
    (fresh : z ∈ indexedAttachmentFresh K
      (pairSecondField I J K Qs) (pairSecondField I J K rs) (pairSecondField I J K As)) :
    ∃ i ∈ I, ∃ j ∈ J, ∃ q, z = ZFSet.pair (ZFSet.pair i j) q ∧
      ZFSet.pair i j ∈ K ∧ ZFSet.pair j q ∈ indexedAttachmentFresh J Qs rs As := by
  obtain ⟨k, hk, q, rfl, _⟩ := (mem_indexedAttachmentFresh _ _ _ _ z).1 fresh
  obtain ⟨i, hi, j, hj, rfl⟩ := ZFSet.mem_prod.1 (subset hk)
  exact ⟨i, hi, j, hj, q, rfl, (recursiveFresh_iff hi hj).1 fresh⟩

theorem negativeRecursiveFresh_mem
    {I J D L Qs rs As Sources Fs i j q a F : ZFSet.{u}}
    (sources : ZFSet.IsFunc I D Sources) (filters : FunctionGraphOn J Fs)
    (source : ZFSet.pair i a ∈ Sources) (filter : ZFSet.pair j F ∈ Fs)
    (fresh : ZFSet.pair j q ∈ indexedAttachmentFresh J Qs rs As) (negative : a ∉ F) :
    let K := recursiveAttachmentIndices I J D (ZFSet.sUnion (ZFSet.sUnion Fs)) Sources Fs
    ZFSet.pair L (ZFSet.pair (ZFSet.pair i j) q) ∈ taggedExtension L
      (indexedAttachmentFresh K (pairSecondField I J K Qs)
        (pairSecondField I J K rs) (pairSecondField I J K As)) := by
  apply pair_mem_taggedExtension.2
  apply (recursiveFresh_iff (ZFSet.pair_mem_prod.1 (sources.1 source)).1 (filters.pair_source filter)).2
  exact ⟨(recursiveAttachmentIndices_entry_iff sources filters.to_isFunc source filter).2 negative, fresh⟩

end PartitionPilot.Forcing



namespace PartitionPilot.Forcing.TransitiveGround

open SetFormula
universe u
variable (M : TransitiveGround.{u})

theorem recursiveSeparatorFamily_mem
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    {K I J D L Maps Ss : ZFSet.{u}} (hK : K ∈ M.sets) (hI : I ∈ M.sets)
    (hJ : J ∈ M.sets) (hD : D ∈ M.sets) (hL : L ∈ M.sets)
    (hMaps : Maps ∈ M.sets) (hSs : Ss ∈ M.sets) :
    recursiveSeparatorFamily K I J D L Maps Ss ∈ M.sets := by
  have bound := M.union_mem unions (M.union_mem unions hMaps)
  exact M.familyEvaluationGraph_mem pairing unions powers separation hK hD hL bound
    (M.pairFieldGraph_mem pairing unions powers separation true hI hJ hK bound hMaps)
    (M.pairFieldGraph_mem pairing unions powers separation false hI hJ hK hD hSs)

theorem groundRecursiveBatchInputs
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    {K I J D L rD rL μD μL Qs rs μs As Es Fs Ss Maps : ZFSet.{u}}
    (d : AttachmentBatchInputs D rD μD J Qs rs μs As Es Fs Ss)
    (target : MeetOrderCode L rL μL) (maps : FunctionGraphOn I Maps)
    (valid : ∀ i S, ZFSet.pair i S ∈ Maps → MeetEmbeddingCode D L rD rL μD μL S)
    (subset : K ⊆ ZFSet.prod I J)
    (hK : K ∈ M.sets) (hI : I ∈ M.sets) (hJ : J ∈ M.sets)
    (hD : D ∈ M.sets) (hL : L ∈ M.sets) (hrL : rL ∈ M.sets)
    (hQs : Qs ∈ M.sets) (hEs : Es ∈ M.sets) (hFs : Fs ∈ M.sets)
    (hMaps : Maps ∈ M.sets) :
    AttachmentBatchInputs L rL μL K
      (pairSecondField I J K Qs) (pairSecondField I J K rs)
      (pairSecondField I J K μs) (pairSecondField I J K As)
      (M.groundPairCompositions K I J (familyPointBound Qs) D L Es Maps)
      (M.groundPairPushFilters K I J L rL Maps Fs)
      (recursiveSeparatorFamily K I J D L Maps Ss) := by
  obtain ⟨_, composites, compositeEntries⟩ := M.groundPairCompositions_spec
    pairing unions powers separation hK hI hJ (M.familyPointBound_mem unions hQs)
    hD hL hEs hMaps d.embeddings maps subset
  obtain ⟨_, filters, filterEntries⟩ := M.groundPairPushFilters_spec
    pairing unions powers separation hK hI hJ hL hrL hMaps hFs maps d.filters subset
  refine ⟨target, ⟨_, pairFieldGraph_function false subset d.spaces.to_isFunc⟩,
    ⟨_, pairFieldGraph_function false subset d.relations.to_isFunc⟩,
    ⟨_, pairFieldGraph_function false subset d.meets.to_isFunc⟩,
    ⟨_, pairFieldGraph_function false subset d.anchors.to_isFunc⟩,
    ⟨_, composites⟩, ⟨_, filters⟩,
    ⟨_, recursiveSeparatorFamily_function subset maps d.separator_function
      (fun i S entry => (valid i S entry).injection.function)⟩, ?_⟩
  intro k hk Q r μ a ell' F' e' qEntry rEntry μEntry aEntry ellEntry FEntry eEntry
  obtain ⟨i, hi, j, hj, rfl⟩ := ZFSet.mem_prod.1 (subset hk)
  have qOriginal := ((pairSecondField_entry_iff hi hj).1 qEntry).2
  have rOriginal := ((pairSecondField_entry_iff hi hj).1 rEntry).2
  have μOriginal := ((pairSecondField_entry_iff hi hj).1 μEntry).2
  have aOriginal := ((pairSecondField_entry_iff hi hj).1 aEntry).2
  obtain ⟨ell, oldEll⟩ := d.embeddings.total hj
  obtain ⟨F, oldF⟩ := d.filters.total hj
  obtain ⟨e, oldE⟩ := d.separators.total hj
  obtain ⟨S, oldS⟩ := maps.total hi
  have old := d.valid j hj Q r μ a ell F e qOriginal rOriginal μOriginal aOriginal oldEll oldF oldE
  have ellEq := ((compositeEntries i j ell S ell' oldEll oldS).1 ellEntry).2
  have filterEq := ((filterEntries i j S F F' oldS oldF).1 FEntry).2
  have image := ((recursiveSeparatorFamily_entry_iff subset maps d.separator_function hk oldS oldE).1 eEntry).2
  have domainEq : relationCompose (familyPointBound Qs) D L ell S =
      relationCompose (attachmentIdeal Q r a) D L ell S :=
    relationCompose_domain_eq
      (fun _ hz => mem_familyPointBound_of_entry qOriginal ((mem_attachmentIdeal Q r a _).1 hz).1)
      old.base_function.1
  rw [ellEq, domainEq, filterEq]
  exact old.pushforward target (valid i S oldS) image

end PartitionPilot.Forcing.TransitiveGround



namespace PartitionPilot.Forcing

open Compression.RecursiveMaps
universe u

structure CodedRecursiveMapInputs
    {D rD μD J Qs rs μs As Es Fs Ss : ZFSet.{u}}
    (d : AttachmentBatchInputs D rD μD J Qs rs μs As Es Fs Ss)
    (I Maps Sources Reps G m inv one A : ZFSet.{u}) : Prop where
  maps : FunctionGraphOn I Maps
  sources : ZFSet.IsFunc I D Sources
  representatives : ZFSet.IsFunc I G Reps
  group : GroupCode G m inv one
  action : PosetActionCode G d.batchCarrier m one d.batchOrder A
  valid : ∀ i S, ZFSet.pair i S ∈ Maps →
    MeetEmbeddingCode D d.batchCarrier rD d.batchOrder μD d.batchMeetGraph S
  agreement : ∀ i a g S x y, ZFSet.pair i a ∈ Sources → ZFSet.pair i g ∈ Reps →
    ZFSet.pair i S ∈ Maps → x ∈ D → ZFSet.pair x a ∈ rD →
      (ZFSet.pair x y ∈ S ↔ ZFSet.pair (ZFSet.pair g x) y ∈ A)

namespace CodedRecursiveMapInputs

variable {D rD μD J Qs rs μs As Es Fs Ss I Maps Sources Reps G m inv one A : ZFSet.{u}}
variable {d : AttachmentBatchInputs D rD μD J Qs rs μs As Es Fs Ss}
variable (h : CodedRecursiveMapInputs d I Maps Sources Reps G m inv one A)

noncomputable def source (i : {i : ZFSet.{u} // i ∈ I}) : {x : ZFSet.{u} // x ∈ D} :=
  let graph : FunctionGraphOn I Sources := ⟨D, h.sources⟩
  ⟨graph.value i, (ZFSet.pair_mem_prod.1 (h.sources.1 (graph.value_entry i))).2⟩

theorem source_entry (i : {i : ZFSet.{u} // i ∈ I}) :
    ZFSet.pair i.val (h.source i).val ∈ Sources :=
  (show FunctionGraphOn I Sources from ⟨D, h.sources⟩).value_entry i

noncomputable def actor (i : {i : ZFSet.{u} // i ∈ I}) : {g : ZFSet.{u} // g ∈ G} :=
  let graph : FunctionGraphOn I Reps := ⟨G, h.representatives⟩
  ⟨graph.value i, (ZFSet.pair_mem_prod.1 (h.representatives.1 (graph.value_entry i))).2⟩

theorem actor_entry (i : {i : ZFSet.{u} // i ∈ I}) : ZFSet.pair i.val (h.actor i).val ∈ Reps :=
  (show FunctionGraphOn I Reps from ⟨G, h.representatives⟩).value_entry i

noncomputable def previous (i : {i : ZFSet.{u} // i ∈ I}) :
    MeetEmbedding d.oldOrder.toMeetOrder d.templates.extension :=
  compose ((h.valid i.val _ (h.maps.value_entry i)).toMeetEmbedding d.oldOrder d.batch_meetOrder)
    d.coding.decodingIso.toMeetEmbedding

theorem previous_entry (i : {i : ZFSet.{u} // i ∈ I}) (x : {x : ZFSet.{u} // x ∈ D}) :
    ZFSet.pair x.val (d.coding.encode ((h.previous i).toFun x)) ∈ h.maps.value i := by
  change ZFSet.pair x.val (d.coding.encode (d.coding.decodingIso.toFun
    (((h.valid i.val _ (h.maps.value_entry i)).toMeetEmbedding d.oldOrder d.batch_meetOrder).toFun x))) ∈ _
  rw [d.coding.decodingIso_encode]
  exact (h.valid i.val _ (h.maps.value_entry i)).toMeetEmbedding_entry d.oldOrder d.batch_meetOrder x

noncomputable def representative (i : {i : ZFSet.{u} // i ∈ I}) :
    Compression.MeetIso d.templates.extension d.templates.extension := by
  let encoding := d.coding.encodingIso
  let acted := h.action.toMeetIso h.group d.batch_meetOrder (h.actor i)
  refine isoOfOrder
    (fun x => encoding.inverse (acted.toFun (encoding.toFun x)))
    (fun x => encoding.inverse (acted.inverse (encoding.toFun x))) ?_ ?_ ?_
  · intro x
    rw [encoding.right_inverse, acted.left_inverse, encoding.left_inverse]
  · intro x
    rw [encoding.right_inverse, acted.right_inverse, encoding.left_inverse]
  · intro x y
    exact ((inverseIso encoding).le_iff _ _).trans
      ((acted.le_iff _ _).trans (encoding.le_iff x y))

theorem representative_entry (i : {i : ZFSet.{u} // i ∈ I})
    (x : {x : ZFSet.{u} // x ∈ D} ⊕ d.templates.Fresh) :
    ZFSet.pair (ZFSet.pair (h.actor i).val (d.coding.encode x))
      (d.coding.encode ((h.representative i).toFun x)) ∈ A := by
  change ZFSet.pair (ZFSet.pair (h.actor i).val (d.coding.encode x))
    (d.coding.encode (d.coding.decode
      ((h.action.toMeetIso h.group d.batch_meetOrder (h.actor i)).toFun
        ⟨d.coding.encode x, d.coding.encode_mem x⟩))) ∈ A
  rw [d.coding.encode_decode]
  exact h.action.toMeetIso_entry h.group d.batch_meetOrder (h.actor i)
    ⟨d.coding.encode x, d.coding.encode_mem x⟩

noncomputable def toInputs : Inputs d.templates {i : ZFSet.{u} // i ∈ I} where
  source := h.source
  previous := h.previous
  representative := h.representative
  agree := by
    intro i x lower
    apply d.coding.encode_injective
    have previous := (h.agreement i.val (h.source i).val (h.actor i).val (h.maps.value i)
      x.val _ (h.source_entry i) (h.actor_entry i) (h.maps.value_entry i) x.property lower).1
        (h.previous_entry i x)
    exact (show FunctionGraphOn (ZFSet.prod G d.batchCarrier) A from
      ⟨d.batchCarrier, h.action.function⟩).unique previous (h.representative_entry i (.inl x))

theorem toInputs_previous_entry (i : {i : ZFSet.{u} // i ∈ I})
    (x : {x : ZFSet.{u} // x ∈ D}) :
    ZFSet.pair x.val (d.coding.encode ((h.toInputs.previous i).toFun x)) ∈ h.maps.value i :=
  h.previous_entry i x

theorem toInputs_representative_entry (i : {i : ZFSet.{u} // i ∈ I})
    (x : {x : ZFSet.{u} // x ∈ D} ⊕ d.templates.Fresh) :
    ZFSet.pair (ZFSet.pair (h.actor i).val (d.coding.encode x))
      (d.coding.encode ((h.toInputs.representative i).toFun x)) ∈ A :=
  h.representative_entry i x

end CodedRecursiveMapInputs

end PartitionPilot.Forcing



namespace PartitionPilot.Forcing.CodedRecursiveMapInputs

open Compression.RecursiveMaps
universe u
variable {D rD μD J Qs rs μs As Es Fs Ss I Maps Sources Reps G m inv one A : ZFSet.{u}}
variable {d : AttachmentBatchInputs D rD μD J Qs rs μs As Es Fs Ss}
variable (h : CodedRecursiveMapInputs d I Maps Sources Reps G m inv one A)

noncomputable abbrev nextIndices (_h : CodedRecursiveMapInputs d I Maps Sources Reps G m inv one A) :=
  recursiveAttachmentIndices I J D (ZFSet.sUnion (ZFSet.sUnion Fs)) Sources Fs

noncomputable abbrev NextInputs (M : TransitiveGround.{u}) :=
  AttachmentBatchInputs d.batchCarrier d.batchOrder d.batchMeetGraph h.nextIndices
    (pairSecondField I J h.nextIndices Qs) (pairSecondField I J h.nextIndices rs)
    (pairSecondField I J h.nextIndices μs) (pairSecondField I J h.nextIndices As)
    (M.groundPairCompositions h.nextIndices I J (familyPointBound Qs) D d.batchCarrier Es Maps)
    (M.groundPairPushFilters h.nextIndices I J d.batchCarrier d.batchOrder Maps Fs)
    (recursiveSeparatorFamily h.nextIndices I J D d.batchCarrier Maps Ss)

noncomputable def nextIndex (label : h.toInputs.Labels) :
    {k : ZFSet.{u} // k ∈ h.nextIndices} :=
  ⟨ZFSet.pair label.1.val label.2.val.val,
    (recursiveAttachmentIndices_entry_iff h.sources d.filters.to_isFunc
      (h.source_entry label.1) (d.filter_entry label.2.val)).2 label.2.property⟩

theorem nextIndex_injective : Function.Injective h.nextIndex := by
  rintro ⟨i, j⟩ ⟨i', j'⟩ equal
  have parts := ZFSet.pair_inj.1 (congrArg Subtype.val equal)
  have left : i = i' := Subtype.ext parts.1
  subst i'
  have right : j = j' := Subtype.ext (Subtype.ext parts.2)
  subst j'
  rfl

theorem nextIndex_surjective : Function.Surjective h.nextIndex := by
  intro k
  obtain ⟨i, hi, j, hj, equal⟩ := ZFSet.mem_prod.1
    (recursiveAttachmentIndices_subset I J D (ZFSet.sUnion (ZFSet.sUnion Fs)) Sources Fs k.property)
  let i' : {i : ZFSet.{u} // i ∈ I} := ⟨i, hi⟩
  let j' : {j : ZFSet.{u} // j ∈ J} := ⟨j, hj⟩
  have negative : ¬ d.templates.upper j' (h.toInputs.source i') :=
    (recursiveAttachmentIndices_entry_iff h.sources d.filters.to_isFunc
      (h.source_entry i') (d.filter_entry j')).1 (equal ▸ k.property)
  exact ⟨⟨i', ⟨j', negative⟩⟩, Subtype.ext equal.symm⟩

variable (M : TransitiveGround.{u}) (next : h.NextInputs M)

theorem next_space (label : h.toInputs.Labels) :
    next.space (h.nextIndex label) = d.space label.2.val :=
  d.spaces.unique
    ((pairSecondField_entry_iff label.1.property label.2.val.property).1
      (next.space_entry (h.nextIndex label))).2 (d.space_entry label.2.val)

theorem next_rel (label : h.toInputs.Labels) :
    next.rel (h.nextIndex label) = d.rel label.2.val :=
  d.relations.unique
    ((pairSecondField_entry_iff label.1.property label.2.val.property).1
      (next.rel_entry (h.nextIndex label))).2 (d.rel_entry label.2.val)

theorem next_meet (label : h.toInputs.Labels) :
    next.meet (h.nextIndex label) = d.meet label.2.val :=
  d.meets.unique
    ((pairSecondField_entry_iff label.1.property label.2.val.property).1
      (next.meet_entry (h.nextIndex label))).2 (d.meet_entry label.2.val)

theorem next_anchor (label : h.toInputs.Labels) :
    next.anchor (h.nextIndex label) = d.anchor label.2.val :=
  d.anchors.unique
    ((pairSecondField_entry_iff label.1.property label.2.val.property).1
      (next.anchor_entry (h.nextIndex label))).2 (d.anchor_entry label.2.val)

theorem next_embed (label : h.toInputs.Labels) :
    next.embed (h.nextIndex label) = relationCompose (familyPointBound Qs) D d.batchCarrier
      (d.embed label.2.val) (h.maps.value label.1) :=
  ((pairCompositionFamily_entry_iff d.embeddings h.maps
    (d.embed_entry label.2.val) (h.maps.value_entry label.1)).1
      (next.embed_entry (h.nextIndex label))).2.2

theorem next_filter (label : h.toInputs.Labels) :
    next.filter (h.nextIndex label) = pushFilterCode d.batchCarrier d.batchOrder
      (h.maps.value label.1) (d.filter label.2.val) :=
  ((pairPushFilterFamily_entry_iff h.maps d.filters
    (h.maps.value_entry label.1) (d.filter_entry label.2.val)).1
      (next.filter_entry (h.nextIndex label))).2.2

noncomputable def nextFresh (q : h.toInputs.nextBatch.Fresh) : next.templates.Fresh :=
  ⟨h.nextIndex q.1, ⟨⟨q.2.val.val, (h.next_space M next q.1).symm ▸ q.2.val.property⟩,
    fun lower => q.2.property (by
      change ZFSet.pair q.2.val.val (next.anchor (h.nextIndex q.1)) ∈
        next.rel (h.nextIndex q.1) at lower
      rwa [h.next_anchor M next, h.next_rel M next] at lower)⟩⟩

theorem nextFresh_injective : Function.Injective (h.nextFresh M next) := by
  rintro ⟨a, q⟩ ⟨b, t⟩ equal
  have same : a = b := h.nextIndex_injective (congrArg Sigma.fst equal)
  subst b
  have values : q.val.val = t.val.val :=
    congrArg (fun z : next.templates.Fresh => z.2.val.val) equal
  exact congrArg (Sigma.mk a) (Subtype.ext (Subtype.ext values))

theorem nextFresh_surjective : Function.Surjective (h.nextFresh M next) := by
  rintro ⟨k, q⟩
  obtain ⟨label, equal⟩ := h.nextIndex_surjective k
  subst k
  have member : q.val.val ∈ d.space label.2.val :=
    h.next_space M next label ▸ q.val.property
  have outside : ZFSet.pair q.val.val (d.anchor label.2.val) ∉ d.rel label.2.val := by
    intro lower
    apply q.property
    change ZFSet.pair q.val.val (next.anchor (h.nextIndex label)) ∈ next.rel (h.nextIndex label)
    rwa [h.next_anchor M next, h.next_rel M next]
  exact ⟨⟨label, ⟨⟨q.val.val, member⟩, outside⟩⟩, rfl⟩

theorem nextFresh_inside_iff (q t : h.toInputs.nextBatch.Fresh) :
    next.templates.Inside (h.nextFresh M next q) (h.nextFresh M next t) ↔
      h.toInputs.nextBatch.Inside q t := by
  rcases q with ⟨a, q⟩
  rcases t with ⟨b, t⟩
  constructor
  · rintro ⟨same, lower⟩
    have eq : a = b := h.nextIndex_injective same
    subst b
    refine ⟨rfl, ?_⟩
    change ZFSet.pair q.val.val t.val.val ∈ next.rel (h.nextIndex a) at lower
    change ZFSet.pair q.val.val t.val.val ∈ d.rel a.2.val
    rwa [h.next_rel M next] at lower
  · rintro ⟨same, lower⟩
    change a = b at same
    subst b
    refine ⟨rfl, ?_⟩
    change ZFSet.pair q.val.val t.val.val ∈ next.rel (h.nextIndex a)
    rw [h.next_rel M next]
    exact lower

end PartitionPilot.Forcing.CodedRecursiveMapInputs



namespace PartitionPilot.Forcing.CodedRecursiveMapInputs

universe u
variable {D rD μD J Qs rs μs As Es Fs Ss I Maps Sources Reps G m inv one A : ZFSet.{u}}
variable {d : AttachmentBatchInputs D rD μD J Qs rs μs As Es Fs Ss}
variable (h : CodedRecursiveMapInputs d I Maps Sources Reps G m inv one A)
variable (M : TransitiveGround.{u}) (next : h.NextInputs M)

noncomputable abbrev liftGraph :=
  liftedCompressionGraph I J D d.batchCarrier next.batchCarrier
    (indexedAttachmentFresh J Qs rs As) (familyPointBound Qs) Maps Sources Fs Reps G A

noncomputable abbrev liftSection (i : ZFSet.{u}) :=
  indexedRelationSection d.batchCarrier next.batchCarrier (h.liftGraph M next) i

theorem liftGraph_function :
    ZFSet.IsFunc (ZFSet.prod I d.batchCarrier) next.batchCarrier (h.liftGraph M next) :=
  liftedCompressionGraph_function rfl
    (fun _ hz => indexedAttachmentDomain_subset J Qs (indexedAttachmentFresh_subset J Qs rs As hz))
    (fun _ hz => old_mem_taggedExtension hz) h.maps
    (fun i S entry => (h.valid i S entry).injection.function)
    h.sources d.filters h.representatives h.action.function
    (fun _ _ _ _ _ _ _ _ fresh source filter negative =>
      negativeRecursiveFresh_mem h.sources d.filters source filter fresh negative)

theorem liftSection_function {i : ZFSet.{u}} (hi : i ∈ I) :
    ZFSet.IsFunc d.batchCarrier next.batchCarrier (h.liftSection M next i) :=
  indexedRelationSection_function (h.liftGraph_function M next) hi

theorem liftGraph_old_iff {i S x y : ZFSet.{u}}
    (mapEntry : ZFSet.pair i S ∈ Maps) (hx : x ∈ D) :
    ZFSet.pair (ZFSet.pair i x) y ∈ h.liftGraph M next ↔ ZFSet.pair x y ∈ S := by
  rw [liftGraph, liftedCompressionGraph_old_iff h.maps mapEntry hx]
  constructor
  · exact fun entry => entry.2.2
  · intro entry
    exact ⟨old_mem_taggedExtension hx, old_mem_taggedExtension
      (ZFSet.pair_mem_prod.1 ((h.valid i S mapEntry).injection.function.1 entry)).2, entry⟩

theorem liftGraph_positive_iff {i j q a F g y : ZFSet.{u}}
    (source : ZFSet.pair i a ∈ Sources) (filter : ZFSet.pair j F ∈ Fs)
    (representative : ZFSet.pair i g ∈ Reps)
    (fresh : ZFSet.pair j q ∈ indexedAttachmentFresh J Qs rs As) (positive : a ∈ F) :
    ZFSet.pair (ZFSet.pair i (ZFSet.pair D (ZFSet.pair j q))) y ∈ h.liftGraph M next ↔
      ZFSet.pair (ZFSet.pair g (ZFSet.pair D (ZFSet.pair j q))) y ∈ A := by
  have bounds := ZFSet.pair_mem_prod.1 (indexedAttachmentDomain_subset J Qs
    (indexedAttachmentFresh_subset J Qs rs As fresh))
  have ha := (ZFSet.pair_mem_prod.1 (h.sources.1 source)).2
  have sourceFunc : FunctionGraphOn I Sources := ⟨D, h.sources⟩
  rw [liftGraph, liftedCompressionGraph_fresh_iff sourceFunc d.filters source filter
    bounds.1 bounds.2 ha fresh]
  constructor
  · rintro ⟨_, _, ⟨_, g', _, representative', acted⟩ | ⟨negative, _⟩⟩
    · exact (show FunctionGraphOn I Reps from ⟨G, h.representatives⟩).unique
        representative' representative ▸ acted
    · exact False.elim (negative positive)
  · intro acted
    have hy := (ZFSet.pair_mem_prod.1 (h.action.function.1 acted)).2
    exact ⟨pair_mem_taggedExtension.2 fresh, old_mem_taggedExtension hy,
      Or.inl ⟨positive, g, (ZFSet.pair_mem_prod.1 (h.representatives.1 representative)).2,
        representative, acted⟩⟩

theorem liftGraph_negative_iff {i j q a F y : ZFSet.{u}}
    (source : ZFSet.pair i a ∈ Sources) (filter : ZFSet.pair j F ∈ Fs)
    (fresh : ZFSet.pair j q ∈ indexedAttachmentFresh J Qs rs As) (negative : a ∉ F) :
    ZFSet.pair (ZFSet.pair i (ZFSet.pair D (ZFSet.pair j q))) y ∈ h.liftGraph M next ↔
      y = ZFSet.pair d.batchCarrier (ZFSet.pair (ZFSet.pair i j) q) := by
  have bounds := ZFSet.pair_mem_prod.1 (indexedAttachmentDomain_subset J Qs
    (indexedAttachmentFresh_subset J Qs rs As fresh))
  have ha := (ZFSet.pair_mem_prod.1 (h.sources.1 source)).2
  have sourceFunc : FunctionGraphOn I Sources := ⟨D, h.sources⟩
  rw [liftGraph, liftedCompressionGraph_fresh_iff sourceFunc d.filters source filter
    bounds.1 bounds.2 ha fresh]
  constructor
  · rintro ⟨_, _, ⟨positive, _⟩ | ⟨_, equal⟩⟩
    · exact False.elim (negative positive)
    · exact equal
  · intro equal
    exact ⟨pair_mem_taggedExtension.2 fresh,
      equal.symm ▸ negativeRecursiveFresh_mem h.sources d.filters source filter fresh negative,
      Or.inr ⟨negative, equal⟩⟩






theorem liftGraph_agrees_on_base {i a g x y : ZFSet.{u}}
    (source : ZFSet.pair i a ∈ Sources) (representative : ZFSet.pair i g ∈ Reps)
    (hx : x ∈ d.batchCarrier) (below : ZFSet.pair x a ∈ d.batchOrder) :
    ZFSet.pair (ZFSet.pair i x) y ∈ h.liftGraph M next ↔
      ZFSet.pair (ZFSet.pair g x) y ∈ A := by
  have hi := (ZFSet.pair_mem_prod.1 (h.sources.1 source)).1
  have ha := (ZFSet.pair_mem_prod.1 (h.sources.1 source)).2
  obtain ⟨X, rfl⟩ := d.coding.encode_surjective x hx
  have lower := (d.coding.le_encode X (.inl ⟨a, ha⟩)).1 below
  cases X with
  | inl p =>
    obtain ⟨S, mapEntry⟩ := h.maps.total hi
    exact (h.liftGraph_old_iff M next mapEntry p.property).trans
      (h.agreement i a g S p.val y source representative mapEntry p.property lower)
  | inr q =>
    exact h.liftGraph_positive_iff M next source (d.filter_entry q.1) representative
      (d.freshCode_mem q) lower

theorem liftSection_agrees_on_base {i a g x y : ZFSet.{u}}
    (source : ZFSet.pair i a ∈ Sources) (representative : ZFSet.pair i g ∈ Reps)
    (hx : x ∈ d.batchCarrier) (below : ZFSet.pair x a ∈ d.batchOrder) :
    ZFSet.pair x y ∈ h.liftSection M next i ↔
      ZFSet.pair (ZFSet.pair g x) y ∈ A := by
  rw [liftSection, pair_mem_indexedRelationSection, h.liftGraph_agrees_on_base M next source representative hx below]
  constructor
  · exact fun h => h.2.2
  · intro acted
    exact ⟨hx, old_mem_taggedExtension (ZFSet.pair_mem_prod.1 (h.action.function.1 acted)).2, acted⟩

end PartitionPilot.Forcing.CodedRecursiveMapInputs

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

structure EligibleTaskCode (P G r μ A source target base separator F : ZFSet.{u}) : Prop where
  source_mem : source ∈ P
  target_mem : target ∈ P
  separator_mem : separator ∈ P
  filter : MeetFilterCode P r μ F
  lower : ZFSet.pair target separator ∈ r
  strict : ZFSet.pair separator target ∉ r
  upper : ∀ x ∈ F, ZFSet.pair separator x ∈ r
  representative : ∃ g ∈ G, RestrictedActionCode P r A g source target base

namespace BoundedFormula

open SetFormula

def eligibleTaskFormula {n} (P G r μ A source target base separator F : Fin n) : BoundedFormula n :=
  .conj (.mem source P) (.conj (.mem target P) (.conj (.mem separator P)
    (.conj (meetFilterFormula P r μ F) (.conj (pairMembershipFormula target separator r)
      (.conj (.neg (pairMembershipFormula separator target r))
        (.conj (allMem F (pairMembershipFormula separator.succ 0 r.succ))
          (exMem G (restrictedActionFormula P.succ r.succ A.succ 0
            source.succ target.succ base.succ))))))))

end BoundedFormula

namespace BoundedFormula

open SetFormula

def eligibleTaskEntryFormula {n} (z P G r μ A R U Labels : Fin n) : BoundedFormula n :=
  let lift (i : Fin n) := i.succ.succ.succ.succ.succ.succ
  exMem P (exMem P.succ (exMem R.succ.succ (exMem P.succ.succ.succ
    (exMem U.succ.succ.succ.succ (exMem Labels.succ.succ.succ.succ.succ
      (.conj (literalTaskFormula (lift z) 5 4 3 2 1 0)
        (eligibleTaskFormula (lift P) (lift G) (lift r) (lift μ) (lift A) 5 4 3 2 1)))))))

end BoundedFormula

namespace BoundedFormula

open SetFormula

def taskRepresentativeFormula {n} (task g P r A R U Labels : Fin n) : BoundedFormula n :=
  let lift (i : Fin n) := i.succ.succ.succ.succ.succ.succ
  exMem P (exMem P.succ (exMem R.succ.succ (exMem P.succ.succ.succ
    (exMem U.succ.succ.succ.succ (exMem Labels.succ.succ.succ.succ.succ
      (.conj (literalTaskFormula (lift task) 5 4 3 2 1 0)
        (restrictedActionFormula (lift P) (lift r) (lift A) (lift g) 5 4 3)))))))

def taskRepresentativeEntryFormula {n} (z I P G r A R U Labels : Fin n) : BoundedFormula n :=
  exMem I (exMem G.succ (.conj (orderedPairFormula z.succ.succ 1 0)
    (taskRepresentativeFormula 1 0 P.succ.succ r.succ.succ A.succ.succ
      R.succ.succ U.succ.succ Labels.succ.succ)))

end BoundedFormula

end PartitionPilot.Forcing

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Definability_TaskTransportFormulas
attribute [-instance] _root_.OAI.PartitionPilot.Forcing.GroundMainPrefix.withTopSmall
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PartitionPilot.Forcing.BoundedFormula

open SetFormula
universe u

def taskTransportFormula {n} (P R U Labels A g t t' : Fin n) : BoundedFormula n :=
  let lift (i : Fin n) := i.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ
  exMem P (exMem P.succ (exMem R.succ.succ (exMem P.succ.succ.succ
    (exMem U.succ.succ.succ.succ (exMem Labels.succ.succ.succ.succ.succ
      (exMem P.succ.succ.succ.succ.succ.succ
        (exMem R.succ.succ.succ.succ.succ.succ.succ
          (exMem P.succ.succ.succ.succ.succ.succ.succ.succ
            (exMem U.succ.succ.succ.succ.succ.succ.succ.succ.succ
              (.conj (literalTaskFormula (lift t) 9 8 7 6 5 4)
                (.conj (literalTaskFormula (lift t') 9 3 2 1 0 4)
                  (.conj (tripleMembershipFormula (lift g) 8 3 (lift A))
                    (.conj (tripleMembershipFormula (lift g) 6 1 (lift A))
                      (.conj (actionPostcomposeFormula (lift P) (lift A) (lift g) 7 2)
                        (actionImageEqualityFormula (lift P) (lift A) (lift g) 5 0)))))))))))))))

def taskTransportEntryFormula {n} (z G I P R U Labels A : Fin n) : BoundedFormula n :=
  exMem G (exMem I.succ (exMem I.succ.succ
    (.conj (orderedTripleFormula z.succ.succ.succ 2 1 0)
      (taskTransportFormula P.succ.succ.succ R.succ.succ.succ U.succ.succ.succ
        Labels.succ.succ.succ A.succ.succ.succ 2 1 0))))

end PartitionPilot.Forcing.BoundedFormula

end

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Forcing_CodedRecursiveTaskActions
attribute [-instance] _root_.OAI.PartitionPilot.Forcing.GroundMainPrefix.withTopSmall
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PartitionPilot.Forcing

section

universe u

theorem PosetActionCode.toSetAction {G P m e r A : ZFSet.{u}}
    (action : PosetActionCode G P m e r A) : SetActionCode G P m e A :=
  ⟨action.function, action.one, action.mul⟩

noncomputable def taggedActionGraph (G P N A B : ZFSet.{u}) : ZFSet.{u} :=
  A ∪ ZFSet.sep (fun z => ∃ g ∈ G, ∃ q ∈ N, ∃ t ∈ N,
    z = ZFSet.pair (ZFSet.pair g (ZFSet.pair P q)) (ZFSet.pair P t) ∧
      ZFSet.pair (ZFSet.pair g q) t ∈ B)
    (ZFSet.prod (ZFSet.prod G (taggedExtension P N)) (taggedExtension P N))

theorem triple_mem_taggedActionGraph (G P N A B g x y : ZFSet.{u}) :
    ZFSet.pair (ZFSet.pair g x) y ∈ taggedActionGraph G P N A B ↔
      ZFSet.pair (ZFSet.pair g x) y ∈ A ∨
        (g ∈ G ∧ ∃ q ∈ N, ∃ t ∈ N, x = ZFSet.pair P q ∧ y = ZFSet.pair P t ∧
          ZFSet.pair (ZFSet.pair g q) t ∈ B) := by
  rw [taggedActionGraph, ZFSet.mem_union, ZFSet.mem_sep]
  apply or_congr Iff.rfl
  constructor
  · rintro ⟨_, g', hg, q, hq, t, ht, equal, entry⟩
    obtain ⟨first, last⟩ := ZFSet.pair_inj.1 equal
    obtain ⟨actor, middle⟩ := ZFSet.pair_inj.1 first
    subst g'
    exact ⟨hg, q, hq, t, ht, middle, last, entry⟩
  · rintro ⟨hg, q, hq, t, ht, rfl, rfl, entry⟩
    exact ⟨ZFSet.pair_mem_prod.2 ⟨ZFSet.pair_mem_prod.2
      ⟨hg, pair_mem_taggedExtension.2 hq⟩, pair_mem_taggedExtension.2 ht⟩,
      g, hg, q, hq, t, ht, rfl, entry⟩

theorem taggedActionGraph_old_iff {G P N A B g x y : ZFSet.{u}} (hx : x ∈ P) :
    ZFSet.pair (ZFSet.pair g x) y ∈ taggedActionGraph G P N A B ↔
      ZFSet.pair (ZFSet.pair g x) y ∈ A := by
  rw [triple_mem_taggedActionGraph]
  refine ⟨fun h => h.elim id ?_, Or.inl⟩
  rintro ⟨_, q, _, t, _, equal, _, _⟩
  exact False.elim (pair_tag_not_mem P q (equal ▸ hx))

theorem taggedActionGraph_fresh_iff {G P N m e A B g q y : ZFSet.{u}}
    (old : SetActionCode G P m e A) (fresh : SetActionCode G N m e B) :
    ZFSet.pair (ZFSet.pair g (ZFSet.pair P q)) y ∈ taggedActionGraph G P N A B ↔
      ∃ t ∈ N, y = ZFSet.pair P t ∧ ZFSet.pair (ZFSet.pair g q) t ∈ B := by
  rw [triple_mem_taggedActionGraph]
  constructor
  · rintro (entry | ⟨_, q', _, t, ht, equal, hy, entry⟩)
    · exact False.elim (pair_tag_not_mem P q (old.entry_shape entry).2.1)
    · have same := (ZFSet.pair_inj.1 equal).2
      subst q'
      exact ⟨t, ht, hy, entry⟩
  · rintro ⟨t, ht, hy, entry⟩
    have shape := fresh.entry_shape entry
    exact Or.inr ⟨shape.1, q, shape.2.1, t, ht, rfl, hy, entry⟩

theorem taggedActionGraph_fresh_pair_iff {G P N m e A B g q t : ZFSet.{u}}
    (old : SetActionCode G P m e A) (fresh : SetActionCode G N m e B) :
    ZFSet.pair (ZFSet.pair g (ZFSet.pair P q)) (ZFSet.pair P t) ∈
      taggedActionGraph G P N A B ↔ ZFSet.pair (ZFSet.pair g q) t ∈ B := by
  rw [taggedActionGraph_fresh_iff old fresh]
  constructor
  · rintro ⟨t', _, equal, entry⟩
    exact (ZFSet.pair_inj.1 equal).2.symm ▸ entry
  · intro entry
    exact ⟨t, (fresh.entry_shape entry).2.2, rfl, entry⟩

theorem taggedActionGraph_subset {G P N m e A B : ZFSet.{u}}
    (old : SetActionCode G P m e A) :
    taggedActionGraph G P N A B ⊆
      ZFSet.prod (ZFSet.prod G (taggedExtension P N)) (taggedExtension P N) := by
  intro z hz
  rcases ZFSet.mem_union.1 hz with oldEntry | freshEntry
  · obtain ⟨v, hv, y, hy, rfl⟩ := ZFSet.mem_prod.1 (old.function.1 oldEntry)
    obtain ⟨g, hg, x, hx, rfl⟩ := ZFSet.mem_prod.1 hv
    exact ZFSet.pair_mem_prod.2 ⟨ZFSet.pair_mem_prod.2
      ⟨hg, old_mem_taggedExtension hx⟩, old_mem_taggedExtension hy⟩
  · exact (ZFSet.mem_sep.1 freshEntry).1

theorem taggedActionGraph_function {G P N m e A B : ZFSet.{u}}
    (old : SetActionCode G P m e A) (fresh : SetActionCode G N m e B) :
    ZFSet.IsFunc (ZFSet.prod G (taggedExtension P N)) (taggedExtension P N)
      (taggedActionGraph G P N A B) := by
  refine ⟨taggedActionGraph_subset old, ?_⟩
  intro v hv
  obtain ⟨g, hg, x, hx, rfl⟩ := ZFSet.mem_prod.1 hv
  rcases mem_taggedExtension.1 hx with hx | ⟨q, hq, rfl⟩
  · obtain ⟨y, entry, unique⟩ := old.function.2 (ZFSet.pair g x) (ZFSet.pair_mem_prod.2 ⟨hg, hx⟩)
    exact ⟨y, taggedActionGraph_old_iff hx |>.2 entry,
      fun z hz => unique z ((taggedActionGraph_old_iff hx).1 hz)⟩
  · obtain ⟨t, entry, unique⟩ := fresh.function.2 (ZFSet.pair g q) (ZFSet.pair_mem_prod.2 ⟨hg, hq⟩)
    refine ⟨ZFSet.pair P t, (taggedActionGraph_fresh_pair_iff old fresh).2 entry, ?_⟩
    intro y hy
    obtain ⟨t', _, equal, entry'⟩ := (taggedActionGraph_fresh_iff old fresh).1 hy
    exact equal.trans (congrArg (ZFSet.pair P) (unique t' entry'))

theorem taggedActionGraph_one {G P N m e A B : ZFSet.{u}}
    (old : SetActionCode G P m e A) (fresh : SetActionCode G N m e B) :
    ∀ x ∈ taggedExtension P N, ZFSet.pair (ZFSet.pair e x) x ∈ taggedActionGraph G P N A B := by
  intro x hx
  rcases mem_taggedExtension.1 hx with hx | ⟨q, hq, rfl⟩
  · exact (taggedActionGraph_old_iff hx).2 (old.one x hx)
  · exact (taggedActionGraph_fresh_pair_iff old fresh).2 (fresh.one q hq)

theorem taggedActionGraph_mul {G P N m e A B : ZFSet.{u}}
    (old : SetActionCode G P m e A) (fresh : SetActionCode G N m e B) :
    ∀ g ∈ G, ∀ h ∈ G, ∀ k ∈ G, ∀ p ∈ taggedExtension P N,
      ∀ q ∈ taggedExtension P N, ∀ s ∈ taggedExtension P N,
        ZFSet.pair (ZFSet.pair g h) k ∈ m →
        ZFSet.pair (ZFSet.pair h p) q ∈ taggedActionGraph G P N A B →
        ZFSet.pair (ZFSet.pair g q) s ∈ taggedActionGraph G P N A B →
        ZFSet.pair (ZFSet.pair k p) s ∈ taggedActionGraph G P N A B := by
  intro g hg h hh k hk p hp q _ s _ product first second
  rcases mem_taggedExtension.1 hp with hp | ⟨x, hx, rfl⟩
  · have first' := (taggedActionGraph_old_iff hp).1 first
    have hq := (old.entry_shape first').2.2
    have second' := (taggedActionGraph_old_iff hq).1 second
    have hs := (old.entry_shape second').2.2
    exact (taggedActionGraph_old_iff hp).2 (old.mul g hg h hh k hk p hp q hq s hs product first' second')
  · obtain ⟨y, hy, rfl, first'⟩ := (taggedActionGraph_fresh_iff old fresh).1 first
    obtain ⟨z, hz, rfl, second'⟩ := (taggedActionGraph_fresh_iff old fresh).1 second
    exact (taggedActionGraph_fresh_pair_iff old fresh).2
      (fresh.mul g hg h hh k hk x hx y hy z hz product first' second')

theorem SetActionCode.tagged {G P N m e A B : ZFSet.{u}}
    (old : SetActionCode G P m e A) (fresh : SetActionCode G N m e B) :
    SetActionCode G (taggedExtension P N) m e (taggedActionGraph G P N A B) :=
  ⟨taggedActionGraph_function old fresh, taggedActionGraph_one old fresh, taggedActionGraph_mul old fresh⟩

end

namespace SetActionCode

open SetRealization
universe u
variable {G X m inv one A : ZFSet.{u}}
variable (action : SetActionCode G X m one A)

noncomputable def rawAct (g : {g : ZFSet.{u} // g ∈ G})
    (x : {x : ZFSet.{u} // x ∈ X}) : {x : ZFSet.{u} // x ∈ X} :=
  let graph : FunctionGraphOn (ZFSet.prod G X) A := ⟨X, action.function⟩
  let input := (⟨ZFSet.pair g.val x.val, ZFSet.pair_mem_prod.2 ⟨g.property, x.property⟩⟩ :
    {z : ZFSet.{u} // z ∈ ZFSet.prod G X})
  ⟨graph.value input, (ZFSet.pair_mem_prod.1 (action.function.1 (graph.value_entry input))).2⟩

theorem rawAct_entry (g : {g : ZFSet.{u} // g ∈ G}) (x : {x : ZFSet.{u} // x ∈ X}) :
    ZFSet.pair (ZFSet.pair g.val x.val) (action.rawAct g x).val ∈ A :=
  (show FunctionGraphOn (ZFSet.prod G X) A from ⟨X, action.function⟩).value_entry
    ⟨ZFSet.pair g.val x.val, ZFSet.pair_mem_prod.2 ⟨g.property, x.property⟩⟩

noncomputable def inverseActor (group : GroupCode G m inv one)
    (g : {g : ZFSet.{u} // g ∈ G}) : {g : ZFSet.{u} // g ∈ G} :=
  ⟨SetMembers.raw (group.inv (SetMembers.ofMem g.val g.property)),
    SetMembers.raw_mem _⟩

theorem inverseActor_left (group : GroupCode G m inv one)
    (g : {g : ZFSet.{u} // g ∈ G}) :
    ZFSet.pair (ZFSet.pair (inverseActor group g).val g.val) one ∈ m := by
  apply group.inv_mul g.val g.property _ (inverseActor group g).property
  simpa only [inverseActor, SetMembers.raw_ofMem] using
    group.inv_mem (SetMembers.ofMem g.val g.property)

theorem inverseActor_right (group : GroupCode G m inv one)
    (g : {g : ZFSet.{u} // g ∈ G}) :
    ZFSet.pair (ZFSet.pair g.val (inverseActor group g).val) one ∈ m := by
  let actor := SetMembers.ofMem g.val g.property
  have equal : group.mul actor (group.inv actor) = group.one := by
    let := group.toGroup
    exact mul_inv_cancel actor
  have entry := group.mul_mem actor (group.inv actor)
  rw [equal, group.raw_one] at entry
  simpa only [actor, inverseActor, SetMembers.raw_ofMem] using entry

theorem rawAct_inverse_left (group : GroupCode G m inv one)
    (g : {g : ZFSet.{u} // g ∈ G}) (x : {x : ZFSet.{u} // x ∈ X}) :
    action.rawAct (inverseActor group g) (action.rawAct g x) = x := by
  apply Subtype.ext
  exact action.entry_unique
    (action.mul _ (inverseActor group g).property g.val g.property one group.identity_mem
      x.val x.property _ (action.rawAct g x).property _
      (action.rawAct (inverseActor group g) (action.rawAct g x)).property
      (inverseActor_left group g) (action.rawAct_entry g x)
      (action.rawAct_entry (inverseActor group g) (action.rawAct g x)))
    (action.one x.val x.property)

theorem rawAct_inverse_right (group : GroupCode G m inv one)
    (g : {g : ZFSet.{u} // g ∈ G}) (x : {x : ZFSet.{u} // x ∈ X}) :
    action.rawAct g (action.rawAct (inverseActor group g) x) = x := by
  apply Subtype.ext
  exact action.entry_unique
    (action.mul g.val g.property _ (inverseActor group g).property one group.identity_mem
      x.val x.property _ (action.rawAct (inverseActor group g) x).property _
      (action.rawAct g (action.rawAct (inverseActor group g) x)).property
      (inverseActor_right group g) (action.rawAct_entry (inverseActor group g) x)
      (action.rawAct_entry g (action.rawAct (inverseActor group g) x)))
    (action.one x.val x.property)

noncomputable def toPerm (group : GroupCode G m inv one)
    (g : {g : ZFSet.{u} // g ∈ G}) : Equiv.Perm {x : ZFSet.{u} // x ∈ X} where
  toFun := action.rawAct g
  invFun := action.rawAct (inverseActor group g)
  left_inv := action.rawAct_inverse_left group g
  right_inv := action.rawAct_inverse_right group g

end SetActionCode

section

universe u

namespace BoundedFormula

open SetFormula

def taggedActionEntryFormula {n} (z G P N B : Fin n) : BoundedFormula n :=
  exMem G (exMem N.succ (exMem N.succ.succ
    (.conj (nestedActionTripleFormula z.succ.succ.succ 2 P.succ.succ.succ 1 P.succ.succ.succ 0)
      (tripleMembershipFormula 2 1 0 B.succ.succ.succ))))

theorem truth_taggedActionEntryFormula {n} (z G P N B : Fin n)
    (env : Fin n → ZFSet.{u}) :
    Truth (taggedActionEntryFormula z G P N B) env ↔
      ∃ g ∈ env G, ∃ q ∈ env N, ∃ t ∈ env N,
        env z = ZFSet.pair (ZFSet.pair g (ZFSet.pair (env P) q)) (ZFSet.pair (env P) t) ∧
          ZFSet.pair (ZFSet.pair g q) t ∈ env B := by
  simp only [taggedActionEntryFormula, truth_exMem, Truth,
    truth_nestedActionTripleFormula, truth_tripleMembershipFormula]
  rfl

end BoundedFormula

namespace TransitiveGround

open SetFormula

theorem taggedActionGraph_mem (M : TransitiveGround.{u})
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    {G P N A B : ZFSet.{u}} (hG : G ∈ M.sets) (hP : P ∈ M.sets)
    (hN : N ∈ M.sets) (hA : A ∈ M.sets) (hB : B ∈ M.sets) :
    taggedActionGraph G P N A B ∈ M.sets := by
  have hL := M.taggedExtension_mem pairing unions powers separation hP hN
  let params := extend G (extend P (extend N (extend B Fin.elim0)))
  have selected := M.bounded_separation_mem separation
    (BoundedFormula.taggedActionEntryFormula 0 1 2 3 4) params
    (Fin.cases hG (Fin.cases hP (Fin.cases hN (Fin.cases hB (fun i => Fin.elim0 i)))))
    (M.prod_mem pairing unions powers separation
      (M.prod_mem pairing unions powers separation hG hL) hL)
  have equal : ZFSet.sep (fun z => BoundedFormula.Truth
      (BoundedFormula.taggedActionEntryFormula 0 1 2 3 4) (extend z params))
      (ZFSet.prod (ZFSet.prod G (taggedExtension P N)) (taggedExtension P N)) =
      ZFSet.sep (fun z => ∃ g ∈ G, ∃ q ∈ N, ∃ t ∈ N,
        z = ZFSet.pair (ZFSet.pair g (ZFSet.pair P q)) (ZFSet.pair P t) ∧
          ZFSet.pair (ZFSet.pair g q) t ∈ B)
        (ZFSet.prod (ZFSet.prod G (taggedExtension P N)) (taggedExtension P N)) := by
    apply ZFSet.ext
    intro z
    rw [ZFSet.mem_sep, ZFSet.mem_sep]
    exact and_congr Iff.rfl (BoundedFormula.truth_taggedActionEntryFormula 0 1 2 3 4 _)
  exact M.binary_union_mem pairing unions hA (equal ▸ selected)

end TransitiveGround

end

open Compression.RecursiveMaps
universe u

structure CodedRecursiveTaskAction
    {D rD μD J Qs rs μs As Es Fs Ss I Maps Sources Reps G m inv one A : ZFSet.{u}}
    {d : AttachmentBatchInputs D rD μD J Qs rs μs As Es Fs Ss}
    (h : CodedRecursiveMapInputs d I Maps Sources Reps G m inv one A)
    (T : ZFSet.{u}) : Prop where
  taskAction : SetActionCode G I m one T
  source : ∀ g i j a b, ZFSet.pair (ZFSet.pair g i) j ∈ T →
    ZFSet.pair i a ∈ Sources → ZFSet.pair j b ∈ Sources → a = b
  intertwine : ∀ g i j S S' p x y, ZFSet.pair (ZFSet.pair g i) j ∈ T →
    ZFSet.pair i S ∈ Maps → ZFSet.pair j S' ∈ Maps →
    ZFSet.pair p x ∈ S → ZFSet.pair p y ∈ S' → ZFSet.pair (ZFSet.pair g x) y ∈ A

namespace CodedRecursiveTaskAction

variable {D rD μD J Qs rs μs As Es Fs Ss I Maps Sources Reps G m inv one A T : ZFSet.{u}}
variable {d : AttachmentBatchInputs D rD μD J Qs rs μs As Es Fs Ss}
variable {h : CodedRecursiveMapInputs d I Maps Sources Reps G m inv one A}
variable (s : CodedRecursiveTaskAction h T)

noncomputable def current (_s : CodedRecursiveTaskAction h T) (g : {g : ZFSet.{u} // g ∈ G}) :
    Compression.MeetIso d.templates.extension d.templates.extension := by
  let encoding := d.coding.encodingIso
  let acted := h.action.toMeetIso h.group d.batch_meetOrder g
  refine isoOfOrder
    (fun x => encoding.inverse (acted.toFun (encoding.toFun x)))
    (fun x => encoding.inverse (acted.inverse (encoding.toFun x))) ?_ ?_ ?_
  · intro x
    rw [encoding.right_inverse, acted.left_inverse, encoding.left_inverse]
  · intro x
    rw [encoding.right_inverse, acted.right_inverse, encoding.left_inverse]
  · intro x y
    exact ((inverseIso encoding).le_iff _ _).trans
      ((acted.le_iff _ _).trans (encoding.le_iff x y))

theorem current_entry (g : {g : ZFSet.{u} // g ∈ G})
    (x : {x : ZFSet.{u} // x ∈ D} ⊕ d.templates.Fresh) :
    ZFSet.pair (ZFSet.pair g.val (d.coding.encode x))
      (d.coding.encode ((s.current g).toFun x)) ∈ A := by
  change ZFSet.pair (ZFSet.pair g.val (d.coding.encode x))
    (d.coding.encode (d.coding.decode ((h.action.toMeetIso h.group d.batch_meetOrder g).toFun
      ⟨d.coding.encode x, d.coding.encode_mem x⟩))) ∈ A
  rw [d.coding.encode_decode]
  exact h.action.toMeetIso_entry h.group d.batch_meetOrder g
    ⟨d.coding.encode x, d.coding.encode_mem x⟩

noncomputable def toTaskSymmetry (g : {g : ZFSet.{u} // g ∈ G}) : TaskSymmetry h.toInputs where
  perm := s.taskAction.rawAct g
  inverse := (s.taskAction.toPerm h.group g).invFun
  left_inverse := (s.taskAction.toPerm h.group g).left_inv
  right_inverse := (s.taskAction.toPerm h.group g).right_inv
  current := s.current g
  source i := Subtype.ext (s.source g.val i.val _ _ _ (s.taskAction.rawAct_entry g i)
    (h.source_entry i) (h.source_entry (s.taskAction.rawAct g i))).symm
  intertwine i p := by
    apply d.coding.encode_injective
    exact h.action.toSetAction.entry_unique (s.current_entry g ((h.toInputs.previous i).toFun p))
      (s.intertwine g.val i.val _ _ _ p.val _ _ (s.taskAction.rawAct_entry g i)
        (h.maps.value_entry i) (h.maps.value_entry (s.taskAction.rawAct g i))
        (h.toInputs_previous_entry i p) (h.toInputs_previous_entry (s.taskAction.rawAct g i) p))

theorem toTaskSymmetry_perm_entry (g : {g : ZFSet.{u} // g ∈ G})
    (i : {i : ZFSet.{u} // i ∈ I}) :
    ZFSet.pair (ZFSet.pair g.val i.val) ((s.toTaskSymmetry g).perm i).val ∈ T :=
  s.taskAction.rawAct_entry g i

theorem toTaskSymmetry_current_entry (g : {g : ZFSet.{u} // g ∈ G})
    (x : {x : ZFSet.{u} // x ∈ D} ⊕ d.templates.Fresh) :
    ZFSet.pair (ZFSet.pair g.val (d.coding.encode x))
      (d.coding.encode ((s.toTaskSymmetry g).current.toFun x)) ∈ A := s.current_entry g x

end CodedRecursiveTaskAction

end PartitionPilot.Forcing

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Forcing_GroundRowGenerics
attribute [-instance] _root_.OAI.PartitionPilot.Forcing.GroundMainPrefix.withTopSmall
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section



namespace PartitionPilot.Forcing.BoundedFormula

open SetFormula
universe u

def rowDistinguishingFormula {n} (p i j c y : Fin n) : BoundedFormula n :=
  exMem c (exMem y.succ (exMem y.succ.succ
    (.conj (.neg (.equal 1 0))
      (.conj (tripleMembershipFormula i.succ.succ.succ 2 1 p.succ.succ.succ)
        (tripleMembershipFormula j.succ.succ.succ 2 0 p.succ.succ.succ)))))

end PartitionPilot.Forcing.BoundedFormula

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

namespace BoundedFormula

def rowAssignmentActionEntryFormula {n} (z G Q C B J rowRange assignmentRange rowMaps assignmentMaps : Fin n) :
    BoundedFormula n :=
  let lift (i : Fin n) := i.succ.succ.succ.succ.succ.succ.succ.succ.succ
  exMem G (exMem Q.succ (exMem Q.succ.succ (exMem C.succ.succ.succ
    (exMem B.succ.succ.succ.succ (exMem C.succ.succ.succ.succ.succ
      (exMem B.succ.succ.succ.succ.succ.succ (exMem rowRange.succ.succ.succ.succ.succ.succ.succ
        (exMem assignmentRange.succ.succ.succ.succ.succ.succ.succ.succ
          (.conj (orderedTripleFormula (lift z) 8 7 6)
            (.conj (orderedPairFormula 7 5 4) (.conj (orderedPairFormula 6 3 2)
              (.conj (pairMembershipFormula 8 1 (lift rowMaps))
                (.conj (pairMembershipFormula 5 3 1)
                  (.conj (pairMembershipFormula 8 0 (lift assignmentMaps))
                    (relationImageEqualityFormula 2 4 (lift J) 0)))))))))))))))

theorem truth_rowAssignmentActionEntryFormula {n}
    (z G Q C B J rowRange assignmentRange rowMaps assignmentMaps : Fin n)
    (env : Fin n → ZFSet.{u}) :
    Truth (rowAssignmentActionEntryFormula z G Q C B J rowRange assignmentRange rowMaps assignmentMaps) env ↔
      ∃ g ∈ env G, ∃ x ∈ env Q, ∃ y ∈ env Q, ∃ p ∈ env C, ∃ A ∈ env B, ∃ q ∈ env C, ∃ D ∈ env B,
        ∃ rf ∈ env rowRange, ∃ af ∈ env assignmentRange,
          env z = ZFSet.pair (ZFSet.pair g x) y ∧ x = ZFSet.pair p A ∧ y = ZFSet.pair q D ∧
          ZFSet.pair g rf ∈ env rowMaps ∧ ZFSet.pair p q ∈ rf ∧
          ZFSet.pair g af ∈ env assignmentMaps ∧ D = relationImage A (env J) af := by
  simp only [rowAssignmentActionEntryFormula, truth_exMem, Truth, truth_orderedTripleFormula,
    truth_orderedPairFormula, truth_pairMembershipFormula, truth_relationImageEqualityFormula]
  rfl

end BoundedFormula

end PartitionPilot.Forcing

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Definability_SmallFunctionActionFormulas
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

namespace BoundedFormula

def renameActionFormula {n} (p q g x y a : Fin n) : BoundedFormula n :=
  .allMem x (.allMem x.succ (.allMem y.succ.succ
    (imp (tripleMembershipFormula g.succ.succ.succ 2 1 a.succ.succ.succ)
      (.conj (imp (pairMembershipFormula 2 0 p.succ.succ.succ) (pairMembershipFormula 1 0 q.succ.succ.succ))
        (imp (pairMembershipFormula 1 0 q.succ.succ.succ) (pairMembershipFormula 2 0 p.succ.succ.succ))))))

theorem truth_renameActionFormula {n} (p q g x y a : Fin n) (env : Fin n → ZFSet.{u}) :
    Truth (renameActionFormula p q g x y a) env ↔
      RenameActionRelation (env x) (env y) (env a) (env g) (env p) (env q) := by
  simp only [renameActionFormula, Truth, truth_imp, truth_tripleMembershipFormula, truth_pairMembershipFormula]
  constructor
  · intro h i hi j hj v hv rel
    exact ⟨(h i hi j hj v hv rel).1, (h i hi j hj v hv rel).2⟩
  · intro h i hi j hj v hv rel
    exact ⟨(h i hi j hj v hv rel).1, (h i hi j hj v hv rel).2⟩

def smallActionEntryFormula {n} (z g p x y a : Fin n) : BoundedFormula n :=
  exMem g (exMem p.succ (exMem p.succ.succ
    (.conj (orderedTripleFormula z.succ.succ.succ 2 1 0)
      (renameActionFormula 1 0 2 x.succ.succ.succ y.succ.succ.succ a.succ.succ.succ))))

theorem truth_smallActionEntryFormula {n} (z g p x y a : Fin n) (env : Fin n → ZFSet.{u}) :
    Truth (smallActionEntryFormula z g p x y a) env ↔
      ∃ h ∈ env g, ∃ r ∈ env p, ∃ s ∈ env p,
        env z = ZFSet.pair (ZFSet.pair h r) s ∧
          RenameActionRelation (env x) (env y) (env a) h r s := by
  simp only [smallActionEntryFormula, truth_exMem, Truth, truth_orderedTripleFormula, truth_renameActionFormula]
  rfl

end BoundedFormula

end PartitionPilot.Forcing

end

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



namespace PartitionPilot.Forcing

open SetRealization
universe u

@[instance_reducible]
def columnOrder (C : ZFSet.{u}) : PartialOrder (SetMembers C) where
  le := Eq
  le_refl _ := rfl
  le_trans _ _ _ := Eq.trans
  le_antisymm _ _ h _ := h

end PartitionPilot.Forcing



end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Definability_PrincipalSupportFormulas
attribute [-instance] _root_.OAI.PartitionPilot.Forcing.GroundMainPrefix.withTopSmall
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PartitionPilot.Forcing.BoundedFormula

open SetFormula SetRealization
universe u

def principalSupportFormula {n} (g c l r a : Fin n) : BoundedFormula n :=
  .allMem l (imp (pairMembershipFormula 0 c.succ r.succ)
    (tripleMembershipFormula g.succ 0 0 a.succ))

def principalSupportEntryFormula {n} (z l g r a : Fin n) : BoundedFormula n :=
  exMem l (exMem g.succ (.conj (orderedPairFormula z.succ.succ 1 0)
    (principalSupportFormula 0 1 l.succ.succ r.succ.succ a.succ.succ)))

theorem truth_principalSupportFormula {n} (g c l r a : Fin n) (env : Fin n → ZFSet.{u}) :
    Truth (principalSupportFormula g c l r a) env ↔
      ∀ x ∈ env l, ZFSet.pair x (env c) ∈ env r → ZFSet.pair (ZFSet.pair (env g) x) x ∈ env a := by
  simp only [principalSupportFormula, Truth, truth_imp, truth_pairMembershipFormula,
    truth_tripleMembershipFormula]
  rfl

theorem truth_principalSupportEntryFormula {n} (z l g r a : Fin n) (env : Fin n → ZFSet.{u}) :
    Truth (principalSupportEntryFormula z l g r a) env ↔
      ∃ c ∈ env l, ∃ h ∈ env g, env z = ZFSet.pair c h ∧
        ∀ x ∈ env l, ZFSet.pair x c ∈ env r → ZFSet.pair (ZFSet.pair h x) x ∈ env a := by
  simp only [principalSupportEntryFormula, truth_exMem, Truth, truth_orderedPairFormula,
    truth_principalSupportFormula]
  rfl

variable {G I : Type u} [Group G] [PartialOrder I]

theorem principalSupportEntry_correct (d : PosetAction G I) (b : Presentation I) (t : Presentation G)
    (z : ZFSet.{u}) :
    Truth (principalSupportEntryFormula 0 1 2 3 4)
      (extend z (extend b.carrier (extend t.carrier
        (extend b.conditionOrder (extend (d.actionGraph b t) Fin.elim0))))) ↔
      z ∈ supportBasisCode b t d.principalFix := by
  rw [truth_principalSupportEntryFormula, supportBasisCode, Presentation.mem_subset]
  constructor
  · rintro ⟨c, hc, h, hh, eq, fixed⟩
    obtain ⟨C, rfl⟩ := (b.mem_carrier c).1 hc
    obtain ⟨g, rfl⟩ := (t.mem_carrier h).1 hh
    refine ⟨(C, g), ?_, eq.symm⟩
    intro x lower
    exact (d.triple_mem_actionGraph b t g x x).1
      (fixed _ (b.encode_mem x) ((b.pair_mem_conditionOrder x C).2 lower))
  · rintro ⟨⟨C, g⟩, fixed, eq⟩
    refine ⟨b.encode C, b.encode_mem C, t.encode g, t.encode_mem g, eq.symm, ?_⟩
    intro x hx lower
    obtain ⟨y, rfl⟩ := (b.mem_carrier x).1 hx
    exact (d.triple_mem_actionGraph b t g y y).2 (fixed y ((b.pair_mem_conditionOrder y C).1 lower))

end PartitionPilot.Forcing.BoundedFormula

end

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
namespace SetFormula

def refinementClassCodeFormula : SetFormula 7 :=
  exactSetFormula 0 (reindex (extend 0 (fun j : Fin 6 => j.succ.succ)) refinementClassEntryFormula)

end SetFormula
end PartitionPilot.Forcing

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Definability_RefinementValidityCodes
attribute [-instance] _root_.OAI.PartitionPilot.Forcing.GroundMainPrefix.withTopSmall
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PartitionPilot.Forcing
universe u

namespace BoundedFormula
open SetFormula

def refinementValidityFormula : BoundedFormula 4 :=
  .conj (subsetFormula 0 3)
    (.conj (equivalenceRelationFormula 0 1)
      (.conj (equivalenceRelationFormula 0 2) (subsetFormula 1 2)))

end BoundedFormula

end PartitionPilot.Forcing

end

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Transfinite_GroundCountableProducts
attribute [-instance] _root_.OAI.PartitionPilot.Forcing.GroundMainPrefix.withTopSmall
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PartitionPilot.Forcing

universe u

namespace BoundedFormula

def relationProductEntryFormula {n} (z a b c d f g : Fin n) : BoundedFormula n :=
  let lift (i : Fin n) := i.succ.succ.succ.succ
  exMem a (exMem b.succ (exMem c.succ.succ (exMem d.succ.succ.succ
    (.conj (pairOfPairsFormula (lift z) 3 2 1 0)
      (.conj (pairMembershipFormula 3 1 (lift f)) (pairMembershipFormula 2 0 (lift g)))))))

theorem truth_relationProductEntryFormula {n} (z a b c d f g : Fin n)
    (env : Fin n → ZFSet.{u}) :
    Truth (relationProductEntryFormula z a b c d f g) env ↔
      ∃ x ∈ env a, ∃ y ∈ env b, ∃ p ∈ env c, ∃ q ∈ env d,
        env z = ZFSet.pair (ZFSet.pair x y) (ZFSet.pair p q) ∧
          ZFSet.pair x p ∈ env f ∧ ZFSet.pair y q ∈ env g := by
  simp only [relationProductEntryFormula, truth_exMem, Truth,
    truth_pairOfPairsFormula, truth_pairMembershipFormula]
  rfl

end BoundedFormula

namespace TransitiveGround

open SetFormula
variable (M : TransitiveGround.{u})

theorem relationProduct_mem
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    {A B C D f g : ZFSet.{u}} (hA : A ∈ M.sets) (hB : B ∈ M.sets)
    (hC : C ∈ M.sets) (hD : D ∈ M.sets) (hf : f ∈ M.sets) (hg : g ∈ M.sets) :
    relationProduct A B C D f g ∈ M.sets := by
  let params := extend A (extend B (extend C (extend D (extend f (extend g Fin.elim0)))))
  have selected := M.bounded_separation_mem separation
    (BoundedFormula.relationProductEntryFormula 0 1 2 3 4 5 6) params
    (Fin.cases hA (Fin.cases hB (Fin.cases hC (Fin.cases hD
      (Fin.cases hf (Fin.cases hg (fun i => Fin.elim0 i)))))))
    (M.prod_mem pairing unions powers separation
      (M.prod_mem pairing unions powers separation hA hB)
      (M.prod_mem pairing unions powers separation hC hD))
  have equal : ZFSet.sep (fun z => BoundedFormula.Truth
      (BoundedFormula.relationProductEntryFormula 0 1 2 3 4 5 6) (extend z params))
      (ZFSet.prod (ZFSet.prod A B) (ZFSet.prod C D)) = relationProduct A B C D f g := by
    apply ZFSet.ext
    intro z
    rw [ZFSet.mem_sep, relationProduct, ZFSet.mem_sep]
    exact and_congr Iff.rfl (BoundedFormula.truth_relationProductEntryFormula 0 1 2 3 4 5 6 _)
  exact equal ▸ selected

end TransitiveGround

end PartitionPilot.Forcing

end

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

namespace BoundedFormula

def pairedGraphEntryFormula {n} (z L H K f g : Fin n) : BoundedFormula n :=
  let lift (i : Fin n) := i.succ.succ.succ
  exMem L (exMem H.succ (exMem K.succ.succ
    (.conj (orderedRightTripleFormula (lift z) 2 1 0)
      (.conj (pairMembershipFormula 2 1 (lift f)) (pairMembershipFormula 2 0 (lift g))))))

theorem truth_pairedGraphEntryFormula {n} (z L H K f g : Fin n) (env : Fin n → ZFSet.{u}) :
    Truth (pairedGraphEntryFormula z L H K f g) env ↔
      env z ∈ pairedGraph (env L) (env H) (env K) (env f) (env g) := by
  simp only [pairedGraphEntryFormula, truth_exMem, Truth, truth_orderedRightTripleFormula,
    truth_pairMembershipFormula, mem_pairedGraph]
  rfl

end BoundedFormula

end PartitionPilot.Forcing

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
namespace BoundedFormula

theorem truth_assignmentCutFormula {n : Nat} (cut levels alpha A : Fin n)
    (env : Fin n → ZFSet.{u}) :
    Truth (assignmentCutFormula cut levels alpha A) env ↔
      env cut = assignmentCut (env levels) (env alpha) (env A) := by
  simp only [assignmentCutFormula, Truth, truth_exMem, truth_pairMembershipFormula,
    truth_imp, extend]
  constructor
  · rintro ⟨forward, backward⟩
    apply ZFSet.ext
    intro z
    rw [mem_assignmentCut]
    exact ⟨forward z, fun h => backward z h.1 h.2⟩
  · intro equal
    constructor
    · intro z hz
      exact (mem_assignmentCut _ _ _ z).1 (equal ▸ hz)
    · intro z hz lower
      change z ∈ env cut
      rw [equal]
      exact (mem_assignmentCut _ _ _ z).2 ⟨hz, lower⟩

end BoundedFormula

end PartitionPilot.Forcing



end

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

def stageOneForcingFormula {n : Nat} (phi : SetFormula n) : SetFormula (n + 3) :=
  forcingTranslation (ordinaryGroundPrimitives (0 : Fin 2) 1) phi
    (extend 1 (extend 2 Fin.elim0)) 0 (fun j => j.succ.succ.succ)

end SetFormula

def stageOneRawForces (M : TransitiveGround.{u}) (P r p : ZFSet.{u})
    {n : Nat} (phi : SetFormula n) (names : Fin n → ZFSet.{u}) : Prop :=
  Realize M.sets (stageOneForcingFormula phi) (extend p (extend P (extend r names)))

def stageOneRawClass (M : TransitiveGround.{u}) (T P r top R w c : ZFSet.{u}) : Prop :=
  Realize M.sets refinementClassCodeFormula
    (extend c (extend T (extend R (extend w (extend P (extend r (extend top Fin.elim0)))))))

end PartitionPilot.Forcing



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

def stageOneRawProfile (M : TransitiveGround.{u}) (P r lower nodes nodeOrder visibility E bu aw : ZFSet.{u}) : Prop :=
  ∀ v ∈ nodes, ZFSet.pair E v ∈ nodeOrder →
    ∃ V ∈ M.sets, ZFSet.pair v V ∈ visibility ∧
      stageOneRawForces M P r lower refinementProfileFormula ![bu, aw, V]

def stageOneRawCompatibility (M : TransitiveGround.{u}) (P r lower visibility maps C idx bu aw : ZFSet.{u}) : Prop :=
  ∃ V ∈ M.sets, ∃ D ∈ M.sets, ZFSet.pair C V ∈ visibility ∧ ZFSet.pair idx D ∈ maps ∧
    stageOneRawForces M P r lower refinementCompatibilityFormula ![aw, V, bu, D]

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
open SetFormula
universe u

theorem TransitiveGround.groundEmbeddable_retarget {M : TransitiveGround.{u}} {A B C : ZFSet.{u}}
    (small : M.groundEmbeddable A B) (subset : B ⊆ C) : M.groundEmbeddable A C := by
  obtain ⟨f, hf, code⟩ := small
  exact ⟨f, hf, code.retarget subset⟩

namespace GroundBelow
variable {M : TransitiveGround.{u}} {A B K : ZFSet.{u}}

theorem common_bound (first : GroundBelow M A K) (second : GroundBelow M B K)
    (ordinal : ordinalSetProperty K) :
    ∃ γ ∈ K, M.groundEmbeddable A γ ∧ M.groundEmbeddable B γ := by
  obtain ⟨α, hα, first⟩ := first
  obtain ⟨β, hβ, second⟩ := second
  obtain ⟨γ, hγ, left, right⟩ := ordinalSetProperty_pair_bound ordinal hα hβ
  exact ⟨γ, hγ, TransitiveGround.groundEmbeddable_retarget first left, TransitiveGround.groundEmbeddable_retarget second right⟩

theorem of_member
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (hK : K ∈ M.sets) (hA : A ∈ K) : GroundBelow M A K :=
  ⟨A, hA, identityFunctionGraph A,
    M.identityFunctionGraph_mem pairing unions powers separation (M.transitive hK hA),
    identityFunctionGraph_injection A⟩

end GroundBelow

end PartitionPilot.Forcing



end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Forcing_GroundProductSizeWitnesses
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

theorem groundEmbeddable_product_targets
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    {A B C D : ZFSet.{u}} (hA : A ∈ M.sets) (hB : B ∈ M.sets)
    (hC : C ∈ M.sets) (hD : D ∈ M.sets)
    (first : M.groundEmbeddable A C) (second : M.groundEmbeddable B D) :
    M.groundEmbeddable (ZFSet.prod A B) (ZFSet.prod C D) := by
  obtain ⟨f, hf, first⟩ := first
  obtain ⟨g, hg, second⟩ := second
  exact ⟨relationProduct A B C D f g,
    M.relationProduct_mem pairing unions powers separation hA hB hC hD hf hg,
    relationProduct_injection first second⟩

theorem square_subset_groundPower_twice
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    {A : ZFSet.{u}} (hA : A ∈ M.sets) :
    ZFSet.prod A A ⊆ M.groundPower (M.groundPower A) := by
  intro z hz
  obtain ⟨x, hx, y, hy, rfl⟩ := ZFSet.mem_prod.1 hz
  have hxM := M.transitive hA hx
  have hyM := M.transitive hA hy
  apply (M.mem_groundPower _ _).2
  refine ⟨M.orderedPair_mem pairing hxM hyM, ?_⟩
  intro t ht
  rcases ZFSet.mem_pair.1 ht with rfl | rfl
  · apply (M.mem_groundPower _ _).2
    refine ⟨?_, ?_⟩
    · simpa only [ZFSet.pair_eq_singleton] using M.unorderedPair_mem pairing hxM hxM
    · intro w hw
      exact (ZFSet.mem_singleton.1 hw) ▸ hx
  · apply (M.mem_groundPower _ _).2
    refine ⟨M.unorderedPair_mem pairing hxM hyM, ?_⟩
    intro w hw
    rcases ZFSet.mem_pair.1 hw with rfl | rfl
    · exact hx
    · exact hy

end PartitionPilot.Forcing.TransitiveGround

end

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Definability_GroundBelowRelationSpaces
attribute [-instance] _root_.OAI.PartitionPilot.Forcing.GroundMainPrefix.withTopSmall
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PartitionPilot.Forcing.GroundBelow
open SetFormula
universe u
variable {M : TransitiveGround.{u}} {A B K : ZFSet.{u}}

theorem product
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (hA : A ∈ M.sets) (hB : B ∈ M.sets) (hK : K ∈ M.sets)
    (ordinal : ordinalSetProperty K) (strong : GroundStrongLimit M K)
    (first : GroundBelow M A K) (second : GroundBelow M B K) :
    GroundBelow M (ZFSet.prod A B) K := by
  obtain ⟨γ, hγ, first, second⟩ := first.common_bound second ordinal
  have hγM := M.transitive hK hγ
  have squareGround := M.prod_mem pairing unions powers separation hγM hγM
  have powerGround := M.groundPower_mem powers hγM
  have twice := strong.power_closed pairing unions powers separation powerGround hK (strong γ hγ)
  have square := twice.restrict separation squareGround hK (M.square_subset_groundPower_twice pairing hγM)
  exact square.of_embeddable pairing unions powers separation
    (M.prod_mem pairing unions powers separation hA hB) squareGround hK
    (M.groundEmbeddable_product_targets pairing unions powers separation hA hB hγM hγM first second)

end PartitionPilot.Forcing.GroundBelow



end

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Geometry_GroundMeetGeneratorSteps
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

namespace BoundedFormula

def meetGeneratorStepFormula {n} (z P μ A : Fin n) : BoundedFormula n :=
  .exMem P (.exMem P.succ (.exMem A.succ.succ
    (.conj (orderedPairFormula z.succ.succ.succ 2 1)
      (tripleMembershipFormula 2 0 1 μ.succ.succ.succ))))

end BoundedFormula

end PartitionPilot.Forcing

end

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Geometry_GroundHeightPushforward
attribute [-instance] _root_.OAI.PartitionPilot.Forcing.GroundMainPrefix.withTopSmall
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PartitionPilot.Forcing
open SetFormula SetRealization
open Compression.RecursiveMaps Attachment CosetGeometry
universe u

namespace BoundedFormula

def flatCopyEmbeddingEntryFormula {n} (z U Q classifier w : Fin n) : BoundedFormula n :=
  exMem U (exMem Q.succ (.conj (orderedPairFormula z.succ.succ 1 0)
    (tripleMembershipFormula w.succ.succ 1 0 classifier.succ.succ)))

theorem truth_flatCopyEmbeddingEntryFormula {n}
    (z U Q classifier w : Fin n) (env : Fin n → ZFSet.{u}) :
    Truth (flatCopyEmbeddingEntryFormula z U Q classifier w) env ↔
      ∃ x ∈ env U, ∃ y ∈ env Q, env z = ZFSet.pair x y ∧
        ZFSet.pair (ZFSet.pair (env w) x) y ∈ env classifier := by
  simp only [flatCopyEmbeddingEntryFormula, Truth, truth_exMem, truth_orderedPairFormula,
    truth_tripleMembershipFormula]
  rfl

end BoundedFormula

end PartitionPilot.Forcing

namespace PartitionPilot.Forcing
open SetFormula
universe u

noncomputable def pushedHeightGraph (A B H e h : ZFSet.{u}) : ZFSet.{u} :=
  relationCompose (relationImage A B e) A H (relationConverse A B e) h

theorem pushedHeightGraph_entry {A B H e h x y z : ZFSet.{u}}
    (embedding : InjectionCode A B e) (height : ZFSet.IsFunc A H h)
    (copy : ZFSet.pair x y ∈ e) :
    ZFSet.pair y z ∈ pushedHeightGraph A B H e h ↔ ZFSet.pair x z ∈ h := by
  have bounds := ZFSet.pair_mem_prod.1 (embedding.function.1 copy)
  rw [pushedHeightGraph, pair_mem_relationCompose]
  constructor
  · rintro ⟨_, _, a, _, inverse, entry⟩
    have copied := (pair_mem_relationConverse _ _ _ _ _).1 inverse
    have same := embedding.injective a x y copied.2.2 copy
    exact same ▸ entry
  · intro entry
    exact ⟨(mem_relationImage A B e y).2 ⟨bounds.2, x, bounds.1, copy⟩,
      (ZFSet.pair_mem_prod.1 (height.1 entry)).2, x, bounds.1,
      (pair_mem_relationConverse A B e x y).2 ⟨bounds.1, bounds.2, copy⟩, entry⟩

theorem pushedHeightGraph_function {A B H e h : ZFSet.{u}}
    (embedding : InjectionCode A B e) (height : ZFSet.IsFunc A H h) :
    ZFSet.IsFunc (relationImage A B e) H (pushedHeightGraph A B H e h) :=
  relationCompose_function_of_subset embedding.converse_image.function height (fun _ hx => hx)

end PartitionPilot.Forcing

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



namespace PartitionPilot.Forcing

universe u






namespace BoundedFormula

open SetFormula

def indexedTaskActionEntryFormula {n} (z G I P T : Fin n) : BoundedFormula n :=
  let lift (j : Fin n) := j.succ.succ.succ.succ
  exMem G (exMem I.succ (exMem I.succ.succ (exMem P.succ.succ.succ
    (.conj (nestedActionTripleFormula (lift z) 3 2 0 1 0)
      (tripleMembershipFormula 3 2 1 (lift T))))))

theorem truth_indexedTaskActionEntryFormula {n} (z G I P T : Fin n)
    (env : Fin n → ZFSet.{u}) :
    Truth (indexedTaskActionEntryFormula z G I P T) env ↔
      ∃ g ∈ env G, ∃ i ∈ env I, ∃ j ∈ env I, ∃ q ∈ env P,
        env z = ZFSet.pair (ZFSet.pair g (ZFSet.pair i q)) (ZFSet.pair j q) ∧
          ZFSet.pair (ZFSet.pair g i) j ∈ env T := by
  simp only [indexedTaskActionEntryFormula, truth_exMem, Truth,
    truth_nestedActionTripleFormula, truth_tripleMembershipFormula]
  rfl

end BoundedFormula

namespace TransitiveGround

open SetFormula

theorem indexedTaskActionGraph_mem (M : TransitiveGround.{u})
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    {G I P N T : ZFSet.{u}} (hG : G ∈ M.sets) (hI : I ∈ M.sets)
    (hP : P ∈ M.sets) (hN : N ∈ M.sets) (hT : T ∈ M.sets) :
    indexedTaskActionGraph G I P N T ∈ M.sets := by
  let params := extend G (extend I (extend P (extend T Fin.elim0)))
  have selected := M.bounded_separation_mem separation
    (BoundedFormula.indexedTaskActionEntryFormula 0 1 2 3 4) params
    (Fin.cases hG (Fin.cases hI (Fin.cases hP (Fin.cases hT (fun i => Fin.elim0 i)))))
    (M.prod_mem pairing unions powers separation
      (M.prod_mem pairing unions powers separation hG hN) hN)
  have equal : ZFSet.sep (fun z => BoundedFormula.Truth
      (BoundedFormula.indexedTaskActionEntryFormula 0 1 2 3 4) (extend z params))
      (ZFSet.prod (ZFSet.prod G N) N) = indexedTaskActionGraph G I P N T := by
    apply ZFSet.ext
    intro z
    rw [ZFSet.mem_sep, indexedTaskActionGraph, ZFSet.mem_sep]
    exact and_congr Iff.rfl (BoundedFormula.truth_indexedTaskActionEntryFormula 0 1 2 3 4 _)
  exact equal ▸ selected

end TransitiveGround

end PartitionPilot.Forcing



namespace PartitionPilot.Forcing.CodedRecursiveMapInputs

universe u
variable {D rD μD J Qs rs μs As Es Fs Ss I Maps Sources Reps G m inv one A : ZFSet.{u}}
variable {d : AttachmentBatchInputs D rD μD J Qs rs μs As Es Fs Ss}
variable (h : CodedRecursiveMapInputs d I Maps Sources Reps G m inv one A)

noncomputable abbrev nextFreshSet :=
  indexedAttachmentFresh h.nextIndices (pairSecondField I J h.nextIndices Qs)
    (pairSecondField I J h.nextIndices rs) (pairSecondField I J h.nextIndices As)

noncomputable def nextIndexAction (T : ZFSet.{u}) :=
  indexedTaskActionGraph G I J h.nextIndices T

noncomputable def nextFreshAction (T : ZFSet.{u}) :=
  indexedTaskActionGraph G h.nextIndices (familyPointBound Qs) h.nextFreshSet (h.nextIndexAction T)

noncomputable def nextActionGraph (T : ZFSet.{u}) :=
  taggedActionGraph G d.batchCarrier h.nextFreshSet A (h.nextFreshAction T)

theorem nextFreshSet_shape : h.nextFreshSet ⊆ ZFSet.prod h.nextIndices (familyPointBound Qs) := by
  intro z fresh
  obtain ⟨i, _, j, _, q, rfl, index, oldFresh⟩ := recursiveFresh_shape
    (recursiveAttachmentIndices_subset I J D (⋃₀ ⋃₀ Fs) Sources Fs) fresh
  have bounds := ZFSet.pair_mem_prod.1 (indexedAttachmentDomain_subset J Qs
    (indexedAttachmentFresh_subset J Qs rs As oldFresh))
  exact ZFSet.pair_mem_prod.2 ⟨index, bounds.2⟩

variable {T : ZFSet.{u}} (task : SetActionCode G I m one T)
variable (sourceInvariant : ∀ g i j a b, ZFSet.pair (ZFSet.pair g i) j ∈ T →
  ZFSet.pair i a ∈ Sources → ZFSet.pair j b ∈ Sources → a = b)

include task sourceInvariant in
theorem nextIndices_closed {g i i' j : ZFSet.{u}}
    (entry : ZFSet.pair (ZFSet.pair g i) i' ∈ T)
    (index : ZFSet.pair i j ∈ h.nextIndices) : ZFSet.pair i' j ∈ h.nextIndices := by
  have bounds := task.entry_shape entry
  have hj := (ZFSet.pair_mem_prod.1
    (recursiveAttachmentIndices_subset I J D (⋃₀ ⋃₀ Fs) Sources Fs index)).2
  let a := h.source ⟨i, bounds.2.1⟩
  let b := h.source ⟨i', bounds.2.2⟩
  let f := d.filter ⟨j, hj⟩
  have equal : a.val = b.val := sourceInvariant g i i' a.val b.val entry
    (h.source_entry ⟨i, bounds.2.1⟩) (h.source_entry ⟨i', bounds.2.2⟩)
  have negative : a.val ∉ f := (recursiveAttachmentIndices_entry_iff h.sources d.filters.to_isFunc
    (h.source_entry ⟨i, bounds.2.1⟩) (d.filter_entry ⟨j, hj⟩)).1 index
  exact (recursiveAttachmentIndices_entry_iff h.sources d.filters.to_isFunc
    (h.source_entry ⟨i', bounds.2.2⟩) (d.filter_entry ⟨j, hj⟩)).2 (equal ▸ negative)

include task sourceInvariant in
theorem nextIndexAction_setAction : SetActionCode G h.nextIndices m one (h.nextIndexAction T) :=
  indexedTaskActionGraph_setAction task
    (recursiveAttachmentIndices_subset I J D (⋃₀ ⋃₀ Fs) Sources Fs)
    (fun _ _ _ _ _ _ _ _ index entry => h.nextIndices_closed task sourceInvariant entry index)

include task sourceInvariant in
theorem nextFreshAction_setAction : SetActionCode G h.nextFreshSet m one (h.nextFreshAction T) := by
  apply indexedTaskActionGraph_setAction (h.nextIndexAction_setAction task sourceInvariant) h.nextFreshSet_shape
  intro g _ k _ k' hk' q _ fresh entry
  obtain ⟨_, _, _, i, hi, i', hi', j, hj, rfl, rfl, _⟩ :=
    (triple_mem_indexedTaskActionGraph G I J h.nextIndices T g k k').1 entry
  exact (recursiveFresh_iff hi' hj).2 ⟨hk', ((recursiveFresh_iff hi hj).1 fresh).2⟩

include task sourceInvariant in
theorem nextAction_setAction (M : TransitiveGround.{u}) (next : h.NextInputs M) :
    SetActionCode G next.batchCarrier m one (h.nextActionGraph T) :=
  h.action.toSetAction.tagged (h.nextFreshAction_setAction task sourceInvariant)

theorem nextAction_old_iff {g x y : ZFSet.{u}} (hx : x ∈ d.batchCarrier) :
    ZFSet.pair (ZFSet.pair g x) y ∈ h.nextActionGraph T ↔
      ZFSet.pair (ZFSet.pair g x) y ∈ A := taggedActionGraph_old_iff hx

include task sourceInvariant in
theorem nextAction_fresh_pair_iff {g q t : ZFSet.{u}} :
    ZFSet.pair (ZFSet.pair g (ZFSet.pair d.batchCarrier q)) (ZFSet.pair d.batchCarrier t) ∈
      h.nextActionGraph T ↔ ZFSet.pair (ZFSet.pair g q) t ∈ h.nextFreshAction T :=
  taggedActionGraph_fresh_pair_iff h.action.toSetAction (h.nextFreshAction_setAction task sourceInvariant)

include task in
theorem nextFreshAction_pair_iff {g i i' j q : ZFSet.{u}}
    (source : ZFSet.pair (ZFSet.pair i j) q ∈ h.nextFreshSet)
    (target : ZFSet.pair (ZFSet.pair i' j) q ∈ h.nextFreshSet) :
    ZFSet.pair (ZFSet.pair g (ZFSet.pair (ZFSet.pair i j) q))
      (ZFSet.pair (ZFSet.pair i' j) q) ∈ h.nextFreshAction T ↔
      ZFSet.pair (ZFSet.pair g i) i' ∈ T := by
  have sb := ZFSet.pair_mem_prod.1 (h.nextFreshSet_shape source)
  have tb := ZFSet.pair_mem_prod.1 (h.nextFreshSet_shape target)
  have si := ZFSet.pair_mem_prod.1
    (recursiveAttachmentIndices_subset I J D (⋃₀ ⋃₀ Fs) Sources Fs sb.1)
  have ti := ZFSet.pair_mem_prod.1
    (recursiveAttachmentIndices_subset I J D (⋃₀ ⋃₀ Fs) Sources Fs tb.1)
  rw [nextFreshAction, indexedTaskActionGraph_entry_iff, nextIndexAction,
    indexedTaskActionGraph_entry_iff]
  constructor
  · exact fun entry => entry.2.2.2.2.2.2.2.2.2.2.2.2.2.2
  · intro entry
    have hg := (task.entry_shape entry).1
    exact ⟨hg, sb.1, tb.1, sb.2, rfl, source, target,
      hg, si.1, ti.1, si.2, rfl, sb.1, tb.1, entry⟩

include task sourceInvariant in
theorem nextFreshSet_closed {g i i' j q : ZFSet.{u}}
    (entry : ZFSet.pair (ZFSet.pair g i) i' ∈ T)
    (source : ZFSet.pair (ZFSet.pair i j) q ∈ h.nextFreshSet) :
    ZFSet.pair (ZFSet.pair i' j) q ∈ h.nextFreshSet := by
  have bounds := task.entry_shape entry
  have index := (ZFSet.pair_mem_prod.1 (h.nextFreshSet_shape source)).1
  have hj := (ZFSet.pair_mem_prod.1
    (recursiveAttachmentIndices_subset I J D (⋃₀ ⋃₀ Fs) Sources Fs index)).2
  exact (recursiveFresh_iff bounds.2.2 hj).2
    ⟨h.nextIndices_closed task sourceInvariant entry index,
      ((recursiveFresh_iff bounds.2.1 hj).1 source).2⟩

include task sourceInvariant in
theorem nextAction_fresh_entry {g i i' j q : ZFSet.{u}}
    (entry : ZFSet.pair (ZFSet.pair g i) i' ∈ T)
    (source : ZFSet.pair (ZFSet.pair i j) q ∈ h.nextFreshSet) :
    ZFSet.pair (ZFSet.pair g (ZFSet.pair d.batchCarrier (ZFSet.pair (ZFSet.pair i j) q)))
      (ZFSet.pair d.batchCarrier (ZFSet.pair (ZFSet.pair i' j) q)) ∈ h.nextActionGraph T :=
  (h.nextAction_fresh_pair_iff task sourceInvariant).2
    ((h.nextFreshAction_pair_iff task source
      (h.nextFreshSet_closed task sourceInvariant entry source)).2 entry)

end PartitionPilot.Forcing.CodedRecursiveMapInputs



namespace PartitionPilot.Forcing.CodedRecursiveMapInputs

open SetFormula
universe u
variable {D rD μD J Qs rs μs As Es Fs Ss I Maps Sources Reps G m inv one A : ZFSet.{u}}
variable {d : AttachmentBatchInputs D rD μD J Qs rs μs As Es Fs Ss}
variable (h : CodedRecursiveMapInputs d I Maps Sources Reps G m inv one A)
variable (M : TransitiveGround.{u})

theorem nextIndices_mem
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (hI : I ∈ M.sets) (hJ : J ∈ M.sets) (hD : D ∈ M.sets)
    (hFs : Fs ∈ M.sets) (hSources : Sources ∈ M.sets) : h.nextIndices ∈ M.sets :=
  M.recursiveAttachmentIndices_mem pairing unions powers separation hI hJ hD
    (M.union_mem unions (M.union_mem unions hFs)) hSources hFs

theorem nextFreshSet_mem
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (hI : I ∈ M.sets) (hJ : J ∈ M.sets) (hD : D ∈ M.sets)
    (hQs : Qs ∈ M.sets) (hrs : rs ∈ M.sets) (hAs : As ∈ M.sets)
    (hFs : Fs ∈ M.sets) (hSources : Sources ∈ M.sets) : h.nextFreshSet ∈ M.sets := by
  have hK := h.nextIndices_mem M pairing unions powers separation hI hJ hD hFs hSources
  have field : ∀ F ∈ M.sets, pairSecondField I J h.nextIndices F ∈ M.sets := by
    intro F hF
    exact M.pairFieldGraph_mem pairing unions powers separation false hI hJ hK
      (M.union_mem unions (M.union_mem unions hF)) hF
  exact M.indexedAttachmentFresh_mem pairing unions powers separation hK
    (field Qs hQs) (field rs hrs) (field As hAs)

theorem nextIndexAction_mem
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    {T : ZFSet.{u}} (hI : I ∈ M.sets) (hJ : J ∈ M.sets) (hD : D ∈ M.sets)
    (hFs : Fs ∈ M.sets) (hSources : Sources ∈ M.sets)
    (hG : G ∈ M.sets) (hT : T ∈ M.sets) : h.nextIndexAction T ∈ M.sets :=
  M.indexedTaskActionGraph_mem pairing unions powers separation hG hI hJ
    (h.nextIndices_mem M pairing unions powers separation hI hJ hD hFs hSources) hT

theorem nextFreshAction_mem
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    {T : ZFSet.{u}} (hI : I ∈ M.sets) (hJ : J ∈ M.sets) (hD : D ∈ M.sets)
    (hQs : Qs ∈ M.sets) (hrs : rs ∈ M.sets) (hAs : As ∈ M.sets)
    (hFs : Fs ∈ M.sets) (hSources : Sources ∈ M.sets)
    (hG : G ∈ M.sets) (hT : T ∈ M.sets) : h.nextFreshAction T ∈ M.sets :=
  M.indexedTaskActionGraph_mem pairing unions powers separation hG
    (h.nextIndices_mem M pairing unions powers separation hI hJ hD hFs hSources)
    (M.familyPointBound_mem unions hQs)
    (h.nextFreshSet_mem M pairing unions powers separation hI hJ hD hQs hrs hAs hFs hSources)
    (h.nextIndexAction_mem M pairing unions powers separation hI hJ hD hFs hSources hG hT)

theorem nextActionGraph_mem
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    {T : ZFSet.{u}} (hI : I ∈ M.sets) (hJ : J ∈ M.sets) (hD : D ∈ M.sets)
    (hL : d.batchCarrier ∈ M.sets)
    (hQs : Qs ∈ M.sets) (hrs : rs ∈ M.sets) (hAs : As ∈ M.sets)
    (hFs : Fs ∈ M.sets) (hSources : Sources ∈ M.sets)
    (hG : G ∈ M.sets) (hA : A ∈ M.sets) (hT : T ∈ M.sets) :
    h.nextActionGraph T ∈ M.sets :=
  M.taggedActionGraph_mem pairing unions powers separation hG hL
    (h.nextFreshSet_mem M pairing unions powers separation hI hJ hD hQs hrs hAs hFs hSources) hA
    (h.nextFreshAction_mem M pairing unions powers separation hI hJ hD hQs hrs hAs hFs hSources hG hT)

end PartitionPilot.Forcing.CodedRecursiveMapInputs

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Definability_LiftedCompressionFormulas
attribute [-instance] _root_.OAI.PartitionPilot.Forcing.GroundMainPrefix.withTopSmall
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PartitionPilot.Forcing.BoundedFormula

open SetFormula
universe u

theorem truth_rightTripleFormula {n} (z a b c : Fin n) (env : Fin n → ZFSet.{u}) :
    Truth (rightTripleFormula z a b c) env ↔
      env z = ZFSet.pair (env a) (ZFSet.pair (env b) (env c)) := by
  simp only [rightTripleFormula, truth_exMem, Truth, truth_orderedPairFormula]
  change (∃ s ∈ env z, ∃ t ∈ s, t = ZFSet.pair (env b) (env c) ∧
    env z = ZFSet.pair (env a) t) ↔ _
  constructor
  · rintro ⟨_, _, _, _, rfl, equal⟩
    exact equal
  · intro equal
    refine ⟨{env a, ZFSet.pair (env b) (env c)}, ?_, ZFSet.pair (env b) (env c),
      ZFSet.mem_pair.2 (Or.inr rfl), rfl, equal⟩
    rw [equal]
    exact ZFSet.mem_pair.2 (Or.inr rfl)

def taggedPairTripleFormula {n} (z l i j q : Fin n) : BoundedFormula n :=
  exMem z (exMem 0 (.conj (orderedTripleFormula 0 i.succ.succ j.succ.succ q.succ.succ)
    (orderedPairFormula z.succ.succ l.succ.succ 0)))

theorem truth_taggedPairTripleFormula {n} (z l i j q : Fin n) (env : Fin n → ZFSet.{u}) :
    Truth (taggedPairTripleFormula z l i j q) env ↔
      env z = ZFSet.pair (env l) (ZFSet.pair (ZFSet.pair (env i) (env j)) (env q)) := by
  simp only [taggedPairTripleFormula, truth_exMem, Truth, truth_orderedTripleFormula,
    truth_orderedPairFormula]
  change (∃ s ∈ env z, ∃ t ∈ s, t = ZFSet.pair (ZFSet.pair (env i) (env j)) (env q) ∧
    env z = ZFSet.pair (env l) t) ↔ _
  constructor
  · rintro ⟨_, _, _, _, rfl, equal⟩
    exact equal
  · intro equal
    refine ⟨{env l, ZFSet.pair (ZFSet.pair (env i) (env j)) (env q)}, ?_,
      ZFSet.pair (ZFSet.pair (env i) (env j)) (env q),
      ZFSet.mem_pair.2 (Or.inr rfl), rfl, equal⟩
    rw [equal]
    exact ZFSet.mem_pair.2 (Or.inr rfl)

theorem truth_liftOldEntryFormula {n} (d maps bound i x y : Fin n)
    (env : Fin n → ZFSet.{u}) :
    Truth (liftOldEntryFormula d maps bound i x y) env ↔
      env x ∈ env d ∧ ∃ S ∈ env bound,
        ZFSet.pair (env i) S ∈ env maps ∧ ZFSet.pair (env x) (env y) ∈ S := by
  simp only [liftOldEntryFormula, Truth, truth_exMem, truth_pairMembershipFormula]
  rfl

def liftFreshEntryFormula {n} (d l j b ns sources fs bound reps g action i x y : Fin n) : BoundedFormula n :=
  let up (t : Fin n) := t.succ.succ.succ.succ
  exMem j (exMem b.succ (exMem d.succ.succ (exMem bound.succ.succ.succ
    (.conj (rightTripleFormula (up x) (up d) 3 2)
      (.conj (pairMembershipFormula 3 2 (up ns))
        (.conj (pairMembershipFormula (up i) 1 (up sources))
          (.conj (pairMembershipFormula 3 0 (up fs))
            (disj (.conj (.mem 1 0) (exMem (up g)
              (.conj (pairMembershipFormula (up i).succ 0 (up reps).succ)
                (tripleMembershipFormula 0 (up x).succ (up y).succ (up action).succ))))
              (.conj (.neg (.mem 1 0)) (taggedPairTripleFormula (up y) (up l) (up i) 3 2))))))))))

theorem truth_liftFreshEntryFormula {n} (d l j b ns sources fs bound reps g action i x y : Fin n)
    (env : Fin n → ZFSet.{u}) :
    Truth (liftFreshEntryFormula d l j b ns sources fs bound reps g action i x y) env ↔
      ∃ h ∈ env j, ∃ q ∈ env b, ∃ a ∈ env d, ∃ F ∈ env bound,
        env x = ZFSet.pair (env d) (ZFSet.pair h q) ∧ ZFSet.pair h q ∈ env ns ∧
        ZFSet.pair (env i) a ∈ env sources ∧ ZFSet.pair h F ∈ env fs ∧
        ((a ∈ F ∧ ∃ actor ∈ env g, ZFSet.pair (env i) actor ∈ env reps ∧
          ZFSet.pair (ZFSet.pair actor (env x)) (env y) ∈ env action) ∨
          (a ∉ F ∧ env y = ZFSet.pair (env l) (ZFSet.pair (ZFSet.pair (env i) h) q))) := by
  simp only [liftFreshEntryFormula, truth_exMem, Truth, truth_disj,
    truth_rightTripleFormula, truth_pairMembershipFormula, truth_tripleMembershipFormula,
    truth_taggedPairTripleFormula]
  rfl

def liftedCompressionEntryFormula {n} (z i j d l c ns b maps sources fs reps g action v w : Fin n) :
    BoundedFormula n :=
  let up (t : Fin n) := t.succ.succ.succ
  exMem i (exMem l.succ (exMem c.succ.succ
    (.conj (orderedTripleFormula (up z) 2 1 0)
      (disj (liftOldEntryFormula (up d) (up maps) (up v) 2 1 0)
        (liftFreshEntryFormula (up d) (up l) (up j) (up b) (up ns)
          (up sources) (up fs) (up w) (up reps) (up g) (up action) 2 1 0)))))

theorem truth_liftedCompressionEntryFormula {n} (z i j d l c ns b maps sources fs reps g action v w : Fin n)
    (env : Fin n → ZFSet.{u}) (mapsBound : env v = ZFSet.sUnion (ZFSet.sUnion (env maps)))
    (filterBound : env w = ZFSet.sUnion (ZFSet.sUnion (env fs))) :
    Truth (liftedCompressionEntryFormula z i j d l c ns b maps sources fs reps g action v w) env ↔
      ∃ task ∈ env i, ∃ x ∈ env l, ∃ y ∈ env c,
        env z = ZFSet.pair (ZFSet.pair task x) y ∧
          (liftOldEntry (env d) (env maps) task x y ∨
            liftFreshEntry (env d) (env l) (env j) (env b) (env ns)
              (env sources) (env fs) (env reps) (env g) (env action) task x y) := by
  simp only [liftedCompressionEntryFormula, truth_exMem, Truth, truth_disj,
    truth_orderedTripleFormula, truth_liftOldEntryFormula, truth_liftFreshEntryFormula]
  simp only [liftOldEntry, liftFreshEntry, extend, Fin.cases_succ, Fin.cases_zero,
    mapsBound, filterBound]
  rfl

end PartitionPilot.Forcing.BoundedFormula

end

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Geometry_GroundLiftedCompressionGraphs
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

theorem liftedCompressionGraph_mem
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    {I J D L C N B Maps Sources Fs Reps G A : ZFSet.{u}}
    (hI : I ∈ M.sets) (hJ : J ∈ M.sets) (hD : D ∈ M.sets)
    (hL : L ∈ M.sets) (hC : C ∈ M.sets) (hN : N ∈ M.sets) (hB : B ∈ M.sets)
    (hMaps : Maps ∈ M.sets) (hSources : Sources ∈ M.sets) (hFs : Fs ∈ M.sets)
    (hReps : Reps ∈ M.sets) (hG : G ∈ M.sets) (hA : A ∈ M.sets) :
    liftedCompressionGraph I J D L C N B Maps Sources Fs Reps G A ∈ M.sets := by
  have hV := M.union_mem unions (M.union_mem unions hMaps)
  have hW := M.union_mem unions (M.union_mem unions hFs)
  let params := extend (I) (extend (J) (extend (D) (extend (L) (extend (C) (extend (N) (extend (B) (extend (Maps) (extend (Sources) (extend (Fs) (extend (Reps) (extend (G) (extend (A) (extend (ZFSet.sUnion (ZFSet.sUnion Maps)) (extend (ZFSet.sUnion (ZFSet.sUnion Fs)) (Fin.elim0)))))))))))))))
  have selected := M.bounded_separation_mem separation
    (BoundedFormula.liftedCompressionEntryFormula 0 1 2 3 4 5 6 7 8 9 10 11 12 13 14 15) params
    (Fin.cases hI (Fin.cases hJ (Fin.cases hD (Fin.cases hL (Fin.cases hC (Fin.cases hN (Fin.cases hB (Fin.cases hMaps (Fin.cases hSources (Fin.cases hFs (Fin.cases hReps (Fin.cases hG (Fin.cases hA (Fin.cases hV (Fin.cases hW (fun i => Fin.elim0 i))))))))))))))))
    (M.prod_mem pairing unions powers separation
      (M.prod_mem pairing unions powers separation hI hL) hC)
  have equal : ZFSet.sep (fun z => BoundedFormula.Truth
      (BoundedFormula.liftedCompressionEntryFormula 0 1 2 3 4 5 6 7 8 9 10 11 12 13 14 15)
        (extend z params)) (ZFSet.prod (ZFSet.prod I L) C) =
      liftedCompressionGraph I J D L C N B Maps Sources Fs Reps G A := by
    apply ZFSet.ext
    intro z
    rw [ZFSet.mem_sep, liftedCompressionGraph, ZFSet.mem_sep]
    exact and_congr Iff.rfl
      (BoundedFormula.truth_liftedCompressionEntryFormula 0 1 2 3 4 5 6 7 8 9 10 11 12 13 14 15
        (extend z params) rfl rfl)
  exact equal ▸ selected

noncomputable def groundLiftedCompressionFamily
    (I J D L C N B Maps Sources Fs Reps G A : ZFSet.{u}) : ZFSet.{u} :=
  M.indexedRelationSections I L C (liftedCompressionGraph I J D L C N B Maps Sources Fs Reps G A)

theorem groundLiftedCompressionFamily_spec
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    {I J D L C N B Maps Sources Fs Reps G A : ZFSet.{u}}
    (hI : I ∈ M.sets) (hJ : J ∈ M.sets) (hD : D ∈ M.sets)
    (hL : L ∈ M.sets) (hC : C ∈ M.sets) (hN : N ∈ M.sets) (hB : B ∈ M.sets)
    (hMaps : Maps ∈ M.sets) (hSources : Sources ∈ M.sets) (hFs : Fs ∈ M.sets)
    (hReps : Reps ∈ M.sets) (hG : G ∈ M.sets) (hA : A ∈ M.sets) :
    M.groundLiftedCompressionFamily I J D L C N B Maps Sources Fs Reps G A ∈ M.sets ∧
      FunctionGraphOn I (M.groundLiftedCompressionFamily I J D L C N B Maps Sources Fs Reps G A) ∧
      ∀ i f, ZFSet.pair i f ∈ M.groundLiftedCompressionFamily I J D L C N B Maps Sources Fs Reps G A ↔
        i ∈ I ∧ f = indexedRelationSection L C
          (liftedCompressionGraph I J D L C N B Maps Sources Fs Reps G A) i := by
  have graph := M.liftedCompressionGraph_mem pairing unions powers separation
    hI hJ hD hL hC hN hB hMaps hSources hFs hReps hG hA
  obtain ⟨member, function, entries⟩ := M.indexedRelationSections_spec
    pairing unions powers separation hI hL hC graph
  exact ⟨member, ⟨_, function⟩, entries⟩

end PartitionPilot.Forcing.TransitiveGround

end

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

namespace BoundedFormula

theorem truth_liftedCompressionEntryFormula_mem {n}
    (z i j d l c ns b maps sources fs reps g action v w : Fin n)
    (env : Fin n → ZFSet.{u}) (mapsBound : env v = ZFSet.sUnion (ZFSet.sUnion (env maps)))
    (filterBound : env w = ZFSet.sUnion (ZFSet.sUnion (env fs))) :
    Truth (liftedCompressionEntryFormula z i j d l c ns b maps sources fs reps g action v w) env ↔
      env z ∈ liftedCompressionGraph (env i) (env j) (env d) (env l) (env c)
        (env ns) (env b) (env maps) (env sources) (env fs) (env reps) (env g) (env action) := by
  rw [truth_liftedCompressionEntryFormula _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ mapsBound filterBound,
    liftedCompressionGraph, ZFSet.mem_sep]
  constructor
  · intro entry
    obtain ⟨task, hi, x, hx, y, hy, equal, branch⟩ := entry
    exact ⟨equal.symm ▸ ZFSet.pair_mem_prod.2 ⟨ZFSet.pair_mem_prod.2 ⟨hi, hx⟩, hy⟩, task, hi, x, hx, y, hy, equal, branch⟩
  · exact And.right

end BoundedFormula

end PartitionPilot.Forcing

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

section
universe u

theorem batchTemplateGraph_eq_section (I P Qs rs As Es i : ZFSet.{u}) :
    batchTemplateGraph I P Qs rs As Es i =
      indexedRelationSection (familyPointBound Qs)
        (taggedExtension P (indexedAttachmentFresh I Qs rs As))
        (batchAttachmentTemplateGraph I P Qs rs As Es) i := rfl

namespace TransitiveGround
open SetFormula
variable (M : TransitiveGround.{u})

noncomputable def batchEmbeddingFamily (I P Qs rs As Es : ZFSet.{u}) : ZFSet.{u} :=
  M.indexedRelationSections I (familyPointBound Qs)
    (taggedExtension P (indexedAttachmentFresh I Qs rs As))
    (batchAttachmentTemplateGraph I P Qs rs As Es)

theorem batchEmbeddingFamily_spec
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    {I P Qs rs As Es : ZFSet.{u}} (hI : I ∈ M.sets) (hP : P ∈ M.sets)
    (hQs : Qs ∈ M.sets) (hrs : rs ∈ M.sets) (hAs : As ∈ M.sets) (hEs : Es ∈ M.sets) :
    M.batchEmbeddingFamily I P Qs rs As Es ∈ M.sets ∧
      FunctionGraphOn I (M.batchEmbeddingFamily I P Qs rs As Es) ∧
      ∀ i f, ZFSet.pair i f ∈ M.batchEmbeddingFamily I P Qs rs As Es ↔
        i ∈ I ∧ f = batchTemplateGraph I P Qs rs As Es i := by
  have hN := M.indexedAttachmentFresh_mem pairing unions powers separation hI hQs hrs hAs
  have hL := M.taggedExtension_mem pairing unions powers separation hP hN
  have hB := M.familyPointBound_mem unions hQs
  have hR := M.batchAttachmentTemplateGraph_mem pairing unions powers separation hI hP hQs hrs hAs hEs
  obtain ⟨member, function, entries⟩ := M.indexedRelationSections_spec
    pairing unions powers separation hI hB hL hR
  refine ⟨member, ⟨_, function⟩, ?_⟩
  intro i f
  exact (entries i f).trans (and_congr Iff.rfl (by rw [batchTemplateGraph_eq_section]))

theorem exists_batchAttachment_embedding_family
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    {P rP μP I Qs rs μs As Es Fs Ss : ZFSet.{u}}
    (d : AttachmentBatchInputs P rP μP I Qs rs μs As Es Fs Ss)
    (hP : P ∈ M.sets) (hrP : rP ∈ M.sets) (hI : I ∈ M.sets)
    (hQs : Qs ∈ M.sets) (hrs : rs ∈ M.sets) (hμs : μs ∈ M.sets)
    (hAs : As ∈ M.sets) (hEs : Es ∈ M.sets) (hFs : Fs ∈ M.sets)
    (_hSs : Ss ∈ M.sets) :
    d.batchCarrier ∈ M.sets ∧ d.batchOrder ∈ M.sets ∧ d.batchMeetGraph ∈ M.sets ∧
    MeetOrderCode d.batchCarrier d.batchOrder d.batchMeetGraph ∧
    ∃ family ∈ M.sets, FunctionGraphOn I family ∧
      (∀ i f, ZFSet.pair i f ∈ family ↔ i ∈ I ∧ f = batchTemplateGraph I P Qs rs As Es i) ∧
      ∀ (i : {i : ZFSet.{u} // i ∈ I}) f, ZFSet.pair i.val f ∈ family →
        MeetEmbeddingCode (d.space i) d.batchCarrier (d.rel i) d.batchOrder
          (d.meet i) d.batchMeetGraph f := by
  obtain ⟨hL, hr, hm, _, _, _⟩ := M.batchAttachment_ground_codes
    pairing unions powers separation d hP hrP hI hQs hrs hμs hAs hEs hFs
  obtain ⟨member, function, entries⟩ := M.batchEmbeddingFamily_spec
    pairing unions powers separation hI hP hQs hrs hAs hEs
  refine ⟨hL, hr, hm, d.batch_meetOrder, M.batchEmbeddingFamily I P Qs rs As Es,
    member, function, entries, ?_⟩
  intro i f entry
  have eq := ((entries i.val f).1 entry).2
  exact eq.symm ▸ d.batch_template_embedding_code i

end TransitiveGround

end

end PartitionPilot.Forcing

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Definability_RecursiveActionRealization
attribute [-instance] _root_.OAI.PartitionPilot.Forcing.GroundMainPrefix.withTopSmall
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PartitionPilot.Forcing.CodedRecursiveMapInputs

open Compression.RecursiveMaps
universe u
variable {D rD μD J Qs rs μs As Es Fs Ss I Maps Sources Reps G m inv one A : ZFSet.{u}}
variable {d : AttachmentBatchInputs D rD μD J Qs rs μs As Es Fs Ss}
variable (h : CodedRecursiveMapInputs d I Maps Sources Reps G m inv one A)
variable (M : TransitiveGround.{u}) (next : h.NextInputs M)

theorem next_upper (label : h.toInputs.Labels)
    (x : {x : ZFSet.{u} // x ∈ D} ⊕ d.templates.Fresh) :
    next.templates.upper (h.nextIndex label) ⟨d.coding.encode x, d.coding.encode_mem x⟩ ↔
      h.toInputs.nextBatch.upper label x := by
  change d.coding.encode x ∈ next.filter (h.nextIndex label) ↔ _
  rw [h.next_filter M next, mem_pushFilterCode]
  constructor
  · rintro ⟨_, a, ha, z, _, entry, lower⟩
    let a' : {a : ZFSet.{u} // a ∈ D} := ⟨a, (d.fiber label.2.val).filter.subset ha⟩
    have equal := (show FunctionGraphOn D (h.maps.value label.1) from
      ⟨d.batchCarrier, (h.valid _ _ (h.maps.value_entry label.1)).injection.function⟩).unique
      entry (h.toInputs_previous_entry label.1 a')
    exact ⟨a', ha, (d.coding.le_encode _ x).1 (equal ▸ lower)⟩
  · rintro ⟨a, ha, lower⟩
    exact ⟨d.coding.encode_mem x, a.val, ha,
      d.coding.encode ((h.toInputs.previous label.1).toFun a), d.coding.encode_mem _,
      h.toInputs_previous_entry label.1 a, (d.coding.le_encode _ x).2 lower⟩

theorem nextFresh_shadow (q : h.toInputs.nextBatch.Fresh) :
    (next.templates.shadow (h.nextFresh M next q)).val =
      d.coding.encode (h.toInputs.nextBatch.shadow q) := by
  have oldEntry := (d.fiber q.1.2.val).shadow_entry ⟨(), q.2⟩
  obtain ⟨_, _, c, hc, meetEntry, baseEntry⟩ :=
    (pair_mem_attachmentShadowGraph _ _ _ _ _ _ _).1 oldEntry
  apply Eq.symm
  apply next.freshCode_shadow_value (h.nextFresh M next q)
  apply (next.batch_shadow_entry_iff (h.nextIndex q.1) q.2.val.val _).2
  rw [h.next_space M next, h.next_meet M next, h.next_embed M next, h.next_anchor M next]
  apply (pair_mem_attachmentShadowGraph _ _ _ _ _ _ _).2
  refine ⟨q.2.val.property, d.coding.encode_mem _, c, hc, meetEntry, ?_⟩
  apply (pair_mem_relationCompose _ _ _ _ _ _ _).2
  refine ⟨mem_familyPointBound_of_entry (d.space_entry q.1.2.val) hc,
    d.coding.encode_mem _, (d.templates.shadow ⟨q.1.2.val, q.2⟩).val,
    (d.templates.shadow ⟨q.1.2.val, q.2⟩).property, baseEntry, ?_⟩
  exact h.toInputs_previous_entry q.1.1 (d.templates.shadow ⟨q.1.2.val, q.2⟩)

noncomputable def nextNodes :
    ({x : ZFSet.{u} // x ∈ D} ⊕ d.templates.Fresh) ⊕ h.toInputs.nextBatch.Fresh →
      {x : ZFSet.{u} // x ∈ d.batchCarrier} ⊕ next.templates.Fresh
  | .inl x => .inl ⟨d.coding.encode x, d.coding.encode_mem x⟩
  | .inr q => .inr (h.nextFresh M next q)

noncomputable def nextEncode
    (x : ({x : ZFSet.{u} // x ∈ D} ⊕ d.templates.Fresh) ⊕ h.toInputs.nextBatch.Fresh) :
    ZFSet.{u} := next.coding.encode (h.nextNodes M next x)

theorem nextEncode_old (x : {x : ZFSet.{u} // x ∈ D} ⊕ d.templates.Fresh) :
    h.nextEncode M next (.inl x) = d.coding.encode x := rfl

theorem nextEncode_fresh (q : h.toInputs.nextBatch.Fresh) :
    h.nextEncode M next (.inr q) = ZFSet.pair d.batchCarrier
      (ZFSet.pair (ZFSet.pair q.1.1.val q.1.2.val.val) q.2.val.val) := rfl

theorem nextEncode_mem
    (x : ({x : ZFSet.{u} // x ∈ D} ⊕ d.templates.Fresh) ⊕ h.toInputs.nextBatch.Fresh) :
    h.nextEncode M next x ∈ next.batchCarrier := next.coding.encode_mem _

theorem nextNodes_injective : Function.Injective (h.nextNodes M next) := by
  intro x y equal
  cases x with
  | inl x =>
    cases y with
    | inl y =>
      exact congrArg Sum.inl (d.coding.encode_injective
        (congrArg Subtype.val (Sum.inl.inj equal)))
    | inr y => cases equal
  | inr x =>
    cases y with
    | inl y => cases equal
    | inr y => exact congrArg Sum.inr (h.nextFresh_injective M next (Sum.inr.inj equal))

theorem nextNodes_surjective : Function.Surjective (h.nextNodes M next) := by
  intro x
  cases x with
  | inl x =>
    obtain ⟨y, equal⟩ := d.coding.encode_surjective x.val x.property
    exact ⟨.inl y, congrArg Sum.inl (Subtype.ext equal)⟩
  | inr q =>
    obtain ⟨p, equal⟩ := h.nextFresh_surjective M next q
    exact ⟨.inr p, congrArg Sum.inr equal⟩

theorem nextEncode_injective : Function.Injective (h.nextEncode M next) :=
  fun _ _ equal => h.nextNodes_injective M next (next.coding.encode_injective equal)

theorem nextEncode_surjective : ∀ z ∈ next.batchCarrier,
    ∃ x, h.nextEncode M next x = z := by
  intro z hz
  obtain ⟨y, equal⟩ := next.coding.encode_surjective z hz
  obtain ⟨x, rfl⟩ := h.nextNodes_surjective M next y
  exact ⟨x, equal⟩

theorem next_le_encode
    (x y : ({x : ZFSet.{u} // x ∈ D} ⊕ d.templates.Fresh) ⊕ h.toInputs.nextBatch.Fresh) :
    ZFSet.pair (h.nextEncode M next x) (h.nextEncode M next y) ∈ next.batchOrder ↔
      h.toInputs.nextBatch.extension.le x y := by
  change ZFSet.pair (next.coding.encode (h.nextNodes M next x))
    (next.coding.encode (h.nextNodes M next y)) ∈ next.batchOrder ↔ _
  rw [next.coding.le_encode]
  cases x with
  | inl x =>
    cases y with
    | inl y => exact d.coding.le_encode x y
    | inr q =>
      change ZFSet.pair (d.coding.encode x) (next.templates.shadow (h.nextFresh M next q)).val ∈
        d.batchOrder ↔ d.templates.extension.le x (h.toInputs.nextBatch.shadow q)
      rw [h.nextFresh_shadow M next]
      exact d.coding.le_encode x _
  | inr q =>
    cases y with
    | inl y => exact h.next_upper M next q.1 y
    | inr t =>
      change (next.templates.Inside (h.nextFresh M next q) (h.nextFresh M next t) ∨
        next.templates.upper (h.nextIndex q.1) (next.templates.shadow (h.nextFresh M next t))) ↔
        (h.toInputs.nextBatch.Inside q t ∨
          h.toInputs.nextBatch.upper q.1 (h.toInputs.nextBatch.shadow t))
      apply or_congr (h.nextFresh_inside_iff M next q t)
      have equal : next.templates.shadow (h.nextFresh M next t) =
          ⟨d.coding.encode (h.toInputs.nextBatch.shadow t), d.coding.encode_mem _⟩ :=
        Subtype.ext (h.nextFresh_shadow M next t)
      rw [equal]
      exact h.next_upper M next q.1 _

theorem next_meet_entry
    (x y : ({x : ZFSet.{u} // x ∈ D} ⊕ d.templates.Fresh) ⊕ h.toInputs.nextBatch.Fresh) :
    ZFSet.pair (ZFSet.pair (h.nextEncode M next x) (h.nextEncode M next y))
      (h.nextEncode M next (h.toInputs.nextBatch.extension.meet x y)) ∈ next.batchMeetGraph := by
  apply next.batch_meetOrder.pair_iff.2
  refine ⟨h.nextEncode_mem M next x, h.nextEncode_mem M next y, h.nextEncode_mem M next _,
    (h.next_le_encode M next _ x).2 (h.toInputs.nextBatch.extension.meet_le_left x y),
    (h.next_le_encode M next _ y).2 (h.toInputs.nextBatch.extension.meet_le_right x y), ?_⟩
  intro z hz zx zy
  obtain ⟨w, rfl⟩ := h.nextEncode_surjective M next z hz
  exact (h.next_le_encode M next _ _).2 (h.toInputs.nextBatch.extension.le_meet
    ((h.next_le_encode M next _ _).1 zx) ((h.next_le_encode M next _ _).1 zy))

end PartitionPilot.Forcing.CodedRecursiveMapInputs



namespace PartitionPilot.Forcing.CodedRecursiveTaskAction

universe u
variable {D rD μD J Qs rs μs As Es Fs Ss I Maps Sources Reps G m inv one A T : ZFSet.{u}}
variable {d : AttachmentBatchInputs D rD μD J Qs rs μs As Es Fs Ss}
variable {h : CodedRecursiveMapInputs d I Maps Sources Reps G m inv one A}
variable (s : CodedRecursiveTaskAction h T)
variable (M : TransitiveGround.{u}) (next : h.NextInputs M)

theorem nextAction_entry (g : {g : ZFSet.{u} // g ∈ G})
    (x : ({x : ZFSet.{u} // x ∈ D} ⊕ d.templates.Fresh) ⊕ h.toInputs.nextBatch.Fresh) :
    ZFSet.pair (ZFSet.pair g.val (h.nextEncode M next x))
      (h.nextEncode M next ((s.toTaskSymmetry g).nextIso.toFun x)) ∈ h.nextActionGraph T := by
  cases x with
  | inl x =>
    rw [(s.toTaskSymmetry g).nextIso_old, h.nextEncode_old, h.nextEncode_old]
    exact (h.nextAction_old_iff (d.coding.encode_mem x)).2 (s.toTaskSymmetry_current_entry g x)
  | inr q =>
    rw [(s.toTaskSymmetry g).nextIso_fresh, h.nextEncode_fresh, h.nextEncode_fresh]
    exact h.nextAction_fresh_entry s.taskAction s.source
      (s.toTaskSymmetry_perm_entry g q.1.1) (next.freshCode_mem (h.nextFresh M next q))

theorem nextAction_entry_iff (g : {g : ZFSet.{u} // g ∈ G})
    (x : ({x : ZFSet.{u} // x ∈ D} ⊕ d.templates.Fresh) ⊕ h.toInputs.nextBatch.Fresh)
    (y : ZFSet.{u}) :
    ZFSet.pair (ZFSet.pair g.val (h.nextEncode M next x)) y ∈ h.nextActionGraph T ↔
      y = h.nextEncode M next ((s.toTaskSymmetry g).nextIso.toFun x) := by
  constructor
  · intro entry
    exact (h.nextAction_setAction s.taskAction s.source M next).entry_unique entry
      (s.nextAction_entry M next g x)
  · intro equal
    exact equal.symm ▸ s.nextAction_entry M next g x

include s in
theorem nextAction_order_iff {g x y x' y' : ZFSet.{u}}
    (first : ZFSet.pair (ZFSet.pair g x) x' ∈ h.nextActionGraph T)
    (second : ZFSet.pair (ZFSet.pair g y) y' ∈ h.nextActionGraph T) :
    ZFSet.pair x' y' ∈ next.batchOrder ↔ ZFSet.pair x y ∈ next.batchOrder := by
  have sx := (h.nextAction_setAction s.taskAction s.source M next).entry_shape first
  have sy := (h.nextAction_setAction s.taskAction s.source M next).entry_shape second
  let actor : {g : ZFSet.{u} // g ∈ G} := ⟨g, sx.1⟩
  obtain ⟨a, rfl⟩ := h.nextEncode_surjective M next x sx.2.1
  obtain ⟨b, rfl⟩ := h.nextEncode_surjective M next y sy.2.1
  rw [(s.nextAction_entry_iff M next actor a x').1 first,
    (s.nextAction_entry_iff M next actor b y').1 second, h.next_le_encode, h.next_le_encode]
  exact (s.toTaskSymmetry actor).nextIso.le_iff a b

include s in
theorem nextAction_code :
    PosetActionCode G next.batchCarrier m one next.batchOrder (h.nextActionGraph T) where
  function := (h.nextAction_setAction s.taskAction s.source M next).function
  one := (h.nextAction_setAction s.taskAction s.source M next).one
  mul := (h.nextAction_setAction s.taskAction s.source M next).mul
  monotone := fun _ _ _ _ _ _ _ _ _ _ first second lower =>
    (s.nextAction_order_iff M next first second).2 lower

end PartitionPilot.Forcing.CodedRecursiveTaskAction

end

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Forcing_InitialRecursiveActionAgreement
attribute [-instance] _root_.OAI.PartitionPilot.Forcing.GroundMainPrefix.withTopSmall
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PartitionPilot.Forcing.CodedRecursiveTaskAction

universe u
variable {D rD μD J Qs rs μs As Es Fs Ss I Maps Sources Reps G m inv one A T : ZFSet.{u}}
variable {d : AttachmentBatchInputs D rD μD J Qs rs μs As Es Fs Ss}
variable {h : CodedRecursiveMapInputs d I Maps Sources Reps G m inv one A}
variable (s : CodedRecursiveTaskAction h T)
variable (M : TransitiveGround.{u}) (next : h.NextInputs M)

include s in
theorem nextAction_agreement
    (g k : {g : ZFSet.{u} // g ∈ G})
    (topPoint : {x : ZFSet.{u} // x ∈ D})
    (top : ∀ x ∈ D, ZFSet.pair x topPoint.val ∈ rD)
    (v : {x : ZFSet.{u} // x ∈ D}) (positive : ZFSet.{u} → Prop)
    (negative : ∀ i S a cap base w,
      ZFSet.pair i S ∈ Maps → ZFSet.pair i a ∈ Sources →
      ZFSet.pair topPoint.val cap ∈ S → ZFSet.pair a base ∈ S →
      ¬ positive i → ZFSet.pair (ZFSet.pair cap v.val) w ∈ d.batchMeetGraph →
      ZFSet.pair w base ∈ d.batchOrder)
    (currentAgree : ActionAgreementBelow d.batchCarrier d.batchOrder A g.val k.val v.val)
    (taskAgree : ∀ i i' i'', positive i →
      ZFSet.pair (ZFSet.pair g.val i) i' ∈ T →
      ZFSet.pair (ZFSet.pair k.val i) i'' ∈ T → i' = i'') :
    ActionAgreementBelow next.batchCarrier next.batchOrder
      (h.nextActionGraph T) g.val k.val v.val := by
  have typedNegative : ∀ i : {i : ZFSet.{u} // i ∈ I}, ¬ positive i.val →
      d.templates.extension.le
        (d.templates.extension.meet ((h.toInputs.previous i).toFun topPoint) (.inl v))
        ((h.toInputs.previous i).toFun (h.toInputs.source i)) := by
    intro i notPositive
    apply (d.coding.le_encode _ _).1
    exact negative i.val (h.maps.value i) (h.source i).val _ _ _
      (h.maps.value_entry i) (h.source_entry i)
      (h.toInputs_previous_entry i topPoint)
      (h.toInputs_previous_entry i (h.toInputs.source i)) notPositive
      (d.coding.encoded_meet_entry ((h.toInputs.previous i).toFun topPoint) (.inl v))
  have typedCurrent : ∀ x, d.templates.extension.le x (.inl v) →
      (s.toTaskSymmetry g).current.toFun x = (s.toTaskSymmetry k).current.toFun x := by
    intro x lower
    apply d.coding.encode_injective
    exact currentAgree.entry_eq h.action k.property (d.coding.encode_mem x)
      ((d.coding.le_encode x (.inl v)).2 lower)
      (s.toTaskSymmetry_current_entry g x) (s.toTaskSymmetry_current_entry k x)
  have typedTasks : ∀ i : {i : ZFSet.{u} // i ∈ I}, positive i.val →
      (s.toTaskSymmetry g).perm i = (s.toTaskSymmetry k).perm i := by
    intro i pos
    exact Subtype.ext (taskAgree i.val _ _ pos
      (s.toTaskSymmetry_perm_entry g i) (s.toTaskSymmetry_perm_entry k i))
  have outputs {x y z : ZFSet.{u}} (hx : x ∈ next.batchCarrier)
      (lower : ZFSet.pair x v.val ∈ next.batchOrder)
      (first : ZFSet.pair (ZFSet.pair g.val x) y ∈ h.nextActionGraph T)
      (second : ZFSet.pair (ZFSet.pair k.val x) z ∈ h.nextActionGraph T) : y = z := by
    obtain ⟨a, rfl⟩ := h.nextEncode_surjective M next x hx
    have below := (h.next_le_encode M next a (.inl (.inl v))).1 lower
    have same := (s.toTaskSymmetry g).agreement_persists (s.toTaskSymmetry k)
      topPoint (fun p => top p.val p.property) v (fun i => positive i.val)
      typedNegative typedCurrent typedTasks a below
    exact ((s.nextAction_entry_iff M next g a y).1 first).trans
      ((congrArg (h.nextEncode M next) same).trans
        ((s.nextAction_entry_iff M next k a z).1 second).symm)
  intro x hx y _ lower
  constructor
  · intro first
    obtain ⟨z, second, _⟩ := (s.nextAction_code M next).function.2
      (ZFSet.pair k.val x) (ZFSet.pair_mem_prod.2 ⟨k.property, hx⟩)
    exact (outputs hx lower first second).symm ▸ second
  · intro second
    obtain ⟨z, first, _⟩ := (s.nextAction_code M next).function.2
      (ZFSet.pair g.val x) (ZFSet.pair_mem_prod.2 ⟨g.property, hx⟩)
    exact outputs hx lower first second ▸ first

end PartitionPilot.Forcing.CodedRecursiveTaskAction

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Geometry_LiftedCompressionEmbeddings
attribute [-instance] _root_.OAI.PartitionPilot.Forcing.GroundMainPrefix.withTopSmall
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PartitionPilot.Forcing.CodedRecursiveMapInputs

universe u
variable {D rD μD J Qs rs μs As Es Fs Ss I Maps Sources Reps G m inv one A : ZFSet.{u}}
variable {d : AttachmentBatchInputs D rD μD J Qs rs μs As Es Fs Ss}
variable (h : CodedRecursiveMapInputs d I Maps Sources Reps G m inv one A)
variable (M : TransitiveGround.{u}) (next : h.NextInputs M)

theorem liftGraph_entry (i : {i : ZFSet.{u} // i ∈ I})
    (x : {x : ZFSet.{u} // x ∈ D} ⊕ d.templates.Fresh) :
    ZFSet.pair (ZFSet.pair i.val (d.coding.encode x))
      (h.nextEncode M next (h.toInputs.lift i x)) ∈ h.liftGraph M next := by
  classical
  cases x with
  | inl x =>
    rw [h.toInputs.lift_old, h.nextEncode_old]
    exact (h.liftGraph_old_iff M next (h.maps.value_entry i) x.property).2
      (h.toInputs_previous_entry i x)
  | inr q =>
    by_cases positive : d.templates.upper q.1 (h.toInputs.source i)
    · rw [h.toInputs.lift_new_inside i q positive, h.nextEncode_old]
      exact (h.liftGraph_positive_iff M next (h.source_entry i) (d.filter_entry q.1)
        (h.actor_entry i) (d.freshCode_mem q) positive).2
        (h.toInputs_representative_entry i (.inr q))
    · rw [h.toInputs.lift_new_outside i q positive, h.nextEncode_fresh]
      exact (h.liftGraph_negative_iff M next (h.source_entry i) (d.filter_entry q.1)
        (d.freshCode_mem q) positive).2 rfl

theorem liftGraph_entry_iff (i : {i : ZFSet.{u} // i ∈ I})
    (x : {x : ZFSet.{u} // x ∈ D} ⊕ d.templates.Fresh) (y : ZFSet.{u}) :
    ZFSet.pair (ZFSet.pair i.val (d.coding.encode x)) y ∈ h.liftGraph M next ↔
      y = h.nextEncode M next (h.toInputs.lift i x) := by
  constructor
  · intro entry
    exact (show FunctionGraphOn (ZFSet.prod I d.batchCarrier) (h.liftGraph M next) from
      ⟨next.batchCarrier, h.liftGraph_function M next⟩).unique entry (h.liftGraph_entry M next i x)
  · intro equal
    exact equal.symm ▸ h.liftGraph_entry M next i x

theorem liftSection_entry (i : {i : ZFSet.{u} // i ∈ I})
    (x : {x : ZFSet.{u} // x ∈ D} ⊕ d.templates.Fresh) :
    ZFSet.pair (d.coding.encode x) (h.nextEncode M next (h.toInputs.lift i x)) ∈
      h.liftSection M next i.val :=
  (pair_mem_indexedRelationSection _ _ _ _ _ _).2
    ⟨d.coding.encode_mem x, h.nextEncode_mem M next _, h.liftGraph_entry M next i x⟩

theorem liftSection_entry_iff (i : {i : ZFSet.{u} // i ∈ I})
    (x : {x : ZFSet.{u} // x ∈ D} ⊕ d.templates.Fresh) (y : ZFSet.{u}) :
    ZFSet.pair (d.coding.encode x) y ∈ h.liftSection M next i.val ↔
      y = h.nextEncode M next (h.toInputs.lift i x) := by
  constructor
  · intro entry
    exact (h.liftGraph_entry_iff M next i x y).1
      ((pair_mem_indexedRelationSection _ _ _ _ _ _).1 entry).2.2
  · intro equal
    exact equal.symm ▸ h.liftSection_entry M next i x

theorem liftSection_order_iff (i : {i : ZFSet.{u} // i ∈ I})
    {x y x' y' : ZFSet.{u}}
    (first : ZFSet.pair x x' ∈ h.liftSection M next i.val)
    (second : ZFSet.pair y y' ∈ h.liftSection M next i.val) :
    ZFSet.pair x' y' ∈ next.batchOrder ↔ ZFSet.pair x y ∈ d.batchOrder := by
  have hx := (ZFSet.pair_mem_prod.1 ((h.liftSection_function M next i.property).1 first)).1
  have hy := (ZFSet.pair_mem_prod.1 ((h.liftSection_function M next i.property).1 second)).1
  obtain ⟨a, rfl⟩ := d.coding.encode_surjective x hx
  obtain ⟨b, rfl⟩ := d.coding.encode_surjective y hy
  rw [(h.liftSection_entry_iff M next i a x').1 first,
    (h.liftSection_entry_iff M next i b y').1 second, h.next_le_encode]
  exact ((h.toInputs.liftedEmbedding i).le_iff a b).trans (d.coding.le_encode a b).symm

theorem liftSection_injection (i : {i : ZFSet.{u} // i ∈ I}) :
    InjectionCode d.batchCarrier next.batchCarrier (h.liftSection M next i.val) where
  function := h.liftSection_function M next i.property
  injective := by
    intro x y z first second
    have hx := (ZFSet.pair_mem_prod.1 ((h.liftSection_function M next i.property).1 first)).1
    have hy := (ZFSet.pair_mem_prod.1 ((h.liftSection_function M next i.property).1 second)).1
    obtain ⟨a, rfl⟩ := d.coding.encode_surjective x hx
    obtain ⟨b, rfl⟩ := d.coding.encode_surjective y hy
    have equal := ((h.liftSection_entry_iff M next i a z).1 first).symm.trans
      ((h.liftSection_entry_iff M next i b z).1 second)
    exact congrArg d.coding.encode (h.toInputs.lift_injective i
      (h.nextEncode_injective M next equal))

theorem liftSection_map_meet (i : {i : ZFSet.{u} // i ∈ I})
    {x y z x' y' z' : ZFSet.{u}}
    (meet : ZFSet.pair (ZFSet.pair x y) z ∈ d.batchMeetGraph)
    (first : ZFSet.pair x x' ∈ h.liftSection M next i.val)
    (second : ZFSet.pair y y' ∈ h.liftSection M next i.val)
    (third : ZFSet.pair z z' ∈ h.liftSection M next i.val) :
    ZFSet.pair (ZFSet.pair x' y') z' ∈ next.batchMeetGraph := by
  have hx := (ZFSet.pair_mem_prod.1 ((h.liftSection_function M next i.property).1 first)).1
  have hy := (ZFSet.pair_mem_prod.1 ((h.liftSection_function M next i.property).1 second)).1
  obtain ⟨a, rfl⟩ := d.coding.encode_surjective x hx
  obtain ⟨b, rfl⟩ := d.coding.encode_surjective y hy
  have same : z = d.coding.encode (d.templates.extension.meet a b) :=
    (show FunctionGraphOn (ZFSet.prod d.batchCarrier d.batchCarrier) d.batchMeetGraph from
      ⟨d.batchCarrier, d.batch_meetOrder.operation⟩).unique meet (d.coding.encoded_meet_entry a b)
  subst z
  rw [(h.liftSection_entry_iff M next i a x').1 first,
    (h.liftSection_entry_iff M next i b y').1 second,
    (h.liftSection_entry_iff M next i (d.templates.extension.meet a b) z').1 third]
  have preserved := (h.toInputs.liftedEmbedding i).map_meet a b
  change h.toInputs.lift i (d.templates.extension.meet a b) =
    h.toInputs.nextBatch.extension.meet (h.toInputs.lift i a) (h.toInputs.lift i b) at preserved
  rw [preserved]
  exact h.next_meet_entry M next (h.toInputs.lift i a) (h.toInputs.lift i b)

theorem liftSection_embedding (i : {i : ZFSet.{u} // i ∈ I}) :
    MeetEmbeddingCode d.batchCarrier next.batchCarrier d.batchOrder next.batchOrder
      d.batchMeetGraph next.batchMeetGraph (h.liftSection M next i.val) where
  injection := h.liftSection_injection M next i
  monotone := fun _ _ _ _ lower first second =>
    (h.liftSection_order_iff M next i first second).2 lower
  map_meet := fun _ _ _ _ _ _ meet first second third =>
    h.liftSection_map_meet M next i meet first second third

end PartitionPilot.Forcing.CodedRecursiveMapInputs

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Transfinite_RecursiveNextMapInputs
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

theorem groundRecursiveAttachment
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    {I J D L rD rL μD μL Qs rs μs As Es Fs Ss Maps Sources : ZFSet.{u}}
    (d : AttachmentBatchInputs D rD μD J Qs rs μs As Es Fs Ss)
    (target : MeetOrderCode L rL μL) (maps : FunctionGraphOn I Maps)
    (sources : ZFSet.IsFunc I D Sources)
    (valid : ∀ i S, ZFSet.pair i S ∈ Maps → MeetEmbeddingCode D L rD rL μD μL S)
    (hI : I ∈ M.sets) (hJ : J ∈ M.sets) (hD : D ∈ M.sets)
    (hL : L ∈ M.sets) (hrL : rL ∈ M.sets)
    (hQs : Qs ∈ M.sets) (hrs : rs ∈ M.sets) (hμs : μs ∈ M.sets)
    (hAs : As ∈ M.sets) (hEs : Es ∈ M.sets) (hFs : Fs ∈ M.sets)
    (hSs : Ss ∈ M.sets) (hMaps : Maps ∈ M.sets) (hSources : Sources ∈ M.sets) :
    let K := recursiveAttachmentIndices I J D (⋃₀ ⋃₀ Fs) Sources Fs
    K ∈ M.sets ∧
    (∀ i j a F, ZFSet.pair i a ∈ Sources → ZFSet.pair j F ∈ Fs →
      (ZFSet.pair i j ∈ K ↔ a ∉ F)) ∧
    ∃ next : AttachmentBatchInputs L rL μL K
      (pairSecondField I J K Qs) (pairSecondField I J K rs)
      (pairSecondField I J K μs) (pairSecondField I J K As)
      (M.groundPairCompositions K I J (familyPointBound Qs) D L Es Maps)
      (M.groundPairPushFilters K I J L rL Maps Fs)
      (recursiveSeparatorFamily K I J D L Maps Ss),
      next.batchCarrier ∈ M.sets ∧ next.batchOrder ∈ M.sets ∧ next.batchMeetGraph ∈ M.sets ∧
      MeetOrderCode next.batchCarrier next.batchOrder next.batchMeetGraph ∧
      ∃ family ∈ M.sets, FunctionGraphOn K family ∧
        (∀ i f, ZFSet.pair i f ∈ family ↔ i ∈ K ∧
          f = batchTemplateGraph K L (pairSecondField I J K Qs)
            (pairSecondField I J K rs) (pairSecondField I J K As)
            (M.groundPairCompositions K I J (familyPointBound Qs) D L Es Maps) i) ∧
        ∀ (i : {i : ZFSet.{u} // i ∈ K}) f, ZFSet.pair i.val f ∈ family →
          MeetEmbeddingCode (next.space i) next.batchCarrier (next.rel i) next.batchOrder
            (next.meet i) next.batchMeetGraph f := by
  dsimp only
  let K := recursiveAttachmentIndices I J D (⋃₀ ⋃₀ Fs) Sources Fs
  have hK : K ∈ M.sets := M.recursiveAttachmentIndices_mem pairing unions powers separation
    hI hJ hD (M.union_mem unions (M.union_mem unions hFs)) hSources hFs
  have subset : K ⊆ ZFSet.prod I J := recursiveAttachmentIndices_subset _ _ _ _ _ _
  have fields {H : ZFSet.{u}} (hH : H ∈ M.sets) : pairSecondField I J K H ∈ M.sets :=
    M.pairFieldGraph_mem pairing unions powers separation false hI hJ hK
      (M.union_mem unions (M.union_mem unions hH)) hH
  have composites := M.groundPairCompositions_spec pairing unions powers separation hK hI hJ
    (M.familyPointBound_mem unions hQs) hD hL hEs hMaps d.embeddings maps subset
  have filters := M.groundPairPushFilters_spec pairing unions powers separation
    hK hI hJ hL hrL hMaps hFs maps d.filters subset
  let next := M.groundRecursiveBatchInputs pairing unions powers separation d target maps valid subset
    hK hI hJ hD hL hrL hQs hEs hFs hMaps
  refine ⟨hK, ?_, next, ?_⟩
  · intro i j a F source filter
    exact recursiveAttachmentIndices_entry_iff sources d.filters.to_isFunc source filter
  · exact M.exists_batchAttachment_embedding_family pairing unions powers separation next
      hL hrL hK (fields hQs) (fields hrs) (fields hμs) (fields hAs)
      composites.1 filters.1
      (M.recursiveSeparatorFamily_mem pairing unions powers separation hK hI hJ hD hL hMaps hSs)

end PartitionPilot.Forcing.TransitiveGround

namespace PartitionPilot.Forcing.CodedRecursiveMapInputs

open SetFormula
universe u
variable {D rD μD J Qs rs μs As Es Fs Ss I Maps Sources Reps G m inv one A : ZFSet.{u}}
variable {d : AttachmentBatchInputs D rD μD J Qs rs μs As Es Fs Ss}
variable (h : CodedRecursiveMapInputs d I Maps Sources Reps G m inv one A)
variable (M : TransitiveGround.{u})

noncomputable abbrev groundLiftFamily (next : h.NextInputs M) :=
  M.groundLiftedCompressionFamily I J D d.batchCarrier next.batchCarrier
    (indexedAttachmentFresh J Qs rs As) (familyPointBound Qs) Maps Sources Fs Reps G A

theorem groundLiftFamily_spec
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (next : h.NextInputs M) (hI : I ∈ M.sets) (hJ : J ∈ M.sets) (hD : D ∈ M.sets)
    (hL : d.batchCarrier ∈ M.sets) (hC : next.batchCarrier ∈ M.sets)
    (hQs : Qs ∈ M.sets) (hrs : rs ∈ M.sets) (hAs : As ∈ M.sets)
    (hMaps : Maps ∈ M.sets) (hSources : Sources ∈ M.sets) (hFs : Fs ∈ M.sets)
    (hReps : Reps ∈ M.sets) (hG : G ∈ M.sets) (hA : A ∈ M.sets) :
    h.liftGraph M next ∈ M.sets ∧ h.groundLiftFamily M next ∈ M.sets ∧
      FunctionGraphOn I (h.groundLiftFamily M next) ∧
      (∀ i f, ZFSet.pair i f ∈ h.groundLiftFamily M next ↔ i ∈ I ∧ f = h.liftSection M next i) ∧
      ∀ i f, ZFSet.pair i f ∈ h.groundLiftFamily M next →
        ZFSet.IsFunc d.batchCarrier next.batchCarrier f := by
  have hN := M.indexedAttachmentFresh_mem pairing unions powers separation hJ hQs hrs hAs
  have hB := M.familyPointBound_mem unions hQs
  have graph := M.liftedCompressionGraph_mem pairing unions powers separation
    hI hJ hD hL hC hN hB hMaps hSources hFs hReps hG hA
  obtain ⟨member, function, entries⟩ := M.groundLiftedCompressionFamily_spec
    pairing unions powers separation hI hJ hD hL hC hN hB hMaps hSources hFs hReps hG hA
  refine ⟨graph, member, function, entries, ?_⟩
  intro i f entry
  obtain ⟨hi, rfl⟩ := (entries i f).1 entry
  exact h.liftSection_function M next hi

theorem exists_groundLiftGraphs
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (hI : I ∈ M.sets) (hJ : J ∈ M.sets) (hD : D ∈ M.sets) (hrD : rD ∈ M.sets)
    (hQs : Qs ∈ M.sets) (hrs : rs ∈ M.sets) (hμs : μs ∈ M.sets)
    (hAs : As ∈ M.sets) (hEs : Es ∈ M.sets) (hFs : Fs ∈ M.sets) (hSs : Ss ∈ M.sets)
    (hMaps : Maps ∈ M.sets) (hSources : Sources ∈ M.sets) (hReps : Reps ∈ M.sets)
    (hG : G ∈ M.sets) (hA : A ∈ M.sets) :
    ∃ next : h.NextInputs M,
      next.batchCarrier ∈ M.sets ∧ next.batchOrder ∈ M.sets ∧ next.batchMeetGraph ∈ M.sets ∧
      MeetOrderCode next.batchCarrier next.batchOrder next.batchMeetGraph ∧
      h.liftGraph M next ∈ M.sets ∧
      ZFSet.IsFunc (ZFSet.prod I d.batchCarrier) next.batchCarrier (h.liftGraph M next) ∧
      h.groundLiftFamily M next ∈ M.sets ∧ FunctionGraphOn I (h.groundLiftFamily M next) ∧
      (∀ i f, ZFSet.pair i f ∈ h.groundLiftFamily M next ↔ i ∈ I ∧ f = h.liftSection M next i) ∧
      ∀ i f, ZFSet.pair i f ∈ h.groundLiftFamily M next →
        ZFSet.IsFunc d.batchCarrier next.batchCarrier f := by
  obtain ⟨hL, hrL, _, _, _, _⟩ := M.batchAttachment_ground_codes
    pairing unions powers separation d hD hrD hJ hQs hrs hμs hAs hEs hFs
  obtain ⟨_, _, next, hC, hrC, hμC, meet, _⟩ := M.groundRecursiveAttachment
    pairing unions powers separation d d.batch_meetOrder h.maps h.sources h.valid
    hI hJ hD hL hrL hQs hrs hμs hAs hEs hFs hSs hMaps hSources
  obtain ⟨graph, family, function, entries, functions⟩ := h.groundLiftFamily_spec M
    pairing unions powers separation next hI hJ hD hL hC hQs hrs hAs
    hMaps hSources hFs hReps hG hA
  exact ⟨next, hC, hrC, hμC, meet, graph, h.liftGraph_function M next,
    family, function, entries, functions⟩

end PartitionPilot.Forcing.CodedRecursiveMapInputs

namespace PartitionPilot.Forcing.CodedRecursiveMapInputs

open SetFormula
universe u
variable {D rD μD J Qs rs μs As Es Fs Ss I Maps Sources Reps G m inv one A : ZFSet.{u}}
variable {d : AttachmentBatchInputs D rD μD J Qs rs μs As Es Fs Ss}
variable (h : CodedRecursiveMapInputs d I Maps Sources Reps G m inv one A)
variable (M : TransitiveGround.{u})

theorem exists_groundLiftEmbeddings
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (hI : I ∈ M.sets) (hJ : J ∈ M.sets) (hD : D ∈ M.sets) (hrD : rD ∈ M.sets)
    (hQs : Qs ∈ M.sets) (hrs : rs ∈ M.sets) (hμs : μs ∈ M.sets)
    (hAs : As ∈ M.sets) (hEs : Es ∈ M.sets) (hFs : Fs ∈ M.sets) (hSs : Ss ∈ M.sets)
    (hMaps : Maps ∈ M.sets) (hSources : Sources ∈ M.sets) (hReps : Reps ∈ M.sets)
    (hG : G ∈ M.sets) (hA : A ∈ M.sets) :
    ∃ next : h.NextInputs M,
      next.batchCarrier ∈ M.sets ∧ next.batchOrder ∈ M.sets ∧ next.batchMeetGraph ∈ M.sets ∧
      MeetOrderCode next.batchCarrier next.batchOrder next.batchMeetGraph ∧
      h.liftGraph M next ∈ M.sets ∧
      ZFSet.IsFunc (ZFSet.prod I d.batchCarrier) next.batchCarrier (h.liftGraph M next) ∧
      h.groundLiftFamily M next ∈ M.sets ∧ FunctionGraphOn I (h.groundLiftFamily M next) ∧
      (∀ i f, ZFSet.pair i f ∈ h.groundLiftFamily M next ↔ i ∈ I ∧ f = h.liftSection M next i) ∧
      ∀ i f, ZFSet.pair i f ∈ h.groundLiftFamily M next →
        MeetEmbeddingCode d.batchCarrier next.batchCarrier d.batchOrder next.batchOrder
          d.batchMeetGraph next.batchMeetGraph f ∧
        ∀ a g x y, ZFSet.pair i a ∈ Sources → ZFSet.pair i g ∈ Reps →
          x ∈ d.batchCarrier → ZFSet.pair x a ∈ d.batchOrder →
            (ZFSet.pair x y ∈ f ↔ ZFSet.pair (ZFSet.pair g x) y ∈ A) := by
  obtain ⟨next, hC, hrC, hμC, meet, graph, func, family, famFunc, entries, _⟩ :=
    h.exists_groundLiftGraphs M pairing unions powers separation hI hJ hD hrD
      hQs hrs hμs hAs hEs hFs hSs hMaps hSources hReps hG hA
  refine ⟨next, hC, hrC, hμC, meet, graph, func, family, famFunc, entries, ?_⟩
  intro i f entry
  obtain ⟨hi, rfl⟩ := (entries i f).1 entry
  refine ⟨h.liftSection_embedding M next ⟨i, hi⟩, ?_⟩
  intro a g x y source representative hx below
  exact h.liftSection_agrees_on_base M next source representative hx below

end PartitionPilot.Forcing.CodedRecursiveMapInputs

namespace PartitionPilot.Forcing.CodedRecursiveMapInputs
open SetFormula
universe u
variable {D rD μD J Qs rs μs As Es Fs Ss I Maps Sources Reps G m inv one A T : ZFSet.{u}}
variable {d : AttachmentBatchInputs D rD μD J Qs rs μs As Es Fs Ss}
variable (h : CodedRecursiveMapInputs d I Maps Sources Reps G m inv one A)
variable (M : TransitiveGround.{u}) (next : h.NextInputs M)

include h in
theorem sources_on_current : ZFSet.IsFunc I d.batchCarrier Sources := by
  refine ⟨?_, h.sources.2⟩
  intro z hz
  obtain ⟨i, hi, a, ha, rfl⟩ := ZFSet.mem_prod.1 (h.sources.1 hz)
  exact ZFSet.pair_mem_prod.2 ⟨hi, old_mem_taggedExtension ha⟩

theorem nextMapInputs_of_family
    (family : FunctionGraphOn I (h.groundLiftFamily M next))
    (entries : ∀ i f, ZFSet.pair i f ∈ h.groundLiftFamily M next ↔
      i ∈ I ∧ f = h.liftSection M next i)
    (action : PosetActionCode G next.batchCarrier m one next.batchOrder (h.nextActionGraph T)) :
    CodedRecursiveMapInputs next I (h.groundLiftFamily M next) Sources Reps
      G m inv one (h.nextActionGraph T) := by
  refine ⟨family, h.sources_on_current, h.representatives, h.group, action, ?_, ?_⟩
  · intro i f entry
    obtain ⟨hi, rfl⟩ := (entries i f).1 entry
    exact h.liftSection_embedding M next ⟨i, hi⟩
  · intro i a g f x y source representative entry hx lower
    obtain ⟨_, rfl⟩ := (entries i f).1 entry
    exact (h.liftSection_agrees_on_base M next source representative hx lower).trans
      (h.nextAction_old_iff hx).symm

end PartitionPilot.Forcing.CodedRecursiveMapInputs

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Forcing_RecursiveNextTaskActions
attribute [-instance] _root_.OAI.PartitionPilot.Forcing.GroundMainPrefix.withTopSmall
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PartitionPilot.Forcing

universe u
variable {D rD μD J Qs rs μs As Es Fs Ss I Maps Sources Reps G m inv one A T : ZFSet.{u}}
variable {d : AttachmentBatchInputs D rD μD J Qs rs μs As Es Fs Ss}

def RecursiveRepresentativeCompatibility
    (_h : CodedRecursiveMapInputs d I Maps Sources Reps G m inv one A) (T : ZFSet.{u}) : Prop :=
  ∀ g i j a u v x y z, ZFSet.pair (ZFSet.pair g i) j ∈ T →
    ZFSet.pair i a ∈ Sources → ZFSet.pair i u ∈ Reps → ZFSet.pair j v ∈ Reps →
    x ∈ d.batchCarrier → ZFSet.pair x a ∈ d.batchOrder →
    ZFSet.pair (ZFSet.pair u x) y ∈ A → ZFSet.pair (ZFSet.pair v x) z ∈ A →
      ZFSet.pair (ZFSet.pair g y) z ∈ A

namespace CodedRecursiveTaskAction

variable {h : CodedRecursiveMapInputs d I Maps Sources Reps G m inv one A}
variable (s : CodedRecursiveTaskAction h T)

theorem toTaskSymmetry_compatible (compatible : RecursiveRepresentativeCompatibility h T)
    (g : {g : ZFSet.{u} // g ∈ G}) (i : {i : ZFSet.{u} // i ∈ I})
    (x : {x : ZFSet.{u} // x ∈ D} ⊕ d.templates.Fresh)
    (below : d.templates.extension.le x (.inl (h.toInputs.source i))) :
    (s.toTaskSymmetry g).current.toFun ((h.toInputs.representative i).toFun x) =
      (h.toInputs.representative ((s.toTaskSymmetry g).perm i)).toFun x := by
  apply d.coding.encode_injective
  exact h.action.toSetAction.entry_unique
    (s.toTaskSymmetry_current_entry g ((h.toInputs.representative i).toFun x))
    (compatible g.val i.val ((s.toTaskSymmetry g).perm i).val (h.source i).val
      (h.actor i).val (h.actor ((s.toTaskSymmetry g).perm i)).val
      (d.coding.encode x) _ _ (s.toTaskSymmetry_perm_entry g i)
      (h.source_entry i) (h.actor_entry i) (h.actor_entry ((s.toTaskSymmetry g).perm i))
      (d.coding.encode_mem x) ((d.coding.le_encode x (.inl (h.toInputs.source i))).2 below)
      (h.toInputs_representative_entry i x)
      (h.toInputs_representative_entry ((s.toTaskSymmetry g).perm i) x))

include s in
theorem liftSection_equivariant (M : TransitiveGround.{u}) (next : h.NextInputs M)
    (compatible : RecursiveRepresentativeCompatibility h T)
    {g i j x y z : ZFSet.{u}} (transport : ZFSet.pair (ZFSet.pair g i) j ∈ T)
    (first : ZFSet.pair x y ∈ h.liftSection M next i)
    (second : ZFSet.pair x z ∈ h.liftSection M next j) :
    ZFSet.pair (ZFSet.pair g y) z ∈ h.nextActionGraph T := by
  have shape := s.taskAction.entry_shape transport
  let actor : {g : ZFSet.{u} // g ∈ G} := ⟨g, shape.1⟩
  let index : {i : ZFSet.{u} // i ∈ I} := ⟨i, shape.2.1⟩
  let target : {i : ZFSet.{u} // i ∈ I} := ⟨j, shape.2.2⟩
  have perm : (s.toTaskSymmetry actor).perm index = target :=
    Subtype.ext (s.taskAction.entry_unique (s.toTaskSymmetry_perm_entry actor index) transport)
  have hx := (ZFSet.pair_mem_prod.1 ((h.liftSection_function M next shape.2.1).1 first)).1
  obtain ⟨X, rfl⟩ := d.coding.encode_surjective x hx
  rw [(h.liftSection_entry_iff M next index X y).1 first,
    (h.liftSection_entry_iff M next target X z).1 second]
  have equation := (s.toTaskSymmetry actor).lift_equivariant
    (s.toTaskSymmetry_compatible compatible actor) index X
  rw [perm] at equation
  have entry := s.nextAction_entry M next actor (h.toInputs.lift index X)
  rwa [equation] at entry

end CodedRecursiveTaskAction

end PartitionPilot.Forcing



namespace PartitionPilot.Forcing.CodedRecursiveTaskAction

universe u
variable {D rD μD J Qs rs μs As Es Fs Ss I Maps Sources Reps G m inv one A T : ZFSet.{u}}
variable {d : AttachmentBatchInputs D rD μD J Qs rs μs As Es Fs Ss}
variable {h : CodedRecursiveMapInputs d I Maps Sources Reps G m inv one A}
variable (s : CodedRecursiveTaskAction h T)

include s in
theorem nextTaskAction_of_family (M : TransitiveGround.{u}) (next : h.NextInputs M)
    (compatible : RecursiveRepresentativeCompatibility h T)
    (entries : ∀ i f, ZFSet.pair i f ∈ h.groundLiftFamily M next ↔
      i ∈ I ∧ f = h.liftSection M next i)
    (inputs : CodedRecursiveMapInputs next I (h.groundLiftFamily M next) Sources Reps
      G m inv one (h.nextActionGraph T)) : CodedRecursiveTaskAction inputs T := by
  refine ⟨s.taskAction, s.source, ?_⟩
  intro g i j f f' x y z transport firstFamily secondFamily first second
  obtain ⟨_, rfl⟩ := (entries i f).1 firstFamily
  obtain ⟨_, rfl⟩ := (entries j f').1 secondFamily
  exact s.liftSection_equivariant M next compatible transport first second

end PartitionPilot.Forcing.CodedRecursiveTaskAction

end

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Geometry_FixedCompressionSeeds
attribute [-instance] _root_.OAI.PartitionPilot.Forcing.GroundMainPrefix.withTopSmall
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PartitionPilot.Forcing

universe u

structure FixedCompressionSeed
    (P r μ A τ I Sources Reps G m inv one T Filters : ZFSet.{u}) : Prop where
  originalOrder : MeetOrderCode P r μ
  originalAction : PosetActionCode G P m one r A
  top_mem : τ ∈ P
  sources : ZFSet.IsFunc I P Sources
  filters : FunctionGraphOn I Filters
  productAgreement : ∀ δ i j g h k a,
    ZFSet.pair (ZFSet.pair δ i) j ∈ T → ZFSet.pair i a ∈ Sources →
    ZFSet.pair i g ∈ Reps → ZFSet.pair j h ∈ Reps →
    ZFSet.pair (ZFSet.pair δ g) k ∈ m → ActionAgreementBelow P r A k h a
  positiveAgreement : ∀ g h v i j k F,
    ActionAgreementBelow P r A g h v → ZFSet.pair i F ∈ Filters → v ∈ F →
    ZFSet.pair (ZFSet.pair g i) j ∈ T →
    ZFSet.pair (ZFSet.pair h i) k ∈ T → j = k

end PartitionPilot.Forcing

end

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Transfinite_GroundInvariantSuccessors
attribute [-instance] _root_.OAI.PartitionPilot.Forcing.GroundMainPrefix.withTopSmall
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace PartitionPilot.Forcing.CodedRecursiveMapInputs

universe u
variable {D rD μD J Qs rs μs As Es Fs Ss I Maps Sources Reps G m inv one A : ZFSet.{u}}
variable {d : AttachmentBatchInputs D rD μD J Qs rs μs As Es Fs Ss}
variable (h : CodedRecursiveMapInputs d I Maps Sources Reps G m inv one A)
variable (M : TransitiveGround.{u}) (next : h.NextInputs M)

theorem liftSection_old_iff {i S x y : ZFSet.{u}}
    (mapEntry : ZFSet.pair i S ∈ Maps) (hx : x ∈ D) :
    ZFSet.pair x y ∈ h.liftSection M next i ↔ ZFSet.pair x y ∈ S := by
  rw [liftSection, pair_mem_indexedRelationSection, h.liftGraph_old_iff M next mapEntry hx]
  constructor
  · exact fun entry => entry.2.2
  · intro entry
    exact ⟨old_mem_taggedExtension hx, old_mem_taggedExtension
      (ZFSet.pair_mem_prod.1 ((h.valid i S mapEntry).injection.function.1 entry)).2, entry⟩





theorem negative_cap_persists {K v b w : ZFSet.{u}}
    (hK : K ∈ d.batchCarrier) (hv : v ∈ d.batchCarrier) (hb : b ∈ d.batchCarrier)
    (negative : ∀ z, ZFSet.pair (ZFSet.pair K v) z ∈ d.batchMeetGraph →
      ZFSet.pair z b ∈ d.batchOrder)
    (entry : ZFSet.pair (ZFSet.pair K v) w ∈ next.batchMeetGraph) :
    ZFSet.pair w b ∈ next.batchOrder := by
  have oldMeet := (next.old_meet_iff hK hv).1 entry
  have hw := (ZFSet.pair_mem_prod.1 (d.batch_meetOrder.operation.1 oldMeet)).2
  exact (next.old_order_iff hw hb).2 (negative w oldMeet)

end PartitionPilot.Forcing.CodedRecursiveMapInputs



namespace PartitionPilot.Forcing

universe u

namespace CodedRecursiveMapInputs

variable {P0 A0 D rD μD J Qs rs μs As Es Fs Ss I Maps Sources Reps G m inv one A T : ZFSet.{u}}
variable {d : AttachmentBatchInputs D rD μD J Qs rs μs As Es Fs Ss}
variable (h : CodedRecursiveMapInputs d I Maps Sources Reps G m inv one A)

theorem nextAction_original_iff (original : P0 ⊆ D)
    (restriction : ∀ g x, x ∈ P0 → ∀ y,
      ZFSet.pair (ZFSet.pair g x) y ∈ A ↔ ZFSet.pair (ZFSet.pair g x) y ∈ A0)
    {g x y : ZFSet.{u}} (hx : x ∈ P0) :
    ZFSet.pair (ZFSet.pair g x) y ∈ h.nextActionGraph T ↔
      ZFSet.pair (ZFSet.pair g x) y ∈ A0 :=
  (h.nextAction_old_iff (d.original_carrier_subset original hx)).trans (restriction g x hx y)

end CodedRecursiveMapInputs






end PartitionPilot.Forcing



namespace PartitionPilot.Forcing.CodedRecursiveTaskAction
open SetFormula
universe u
variable {D rD μD J Qs rs μs As Es Fs Ss I Maps Sources Reps G m inv one A T : ZFSet.{u}}
variable {d : AttachmentBatchInputs D rD μD J Qs rs μs As Es Fs Ss}
variable {h : CodedRecursiveMapInputs d I Maps Sources Reps G m inv one A}
variable (s : CodedRecursiveTaskAction h T) (M : TransitiveGround.{u})

include s in
theorem exists_groundSuccessor
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (compatible : RecursiveRepresentativeCompatibility h T)
    (hI : I ∈ M.sets) (hJ : J ∈ M.sets) (hD : D ∈ M.sets) (hrD : rD ∈ M.sets)
    (hQs : Qs ∈ M.sets) (hrs : rs ∈ M.sets) (hμs : μs ∈ M.sets)
    (hAs : As ∈ M.sets) (hEs : Es ∈ M.sets) (hFs : Fs ∈ M.sets) (hSs : Ss ∈ M.sets)
    (hMaps : Maps ∈ M.sets) (hSources : Sources ∈ M.sets) (hReps : Reps ∈ M.sets)
    (hG : G ∈ M.sets) (hA : A ∈ M.sets) (hT : T ∈ M.sets) :
    ∃ next : h.NextInputs M,
      next.batchCarrier ∈ M.sets ∧ next.batchOrder ∈ M.sets ∧ next.batchMeetGraph ∈ M.sets ∧
      MeetOrderCode next.batchCarrier next.batchOrder next.batchMeetGraph ∧
      h.nextActionGraph T ∈ M.sets ∧
      PosetActionCode G next.batchCarrier m one next.batchOrder (h.nextActionGraph T) ∧
      h.liftGraph M next ∈ M.sets ∧
      ZFSet.IsFunc (ZFSet.prod I d.batchCarrier) next.batchCarrier (h.liftGraph M next) ∧
      h.groundLiftFamily M next ∈ M.sets ∧
      (∀ i f, ZFSet.pair i f ∈ h.groundLiftFamily M next ↔ i ∈ I ∧ f = h.liftSection M next i) ∧
      ∃ nextInputs : CodedRecursiveMapInputs next I (h.groundLiftFamily M next) Sources Reps
        G m inv one (h.nextActionGraph T), CodedRecursiveTaskAction nextInputs T := by
  obtain ⟨next, hC, hrC, hμC, meet, graph, graphFunction, ground, family, entries, _⟩ :=
    h.exists_groundLiftEmbeddings M pairing unions powers separation hI hJ hD hrD
      hQs hrs hμs hAs hEs hFs hSs hMaps hSources hReps hG hA
  obtain ⟨hL, _, _, _, _, _⟩ := M.batchAttachment_ground_codes
    pairing unions powers separation d hD hrD hJ hQs hrs hμs hAs hEs hFs
  have nextAction := s.nextAction_code M next
  have nextInputs := h.nextMapInputs_of_family M next family entries nextAction
  exact ⟨next, hC, hrC, hμC, meet,
    h.nextActionGraph_mem M pairing unions powers separation hI hJ hD hL
      hQs hrs hAs hFs hSources hG hA hT,
    nextAction, graph, graphFunction, ground, entries,
    nextInputs, s.nextTaskAction_of_family M next compatible entries nextInputs⟩

end PartitionPilot.Forcing.CodedRecursiveTaskAction



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

namespace PartitionPilot.Forcing
universe u

namespace CodedRecursiveMapInputs
variable {D rD μD J Qs rs μs As Es Fs Ss I Maps Sources Reps G m inv one A : ZFSet.{u}}
variable {d : AttachmentBatchInputs D rD μD J Qs rs μs As Es Fs Ss}

def toState (_h : CodedRecursiveMapInputs d I Maps Sources Reps G m inv one A) : RecursiveStateData :=
  ⟨D, rD, μD, J, Qs, rs, μs, As, Es, Fs, Ss, Maps, A⟩

end CodedRecursiveMapInputs

namespace RecursiveStateData
noncomputable def fresh (state : RecursiveStateData.{u}) :=
  indexedAttachmentFresh state.J state.Qs state.rs state.As

noncomputable def currentCarrier (state : RecursiveStateData.{u}) :=
  taggedExtension state.D state.fresh

noncomputable def currentOrder (state : RecursiveStateData.{u}) :=
  codedAttachmentOrder state.D state.fresh state.rD
    (batchAttachmentInsideGraph state.J state.Qs state.rs)
    (batchAttachmentShadowGraph state.J state.D state.Qs state.μs state.As state.Es)
    (batchAttachmentUpperGraph state.J state.D state.Qs state.Fs)

noncomputable def currentMeet (state : RecursiveStateData.{u}) :=
  canonicalMeetGraph state.currentCarrier state.currentOrder

noncomputable def successor (state : RecursiveStateData.{u}) (M : TransitiveGround.{u})
    (I Sources Reps G T : ZFSet.{u}) : RecursiveStateData.{u} :=
  let K := recursiveAttachmentIndices I state.J state.D (⋃₀ ⋃₀ state.Fs) Sources state.Fs
  let Qs := pairSecondField I state.J K state.Qs
  let rs := pairSecondField I state.J K state.rs
  let μs := pairSecondField I state.J K state.μs
  let As := pairSecondField I state.J K state.As
  let N := indexedAttachmentFresh K Qs rs As
  let C := taggedExtension state.currentCarrier N
  { D := state.currentCarrier
    rD := state.currentOrder
    μD := state.currentMeet
    J := K
    Qs := Qs
    rs := rs
    μs := μs
    As := As
    Es := M.groundPairCompositions K I state.J (familyPointBound state.Qs)
      state.D state.currentCarrier state.Es state.Maps
    Fs := M.groundPairPushFilters K I state.J state.currentCarrier state.currentOrder state.Maps state.Fs
    Ss := recursiveSeparatorFamily K I state.J state.D state.currentCarrier state.Maps state.Ss
    Maps := M.groundLiftedCompressionFamily I state.J state.D state.currentCarrier C state.fresh
      (familyPointBound state.Qs) state.Maps Sources state.Fs Reps G state.A
    A := taggedActionGraph G state.currentCarrier N state.A
      (indexedTaskActionGraph G K (familyPointBound state.Qs) N
        (indexedTaskActionGraph G I state.J K T)) }

end RecursiveStateData

namespace CodedRecursiveMapInputs
variable {D rD μD J Qs rs μs As Es Fs Ss I Maps Sources Reps G m inv one A T : ZFSet.{u}}
variable {d : AttachmentBatchInputs D rD μD J Qs rs μs As Es Fs Ss}
variable (h : CodedRecursiveMapInputs d I Maps Sources Reps G m inv one A)

theorem toState_successor (M : TransitiveGround.{u}) (next : h.NextInputs M)
    (inputs : CodedRecursiveMapInputs next I (h.groundLiftFamily M next) Sources Reps
      G m inv one (h.nextActionGraph T)) :
    inputs.toState = h.toState.successor M I Sources Reps G T := rfl

end CodedRecursiveMapInputs

structure RecursiveStateCoherence (I : ZFSet.{u}) (first second : RecursiveStateData.{u}) : Prop where
  carrier : first.D ⊆ second.D
  order : ∀ x ∈ first.D, ∀ y ∈ first.D,
    ZFSet.pair x y ∈ second.rD ↔ ZFSet.pair x y ∈ first.rD
  meet : ∀ x ∈ first.D, ∀ y ∈ first.D, ∀ z,
    ZFSet.pair (ZFSet.pair x y) z ∈ second.μD ↔ ZFSet.pair (ZFSet.pair x y) z ∈ first.μD
  currentCarrier : first.currentCarrier ⊆ second.currentCarrier
  currentOrder : ∀ x ∈ first.currentCarrier, ∀ y ∈ first.currentCarrier,
    ZFSet.pair x y ∈ second.currentOrder ↔ ZFSet.pair x y ∈ first.currentOrder
  currentMeet : ∀ x ∈ first.currentCarrier, ∀ y ∈ first.currentCarrier, ∀ z,
    ZFSet.pair (ZFSet.pair x y) z ∈ second.currentMeet ↔
      ZFSet.pair (ZFSet.pair x y) z ∈ first.currentMeet
  action : ∀ g x, x ∈ first.currentCarrier → ∀ y,
    ZFSet.pair (ZFSet.pair g x) y ∈ second.A ↔ ZFSet.pair (ZFSet.pair g x) y ∈ first.A
  maps : ∀ i ∈ I, ∀ S S', ZFSet.pair i S ∈ first.Maps → ZFSet.pair i S' ∈ second.Maps →
    ∀ x ∈ first.D, ∀ y, ZFSet.pair x y ∈ S' ↔ ZFSet.pair x y ∈ S

namespace CodedRecursiveMapInputs
variable {D rD μD J Qs rs μs As Es Fs Ss I Maps Sources Reps G m inv one A T : ZFSet.{u}}
variable {d : AttachmentBatchInputs D rD μD J Qs rs μs As Es Fs Ss}
variable (h : CodedRecursiveMapInputs d I Maps Sources Reps G m inv one A)
variable (M : TransitiveGround.{u}) (next : h.NextInputs M)

theorem next_coherent
    (entries : ∀ i f, ZFSet.pair i f ∈ h.groundLiftFamily M next ↔ i ∈ I ∧ f = h.liftSection M next i)
    (inputs : CodedRecursiveMapInputs next I (h.groundLiftFamily M next) Sources Reps
      G m inv one (h.nextActionGraph T)) : RecursiveStateCoherence I h.toState inputs.toState where
  carrier := fun _ hx => old_mem_taggedExtension hx
  order := fun _ hx _ hy => d.old_order_iff hx hy
  meet := fun _ hx _ hy _ => d.old_meet_iff hx hy
  currentCarrier := fun _ hx => old_mem_taggedExtension hx
  currentOrder := fun _ hx _ hy => next.old_order_iff hx hy
  currentMeet := fun _ hx _ hy _ => next.old_meet_iff hx hy
  action := fun _ _ hx _ => h.nextAction_old_iff hx
  maps := by
    intro i _ S S' oldEntry newEntry x hx y
    obtain ⟨_, rfl⟩ := (entries i S').1 newEntry
    exact h.liftSection_old_iff M next oldEntry hx

end CodedRecursiveMapInputs

end PartitionPilot.Forcing

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

namespace BoundedFormula

open SetFormula

def tripleProductFormula {n} (z G X Y : Fin n) : BoundedFormula n :=
  exMem G (exMem X.succ (exMem Y.succ.succ
    (orderedTripleFormula z.succ.succ.succ 2 1 0)))

theorem truth_tripleProductFormula {n} (z G X Y : Fin n) (env : Fin n → ZFSet.{u}) :
    Truth (tripleProductFormula z G X Y) env ↔
      env z ∈ ZFSet.prod (ZFSet.prod (env G) (env X)) (env Y) := by
  simp only [tripleProductFormula, truth_exMem, truth_orderedTripleFormula]
  change (∃ g ∈ env G, ∃ x ∈ env X, ∃ y ∈ env Y,
    env z = ZFSet.pair (ZFSet.pair g x) y) ↔ _
  constructor
  · rintro ⟨g, hg, x, hx, y, hy, equal⟩
    exact equal.symm ▸ ZFSet.pair_mem_prod.2 ⟨ZFSet.pair_mem_prod.2 ⟨hg, hx⟩, hy⟩
  · intro member
    obtain ⟨gx, hgx, y, hy, eq⟩ := ZFSet.mem_prod.1 member
    obtain ⟨g, hg, x, hx, rfl⟩ := ZFSet.mem_prod.1 hgx
    exact ⟨g, hg, x, hx, y, hy, eq⟩

def indexedTaskActionCompleteEntryFormula {n} (z G I P N T : Fin n) : BoundedFormula n :=
  .conj (tripleProductFormula z G N N) (indexedTaskActionEntryFormula z G I P T)

theorem truth_indexedTaskActionCompleteEntryFormula {n} (z G I P N T : Fin n)
    (env : Fin n → ZFSet.{u}) :
    Truth (indexedTaskActionCompleteEntryFormula z G I P N T) env ↔
      env z ∈ indexedTaskActionGraph (env G) (env I) (env P) (env N) (env T) := by
  simp only [indexedTaskActionCompleteEntryFormula, Truth, truth_tripleProductFormula,
    truth_indexedTaskActionEntryFormula, indexedTaskActionGraph, ZFSet.mem_sep]

def taggedActionCompleteEntryFormula {n} (z G P N A B : Fin n) : BoundedFormula n :=
  disj (.mem z A) (taggedActionEntryFormula z G P N B)

theorem truth_taggedActionCompleteEntryFormula {n} (z G P N A B : Fin n)
    (env : Fin n → ZFSet.{u}) :
    Truth (taggedActionCompleteEntryFormula z G P N A B) env ↔
      env z ∈ taggedActionGraph (env G) (env P) (env N) (env A) (env B) := by
  rw [taggedActionCompleteEntryFormula, truth_disj, taggedActionGraph, ZFSet.mem_union]
  apply or_congr Iff.rfl
  rw [truth_taggedActionEntryFormula, ZFSet.mem_sep]
  constructor
  · intro entry
    obtain ⟨g, hg, q, hq, t, ht, equal, branch⟩ := entry
    exact ⟨equal.symm ▸ ZFSet.pair_mem_prod.2 ⟨ZFSet.pair_mem_prod.2
      ⟨hg, pair_mem_taggedExtension.2 hq⟩, pair_mem_taggedExtension.2 ht⟩, g, hg, q, hq, t, ht, equal, branch⟩
  · exact And.right

end BoundedFormula

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

namespace BoundedFormula

def taskRepresentativesFormula {n} (Reps I P G r A R U Labels : Fin n) : BoundedFormula n :=
  .conj (functionFormula I G Reps)
    (.allMem I (.allMem G.succ (imp (pairMembershipFormula 1 0 Reps.succ.succ)
      (taskRepresentativeFormula 1 0 P.succ.succ r.succ.succ A.succ.succ
        R.succ.succ U.succ.succ Labels.succ.succ))))

end BoundedFormula

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

section
universe u

def FiniteCompressionAccounting (P0 I Sources τ : ZFSet.{u}) (data : RecursiveStateData.{u}) : Prop :=
  ∀ x ∈ data.currentCarrier, x ∈ P0 ∨
    ∃ i ∈ I, ∃ S a k b, ∃ y ∈ data.D,
      ZFSet.pair i S ∈ data.Maps ∧ ZFSet.pair i a ∈ Sources ∧
      ZFSet.pair τ k ∈ S ∧ ZFSet.pair a b ∈ S ∧ ZFSet.pair y x ∈ S ∧
      ZFSet.pair x k ∈ data.currentOrder ∧ ZFSet.pair x b ∉ data.currentOrder

end

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

namespace PartitionPilot.Forcing
open SetFormula
universe u

namespace RecursiveStateData
noncomputable def iterate (initial : RecursiveStateData.{u}) (M : TransitiveGround.{u})
    (I Sources Reps G T : ZFSet.{u}) : Nat → RecursiveStateData.{u}
  | 0 => initial
  | n + 1 => (iterate initial M I Sources Reps G T n).successor M I Sources Reps G T

end RecursiveStateData

end PartitionPilot.Forcing

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Geometry_HeightColumnBoundLaws
attribute [-instance] _root_.OAI.PartitionPilot.Forcing.GroundMainPrefix.withTopSmall
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PartitionPilot.Forcing

universe u

noncomputable def heightColumns (P C D old : ZFSet.{u}) : ZFSet.{u} :=
  relationImage (relationImage P (ZFSet.prod C D) old) C (productFirst C D)

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

structure OwnerStampCode (T stamps : ZFSet.{u}) : Prop where
  function : ZFSet.IsFunc ZFSet.omega T stamps
  strict : ∀ n m a b,
    ZFSet.pair (natSetCode n) a ∈ stamps → ZFSet.pair (natSetCode m) b ∈ stamps →
      (a ∈ b ↔ n < m)

theorem CompressionStampCode.ownerStampCode {base stamps T : ZFSet.{u}}
    (code : CompressionStampCode base stamps T) : OwnerStampCode T stamps := by
  refine ⟨code.function, ?_⟩
  intro n m a b first second
  rw [(code.entries n a).1 first, (code.entries m b).1 second]
  exact compressionStamp_mem_iff base n m

end PartitionPilot.Forcing

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Forcing_OwnerBirthLayerTransport
attribute [-instance] _root_.OAI.PartitionPilot.Forcing.GroundMainPrefix.withTopSmall
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PartitionPilot.Forcing
open SetFormula
universe u

theorem MeetEmbeddingCode.compose {A B C rA rB rC μA μB μC e f : ZFSet.{u}}
    (first : MeetEmbeddingCode A B rA rB μA μB e)
    (second : MeetEmbeddingCode B C rB rC μB μC f) :
    MeetEmbeddingCode A C rA rC μA μC (relationCompose A B C e f) := by
  refine ⟨first.injection.compose second.injection, ?_, ?_⟩
  · intro x y x' y' lower xx yy
    obtain ⟨_, _, a, _, xa, ax⟩ := (pair_mem_relationCompose _ _ _ _ _ _ _).1 xx
    obtain ⟨_, _, b, _, yb, by'⟩ := (pair_mem_relationCompose _ _ _ _ _ _ _).1 yy
    exact second.monotone a b x' y' (first.monotone x y a b lower xa yb) ax by'
  · intro x y z x' y' z' meet xx yy zz
    obtain ⟨_, _, a, _, xa, ax⟩ := (pair_mem_relationCompose _ _ _ _ _ _ _).1 xx
    obtain ⟨_, _, b, _, yb, by'⟩ := (pair_mem_relationCompose _ _ _ _ _ _ _).1 yy
    obtain ⟨_, _, c, _, zc, cz⟩ := (pair_mem_relationCompose _ _ _ _ _ _ _).1 zz
    exact second.map_meet a b c x' y' z' (first.map_meet x y z a b c meet xa yb zc) ax by' cz

theorem relationImage_compose_point {A B C e f x y : ZFSet.{u}}
    (image : x ∈ relationImage A B e) (hy : y ∈ C) (entry : ZFSet.pair x y ∈ f) :
    y ∈ relationImage A C (relationCompose A B C e f) := by
  obtain ⟨hx, a, ha, copied⟩ := (mem_relationImage _ _ _ _).1 image
  exact (mem_relationImage _ _ _ _).2 ⟨hy, a, ha,
    (pair_mem_relationCompose _ _ _ _ _ _ _).2 ⟨ha, hy, x, hx, copied, entry⟩⟩

theorem OldBridgeCode.map {A B rA rB μA μB birthA birthB t x y x' y' e : ZFSet.{u}}
    (source : MeetOrderCode A rA μA) (embedding : MeetEmbeddingCode A B rA rB μA μB e)
    (preserves : ∀ a b s, ZFSet.pair a b ∈ e → ZFSet.pair a s ∈ birthA → ZFSet.pair b s ∈ birthB)
    (xx : ZFSet.pair x x' ∈ e) (yy : ZFSet.pair y y' ∈ e)
    (bridge : OldBridgeCode A rA μA birthA t x y) : OldBridgeCode B rB μB birthB t x' y' := by
  rcases bridge with ⟨z, s, meet, born, before⟩ | ⟨z, hz, s, born, before, between⟩
  · have hz := (ZFSet.pair_mem_prod.1 (source.operation.1 meet)).2
    obtain ⟨z', zz, _⟩ := embedding.injection.function.2 z hz
    exact Or.inl ⟨z', s, embedding.map_meet x y z x' y' z' meet xx yy zz,
      preserves z z' s zz born, before⟩
  · obtain ⟨z', zz, _⟩ := embedding.injection.function.2 z hz
    refine Or.inr ⟨z', (ZFSet.pair_mem_prod.1 (embedding.injection.function.1 zz)).2,
      s, preserves z z' s zz born, before, ?_⟩
    exact between.elim
      (fun h => Or.inl ⟨embedding.monotone x z x' z' h.1 xx zz, embedding.monotone z y z' y' h.2 zz yy⟩)
      (fun h => Or.inr ⟨embedding.monotone y z y' z' h.1 yy zz, embedding.monotone z x z' x' h.2 zz xx⟩)

noncomputable def CodedGrowthLayer.pushforward
    {M : TransitiveGround.{u}} {Space sourceOrder sourceMeet : ZFSet.{u} → ZFSet.{u}}
    {A B rA rB μA μB old born t e : ZFSet.{u}}
    (layer : CodedGrowthLayer M Space sourceOrder sourceMeet A rA μA old t)
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (hA : A ∈ M.sets) (hB : B ∈ M.sets) (he : e ∈ M.sets) (hOmega : ZFSet.omega ∈ M.sets)
    (groundSources : ∀ s ∈ t, Space s ∈ M.sets)
    (source : MeetOrderCode A rA μA) (embedding : MeetEmbeddingCode A B rA rB μA μB e)
    (preserves : ∀ x y a, ZFSet.pair x y ∈ e → (ZFSet.pair y a ∈ born ↔ ZFSet.pair x a ∈ old))
    (noNew : ∀ y ∈ B, ZFSet.pair y t ∈ born → ∃ x ∈ A, ZFSet.pair x y ∈ e) :
    CodedGrowthLayer M Space sourceOrder sourceMeet B rB μB born t := by
  classical
  cases layer with
  | countablePoints D ground small cover =>
    let retained := ZFSet.sep (fun x => x ∈ A) D
    have retainedGround : retained ∈ M.sets :=
      M.bounded_separation_mem separation (.mem 0 1) (extend A Fin.elim0)
        (Fin.cases hA (fun i => Fin.elim0 i)) ground
    have retainedSmall := M.groundEmbeddable_restrict separation retainedGround hOmega
      (fun _ h => (ZFSet.mem_sep.1 h).1) small
    refine .countablePoints (relationImage retained B e)
      (M.relationImage_mem separation retainedGround hB he)
      (M.groundEmbeddable_image pairing unions powers separation retainedGround hB hOmega he
        embedding.injection (fun _ h => (ZFSet.mem_sep.1 h).2) retainedSmall) ?_
    intro y hy yt
    obtain ⟨x, hx, xy⟩ := noNew y hy yt
    exact (mem_relationImage _ _ _ _).2 ⟨hy, x,
      ZFSet.mem_sep.2 ⟨cover x hx ((preserves x y t xy).1 yt), hx⟩, xy⟩
  | copies I parts groundI small groundParts index copy earlier groundCopy copyCode cover inCopy =>
    refine .copies I (relationCompose I A B parts e) groundI small
      (M.relationCompose_mem pairing unions powers separation groundI hA hB groundParts he)
      index (fun i => relationCompose (Space (index i)) A B (copy i) e) earlier
      (fun i hi => M.relationCompose_mem pairing unions powers separation
        (groundSources (index i) (earlier i hi)) hA hB (groundCopy i hi) he)
      (fun i hi => (copyCode i hi).compose embedding) ?_ ?_
    · intro y hy yt
      obtain ⟨x, hx, xy⟩ := noNew y hy yt
      obtain ⟨i, hi, part⟩ := cover x hx ((preserves x y t xy).1 yt)
      exact ⟨i, hi, (pair_mem_relationCompose _ _ _ _ _ _ _).2 ⟨hi, hy, x, hx, part, xy⟩⟩
    · intro i hi y hy part
      obtain ⟨_, _, x, hx, oldPart, xy⟩ := (pair_mem_relationCompose _ _ _ _ _ _ _).1 part
      exact relationImage_compose_point (inCopy i hi x hx oldPart) hy xy
  | separated I index copy earlier groundCopy copyCode component cover separated =>
    let pre (x : {x : ZFSet.{u} // x ∈ B ∧ ZFSet.pair x t ∈ born}) :
        {x : ZFSet.{u} // x ∈ A ∧ ZFSet.pair x t ∈ old} :=
      let a := Classical.choose (noNew x.val x.property.1 x.property.2)
      have spec := Classical.choose_spec (noNew x.val x.property.1 x.property.2)
      ⟨a, spec.1, (preserves a x.val t spec.2).1 x.property.2⟩
    have preEntry (x : {x : ZFSet.{u} // x ∈ B ∧ ZFSet.pair x t ∈ born}) :
        ZFSet.pair (pre x).val x.val ∈ e :=
      (Classical.choose_spec (noNew x.val x.property.1 x.property.2)).2
    refine .separated I index (fun i => relationCompose (Space (index i)) A B (copy i) e) earlier
      (fun i => M.relationCompose_mem pairing unions powers separation
        (groundSources (index i) (earlier i)) hA hB (groundCopy i) he)
      (fun i => (copyCode i).compose embedding) (fun x => component (pre x)) ?_ ?_
    · intro x
      exact relationImage_compose_point (cover (pre x)) x.property.1 (preEntry x)
    · intro x y different
      exact (separated (pre x) (pre y) different).map source embedding
        (fun a b s copied born => (preserves a b s copied).2 born) (preEntry x) (preEntry y)

noncomputable def CodedGrowthLayer.ownerBirth_pushforward
    {M : TransitiveGround.{u}} {Space sourceOrder sourceMeet : ZFSet.{u} → ZFSet.{u}}
    {A B L rA rL μA μL old T0 T levels stamps t e : ZFSet.{u}}
    (layer : CodedGrowthLayer M Space sourceOrder sourceMeet A rA μA old t)
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (hA : A ∈ M.sets) (hL : L ∈ M.sets) (he : e ∈ M.sets) (hOmega : ZFSet.omega ∈ M.sets)
    (groundSources : ∀ s ∈ t, Space s ∈ M.sets)
    (source : MeetOrderCode A rA μA) (embedding : MeetEmbeddingCode A L rA rL μA μL e)
    (carrier : L ⊆ B) (oldFunction : ZFSet.IsFunc A T0 old)
    (before : ∀ n a, ZFSet.pair (natSetCode n) a ∈ stamps → t ∈ a) :
    CodedGrowthLayer M Space sourceOrder sourceMeet L rL μL
      (ownerBirthGraph (relationImage A B e) B T (pushedHeightGraph A B T0 e old) levels stamps) t := by
  have injection : InjectionCode A B e := by
    refine ⟨⟨?_, embedding.injection.function.2⟩, embedding.injection.injective⟩
    intro z hz
    obtain ⟨x, hx, y, hy, rfl⟩ := ZFSet.mem_prod.1 (embedding.injection.function.1 hz)
    exact ZFSet.pair_mem_prod.2 ⟨hx, carrier hy⟩
  have pushed := pushedHeightGraph_function injection oldFunction
  apply layer.pushforward pairing unions powers separation hA hL he hOmega groundSources source embedding
  · intro x y a copied
    have bounds := ZFSet.pair_mem_prod.1 (injection.function.1 copied)
    have oldPoint := (mem_relationImage A B e y).2 ⟨bounds.2, x, bounds.1, copied⟩
    rw [ownerBirthGraph_old_iff oldPoint, pushedHeightGraph_entry injection oldFunction copied]
  · intro y _ entry
    rcases (pair_mem_ownerBirthGraph _ _ _ _ _ _ _ _).1 entry with oldEntry | freshEntry
    · exact (mem_relationImage A B e y).1 (ZFSet.pair_mem_prod.1 (pushed.1 oldEntry)).1 |>.2
    · obtain ⟨_, _, _, n, hn, _, stamp⟩ := freshEntry
      obtain ⟨n, rfl⟩ := (mem_omega_iff_natSetCode n).1 hn
      exact (ZFSet.mem_irrefl t (before n t stamp)).elim

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

def ExternalRectangleCode (P G r μ A c b d g h : ZFSet.{u}) : Prop :=
  c ∈ P ∧ b ∈ P ∧ d ∈ P ∧ g ∈ G ∧ h ∈ G ∧
    ZFSet.pair c d ∈ r ∧ ZFSet.pair b d ∈ r ∧
    ∃ w ∈ P, ZFSet.pair (ZFSet.pair c b) w ∈ μ ∧ ActionAgreementBelow P r A g h w ∧
      ∀ y ∈ P, ∀ z ∈ P, ∀ v ∈ P,
        (ZFSet.pair (ZFSet.pair g d) y ∈ A ∧ ZFSet.pair (ZFSet.pair h d) z ∈ A ∧
          ZFSet.pair (ZFSet.pair g w) v ∈ A) → ZFSet.pair (ZFSet.pair y z) v ∈ μ

noncomputable def externalRectangles (P G r μ A : ZFSet.{u}) : ZFSet.{u} :=
  ZFSet.sep (fun t => ∃ c ∈ P, ∃ b ∈ P, ∃ d ∈ P, ∃ g ∈ G, ∃ h ∈ G,
    t = externalRectangleCode c b d g h ∧ ExternalRectangleCode P G r μ A c b d g h)
    (externalRectangleBound P G)

namespace BoundedFormula
open SetFormula

def rectangleSeparatedFormula {n} (P μ A d w g h : Fin n) : BoundedFormula n :=
  .allMem P (.allMem P.succ (.allMem P.succ.succ
    (imp (.conj (tripleMembershipFormula g.succ.succ.succ d.succ.succ.succ 2 A.succ.succ.succ)
      (.conj (tripleMembershipFormula h.succ.succ.succ d.succ.succ.succ 1 A.succ.succ.succ)
        (tripleMembershipFormula g.succ.succ.succ w.succ.succ.succ 0 A.succ.succ.succ)))
      (tripleMembershipFormula 2 1 0 μ.succ.succ.succ))))

def externalRectangleFormula {n} (P G r μ A c b d g h : Fin n) : BoundedFormula n :=
  .conj (.mem c P) (.conj (.mem b P) (.conj (.mem d P) (.conj (.mem g G) (.conj (.mem h G)
    (.conj (pairMembershipFormula c d r) (.conj (pairMembershipFormula b d r)
      (exMem P (.conj (tripleMembershipFormula c.succ b.succ 0 μ.succ)
        (.conj (actionAgreementBelowFormula P.succ r.succ A.succ g.succ h.succ 0)
          (rectangleSeparatedFormula P.succ μ.succ A.succ d.succ 0 g.succ h.succ))))))))))

def externalRectangleTupleFormula {n} (t c b d g h : Fin n) : BoundedFormula n :=
  nonemptyTupleFormula 4 t
    (Fin.cases c (Fin.cases b (Fin.cases d (Fin.cases g (Fin.cases h Fin.elim0)))))

theorem truth_externalRectangleTupleFormula {n} (t c b d g h : Fin n)
    (env : Fin n → ZFSet.{u}) :
    Truth (externalRectangleTupleFormula t c b d g h) env ↔
      env t = externalRectangleCode (env c) (env b) (env d) (env g) (env h) := by
  rw [externalRectangleTupleFormula, truth_nonemptyTupleFormula]
  rfl

def externalRectanglesEntryFormula {n} (t P G r μ A : Fin n) : BoundedFormula n :=
  exMem P (exMem P.succ (exMem P.succ.succ (exMem G.succ.succ.succ
    (exMem G.succ.succ.succ.succ
      (.conj (externalRectangleTupleFormula t.succ.succ.succ.succ.succ 4 3 2 1 0)
        (externalRectangleFormula P.succ.succ.succ.succ.succ G.succ.succ.succ.succ.succ
          r.succ.succ.succ.succ.succ μ.succ.succ.succ.succ.succ A.succ.succ.succ.succ.succ
          4 3 2 1 0))))))

end BoundedFormula





def CompressionActorCode
    (P G Q H R B e a Sources Reps top Caps i k : ZFSet.{u}) : Prop :=
  (∀ s ∈ P, ∀ g ∈ G, ∀ g' ∈ H, ∀ s' ∈ Q,
    ZFSet.pair i s ∈ Sources → ZFSet.pair i g ∈ Reps →
      ZFSet.pair g g' ∈ a → ZFSet.pair s s' ∈ e →
        ActionAgreementBelow Q R B k g' s') ∧
  ∀ top' ∈ Q, ∀ v ∈ Q, ZFSet.pair top top' ∈ e →
    (ZFSet.pair (ZFSet.pair k top') v ∈ B ↔ ZFSet.pair i v ∈ Caps)

def CompressionActorFulfillmentCode
    (I P G Q H R B e a Sources Reps top Caps : ZFSet.{u}) : Prop :=
  ∀ i ∈ I, ∃ k ∈ H, CompressionActorCode P G Q H R B e a Sources Reps top Caps i k

end PartitionPilot.Forcing



namespace PartitionPilot.Forcing
universe u

namespace BoundedFormula

def rectangleIdealFormula {n} (Q H R B e a c b g h k l : Fin n) : BoundedFormula n :=
  (.conj (.allMem Q (.allMem H.succ (.allMem H.succ.succ (imp (pairMembershipFormula c.succ.succ.succ 2 e.succ.succ.succ) (imp (pairMembershipFormula g.succ.succ.succ 1 a.succ.succ.succ) (imp (pairMembershipFormula h.succ.succ.succ 0 a.succ.succ.succ) (.conj (actionAgreementBelowFormula Q.succ.succ.succ R.succ.succ.succ B.succ.succ.succ k.succ.succ.succ 1 2) (actionAgreementBelowFormula Q.succ.succ.succ R.succ.succ.succ B.succ.succ.succ l.succ.succ.succ 0 2)))))))) (.allMem Q (imp (pairMembershipFormula b.succ 0 e.succ) (actionAgreementBelowFormula Q.succ R.succ B.succ k.succ l.succ 0))))

def rectangleRootMeetFormula {n} (P μ A Q ν B e c d g k : Fin n) : BoundedFormula n :=
  (.allMem P (.allMem P.succ (.allMem P.succ.succ (.allMem Q.succ.succ.succ (.allMem Q.succ.succ.succ.succ (.allMem Q.succ.succ.succ.succ.succ (.allMem Q.succ.succ.succ.succ.succ.succ (imp (tripleMembershipFormula g.succ.succ.succ.succ.succ.succ.succ c.succ.succ.succ.succ.succ.succ.succ 5 A.succ.succ.succ.succ.succ.succ.succ) (imp (tripleMembershipFormula 5 6 4 μ.succ.succ.succ.succ.succ.succ.succ) (imp (pairMembershipFormula d.succ.succ.succ.succ.succ.succ.succ 3 e.succ.succ.succ.succ.succ.succ.succ) (imp (pairMembershipFormula 6 2 e.succ.succ.succ.succ.succ.succ.succ) (imp (pairMembershipFormula 4 1 e.succ.succ.succ.succ.succ.succ.succ) (imp (tripleMembershipFormula k.succ.succ.succ.succ.succ.succ.succ 3 0 B.succ.succ.succ.succ.succ.succ.succ) (tripleMembershipFormula 0 2 1 ν.succ.succ.succ.succ.succ.succ.succ))))))))))))))

def rectangleCrossMeetFormula {n} (Q ν B e b d k l : Fin n) : BoundedFormula n :=
  (.allMem Q (.allMem Q.succ (.allMem Q.succ.succ (.allMem Q.succ.succ.succ (.allMem Q.succ.succ.succ.succ (imp (pairMembershipFormula b.succ.succ.succ.succ.succ 4 e.succ.succ.succ.succ.succ) (imp (pairMembershipFormula d.succ.succ.succ.succ.succ 3 e.succ.succ.succ.succ.succ) (imp (tripleMembershipFormula k.succ.succ.succ.succ.succ 3 2 B.succ.succ.succ.succ.succ) (imp (tripleMembershipFormula l.succ.succ.succ.succ.succ 3 1 B.succ.succ.succ.succ.succ) (imp (tripleMembershipFormula k.succ.succ.succ.succ.succ 4 0 B.succ.succ.succ.succ.succ) (.conj (tripleMembershipFormula 2 1 0 ν.succ.succ.succ.succ.succ) (tripleMembershipFormula l.succ.succ.succ.succ.succ 4 0 B.succ.succ.succ.succ.succ))))))))))))

def rectangleActorPairFormula {n} (P μ A Q H R ν B e a c b d g h k l : Fin n) : BoundedFormula n :=
  (.conj (rectangleIdealFormula Q H R B e a c b g h k l) (.conj (rectangleRootMeetFormula P μ A Q ν B e c d g k) (.conj (rectangleRootMeetFormula P μ A Q ν B e c d h l) (rectangleCrossMeetFormula Q ν B e b d k l))))

def rectangleFulfillmentFormula {n} (P G r μ A Q H R ν B e a : Fin n) : BoundedFormula n :=
  (.allMem P (.allMem P.succ (.allMem P.succ.succ (.allMem G.succ.succ.succ (.allMem G.succ.succ.succ.succ (imp (externalRectangleFormula P.succ.succ.succ.succ.succ G.succ.succ.succ.succ.succ r.succ.succ.succ.succ.succ μ.succ.succ.succ.succ.succ A.succ.succ.succ.succ.succ 4 3 2 1 0) (.exMem H.succ.succ.succ.succ.succ (.exMem H.succ.succ.succ.succ.succ.succ (rectangleActorPairFormula P.succ.succ.succ.succ.succ.succ.succ μ.succ.succ.succ.succ.succ.succ.succ A.succ.succ.succ.succ.succ.succ.succ Q.succ.succ.succ.succ.succ.succ.succ H.succ.succ.succ.succ.succ.succ.succ R.succ.succ.succ.succ.succ.succ.succ ν.succ.succ.succ.succ.succ.succ.succ B.succ.succ.succ.succ.succ.succ.succ e.succ.succ.succ.succ.succ.succ.succ a.succ.succ.succ.succ.succ.succ.succ 6 5 4 3 2 1 0)))))))))

end BoundedFormula

end PartitionPilot.Forcing



end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Geometry_GroundCompressionOrigins
attribute [-instance] _root_.OAI.PartitionPilot.Forcing.GroundMainPrefix.withTopSmall
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI



namespace PartitionPilot.Forcing
open SetFormula
universe u

structure GroundCompressionUnionData (M : TransitiveGround.{u}) (initial : RecursiveStateData.{u})
    (I Sources Reps G m one T : ZFSet.{u}) where
  fields : Fin 13 → ZFSet.{u}
  ground : ∀ j, fields j ∈ M.sets
  fieldUnion : ∀ j, NatUnionCode
    (fun n => (initial.iterate M I Sources Reps G T n).field j) (fields j)
  currentCarrier : NatUnionCode
    (fun n => (initial.iterate M I Sources Reps G T n).currentCarrier) (fields 0)
  currentOrder : NatUnionCode
    (fun n => (initial.iterate M I Sources Reps G T n).currentOrder) (fields 1)
  currentMeet : NatUnionCode
    (fun n => (initial.iterate M I Sources Reps G T n).currentMeet) (fields 2)
  meet : MeetOrderCode (fields 0) (fields 1) (fields 2)
  action : PosetActionCode G (fields 0) m one (fields 1) (fields 12)

end PartitionPilot.Forcing



namespace PartitionPilot.Forcing
universe u

structure GroundCompressionHeightData (M : TransitiveGround.{u}) (initial : RecursiveStateData.{u})
    (I Sources Reps G m one T : ZFSet.{u})
    (union : GroundCompressionUnionData M initial I Sources Reps G m one T)
    (P0 C D rD original : ZFSet.{u}) where
  family : ZFSet.{u}
  family_ground : family ∈ M.sets
  function : FunctionGraphOn ZFSet.omega family
  zero : function.natValue 0 = original
  finite : ∀ n, StrictLexHeightCode (initial.iterate M I Sources Reps G T n).D C D
    (initial.iterate M I Sources Reps G T n).rD (function.natValue n) rD
  adjacent : ∀ n, function.natValue n ⊆ function.natValue (n + 1)
  height : ZFSet.{u}
  height_ground : height ∈ M.sets
  exact_union : NatUnionCode function.natValue height
  code : StrictLexHeightCode (union.fields 0) C D (union.fields 1) height rD
  finite_entries : ∀ n x, x ∈ (initial.iterate M I Sources Reps G T n).D → ∀ y,
    ZFSet.pair x y ∈ height ↔ ZFSet.pair x y ∈ function.natValue n
  original_entries : ∀ x ∈ P0, ∀ y, ZFSet.pair x y ∈ height ↔ ZFSet.pair x y ∈ original
  range_ground : relationImage (union.fields 0) (ZFSet.prod C D) height ∈ M.sets
  range_countable : M.groundEmbeddable (relationImage (union.fields 0) (ZFSet.prod C D) height) ZFSet.omega
  columns : ∀ x a q, ZFSet.pair x (ZFSet.pair a q) ∈ height → a ∈ heightColumns P0 C D original





structure CompressionOriginalData (P r μ A G U u ν B : ZFSet.{u}) : Prop where
  subset : P ⊆ U
  order : ∀ x ∈ P, ∀ y ∈ P, ZFSet.pair x y ∈ u ↔ ZFSet.pair x y ∈ r
  meet : ∀ x ∈ P, ∀ y ∈ P, ∀ z, ZFSet.pair (ZFSet.pair x y) z ∈ ν ↔
    ZFSet.pair (ZFSet.pair x y) z ∈ μ
  action : ∀ g x, x ∈ P → ∀ y, ZFSet.pair (ZFSet.pair g x) y ∈ B ↔
    ZFSet.pair (ZFSet.pair g x) y ∈ A
  agreement : ∀ g ∈ G, ∀ h ∈ G, ∀ v ∈ P, ActionAgreementBelow P r A g h v →
    ActionAgreementBelow U u B g h v






theorem ExternalRectangleCode.lift_compression
    {P r μ A G U u ν B m one c b d g h : ZFSet.{u}}
    (rectangle : ExternalRectangleCode P G r μ A c b d g h)
    (compression : CompressionOriginalData P r μ A G U u ν B)
    (action : PosetActionCode G P m one r A) :
    ExternalRectangleCode U G u ν B c b d g h := by
  obtain ⟨hc, hb, hd, hg, hh, cd, bd, w, hw, cb, agree, separated⟩ := rectangle
  refine ⟨compression.subset hc, compression.subset hb, compression.subset hd, hg, hh,
    (compression.order c hc d hd).2 cd, (compression.order b hb d hd).2 bd,
    w, compression.subset hw, (compression.meet c hc b hb w).2 cb,
    compression.agreement g hg h hh w hw agree, ?_⟩
  intro y _ z _ v _ entries
  have dy := (compression.action g d hd y).1 entries.1
  have dz := (compression.action h d hd z).1 entries.2.1
  have wv := (compression.action g w hw v).1 entries.2.2
  have hy := (ZFSet.pair_mem_prod.1 (action.function.1 dy)).2
  have hz := (ZFSet.pair_mem_prod.1 (action.function.1 dz)).2
  have hv := (ZFSet.pair_mem_prod.1 (action.function.1 wv)).2
  exact (compression.meet y hy z hz v).2 (separated y hy z hz v hv ⟨dy, dz, wv⟩)

end PartitionPilot.Forcing

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Geometry_CompressionUnionBaseFilling
attribute [-instance] _root_.OAI.PartitionPilot.Forcing.GroundMainPrefix.withTopSmall
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI



namespace PartitionPilot.Forcing
open SetFormula
universe u

structure GroundCompressionAlgebra (M : TransitiveGround.{u}) (initial : RecursiveStateData.{u})
    (I Sources Reps G m one T : ZFSet.{u}) where
  union : GroundCompressionUnionData M initial I Sources Reps G m one T
  maps : ZFSet.{u}
  ground : maps ∈ M.sets
  function : FunctionGraphOn I maps
  embedding : ∀ i f, ZFSet.pair i f ∈ maps →
    MeetEmbeddingCode (union.fields 0) (union.fields 0) (union.fields 1) (union.fields 1)
      (union.fields 2) (union.fields 2) f
  entries : ∀ i f, ZFSet.pair i f ∈ maps → ∀ z,
    z ∈ f ↔ ∃ n, ∃ old, ZFSet.pair i old ∈ (initial.iterate M I Sources Reps G T n).Maps ∧ z ∈ old
  restrict : ∀ i f, ZFSet.pair i f ∈ maps → ∀ n old,
    ZFSet.pair i old ∈ (initial.iterate M I Sources Reps G T n).Maps →
      ∀ x ∈ (initial.iterate M I Sources Reps G T n).D, ∀ y,
        ZFSet.pair x y ∈ f ↔ ZFSet.pair x y ∈ old

end PartitionPilot.Forcing



namespace PartitionPilot.Forcing
open SetFormula
universe u

namespace GroundCompressionAlgebra
variable {M : TransitiveGround.{u}} {initial : RecursiveStateData.{u}}
variable {I Sources Reps G m one T : ZFSet.{u}}

def bases (algebra : GroundCompressionAlgebra M initial I Sources Reps G m one T) : ZFSet.{u} :=
  familyEvaluationGraph I (algebra.union.fields 0) (algebra.union.fields 0)
    (ZFSet.sUnion (ZFSet.sUnion algebra.maps)) algebra.maps Sources

noncomputable def caps (algebra : GroundCompressionAlgebra M initial I Sources Reps G m one T)
    (τ : ZFSet.{u}) : ZFSet.{u} :=
  familyEvaluationGraph I (algebra.union.fields 0) (algebra.union.fields 0)
    (ZFSet.sUnion (ZFSet.sUnion algebra.maps)) algebra.maps (constantFamilyGraph I τ)

end GroundCompressionAlgebra

end PartitionPilot.Forcing



end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Definability_GroundExternalRequestSetRecognition
attribute [-instance] _root_.OAI.PartitionPilot.Forcing.GroundMainPrefix.withTopSmall
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PartitionPilot.Forcing

section
universe u

noncomputable def externalRequestCarrier (I P Rectangles : ZFSet.{u}) : ZFSet.{u} :=
  (ZFSet.prod {natSetCode 0} I ∪ ZFSet.prod {natSetCode 1} P) ∪
    ZFSet.prod {natSetCode 2} Rectangles

noncomputable def externalChildLetters (I P Rectangles : ZFSet.{u}) : ZFSet.{u} :=
  ZFSet.prod (externalRequestCarrier I P Rectangles) {natSetCode 0} ∪
    ZFSet.prod (ZFSet.prod {natSetCode 2} Rectangles) {natSetCode 1}

noncomputable def externalRequestTags : ZFSet.{u} :=
  insert (natSetCode 0) (insert (natSetCode 1) {natSetCode 2})

noncomputable def externalTileVertices (Requests Rectangles U : ZFSet.{u}) : ZFSet.{u} :=
  ZFSet.prod (ZFSet.prod Requests {natSetCode 0, natSetCode 1}) U ∪
    ZFSet.prod (ZFSet.prod (ZFSet.prod {natSetCode 2} Rectangles) {natSetCode 2}) U

namespace BoundedFormula
open SetFormula

def requestRectangleOverlapFieldsFormula {n} (r A zero first second i x j y c b g h : Fin n) : BoundedFormula n :=
  disj (.conj (.equal i zero) (.conj (.equal j first)
    (.conj (pairMembershipFormula y c r) (tripleMembershipFormula g y x A))))
    (disj (.conj (.equal i zero) (.conj (.equal j second)
      (.conj (pairMembershipFormula y c r) (tripleMembershipFormula h y x A))))
      (.conj (.equal i first) (.conj (.equal j second)
        (.conj (.equal x y) (pairMembershipFormula x b r)))))

def requestRectangleOverlapFormula {n}
    (P G Rectangles r A zero first second q i x j y : Fin n) : BoundedFormula n :=
  exMem Rectangles (exMem P.succ (exMem P.succ.succ (exMem P.succ.succ.succ
    (exMem G.succ.succ.succ.succ (exMem G.succ.succ.succ.succ.succ
      (.conj (orderedPairFormula q.succ.succ.succ.succ.succ.succ second.succ.succ.succ.succ.succ.succ 5)
        (.conj (externalRectangleTupleFormula 5 4 3 2 1 0)
          (requestRectangleOverlapFieldsFormula r.succ.succ.succ.succ.succ.succ A.succ.succ.succ.succ.succ.succ
            zero.succ.succ.succ.succ.succ.succ first.succ.succ.succ.succ.succ.succ second.succ.succ.succ.succ.succ.succ
            i.succ.succ.succ.succ.succ.succ x.succ.succ.succ.succ.succ.succ
            j.succ.succ.succ.succ.succ.succ y.succ.succ.succ.succ.succ.succ 4 3 1 0))))))))

def externalRequestOverlapForwardFormula {n}
    (P G Rectangles Maps F r A zero first second q i x j y : Fin n) : BoundedFormula n :=
  disj (compressionOverlapFormula Maps F zero first q i x j y)
    (disj (separationOverlapFormula P r zero first q i x j y)
      (requestRectangleOverlapFormula P G Rectangles r A zero first second q i x j y))

theorem truth_externalRequestOverlapForwardFormula {n}
    (P G Rectangles Maps F r A zero first second q i x j y : Fin n) (env : Fin n → ZFSet.{u}) :
    Truth (externalRequestOverlapForwardFormula P G Rectangles Maps F r A zero first second q i x j y) env ↔
      ExternalRequestOverlapForward (env P) (env G) (env Rectangles) (env Maps) (env F) (env r) (env A)
        (env zero) (env first) (env second) (env q) (env i) (env x) (env j) (env y) := by
  simp only [externalRequestOverlapForwardFormula, compressionOverlapFormula, separationOverlapFormula,
    requestRectangleOverlapFormula, requestRectangleOverlapFieldsFormula, Truth, truth_disj, truth_exMem,
    truth_orderedPairFormula, truth_pairMembershipFormula, truth_tripleMembershipFormula,
    truth_externalRectangleTupleFormula, ExternalRequestOverlapForward]
  rfl

def externalRequestOverlapFormula {n}
    (P G Rectangles Maps F r A zero first second q i x j y : Fin n) : BoundedFormula n :=
  disj (.conj (.equal i j) (.equal x y))
    (disj (externalRequestOverlapForwardFormula P G Rectangles Maps F r A zero first second q i x j y)
      (externalRequestOverlapForwardFormula P G Rectangles Maps F r A zero first second q j y i x))

theorem truth_externalRequestOverlapFormula {n}
    (P G Rectangles Maps F r A zero first second q i x j y : Fin n) (env : Fin n → ZFSet.{u}) :
    Truth (externalRequestOverlapFormula P G Rectangles Maps F r A zero first second q i x j y) env ↔
      ExternalRequestOverlapCode (env P) (env G) (env Rectangles) (env Maps) (env F) (env r) (env A)
        (env zero) (env first) (env second) (env q) (env i) (env x) (env j) (env y) := by
  simp only [externalRequestOverlapFormula, Truth, truth_disj,
    truth_externalRequestOverlapForwardFormula, ExternalRequestOverlapCode]

end BoundedFormula

end

section
open SetRealization
universe u

abbrev ExternalRequestIndex (I P R : ZFSet.{u}) :=
  SetMembers I ⊕ (SetMembers P ⊕ SetMembers R)

noncomputable def externalRequestIndexCode {I P R : ZFSet.{u}} :
    ExternalRequestIndex I P R → ZFSet.{u}
  | .inl i => ZFSet.pair (natSetCode 0) (SetMembers.raw i)
  | .inr (.inl x) => ZFSet.pair (natSetCode 1) (SetMembers.raw x)
  | .inr (.inr r) => ZFSet.pair (natSetCode 2) (SetMembers.raw r)

def ExternalRequestChild {I P R : ZFSet.{u}} : ExternalRequestIndex I P R → Type u
  | .inl _ => ULift.{u} Unit
  | .inr (.inl _) => ULift.{u} Unit
  | .inr (.inr _) => ULift.{u} Bool

end

open SetFormula
universe u

end PartitionPilot.Forcing

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Geometry_GroundExternalRequestOverlaps
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

noncomputable def externalRequestOverlapGraph
    (Requests P G Rectangles Maps U r A : ZFSet.{u}) : ZFSet.{u} :=
  let V := externalTileVertices Requests Rectangles U
  ZFSet.sep (fun z => ∃ a ∈ V, ∃ b ∈ V, ∃ q ∈ Requests,
    ∃ i ∈ externalRequestTags, ∃ x ∈ U, ∃ j ∈ externalRequestTags, ∃ y ∈ U,
      z = ZFSet.pair a b ∧ a = ZFSet.pair (ZFSet.pair q i) x ∧
        b = ZFSet.pair (ZFSet.pair q j) y ∧
        ExternalRequestOverlapCode P G Rectangles Maps (ZFSet.sUnion (ZFSet.sUnion Maps)) r A
          (natSetCode 0) (natSetCode 1) (natSetCode 2) q i x j y) (ZFSet.prod V V)

namespace BoundedFormula

def externalRequestOverlapEntryFormula {n}
    (z V Requests Tags U P G Rectangles Maps F r A zero first second : Fin n) : BoundedFormula n :=
  exMem V (exMem V.succ (exMem Requests.succ.succ (exMem Tags.succ.succ.succ
    (exMem U.succ.succ.succ.succ (exMem Tags.succ.succ.succ.succ.succ
      (exMem U.succ.succ.succ.succ.succ.succ
        (.conj (orderedPairFormula z.succ.succ.succ.succ.succ.succ.succ 6 5)
          (.conj (orderedTripleFormula 6 4 3 2)
            (.conj (orderedTripleFormula 5 4 1 0)
              (externalRequestOverlapFormula P.succ.succ.succ.succ.succ.succ.succ
                G.succ.succ.succ.succ.succ.succ.succ Rectangles.succ.succ.succ.succ.succ.succ.succ
                Maps.succ.succ.succ.succ.succ.succ.succ F.succ.succ.succ.succ.succ.succ.succ
                r.succ.succ.succ.succ.succ.succ.succ A.succ.succ.succ.succ.succ.succ.succ
                zero.succ.succ.succ.succ.succ.succ.succ first.succ.succ.succ.succ.succ.succ.succ
                second.succ.succ.succ.succ.succ.succ.succ 4 3 2 1 0))))))))))

theorem truth_externalRequestOverlapEntryFormula {n}
    (z V Requests Tags U P G Rectangles Maps F r A zero first second : Fin n) (env : Fin n → ZFSet.{u}) :
    Truth (externalRequestOverlapEntryFormula z V Requests Tags U P G Rectangles Maps F r A zero first second) env ↔
      ∃ a ∈ env V, ∃ b ∈ env V, ∃ q ∈ env Requests,
        ∃ i ∈ env Tags, ∃ x ∈ env U, ∃ j ∈ env Tags, ∃ y ∈ env U,
          env z = ZFSet.pair a b ∧ a = ZFSet.pair (ZFSet.pair q i) x ∧
            b = ZFSet.pair (ZFSet.pair q j) y ∧
            ExternalRequestOverlapCode (env P) (env G) (env Rectangles) (env Maps) (env F) (env r) (env A)
              (env zero) (env first) (env second) q i x j y := by
  simp only [externalRequestOverlapEntryFormula, Truth, truth_exMem, truth_orderedPairFormula,
    truth_orderedTripleFormula, truth_externalRequestOverlapFormula]
  rfl

end BoundedFormula

end PartitionPilot.Forcing

end

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Transfinite_GroundBatchBirths
attribute [-instance] _root_.OAI.PartitionPilot.Forcing.GroundMainPrefix.withTopSmall
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PartitionPilot.Forcing

section

universe u

theorem MeetEmbeddingCode.enlarge_target
    {A L L' rA r r' μA μ μ' e : ZFSet.{u}}
    (embedding : MeetEmbeddingCode A L rA r μA μ e)
    (carrier : L ⊆ L') (order : r ⊆ r') (meets : μ ⊆ μ') :
    MeetEmbeddingCode A L' rA r' μA μ' e := by
  refine ⟨⟨⟨?_, embedding.injection.function.2⟩, embedding.injection.injective⟩,
    fun x y x' y' below first second => order (embedding.monotone x y x' y' below first second),
    fun x y z x' y' z' meet first second third =>
      meets (embedding.map_meet x y z x' y' z' meet first second third)⟩
  intro z hz
  obtain ⟨x, hx, y, hy, rfl⟩ := ZFSet.mem_prod.1 (embedding.injection.function.1 hz)
  exact ZFSet.pair_mem_prod.2 ⟨hx, carrier hy⟩

theorem relationImage_enlarge_target {A L L' e : ZFSet.{u}} (carrier : L ⊆ L') :
    relationImage A L e ⊆ relationImage A L' e := by
  intro x hx
  obtain ⟨hxL, witness⟩ := (mem_relationImage A L e x).1 hx
  exact (mem_relationImage A L' e x).2 ⟨carrier hxL, witness⟩

theorem OldBridgeCode.of_literal_extension
    {L L' r r' μ μ' birth birth' t x y : ZFSet.{u}}
    (bridge : OldBridgeCode L r μ birth t x y)
    (carrier : L ⊆ L') (order : r ⊆ r') (meets : μ ⊆ μ') (born : birth ⊆ birth') :
    OldBridgeCode L' r' μ' birth' t x y := by
  rcases bridge with ⟨z, a, meet, entry, earlier⟩ | ⟨z, hz, a, entry, earlier, between⟩
  · exact Or.inl ⟨z, a, meets meet, born entry, earlier⟩
  · exact Or.inr ⟨z, carrier hz, a, born entry, earlier,
      between.elim (fun h => Or.inl ⟨order h.1, order h.2⟩)
        (fun h => Or.inr ⟨order h.1, order h.2⟩)⟩

def CodedGrowthLayer.of_literal_extension
    {M : TransitiveGround.{u}} {Space sourceOrder sourceMeet : ZFSet.{u} → ZFSet.{u}}
    {L L' r r' μ μ' birth birth' t : ZFSet.{u}}
    (layer : CodedGrowthLayer M Space sourceOrder sourceMeet L r μ birth t)
    (separation : SetFormula.SeparationSchema M.sets) (hL : L ∈ M.sets)
    (carrier : L ⊆ L') (order : r ⊆ r') (meets : μ ⊆ μ') (born : birth ⊆ birth')
    (fiber : ∀ x ∈ L', ZFSet.pair x t ∈ birth' → x ∈ L ∧ ZFSet.pair x t ∈ birth) :
    CodedGrowthLayer M Space sourceOrder sourceMeet L' r' μ' birth' t := by
  cases layer with
  | countablePoints D ground small cover =>
    exact .countablePoints D ground small (fun x hx entry =>
      cover x (fiber x hx entry).1 (fiber x hx entry).2)
  | copies I parts groundI small groundParts index e earlier groundCopy embedding cover inCopy =>
    let retained := ZFSet.sep (fun z => z ∈ ZFSet.prod I L) parts
    refine .copies I retained groundI small
      (M.injection_restriction_mem separation groundI hL groundParts) index e earlier groundCopy
      (fun i hi => (embedding i hi).enlarge_target carrier order meets)
      ?_ ?_
    · intro x hx entry
      have old := fiber x hx entry
      obtain ⟨i, hi, part⟩ := cover x old.1 old.2
      exact ⟨i, hi, ZFSet.mem_sep.2 ⟨part, ZFSet.pair_mem_prod.2 ⟨hi, old.1⟩⟩⟩
    · intro i hi x _ entry
      obtain ⟨part, bound⟩ := ZFSet.mem_sep.1 entry
      have hxL := (ZFSet.pair_mem_prod.1 bound).2
      exact relationImage_enlarge_target carrier (inCopy i hi x hxL part)
  | separated I index e earlier groundCopy embedding component cover separated =>
    let oldPoint (x : {x : ZFSet.{u} // x ∈ L' ∧ ZFSet.pair x t ∈ birth'}) :
        {x : ZFSet.{u} // x ∈ L ∧ ZFSet.pair x t ∈ birth} :=
      ⟨x.val, fiber x.val x.property.1 x.property.2⟩
    exact .separated I index e earlier groundCopy
      (fun i => (embedding i).enlarge_target carrier order meets)
      (fun x => component (oldPoint x))
      (fun x => relationImage_enlarge_target carrier (cover (oldPoint x)))
      (fun x y different => (separated (oldPoint x) (oldPoint y) different).of_literal_extension
        carrier order meets born)

end

namespace CodedGrowthLayer
open SetFormula
universe u

def empty_of_no_birth {M : TransitiveGround.{u}}
    {Space sourceOrder sourceMeet : ZFSet.{u} → ZFSet.{u}}
    {L r μ birth t : ZFSet.{u}} (inhabited : M.sets.Nonempty)
    (empty : ∀ x ∈ L, ZFSet.pair x t ∉ birth) :
    CodedGrowthLayer M Space sourceOrder sourceMeet L r μ birth t :=
  .countablePoints ∅ (M.empty_mem inhabited) (M.empty_groundEmbeddable ZFSet.omega inhabited)
    (fun x hx entry => False.elim (empty x hx entry))

end CodedGrowthLayer

open SetRealization SetFormula
universe u

end PartitionPilot.Forcing

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Transfinite_GroundCompressionBirthData
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

namespace BoundedFormula

def firstAppearanceBirthEntryFormula {k} (z omega u t domains stamps old bound : Fin k) :
    BoundedFormula k :=
  disj (.mem z old)
    (exMem omega (exMem omega.succ (exMem bound.succ.succ
      (exMem bound.succ.succ.succ (exMem u.succ.succ.succ.succ
        (exMem t.succ.succ.succ.succ.succ
          (.conj (orderedPairFormula z.succ.succ.succ.succ.succ.succ 1 0)
            (.conj (successorFormula 4 5)
              (.conj (pairMembershipFormula 5 3 domains.succ.succ.succ.succ.succ.succ)
                (.conj (pairMembershipFormula 4 2 domains.succ.succ.succ.succ.succ.succ)
                  (.conj (pairMembershipFormula 5 0 stamps.succ.succ.succ.succ.succ.succ)
                    (.conj (.mem 1 2) (.neg (.mem 1 3))))))))))))))

end BoundedFormula

end PartitionPilot.Forcing



namespace PartitionPilot.Forcing
universe u

structure GroundCompressionBirthData (M : TransitiveGround.{u}) (initial : RecursiveStateData.{u})
    (I Sources Reps G m one T : ZFSet.{u})
    (data : GroundCompressionUnionData M initial I Sources Reps G m one T)
    (base old : ZFSet.{u}) where
  stamps : ZFSet.{u}
  stamps_ground : stamps ∈ M.sets
  limit : ZFSet.{u}
  limit_ground : limit ∈ M.sets
  times : CompressionStampCode base stamps limit
  birth : ZFSet.{u}
  birth_ground : birth ∈ M.sets
  extension : NatBirthExtensionCode (fun n => (initial.iterate M I Sources Reps G T n).D)
    (compressionStamp base) old birth
  family : ZFSet.{u}
  family_ground : family ∈ M.sets
  family_function : FunctionGraphOn ZFSet.omega family
  family_entries : ∀ n b, ZFSet.pair (natSetCode n) b ∈ family ↔
    b = graphRestriction (initial.iterate M I Sources Reps G T n).D birth
  initial_function : ZFSet.IsFunc initial.D limit old
  initial_bound : ∀ x t, ZFSet.pair x t ∈ old → t ∈ base ∨ t = base
  function : ZFSet.IsFunc (data.fields 0) limit birth
  original : graphRestriction initial.D birth = old
  finite_old_meet : ∀ n, OldMeetCode (initial.iterate M I Sources Reps G T n).rD
    (initial.iterate M I Sources Reps G T n).μD
    (graphRestriction (initial.iterate M I Sources Reps G T n).D birth)
  old_meet : OldMeetCode (data.fields 1) (data.fields 2) birth
  no_limit_birth : ∀ x, ZFSet.pair x limit ∉ birth

end PartitionPilot.Forcing

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Transfinite_SmallTileHeightInputs
attribute [-instance] _root_.OAI.PartitionPilot.Forcing.GroundMainPrefix.withTopSmall
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PartitionPilot.Forcing
open SetRealization Compression Compression.RecursiveMaps
universe u

variable {P G r μ A m inv one c b d g h : ZFSet.{u}}

noncomputable def ExternalRectangleCode.toSmallActionRectangle
    (code : ExternalRectangleCode P G r μ A c b d g h)
    (group : GroupCode G m inv one) (action : PosetActionCode G P m one r A)
    (meet : MeetOrderCode P r μ) :
    ActionRectangle meet.toSmallMeetOrder (action.toSmallMeetIso group meet) := by
  obtain ⟨hc, hb, hd, hg, hh, cd, bd, witness⟩ := code
  let w := Classical.choose witness
  have mw := (Classical.choose_spec witness).2.1
  have agree := (Classical.choose_spec witness).2.2.1
  have separated := (Classical.choose_spec witness).2.2.2
  let C := SetMembers.ofMem c hc
  let B := SetMembers.ofMem b hb
  let D := SetMembers.ofMem d hd
  let first := SetMembers.ofMem g hg
  let second := SetMembers.ofMem h hh
  have meetValue : SetMembers.raw (meet.smallMeet C B) = w := by
    apply (show FunctionGraphOn (ZFSet.prod P P) μ from ⟨P, meet.operation⟩).unique
      (meet.smallMeet_entry C B)
    simpa only [C, B, SetMembers.raw_ofMem] using mw
  refine {
    C := C
    B := B
    D := D
    first := first
    second := second
    C_le_D := ?_
    B_le_D := ?_
    agree := ?_
    separated := ?_ }
  · simpa only [MeetOrderCode.toSmallMeetOrder, C, D, SetMembers.raw_ofMem] using cd
  · simpa only [MeetOrderCode.toSmallMeetOrder, B, D, SetMembers.raw_ofMem] using bd
  · intro x lower
    apply SetMembers.raw_injective P
    have lowerW : ZFSet.pair (SetMembers.raw x) w ∈ r := meetValue ▸ lower
    apply agree.entry_eq action hh (SetMembers.raw_mem x) lowerW
    · simpa only [first, SetMembers.raw_ofMem, PosetActionCode.toSmallMeetIso] using action.act_mem first x
    · simpa only [second, SetMembers.raw_ofMem, PosetActionCode.toSmallMeetIso] using action.act_mem second x
  · apply SetMembers.raw_injective P
    let y := action.act first D
    let z := action.act second D
    let v := action.act first (meet.smallMeet C B)
    have actMeet : ZFSet.pair (ZFSet.pair g w) (SetMembers.raw v) ∈ A := by
      rw [← meetValue]
      simpa only [first, SetMembers.raw_ofMem] using action.act_mem first (meet.smallMeet C B)
    have value := separated (SetMembers.raw y) (SetMembers.raw_mem y)
      (SetMembers.raw z) (SetMembers.raw_mem z) (SetMembers.raw v) (SetMembers.raw_mem v)
      ⟨by simpa only [first, D, SetMembers.raw_ofMem] using action.act_mem first D,
        by simpa only [second, D, SetMembers.raw_ofMem] using action.act_mem second D, actMeet⟩
    exact (show FunctionGraphOn (ZFSet.prod P P) μ from ⟨P, meet.operation⟩).unique
      (meet.smallMeet_entry y z) value

theorem ExternalRectangleCode.toSmallActionRectangle_fields
    (code : ExternalRectangleCode P G r μ A c b d g h)
    (group : GroupCode G m inv one) (action : PosetActionCode G P m one r A)
    (meet : MeetOrderCode P r μ) :
    let request := code.toSmallActionRectangle group action meet
    SetMembers.raw request.C = c ∧ SetMembers.raw request.B = b ∧
      SetMembers.raw request.D = d ∧ SetMembers.raw request.first = g ∧ SetMembers.raw request.second = h := by
  obtain ⟨hc, hb, hd, hg, hh, cd, bd, witness⟩ := code
  exact ⟨SetMembers.raw_ofMem _ _, SetMembers.raw_ofMem _ _, SetMembers.raw_ofMem _ _,
    SetMembers.raw_ofMem _ _, SetMembers.raw_ofMem _ _⟩

end PartitionPilot.Forcing



end

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Geometry_CompressionExternalTileOverlaps
attribute [-instance] _root_.OAI.PartitionPilot.Forcing.GroundMainPrefix.withTopSmall
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace PartitionPilot.Forcing
universe u

structure GroundCompressionCompletion (M : TransitiveGround.{u}) (initial : RecursiveStateData.{u})
    (I Sources Reps G m one T τ : ZFSet.{u}) where
  algebra : GroundCompressionAlgebra M initial I Sources Reps G m one T
  bases_ground : algebra.bases ∈ M.sets
  caps_ground : algebra.caps τ ∈ M.sets
  bases_function : ZFSet.IsFunc I (algebra.union.fields 0) algebra.bases
  caps_function : ZFSet.IsFunc I (algebra.union.fields 0) (algebra.caps τ)
  top_mem : τ ∈ algebra.union.fields 0
  top : ∀ x ∈ algebra.union.fields 0, ZFSet.pair x τ ∈ algebra.union.fields 1
  range : ∀ i f k x, ZFSet.pair i f ∈ algebra.maps → ZFSet.pair i k ∈ algebra.caps τ →
    ((∃ y ∈ algebra.union.fields 0, ZFSet.pair y x ∈ f) ↔
      x ∈ algebra.union.fields 0 ∧ ZFSet.pair x k ∈ algebra.union.fields 1)
  equivariant : ∀ g i j f h x y z,
    ZFSet.pair (ZFSet.pair g i) j ∈ T →
    ZFSet.pair i f ∈ algebra.maps → ZFSet.pair j h ∈ algebra.maps →
    ZFSet.pair x y ∈ f → ZFSet.pair x z ∈ h →
      ZFSet.pair (ZFSet.pair g y) z ∈ algebra.union.fields 12
  source_agreement : ∀ i f a g x y,
    ZFSet.pair i f ∈ algebra.maps → ZFSet.pair i a ∈ Sources → ZFSet.pair i g ∈ Reps →
    ZFSet.pair x a ∈ algebra.union.fields 1 →
      (ZFSet.pair x y ∈ f ↔ ZFSet.pair (ZFSet.pair g x) y ∈ algebra.union.fields 12)

end PartitionPilot.Forcing



namespace PartitionPilot.Forcing
open SetFormula
universe u

noncomputable def externalCompressionField (I V F : ZFSet.{u}) : ZFSet.{u} :=
  relationCompose (ZFSet.prod {natSetCode 0} I) I V (productSecond {natSetCode 0} I) F

namespace GroundCompressionCompletion
variable {M : TransitiveGround.{u}} {initial : RecursiveStateData.{u}}
variable {I Sources Reps G m one T τ : ZFSet.{u}}
variable (completion : GroundCompressionCompletion M initial I Sources Reps G m one T τ)

noncomputable def externalMaps : ZFSet.{u} :=
  externalCompressionField I completion.algebra.maps.sUnion.sUnion completion.algebra.maps

end GroundCompressionCompletion

end PartitionPilot.Forcing



namespace PartitionPilot.Forcing
universe u

structure GroundHeightedCompression (M : TransitiveGround.{u}) (initial : RecursiveStateData.{u})
    (I Sources Reps G m one T τ P0 C D rD original : ZFSet.{u}) where
  completion : GroundCompressionCompletion M initial I Sources Reps G m one T τ
  heights : GroundCompressionHeightData M initial I Sources Reps G m one T
    completion.algebra.union P0 C D rD original

end PartitionPilot.Forcing



namespace PartitionPilot.Forcing
universe u

structure GroundProfiledCompression (M : TransitiveGround.{u}) (initial : RecursiveStateData.{u})
    (I Sources Reps G m one T τ P0 C D rD original Targets Separators Filters : ZFSet.{u}) where
  heighted : GroundHeightedCompression M initial I Sources Reps G m one T τ P0 C D rD original
  profiles : CodedCompressionProfiles
    (heighted.completion.algebra.union.fields 0) (heighted.completion.algebra.union.fields 1)
    (heighted.completion.algebra.union.fields 2) (heighted.completion.algebra.caps τ)
    Targets Separators Filters

end PartitionPilot.Forcing



namespace PartitionPilot.Forcing
universe u

structure GroundBornCompression (M : TransitiveGround.{u}) (initial : RecursiveStateData.{u})
    (I Sources Reps G m one T τ P0 C D rD original Targets Separators Filters base old : ZFSet.{u}) where
  profiled : GroundProfiledCompression M initial I Sources Reps G m one T τ P0 C D rD original
    Targets Separators Filters
  births : GroundCompressionBirthData M initial I Sources Reps G m one T
    profiled.heighted.completion.algebra.union base old

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

def tileStarVertexCarrier (Q E R : ZFSet.{u}) : ZFSet.{u} := taggedSumCarrier Q (ZFSet.prod E R)
def tileStarEdgeCarrier (E R S : ZFSet.{u}) : ZFSet.{u} := taggedSumCarrier (ZFSet.prod E R) (ZFSet.prod E S)
def tileStarDartCarrier (E R S : ZFSet.{u}) : ZFSet.{u} := ZFSet.prod (tileStarEdgeCarrier E R S) (natSetCode 2)

end

open SetFormula
universe u

def TileStarSourceEntry (E R S Q Edges C request generators multiplication d v : ZFSet.{u}) : Prop :=
  ∃ e ∈ Edges,
    (∃ w ∈ E, ∃ r ∈ R, e = ZFSet.pair (natSetCode 0) (ZFSet.pair w r) ∧
      ((d = ZFSet.pair e (natSetCode 1) ∧ ∃ q ∈ Q, ZFSet.pair w q ∈ C ∧ v = ZFSet.pair (natSetCode 0) q) ∨
       (d = ZFSet.pair e (natSetCode 0) ∧ v = ZFSet.pair (natSetCode 1) (ZFSet.pair w r)))) ∨
    (∃ w ∈ E, ∃ s ∈ S, e = ZFSet.pair (natSetCode 1) (ZFSet.pair w s) ∧
      ((d = ZFSet.pair e (natSetCode 1) ∧ ∃ r ∈ R, ZFSet.pair s r ∈ request ∧ v = ZFSet.pair (natSetCode 1) (ZFSet.pair w r)) ∨
       (d = ZFSet.pair e (natSetCode 0) ∧ ∃ k ∈ E, ∃ a ∈ E, ∃ q ∈ Q,
         ZFSet.pair s k ∈ generators ∧ ZFSet.pair (ZFSet.pair w k) a ∈ multiplication ∧
         ZFSet.pair a q ∈ C ∧ v = ZFSet.pair (natSetCode 0) q)))

def TileStarReverseEntry (Edges d v : ZFSet.{u}) : Prop :=
  ∃ e ∈ Edges,
    (d = ZFSet.pair e (natSetCode 0) ∧ v = ZFSet.pair e (natSetCode 1)) ∨
    (d = ZFSet.pair e (natSetCode 1) ∧ v = ZFSet.pair e (natSetCode 0))

noncomputable def tileStarSourceGraph (E R S Q C request generators multiplication : ZFSet.{u}) : ZFSet.{u} :=
  ZFSet.sep (fun z => ∃ d ∈ tileStarDartCarrier E R S, ∃ v ∈ tileStarVertexCarrier Q E R,
    z = ZFSet.pair d v ∧ TileStarSourceEntry E R S Q (tileStarEdgeCarrier E R S) C request generators multiplication d v)
    (ZFSet.prod (tileStarDartCarrier E R S) (tileStarVertexCarrier Q E R))

noncomputable def tileStarReverseGraph (E R S : ZFSet.{u}) : ZFSet.{u} :=
  ZFSet.sep (fun z => ∃ d ∈ tileStarDartCarrier E R S, ∃ v ∈ tileStarDartCarrier E R S,
    z = ZFSet.pair d v ∧ TileStarReverseEntry (tileStarEdgeCarrier E R S) d v)
    (ZFSet.prod (tileStarDartCarrier E R S) (tileStarDartCarrier E R S))

namespace BoundedFormula

def tileStarSourceFormula {n} (E R S Q Edges C request generators multiplication d v zero one : Fin n) : BoundedFormula n :=
  (exMem Edges (disj (exMem E.succ (exMem R.succ.succ (.conj (orderedRightTripleFormula 2 zero.succ.succ.succ 1 0) (disj (.conj (orderedPairFormula d.succ.succ.succ 2 one.succ.succ.succ) (exMem Q.succ.succ.succ (.conj (pairMembershipFormula 2 0 C.succ.succ.succ.succ) (orderedPairFormula v.succ.succ.succ.succ zero.succ.succ.succ.succ 0)))) (.conj (orderedPairFormula d.succ.succ.succ 2 zero.succ.succ.succ) (orderedRightTripleFormula v.succ.succ.succ one.succ.succ.succ 1 0)))))) (exMem E.succ (exMem S.succ.succ (.conj (orderedRightTripleFormula 2 one.succ.succ.succ 1 0) (disj (.conj (orderedPairFormula d.succ.succ.succ 2 one.succ.succ.succ) (exMem R.succ.succ.succ (.conj (pairMembershipFormula 1 0 request.succ.succ.succ.succ) (orderedRightTripleFormula v.succ.succ.succ.succ one.succ.succ.succ.succ 2 0)))) (.conj (orderedPairFormula d.succ.succ.succ 2 zero.succ.succ.succ) (exMem E.succ.succ.succ (exMem E.succ.succ.succ.succ (exMem Q.succ.succ.succ.succ.succ (.conj (pairMembershipFormula 3 2 generators.succ.succ.succ.succ.succ.succ) (.conj (tripleMembershipFormula 4 2 1 multiplication.succ.succ.succ.succ.succ.succ) (.conj (pairMembershipFormula 1 0 C.succ.succ.succ.succ.succ.succ) (orderedPairFormula v.succ.succ.succ.succ.succ.succ zero.succ.succ.succ.succ.succ.succ 0))))))))))))))

theorem truth_tileStarSourceFormula {n} (E R S Q Edges C request generators multiplication d v zero one : Fin n)
    (env : Fin n → ZFSet.{u}) (hz : env zero = natSetCode 0) (ho : env one = natSetCode 1) :
    Truth (tileStarSourceFormula E R S Q Edges C request generators multiplication d v zero one) env ↔
      TileStarSourceEntry (env E) (env R) (env S) (env Q) (env Edges) (env C)
        (env request) (env generators) (env multiplication) (env d) (env v) := by
  simp only [tileStarSourceFormula, Truth, truth_disj, truth_exMem, truth_orderedPairFormula,
    truth_orderedRightTripleFormula, truth_pairMembershipFormula, truth_tripleMembershipFormula]
  unfold TileStarSourceEntry
  simp only [extend, Fin.cases_zero, Fin.cases_succ]
  rw [hz, ho]
  rfl

theorem truth_tileStarReverseFormula {n} (Edges d v zero one : Fin n) (env : Fin n → ZFSet.{u})
    (hz : env zero = natSetCode 0) (ho : env one = natSetCode 1) :
    Truth (tileStarReverseFormula Edges d v zero one) env ↔ TileStarReverseEntry (env Edges) (env d) (env v) := by
  simp only [tileStarReverseFormula, Truth, truth_disj, truth_exMem, truth_orderedPairFormula]
  unfold TileStarReverseEntry
  simp only [extend, Fin.cases_zero, Fin.cases_succ]
  rw [hz, ho]

def tileStarSourceEntryFormula {n} (z D V E R S Q Edges C request generators multiplication zero one : Fin n) : BoundedFormula n :=
  exMem D (exMem V.succ (.conj (orderedPairFormula z.succ.succ 1 0)
    (tileStarSourceFormula E.succ.succ R.succ.succ S.succ.succ Q.succ.succ Edges.succ.succ C.succ.succ request.succ.succ generators.succ.succ multiplication.succ.succ 1 0 zero.succ.succ one.succ.succ)))

theorem truth_tileStarSourceEntryFormula {n} (z D V E R S Q Edges C request generators multiplication zero one : Fin n)
    (env : Fin n → ZFSet.{u}) (hz : env zero = natSetCode 0) (ho : env one = natSetCode 1) :
    Truth (tileStarSourceEntryFormula z D V E R S Q Edges C request generators multiplication zero one) env ↔
      ∃ d ∈ env D, ∃ v ∈ env V, env z = ZFSet.pair d v ∧
        TileStarSourceEntry (env E) (env R) (env S) (env Q) (env Edges) (env C) (env request) (env generators) (env multiplication) d v := by
  simp only [tileStarSourceEntryFormula, truth_exMem, Truth, truth_orderedPairFormula]
  apply exists_congr
  intro d
  apply and_congr_right
  intro _
  apply exists_congr
  intro v
  apply and_congr_right
  intro _
  exact and_congr Iff.rfl (truth_tileStarSourceFormula E.succ.succ R.succ.succ S.succ.succ Q.succ.succ Edges.succ.succ C.succ.succ request.succ.succ generators.succ.succ multiplication.succ.succ 1 0
    zero.succ.succ one.succ.succ _ hz ho)

theorem truth_tileStarReverseEntryFormula {n} (z D V Edges zero one : Fin n)
    (env : Fin n → ZFSet.{u}) (hz : env zero = natSetCode 0) (ho : env one = natSetCode 1) :
    Truth (tileStarReverseEntryFormula z D V Edges zero one) env ↔
      ∃ d ∈ env D, ∃ v ∈ env V, env z = ZFSet.pair d v ∧
        TileStarReverseEntry (env Edges) d v := by
  simp only [tileStarReverseEntryFormula, truth_exMem, Truth, truth_orderedPairFormula]
  apply exists_congr
  intro d
  apply and_congr_right
  intro _
  apply exists_congr
  intro v
  apply and_congr_right
  intro _
  exact and_congr Iff.rfl (truth_tileStarReverseFormula Edges.succ.succ 1 0
    zero.succ.succ one.succ.succ _ hz ho)

end BoundedFormula

end PartitionPilot.Forcing

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Geometry_GroundBatchHeightGraphs
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

namespace BoundedFormula

open SetFormula

def taggedHeightEntryFormula {n} (w P N H fresh : Fin n) : BoundedFormula n :=
  exMem N (exMem H.succ
    (.conj (orderedTripleFormula w.succ.succ P.succ.succ 1 0)
      (pairMembershipFormula 1 0 fresh.succ.succ)))

end BoundedFormula

end PartitionPilot.Forcing

end

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

namespace BoundedFormula

def lexHeightEntryFormula {n} (z C D rD : Fin n) : BoundedFormula n :=
  let lift (i : Fin n) := i.succ.succ.succ.succ
  exMem C (exMem D.succ (exMem C.succ.succ (exMem D.succ.succ.succ
    (.conj (pairOfPairsFormula (lift z) 3 2 1 0)
      (disj (.mem 3 1) (.conj (.equal 3 1) (pairMembershipFormula 2 0 (lift rD))))))))

end BoundedFormula

end PartitionPilot.Forcing



end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Models_GroundCoherentHeightChoices
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

namespace BoundedFormula

def stagedGraphEntryFormula {n} (z omega b : Fin n) : BoundedFormula n :=
  exMem omega (exMem omega.succ (exMem b.succ.succ (exMem b.succ.succ.succ
    (.conj (pairOfPairsFormula z.succ.succ.succ.succ 3 1 2 0)
      (.conj (successorFormula 2 3) (subsetFormula 1 0))))))

end BoundedFormula

end PartitionPilot.Forcing

end

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Definability_StrictLexHeightFormulas
attribute [-instance] _root_.OAI.PartitionPilot.Forcing.GroundMainPrefix.withTopSmall
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PartitionPilot.Forcing.BoundedFormula

open SetFormula
universe u

def heightColumnsBoundFormula {n} (P C D height columns : Fin n) : BoundedFormula n :=
  .allMem P (.allMem C.succ (.allMem D.succ.succ
    (imp (rightTripleMembershipFormula 2 1 0 height.succ.succ.succ)
      (.mem 1 columns.succ.succ.succ))))

end PartitionPilot.Forcing.BoundedFormula

end

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Transfinite_GroundSerializedChronologyTimeEquality
attribute [-instance] _root_.OAI.PartitionPilot.Forcing.GroundMainPrefix.withTopSmall
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI



namespace PartitionPilot.Forcing
open SetFormula
universe u

structure ChronologyPointCode (T C D rD s L r μ birth height : ZFSet.{u}) : Prop where
  meet : MeetOrderCode L r μ
  birth_function : ZFSet.IsFunc L T birth
  birth_bound : ∀ x ∈ L, ∀ t, ZFSet.pair x t ∈ birth → t = s ∨ t ∈ s
  old_meet : OldMeetCode r μ birth
  strict_height : StrictLexHeightCode L C D r height rD





structure ChronologyCoreCode (T V C D rD : ZFSet.{u})
    (graphs : Fin 5 → ZFSet.{u}) : Prop where
  function : ∀ j, ZFSet.IsFunc T V (graphs j)
  point : ∀ s ∈ T, ∀ L r μ birth height,
    ZFSet.pair s L ∈ graphs 0 → ZFSet.pair s r ∈ graphs 1 →
    ZFSet.pair s μ ∈ graphs 2 → ZFSet.pair s birth ∈ graphs 3 →
    ZFSet.pair s height ∈ graphs 4 → ChronologyPointCode T C D rD s L r μ birth height

end PartitionPilot.Forcing



end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Geometry_GroundInitialCompressionOrigin
attribute [-instance] _root_.OAI.PartitionPilot.Forcing.GroundMainPrefix.withTopSmall
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace PartitionPilot.Forcing
universe u





namespace BoundedFormula
open SetFormula

def heightCandidateEntryFormula {n}
    (z omega B Ps Rs C D rD original K boundPs boundRs : Fin n) : BoundedFormula n :=
  let lift (i : Fin n) := i.succ.succ.succ.succ
  exMem omega (exMem B.succ (exMem boundPs.succ.succ (exMem boundRs.succ.succ.succ
    (.conj (orderedPairFormula (lift z) 3 2)
      (.conj (pairMembershipFormula 3 1 (lift Ps))
        (.conj (pairMembershipFormula 3 0 (lift Rs))
          (.conj (strictLexHeightFormula 1 (lift C) (lift D) 0 2 (lift rD))
            (.conj (subsetFormula (lift original) 2)
              (heightColumnsBoundFormula 1 (lift C) (lift D) 2 (lift K))))))))))

end BoundedFormula

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

namespace BoundedFormula

def externalCosetEntryFormula {n} (z E G inclusion multiplication : Fin n) : BoundedFormula n :=
  exMem E (exMem E.succ (.conj (orderedPairFormula z.succ.succ 1 0)
    (exMem G.succ.succ (exMem E.succ.succ.succ
      (.conj (pairMembershipFormula 1 0 inclusion.succ.succ.succ.succ)
        (tripleMembershipFormula 3 0 2 multiplication.succ.succ.succ.succ))))))

theorem truth_externalCosetEntryFormula {n} (z E G inclusion multiplication : Fin n)
    (env : Fin n → ZFSet.{u}) :
    Truth (externalCosetEntryFormula z E G inclusion multiplication) env ↔
      ∃ w ∈ env E, ∃ v ∈ env E, env z = ZFSet.pair w v ∧
        ∃ j ∈ env G, ∃ k ∈ env E, ZFSet.pair j k ∈ env inclusion ∧
          ZFSet.pair (ZFSet.pair w k) v ∈ env multiplication := by
  simp only [externalCosetEntryFormula, truth_exMem, Truth, truth_orderedPairFormula,
    truth_pairMembershipFormula, truth_tripleMembershipFormula]
  rfl

end BoundedFormula

end PartitionPilot.Forcing



namespace PartitionPilot.Forcing
open SetRealization SetFormula Compression.RecursiveMaps.CosetGeometry
universe u

namespace TransitiveGround
variable (M : TransitiveGround.{u})
noncomputable def externalCosetEquivalence (G S m one : ZFSet.{u}) : ZFSet.{u} :=
  externalCosetRelation (M.externalGroupCarrier G S m one) G
    (M.externalOldInclusion G S m one) (M.externalGroupMultiplication G S m one)
noncomputable def externalCosetCarrier (G S m one : ZFSet.{u}) : ZFSet.{u} :=
  equivalenceClasses (M.externalGroupCarrier G S m one) (M.externalCosetEquivalence G S m one)
noncomputable def externalCosetClassifier (G S m one : ZFSet.{u}) : ZFSet.{u} :=
  equivalenceClassifier (M.externalGroupCarrier G S m one) (M.externalCosetEquivalence G S m one)

end TransitiveGround




namespace TransitiveGround
variable (M : TransitiveGround.{u})
noncomputable def externalStarVertices (G S R m one : ZFSet.{u}) : ZFSet.{u} :=
  tileStarVertexCarrier (M.externalCosetCarrier G S m one) (M.externalGroupCarrier G S m one) R
noncomputable def externalStarDarts (G S R m one : ZFSet.{u}) : ZFSet.{u} :=
  tileStarDartCarrier (M.externalGroupCarrier G S m one) R S

end TransitiveGround

end PartitionPilot.Forcing



namespace PartitionPilot.Forcing
open SetRealization SetFormula
universe u

noncomputable def tileStarRequestGraph (R S : ZFSet.{u}) : ZFSet.{u} :=
  graphRestriction S (productFirst R (natSetCode 2))

end PartitionPilot.Forcing



namespace PartitionPilot.Forcing
open SetRealization SetFormula Compression.RecursiveMaps.CosetGeometry
universe u
namespace TransitiveGround
variable (M : TransitiveGround.{u})
noncomputable def externalStarSource (G S R m one : ZFSet.{u}) : ZFSet.{u} :=
  tileStarSourceGraph (M.externalGroupCarrier G S m one) R S (M.externalCosetCarrier G S m one)
    (M.externalCosetClassifier G S m one) (tileStarRequestGraph R S)
    (M.externalChildGenerators G S m one) (M.externalGroupMultiplication G S m one)

end TransitiveGround

end PartitionPilot.Forcing

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Definability_CompressionExternalStepRealization
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

noncomputable def externalFlatPlacements (E Requests U V S generators m : ZFSet.{u}) : ZFSet.{u} :=
  ZFSet.sep (fun z => ∃ w ∈ E, ∃ a ∈ V, ∃ b ∈ ZFSet.prod E U,
    ∃ q ∈ Requests, ∃ i ∈ externalRequestTags, ∃ x ∈ U, ∃ v ∈ E,
      z = ZFSet.pair (ZFSet.pair w a) b ∧ a = ZFSet.pair (ZFSet.pair q i) x ∧ b = ZFSet.pair v x ∧
        ExternalFlatVertexWordCode E S generators m (natSetCode 0) (natSetCode 1) (natSetCode 2) q i w v)
    (ZFSet.prod (ZFSet.prod E V) (ZFSet.prod E U))

namespace BoundedFormula

def externalFlatVertexWordFormula {n} (E S generators m zero first second q i w v : Fin n) : BoundedFormula n :=
  disj (.conj (.equal i zero) (.equal v w))
    (exMem S (exMem E.succ
      (.conj (disj (.conj (.equal i.succ.succ first.succ.succ)
          (orderedPairFormula 1 q.succ.succ zero.succ.succ))
        (.conj (.equal i.succ.succ second.succ.succ) (orderedPairFormula 1 q.succ.succ first.succ.succ)))
        (.conj (pairMembershipFormula 1 0 generators.succ.succ)
          (tripleMembershipFormula w.succ.succ 0 v.succ.succ m.succ.succ)))))

theorem truth_externalFlatVertexWordFormula {n}
    (E S generators m zero first second q i w v : Fin n) (env : Fin n → ZFSet.{u}) :
    Truth (externalFlatVertexWordFormula E S generators m zero first second q i w v) env ↔
      ExternalFlatVertexWordCode (env E) (env S) (env generators) (env m) (env zero) (env first) (env second)
        (env q) (env i) (env w) (env v) := by
  simp only [externalFlatVertexWordFormula, Truth, truth_exMem, truth_disj, truth_orderedPairFormula,
    truth_pairMembershipFormula, truth_tripleMembershipFormula, ExternalFlatVertexWordCode]
  rfl

def externalFlatPlacementEntryFormula {n}
    (z E Requests Tags U V L S generators m zero first second : Fin n) : BoundedFormula n :=
  exMem E (exMem V.succ (exMem L.succ.succ (exMem Requests.succ.succ.succ
    (exMem Tags.succ.succ.succ.succ (exMem U.succ.succ.succ.succ.succ
      (exMem E.succ.succ.succ.succ.succ.succ
        (.conj (orderedTripleFormula z.succ.succ.succ.succ.succ.succ.succ 6 5 4)
          (.conj (orderedTripleFormula 5 3 2 1)
            (.conj (orderedPairFormula 4 0 1)
              (externalFlatVertexWordFormula E.succ.succ.succ.succ.succ.succ.succ
                S.succ.succ.succ.succ.succ.succ.succ generators.succ.succ.succ.succ.succ.succ.succ
                m.succ.succ.succ.succ.succ.succ.succ zero.succ.succ.succ.succ.succ.succ.succ
                first.succ.succ.succ.succ.succ.succ.succ second.succ.succ.succ.succ.succ.succ.succ
                3 2 6 0))))))))))

theorem truth_externalFlatPlacementEntryFormula {n}
    (z E Requests Tags U V L S generators m zero first second : Fin n) (env : Fin n → ZFSet.{u}) :
    Truth (externalFlatPlacementEntryFormula z E Requests Tags U V L S generators m zero first second) env ↔
      ∃ w ∈ env E, ∃ a ∈ env V, ∃ b ∈ env L, ∃ q ∈ env Requests, ∃ i ∈ env Tags,
        ∃ x ∈ env U, ∃ v ∈ env E,
          env z = ZFSet.pair (ZFSet.pair w a) b ∧ a = ZFSet.pair (ZFSet.pair q i) x ∧ b = ZFSet.pair v x ∧
            ExternalFlatVertexWordCode (env E) (env S) (env generators) (env m) (env zero) (env first) (env second)
              q i w v := by
  simp only [externalFlatPlacementEntryFormula, Truth, truth_exMem, truth_orderedPairFormula,
    truth_orderedTripleFormula, truth_externalFlatVertexWordFormula]
  rfl

end BoundedFormula

namespace BoundedFormula

def externalFlatCoordinateFormula {n} (E U G old m A a b : Fin n) : BoundedFormula n :=
  exMem E (exMem E.succ (exMem E.succ.succ (exMem G.succ.succ.succ
    (exMem U.succ.succ.succ.succ (exMem U.succ.succ.succ.succ.succ
      (.conj (pairMembershipFormula 2 4 old.succ.succ.succ.succ.succ.succ)
        (.conj (tripleMembershipFormula 5 4 3 m.succ.succ.succ.succ.succ.succ)
          (.conj (tripleMembershipFormula 2 1 0 A.succ.succ.succ.succ.succ.succ)
            (.conj (orderedPairFormula a.succ.succ.succ.succ.succ.succ 3 1)
              (orderedPairFormula b.succ.succ.succ.succ.succ.succ 5 0))))))))))

def externalFlatTileStepFormula {n} (E V placements overlaps a b : Fin n) : BoundedFormula n :=
  exMem E (exMem V.succ (exMem V.succ.succ
    (.conj (tripleMembershipFormula 2 1 a.succ.succ.succ placements.succ.succ.succ)
      (.conj (tripleMembershipFormula 2 0 b.succ.succ.succ placements.succ.succ.succ)
        (pairMembershipFormula 1 0 overlaps.succ.succ.succ)))))

theorem truth_externalFlatCoordinateFormula {n} (E U G old m A a b : Fin n) (env : Fin n → ZFSet.{u}) :
    Truth (externalFlatCoordinateFormula E U G old m A a b) env ↔
      ExternalFlatCoordinateCode (env E) (env U) (env G) (env old) (env m) (env A) (env a) (env b) := by
  simp only [externalFlatCoordinateFormula, Truth, truth_exMem, truth_orderedPairFormula,
    truth_pairMembershipFormula, truth_tripleMembershipFormula, ExternalFlatCoordinateCode]
  rfl

theorem truth_externalFlatTileStepFormula {n} (E V placements overlaps a b : Fin n) (env : Fin n → ZFSet.{u}) :
    Truth (externalFlatTileStepFormula E V placements overlaps a b) env ↔
      ExternalFlatTileStepCode (env E) (env V) (env placements) (env overlaps) (env a) (env b) := by
  simp only [externalFlatTileStepFormula, Truth, truth_exMem, truth_pairMembershipFormula,
    truth_tripleMembershipFormula, ExternalFlatTileStepCode]
  rfl

def externalFlatStepFormula {n} (E U G V old m A placements overlaps a b : Fin n) : BoundedFormula n :=
  disj (disj (externalFlatCoordinateFormula E U G old m A a b) (externalFlatTileStepFormula E V placements overlaps a b))
    (disj (externalFlatCoordinateFormula E U G old m A b a) (externalFlatTileStepFormula E V placements overlaps b a))

theorem truth_externalFlatStepFormula {n}
    (E U G V old m A placements overlaps a b : Fin n) (env : Fin n → ZFSet.{u}) :
    Truth (externalFlatStepFormula E U G V old m A placements overlaps a b) env ↔
      ExternalFlatStepCode (env E) (env U) (env G) (env V) (env old) (env m) (env A)
        (env placements) (env overlaps) (env a) (env b) := by
  simp only [externalFlatStepFormula, truth_disj, truth_externalFlatCoordinateFormula,
    truth_externalFlatTileStepFormula, ExternalFlatStepCode]

def externalFlatStepEntryFormula {n} (z L E U G V old m A placements overlaps : Fin n) : BoundedFormula n :=
  exMem L (exMem L.succ (.conj (orderedPairFormula z.succ.succ 1 0)
    (externalFlatStepFormula E.succ.succ U.succ.succ G.succ.succ V.succ.succ old.succ.succ
      m.succ.succ A.succ.succ placements.succ.succ overlaps.succ.succ 1 0)))

theorem truth_externalFlatStepEntryFormula {n}
    (z L E U G V old m A placements overlaps : Fin n) (env : Fin n → ZFSet.{u}) :
    Truth (externalFlatStepEntryFormula z L E U G V old m A placements overlaps) env ↔
      ∃ a ∈ env L, ∃ b ∈ env L, env z = ZFSet.pair a b ∧
        ExternalFlatStepCode (env E) (env U) (env G) (env V) (env old) (env m) (env A)
          (env placements) (env overlaps) a b := by
  simp only [externalFlatStepEntryFormula, Truth, truth_exMem, truth_orderedPairFormula,
    truth_externalFlatStepFormula]
  rfl

end BoundedFormula

end PartitionPilot.Forcing



namespace PartitionPilot.Forcing
open SetFormula SetRealization
universe u

namespace GroundCompressionCompletion
variable {M : TransitiveGround.{u}} {initial : RecursiveStateData.{u}}
variable {I Sources Reps G m one T τ : ZFSet.{u}}
variable (completion : GroundCompressionCompletion M initial I Sources Reps G m one T τ)

noncomputable def externalVertices (P r μ A : ZFSet.{u}) : ZFSet.{u} :=
  externalTileVertices (externalRequestCarrier I P (externalRectangles P G r μ A))
    (externalRectangles P G r μ A) (completion.algebra.union.fields 0)

noncomputable def externalOverlaps (P r μ A : ZFSet.{u}) : ZFSet.{u} :=
  externalRequestOverlapGraph (externalRequestCarrier I P (externalRectangles P G r μ A))
    P G (externalRectangles P G r μ A) completion.externalMaps
    (completion.algebra.union.fields 0) (completion.algebra.union.fields 1) (completion.algebra.union.fields 12)

noncomputable def externalPlacements (P r μ A : ZFSet.{u}) : ZFSet.{u} :=
  let S := externalChildLetters I P (externalRectangles P G r μ A)
  externalFlatPlacements (M.externalGroupCarrier G S m one)
    (externalRequestCarrier I P (externalRectangles P G r μ A))
    (completion.algebra.union.fields 0) (completion.externalVertices P r μ A) S
    (M.externalChildGenerators G S m one) (M.externalGroupMultiplication G S m one)

noncomputable def externalFlatSteps (P r μ A : ZFSet.{u}) : ZFSet.{u} :=
  let S := externalChildLetters I P (externalRectangles P G r μ A)
  externalFlatStepGraph (M.externalGroupCarrier G S m one) (completion.algebra.union.fields 0) G
    (completion.externalVertices P r μ A) (M.externalOldInclusion G S m one)
    (M.externalGroupMultiplication G S m one) (completion.algebra.union.fields 12)
    (completion.externalPlacements P r μ A) (completion.externalOverlaps P r μ A)

noncomputable def externalFlatEquivalence (P r μ A : ZFSet.{u}) : ZFSet.{u} :=
  M.finitePathClosure
    (ZFSet.prod (M.externalGroupCarrier G (externalChildLetters I P (externalRectangles P G r μ A)) m one)
      (completion.algebra.union.fields 0)) (completion.externalFlatSteps P r μ A)

noncomputable def externalPointCarrier (P r μ A : ZFSet.{u}) : ZFSet.{u} :=
  equivalenceClasses
    (ZFSet.prod (M.externalGroupCarrier G (externalChildLetters I P (externalRectangles P G r μ A)) m one)
      (completion.algebra.union.fields 0)) (completion.externalFlatEquivalence P r μ A)

noncomputable def externalPointClassifier (P r μ A : ZFSet.{u}) : ZFSet.{u} :=
  equivalenceClassifier
    (ZFSet.prod (M.externalGroupCarrier G (externalChildLetters I P (externalRectangles P G r μ A)) m one)
      (completion.algebra.union.fields 0)) (completion.externalFlatEquivalence P r μ A)

end GroundCompressionCompletion

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



namespace PartitionPilot.Forcing
open Compression.RecursiveMaps
universe u

namespace BoundedFormula

def lexProductEntryFormula {n} (z C D rC rD : Fin n) : BoundedFormula n :=
  let lift (i : Fin n) := i.succ.succ.succ.succ
  exMem C (exMem D.succ (exMem C.succ.succ (exMem D.succ.succ.succ
    (.conj (pairOfPairsFormula (lift z) 3 2 1 0)
      (disj (pairMembershipFormula 3 1 (lift rC)) (.conj (.equal 3 1) (pairMembershipFormula 2 0 (lift rD))))))))

end BoundedFormula

end PartitionPilot.Forcing


end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Definability_ExternalColumnCodes
attribute [-instance] _root_.OAI.PartitionPilot.Forcing.GroundMainPrefix.withTopSmall
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PartitionPilot.Forcing
open SetRealization Compression.RecursiveMaps
universe u

structure ExternalColumnCode (C K base sequence cap : ZFSet.{u}) : Prop where
  function : ZFSet.IsFunc ZFSet.omega C sequence
  entries : ∀ n y, ZFSet.pair (natSetCode n) y ∈ sequence ↔ y = compressionStamp base n
  base_mem : base ∈ C
  cap_mem : cap ∈ C
  old_bound : ∀ a ∈ K, a ∈ base
  cap_bound : ∀ n, compressionStamp base n ∈ cap

end PartitionPilot.Forcing

end

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Definability_IndexedSubstructureCodes
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

namespace BoundedFormula

def indexedSubmeetEntryFormula {n} (z I B μ domains : Fin n) : BoundedFormula n :=
  exMem I (exMem μ.succ (exMem B.succ.succ (exMem B.succ.succ.succ (exMem B.succ.succ.succ.succ
    (.conj (orderedPairFormula z.succ.succ.succ.succ.succ 4 3)
      (.conj (orderedTripleFormula 3 2 1 0)
        (.conj (pairMembershipFormula 4 2 domains.succ.succ.succ.succ.succ)
          (.conj (pairMembershipFormula 4 1 domains.succ.succ.succ.succ.succ)
            (pairMembershipFormula 4 0 domains.succ.succ.succ.succ.succ)))))))))

end BoundedFormula

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
universe u
namespace GroundCompressionCompletion
variable {M : TransitiveGround.{u}} {initial : RecursiveStateData.{u}}
variable {I Sources Reps G m one T τ : ZFSet.{u}}
variable (completion : GroundCompressionCompletion M initial I Sources Reps G m one T τ)

noncomputable def externalPointOrder (P r μ A : ZFSet.{u}) : ZFSet.{u} :=
  flatCopyOrderGraph (M.externalGroupCarrier G (externalChildLetters I P (externalRectangles P G r μ A)) m one)
    (completion.algebra.union.fields 0) (completion.externalPointCarrier P r μ A)
    (completion.externalPointClassifier P r μ A) (completion.algebra.union.fields 1)

noncomputable def externalPointAction (P r μ A : ZFSet.{u}) : ZFSet.{u} :=
  let S := externalChildLetters I P (externalRectangles P G r μ A)
  flatCopyActionGraph (M.externalGroupCarrier G S m one) (completion.algebra.union.fields 0)
    (completion.externalPointCarrier P r μ A) (completion.externalPointClassifier P r μ A)
    (M.externalGroupMultiplication G S m one)

noncomputable def externalCopyGraph (P r μ A w : ZFSet.{u}) : ZFSet.{u} :=
  flatCopyEmbeddingGraph (completion.algebra.union.fields 0) (completion.externalPointCarrier P r μ A)
    (completion.externalPointClassifier P r μ A) w

end GroundCompressionCompletion

end PartitionPilot.Forcing



namespace PartitionPilot.Forcing
open SetFormula
universe u

namespace BoundedFormula
def vertexImageDomainsEntryFormula {n} (z Requests N U Q V images : Fin n) : BoundedFormula n :=
  exMem Requests (exMem Q.succ (exMem N.succ.succ (exMem U.succ.succ.succ (exMem V.succ.succ.succ.succ
    (.conj (orderedPairFormula z.succ.succ.succ.succ.succ 4 3)
      (.conj (orderedTripleFormula 0 4 2 1)
        (pairMembershipFormula 0 3 images.succ.succ.succ.succ.succ)))))))

theorem truth_vertexImageDomainsEntryFormula {n} (z Requests N U Q V images : Fin n)
    (env : Fin n → ZFSet.{u}) :
    Truth (vertexImageDomainsEntryFormula z Requests N U Q V images) env ↔
      env z ∈ vertexImageDomains (env Requests) (env N) (env U) (env Q) (env V) (env images) := by
  simp only [vertexImageDomainsEntryFormula, truth_exMem, Truth, truth_orderedPairFormula,
    truth_orderedTripleFormula, truth_pairMembershipFormula, vertexImageDomains, ZFSet.mem_sep]
  refine ⟨fun h => ⟨?_, h⟩, And.right⟩
  obtain ⟨r, hr, y, hy, _, _, _, _, _, _, equal, _⟩ := h
  change env z = ZFSet.pair r y at equal
  rw [equal]
  exact ZFSet.pair_mem_prod.2 ⟨hr, hy⟩
end BoundedFormula

namespace GroundCompressionCompletion
variable {M : TransitiveGround.{u}} {initial : RecursiveStateData.{u}}
variable {I Sources Reps G m one T τ : ZFSet.{u}}
variable (completion : GroundCompressionCompletion M initial I Sources Reps G m one T τ)
variable (P r μ A : ZFSet.{u})
local notation "Requests" => externalRequestCarrier I P (externalRectangles P G r μ A)
local notation "U" => completion.algebra.union.fields 0
local notation "Q" => completion.externalPointCarrier P r μ A
local notation "V" => completion.externalVertices P r μ A
local notation "E" => M.externalGroupCarrier G (externalChildLetters I P (externalRectangles P G r μ A)) m one

noncomputable def localTileVertexImages : ZFSet.{u} :=
  relationCompose V (ZFSet.prod E U) Q
    (indexedRelationSection V (ZFSet.prod E U) (completion.externalPlacements P r μ A)
      (M.externalGroupIdentity G (externalChildLetters I P (externalRectangles P G r μ A)) m one))
    (completion.externalPointClassifier P r μ A)

noncomputable def localTilePoints : ZFSet.{u} :=
  vertexImageDomains Requests (natSetCode 3) U Q V (completion.localTileVertexImages P r μ A)

end GroundCompressionCompletion

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
namespace BoundedFormula

def transportedTileCoordinateFormula {n} (z V E I B D action heights bound one : Fin n) : BoundedFormula n :=
  exMem V (exMem E.succ (exMem I.succ.succ (exMem B.succ.succ.succ
    (exMem D.succ.succ.succ.succ (exMem B.succ.succ.succ.succ.succ
      (exMem bound.succ.succ.succ.succ.succ.succ
        (.conj (orderedTripleFormula z.succ.succ.succ.succ.succ.succ.succ 6 3 2)
          (.conj (orderedRightTripleFormula 6 one.succ.succ.succ.succ.succ.succ.succ 5 4)
            (.conj (pairMembershipFormula 4 0 heights.succ.succ.succ.succ.succ.succ.succ)
              (.conj (tripleMembershipFormula 5 1 3 action.succ.succ.succ.succ.succ.succ.succ)
                (pairMembershipFormula 1 2 0)))))))))))

def ownerHeightFreshFormula {n} (z P B V C D owner depths columns coordinates omega : Fin n) : BoundedFormula n :=
  exMem B (exMem V.succ (exMem omega.succ.succ (exMem C.succ.succ.succ
    (exMem D.succ.succ.succ.succ
      (.conj (orderedRightTripleFormula z.succ.succ.succ.succ.succ 4 1 0)
        (.conj (.neg (.mem 4 P.succ.succ.succ.succ.succ))
          (.conj (pairMembershipFormula 4 3 owner.succ.succ.succ.succ.succ)
            (.conj (pairMembershipFormula 3 2 depths.succ.succ.succ.succ.succ)
              (.conj (pairMembershipFormula 2 1 columns.succ.succ.succ.succ.succ)
                (tripleMembershipFormula 3 4 0 coordinates.succ.succ.succ.succ.succ))))))))))

end BoundedFormula

end

section
open SetFormula
universe u

noncomputable def externalTileSlotSupports (V E I U B action vertexImages : ZFSet.{u}) : ZFSet.{u} :=
  ZFSet.sep (fun y => ∃ v ∈ V, ∃ j ∈ natSetCode 3, ∃ x ∈ B, ∃ w ∈ E,
    ∃ r ∈ I, ∃ u ∈ U, ∃ z ∈ B,
      y = ZFSet.pair (ZFSet.pair v j) x ∧ v = ZFSet.pair (natSetCode 1) (ZFSet.pair w r) ∧
        ZFSet.pair (ZFSet.pair (ZFSet.pair r j) u) z ∈ vertexImages ∧
        ZFSet.pair (ZFSet.pair w z) x ∈ action)
    (ZFSet.prod (ZFSet.prod V (natSetCode 3)) B)

namespace BoundedFormula

def slotImageMembershipFormula {n} (r j u z images : Fin n) : BoundedFormula n :=
  exMem images (exMem 0 (exMem 0
    (.conj (orderedTripleFormula 0 r.succ.succ.succ j.succ.succ.succ u.succ.succ.succ)
      (orderedPairFormula 2 0 z.succ.succ.succ))))

theorem truth_slotImageMembershipFormula {n} (r j u z images : Fin n) (env : Fin n → ZFSet.{u}) :
    Truth (slotImageMembershipFormula r j u z images) env ↔
      ZFSet.pair (ZFSet.pair (ZFSet.pair (env r) (env j)) (env u)) (env z) ∈ env images := by
  simp only [slotImageMembershipFormula, truth_exMem, Truth, truth_orderedTripleFormula, truth_orderedPairFormula]
  change (∃ a ∈ env images, ∃ b ∈ a, ∃ c ∈ b,
    c = ZFSet.pair (ZFSet.pair (env r) (env j)) (env u) ∧ a = ZFSet.pair c (env z)) ↔ _
  constructor
  · rintro ⟨a, ha, _, _, c, _, rfl, rfl⟩
    exact ha
  · intro entry
    let c := ZFSet.pair (ZFSet.pair (env r) (env j)) (env u)
    exact ⟨ZFSet.pair c (env z), entry, {c}, ZFSet.mem_pair.2 (Or.inl rfl),
      c, ZFSet.mem_singleton.2 rfl, rfl, rfl⟩

def externalTileSlotSupportFormula {n} (y V E I U B action images one three : Fin n) : BoundedFormula n :=
  exMem V (exMem three.succ (exMem B.succ.succ (exMem E.succ.succ.succ
    (exMem I.succ.succ.succ.succ (exMem U.succ.succ.succ.succ.succ
      (exMem B.succ.succ.succ.succ.succ.succ
        (.conj (orderedTripleFormula y.succ.succ.succ.succ.succ.succ.succ 6 5 4)
          (.conj (orderedRightTripleFormula 6 one.succ.succ.succ.succ.succ.succ.succ 3 2)
            (.conj (slotImageMembershipFormula 2 5 1 0 images.succ.succ.succ.succ.succ.succ.succ)
              (tripleMembershipFormula 3 0 4 action.succ.succ.succ.succ.succ.succ.succ))))))))))

theorem truth_externalTileSlotSupportFormula {n} (y V E I U B action images one three : Fin n)
    (env : Fin n → ZFSet.{u}) (oneEq : env one = natSetCode 1) (threeEq : env three = natSetCode 3) :
    Truth (externalTileSlotSupportFormula y V E I U B action images one three) env ↔
      env y ∈ externalTileSlotSupports (env V) (env E) (env I) (env U) (env B) (env action) (env images) := by
  simp only [externalTileSlotSupportFormula, truth_exMem, Truth, truth_orderedTripleFormula,
    truth_orderedRightTripleFormula, truth_slotImageMembershipFormula, truth_tripleMembershipFormula]
  simp only [extend, Fin.cases_zero, Fin.cases_succ]
  rw [oneEq, threeEq, externalTileSlotSupports, ZFSet.mem_sep]
  refine ⟨fun h => ⟨?_, h⟩, And.right⟩
  obtain ⟨v, hv, j, hj, x, hx, _, _, _, _, _, _, _, _, equal, _⟩ := h
  rw [equal]
  exact ZFSet.pair_mem_prod.2 ⟨ZFSet.pair_mem_prod.2 ⟨hv, hj⟩, hx⟩

end BoundedFormula

end

end PartitionPilot.Forcing

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Definability_ExternalSlotCopyGraphs
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

namespace BoundedFormula

def externalSlotCopyEntryFormula {n} (z V E I U B action images j one : Fin n) : BoundedFormula n :=
  let lift (i : Fin n) := i.succ.succ.succ.succ.succ.succ
  exMem V (exMem U.succ (exMem B.succ.succ (exMem E.succ.succ.succ
    (exMem I.succ.succ.succ.succ (exMem B.succ.succ.succ.succ.succ
      (.conj (orderedTripleFormula (lift z) 5 4 3)
        (.conj (orderedRightTripleFormula 5 (lift one) 2 1)
          (.conj (slotImageMembershipFormula 1 (lift j) 4 0 (lift images))
            (tripleMembershipFormula 2 0 3 (lift action))))))))))

end BoundedFormula

end PartitionPilot.Forcing

end

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

def stageOneRawSingleBody (M : TransitiveGround.{u}) (d : Fin 15 → ZFSet.{u})
    (f : Fin 7 → ZFSet.{u}) (t u w lower : ZFSet.{u}) : Prop :=
  f 0 ∈ d 10 ∧
  f 1 ∈ d 10 ∧
  f 5 ∈ d 14 ∧
  f 6 ∈ d 14 ∧
  ZFSet.pair t (f 0) ∈ d 1 ∧
  ZFSet.pair t (f 1) ∈ d 2 ∧
  ZFSet.pair t (f 2) ∈ d 3 ∧
  ZFSet.pair t (f 3) ∈ d 4 ∧
  ZFSet.pair t (f 4) ∈ d 5 ∧
  stageOneRawClass M (d 6) (d 7) (d 8) (d 9) (f 4) u (f 5) ∧
  stageOneRawClass M (d 6) (d 7) (d 8) (d 9) (f 3) w (f 6) ∧
  stageOneRawForces M (d 7) (d 8) lower refinementActivityFormula ![u, w, f 2] ∧
  stageOneRawProfile M (d 7) (d 8) lower (d 10) (d 11) (d 13) (f 1) (f 5) (f 6) ∧
  stageOneRawCompatibility M (d 7) (d 8) lower (d 13) (d 12) (f 0) t (f 5) (f 6)

def stageOneRawSingle (M : TransitiveGround.{u}) (d : Fin 15 → ZFSet.{u})
    (t u w lower : ZFSet.{u}) : Prop :=
  ∃ f : Fin 7 → ZFSet.{u}, (∀ j, f j ∈ M.sets) ∧ stageOneRawSingleBody M d f t u w lower





def stageOneRawCollisionBody (M : TransitiveGround.{u}) (d : Fin 15 → ZFSet.{u})
    (f : Fin 6 → ZFSet.{u}) (t u u' w w' lower : ZFSet.{u}) : Prop :=
  f 2 ∈ d 14 ∧
  f 3 ∈ d 14 ∧
  f 4 ∈ d 14 ∧
  f 5 ∈ d 14 ∧
  ZFSet.pair t (f 0) ∈ d 4 ∧
  ZFSet.pair t (f 1) ∈ d 5 ∧
  stageOneRawClass M (d 6) (d 7) (d 8) (d 9) (f 1) u (f 2) ∧
  stageOneRawClass M (d 6) (d 7) (d 8) (d 9) (f 1) u' (f 3) ∧
  stageOneRawClass M (d 6) (d 7) (d 8) (d 9) (f 0) w (f 4) ∧
  stageOneRawClass M (d 6) (d 7) (d 8) (d 9) (f 0) w' (f 5) ∧
  stageOneRawForces M (d 7) (d 8) lower refinementCollisionFormula ![f 2, f 3, f 4, f 5]

def stageOneRawCollision (M : TransitiveGround.{u}) (d : Fin 15 → ZFSet.{u})
    (t u u' w w' lower : ZFSet.{u}) : Prop :=
  ∃ f : Fin 6 → ZFSet.{u}, (∀ j, f j ∈ M.sets) ∧ stageOneRawCollisionBody M d f t u u' w w' lower





def stageOneRawTests (M : TransitiveGround.{u}) (d : Fin 15 → ZFSet.{u})
    (A lower : ZFSet.{u}) : Prop :=
  (∀ t ∈ d 0, ∀ u ∈ d 6, ∀ w ∈ d 6, stageOneAssignment t u w ∈ A →
    stageOneRawSingle M d t u w lower) ∧
  (∀ t ∈ d 0, ∀ u ∈ d 6, ∀ u' ∈ d 6, ∀ w ∈ d 6, ∀ w' ∈ d 6,
    stageOneAssignment t u w ∈ A → stageOneAssignment t u' w' ∈ A →
    stageOneRawCollision M d t u u' w w' lower)





def StageTwoConditionCode (M : TransitiveGround.{u}) (levels alpha : ZFSet.{u})
    (d : Fin 15 → ZFSet.{u}) (z : ZFSet.{u}) : Prop :=
  ∃ row A, z = ZFSet.pair row A ∧
    ZFSet.pair row (assignmentCut levels alpha A) ∈ d 7 ∧
    stageOneRawTests M d A (ZFSet.pair row (assignmentCut levels alpha A))

end PartitionPilot.Forcing



namespace PartitionPilot.Forcing
open SetFormula
universe u

noncomputable def refinementFormulaDataCode (d : Fin 15 → ZFSet.{u}) : ZFSet.{u} :=
  nonemptyTupleCode 14 d

def PackedSuccessorConditionCode (M : TransitiveGround.{u})
    (levels alpha data z : ZFSet.{u}) : Prop :=
  ∃ d : Fin 15 → ZFSet.{u}, data = refinementFormulaDataCode d ∧
    StageTwoConditionCode M levels alpha d z

end PartitionPilot.Forcing



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

noncomputable def representativeIndexAdditions (I T Q c X : ZFSet.{u}) : ZFSet.{u} :=
  ZFSet.sep (fun i => ∃ q ∈ Q, AssignmentQueryWithin X T q ∧
    ∃ row A, ZFSet.pair q (ZFSet.pair row A) ∈ c ∧
      ∃ v ∈ T, ∃ w ∈ T, stageOneAssignment i v w ∈ A) I

theorem mem_representativeIndexAdditions (I T Q c X i : ZFSet.{u}) :
    i ∈ representativeIndexAdditions I T Q c X ↔ i ∈ I ∧
      ∃ q ∈ Q, AssignmentQueryWithin X T q ∧
        ∃ row A, ZFSet.pair q (ZFSet.pair row A) ∈ c ∧
          ∃ v ∈ T, ∃ w ∈ T, stageOneAssignment i v w ∈ A :=
  ZFSet.mem_sep

end PartitionPilot.Forcing



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

noncomputable def refinementHistoryIndices (alpha history : ZFSet.{u}) : ZFSet.{u} :=
  ⋃₀ functionGraphRange alpha history

theorem mem_refinementHistoryIndices (alpha history x : ZFSet.{u}) :
    x ∈ refinementHistoryIndices alpha history ↔
      ∃ xi ∈ alpha, ∃ I, ZFSet.pair xi I ∈ history ∧ x ∈ I := by
  rw [refinementHistoryIndices, ZFSet.mem_sUnion]
  constructor
  · rintro ⟨I, hI, hx⟩
    obtain ⟨xi, hxi, entry⟩ := (mem_functionGraphRange alpha history I).1 hI
    exact ⟨xi, hxi, I, entry, hx⟩
  · rintro ⟨xi, hxi, I, entry, hx⟩
    exact ⟨I, (mem_functionGraphRange alpha history I).2 ⟨xi, hxi, entry⟩, hx⟩

end PartitionPilot.Forcing



namespace PartitionPilot.Forcing
universe u

noncomputable def refinementDataHistoryField (stages history : ZFSet.{u}) (j : Fin 15) : ZFSet.{u} :=
  ZFSet.sep (fun z => ∃ alpha ∈ stages, ∃ d : Fin 15 → ZFSet.{u},
    ZFSet.pair alpha (refinementFormulaDataCode d) ∈ history ∧ z = ZFSet.pair alpha (d j))
    (ZFSet.prod stages (tupleFieldBound 14 (⋃₀ ⋃₀ history)))

theorem mem_refinementDataHistoryField (stages history z : ZFSet.{u}) (j : Fin 15) :
    z ∈ refinementDataHistoryField stages history j ↔
      ∃ alpha ∈ stages, ∃ d : Fin 15 → ZFSet.{u},
        ZFSet.pair alpha (refinementFormulaDataCode d) ∈ history ∧ z = ZFSet.pair alpha (d j) := by
  rw [refinementDataHistoryField, ZFSet.mem_sep]
  constructor
  · exact And.right
  · rintro ⟨alpha, halpha, d, entry, rfl⟩
    exact ⟨ZFSet.pair_mem_prod.2 ⟨halpha,
      nonemptyTupleCode_field_mem_bound 14 d (pair_second_mem_doubleUnion entry) j⟩,
      alpha, halpha, d, entry, rfl⟩

theorem pair_mem_refinementDataHistoryField (stages history alpha y : ZFSet.{u}) (j : Fin 15) :
    ZFSet.pair alpha y ∈ refinementDataHistoryField stages history j ↔
      alpha ∈ stages ∧ ∃ d : Fin 15 → ZFSet.{u},
        ZFSet.pair alpha (refinementFormulaDataCode d) ∈ history ∧ y = d j := by
  rw [mem_refinementDataHistoryField]
  constructor
  · rintro ⟨beta, hbeta, d, entry, equal⟩
    obtain ⟨rfl, value⟩ := ZFSet.pair_inj.1 equal
    exact ⟨hbeta, d, entry, value⟩
  · rintro ⟨halpha, d, entry, rfl⟩
    exact ⟨alpha, halpha, d, entry, rfl⟩

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

def ForcingHistoryConditionCode (M : TransitiveGround.{u})
    (stages history levels z : ZFSet.{u}) : Prop :=
  ∀ alpha ∈ stages, ∃ data, ZFSet.pair alpha data ∈ history ∧
    PackedSuccessorConditionCode M levels alpha data z

end PartitionPilot.Forcing

namespace PartitionPilot.Forcing
open SetFormula
universe u

def ForcingHistoryLevelCoverage (stages history levels : ZFSet.{u}) : Prop :=
  ∀ beta ∈ stages, ∀ d : Fin 15 → ZFSet.{u},
    ZFSet.pair beta (refinementFormulaDataCode d) ∈ history →
      ∀ t ∈ d 0, ∀ u ∈ d 6, ∀ w ∈ d 6,
        ZFSet.pair (stageOneAssignment t u w) beta ∈ levels

end PartitionPilot.Forcing

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

namespace BoundedFormula

theorem truth_stageOneAssignmentsMemberFormula {n : Nat} (z I T : Fin n)
    (env : Fin n → ZFSet.{u}) :
    Truth (stageOneAssignmentsMemberFormula z I T) env ↔
      env z ∈ stageOneAssignments (env I) (env T) := by
  simp only [stageOneAssignmentsMemberFormula, truth_exMem, truth_stageOneAssignmentFormula]
  exact (mem_stageOneAssignments _ _ _).symm

theorem truth_stageOneAssignmentsSubsetFormula {n : Nat} (A I T : Fin n)
    (env : Fin n → ZFSet.{u}) :
    Truth (stageOneAssignmentsSubsetFormula A I T) env ↔
      env A ⊆ stageOneAssignments (env I) (env T) := by
  simp only [stageOneAssignmentsSubsetFormula, Truth, truth_stageOneAssignmentsMemberFormula]
  rfl

end BoundedFormula

end PartitionPilot.Forcing

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Definability_GreedyAntichainStepFormulas
attribute [-instance] _root_.OAI.PartitionPilot.Forcing.GroundMainPrefix.withTopSmall
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PartitionPilot.Forcing.BoundedFormula
open SetFormula
universe u

def greedyAntichainStepFormula {n} (Q order D F c alpha prior y : Fin n) : BoundedFormula n :=
  disj (exMem F (.conj (antichainEligibleFormula 0 Q.succ order.succ D.succ alpha.succ prior.succ)
    (pairMembershipFormula 0 y.succ c.succ)))
    (.conj (.neg (exMem D (.neg
      (antichainBlockedFormula 0 Q.succ order.succ D.succ alpha.succ prior.succ)))) (.equal y D))

end PartitionPilot.Forcing.BoundedFormula

end

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Forcing_GroundFixedTopStep
attribute [-instance] _root_.OAI.PartitionPilot.Forcing.GroundMainPrefix.withTopSmall
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PartitionPilot.Forcing

section

universe u

namespace BoundedFormula

open SetFormula

theorem truth_fixedTopActionEntryFormula {n} (z G P : Fin n) (env : Fin n → ZFSet.{u}) :
    Truth (fixedTopActionEntryFormula z G P) env ↔
      ∃ g ∈ env G, env z = ZFSet.pair (ZFSet.pair g (env P)) (env P) := by
  simp only [fixedTopActionEntryFormula, truth_exMem, truth_orderedTripleFormula]
  rfl

end BoundedFormula

end

open SetRealization
universe u

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

namespace BoundedFormula

theorem truth_leastSupportFormula {k} (V omega depths supports x v : Fin k) (env : Fin k → ZFSet.{u}) :
    Truth (leastSupportFormula V omega depths supports x v) env ↔
      LeastSupportCode (env V) (env omega) (env depths) (env supports) (env x) (env v) := by
  simp only [leastSupportFormula, Truth, truth_exMem, truth_imp, truth_pairMembershipFormula]
  rfl

theorem truth_leastSupportEntryFormula {k} (z V Q omega depths supports : Fin k) (env : Fin k → ZFSet.{u}) :
    Truth (leastSupportEntryFormula z V Q omega depths supports) env ↔
      ∃ x ∈ env Q, ∃ v ∈ env V, env z = ZFSet.pair x v ∧
        LeastSupportCode (env V) (env omega) (env depths) (env supports) x v := by
  simp only [leastSupportEntryFormula, truth_exMem, Truth, truth_orderedPairFormula, truth_leastSupportFormula]
  rfl
end BoundedFormula

end PartitionPilot.Forcing



namespace PartitionPilot.Forcing
open SetFormula
universe u

noncomputable def leastSlotOwnerGraph (P B V owner supports : ZFSet.{u}) : ZFSet.{u} :=
  ZFSet.sep (fun z => ∃ x ∈ B, ∃ j ∈ natSetCode 3, ∃ v ∈ V,
    z = ZFSet.pair x j ∧ x ∉ P ∧ ZFSet.pair x v ∈ owner ∧ LeastSlotCode supports v x j)
    (ZFSet.prod B (natSetCode 3))

end PartitionPilot.Forcing

end

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Geometry_ExternalOwnerCoordinateLaws
attribute [-instance] _root_.OAI.PartitionPilot.Forcing.GroundMainPrefix.withTopSmall
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace PartitionPilot.Forcing
open SetRealization SetFormula Compression.RecursiveMaps.CosetGeometry
universe u
namespace GroundCompressionCompletion
variable {M : TransitiveGround.{u}} {initial : RecursiveStateData.{u}}
variable {I Sources Reps G m one T τ : ZFSet.{u}}
variable (completion : GroundCompressionCompletion M initial I Sources Reps G m one T τ)
variable (P r μ A : ZFSet.{u})
noncomputable def externalIdentityCopyGraph : ZFSet.{u} :=
  completion.externalCopyGraph P r μ A
    (M.externalGroupIdentity G (externalChildLetters I P (externalRectangles P G r μ A)) m one)

end GroundCompressionCompletion

end PartitionPilot.Forcing




end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Definability_GroundDepthSlotCodes
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

namespace BoundedFormula

theorem truth_depthSlotEntryFormula (env : Fin 5 → ZFSet.{u}) :
    Truth depthSlotEntryFormula env ↔
      ∃ n ∈ env 1, ∃ j ∈ env 2, ∃ k ∈ env 1, ∃ t ∈ env 1,
        env 0 = ZFSet.pair (ZFSet.pair n j) k ∧
          ZFSet.pair (ZFSet.pair (env 2) n) t ∈ env 3 ∧
          ZFSet.pair (ZFSet.pair t j) k ∈ env 4 := by
  simp only [depthSlotEntryFormula, truth_exMem, Truth,
    truth_orderedTripleFormula, truth_tripleMembershipFormula]
  rfl

end BoundedFormula

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
namespace BoundedFormula

def leastSlotFormula {n} (supports v x j : Fin n) : BoundedFormula n :=
  .conj (tripleMembershipFormula v j x supports)
    (allMem j (.neg (tripleMembershipFormula v.succ 0 x.succ supports.succ)))

theorem truth_leastSlotFormula {n} (supports v x j : Fin n) (env : Fin n → ZFSet.{u}) :
    Truth (leastSlotFormula supports v x j) env ↔
      LeastSlotCode (env supports) (env v) (env x) (env j) := by
  simp only [leastSlotFormula, Truth, truth_tripleMembershipFormula]
  rfl

def leastSlotOwnerEntryFormula {n} (z P B V owner supports three : Fin n) : BoundedFormula n :=
  exMem B (exMem three.succ (exMem V.succ.succ
    (.conj (orderedPairFormula z.succ.succ.succ 2 1)
      (.conj (.neg (.mem 2 P.succ.succ.succ))
        (.conj (pairMembershipFormula 2 0 owner.succ.succ.succ)
          (leastSlotFormula supports.succ.succ.succ 0 2 1))))))

theorem truth_leastSlotOwnerEntryFormula {n} (z P B V owner supports three : Fin n)
    (env : Fin n → ZFSet.{u}) (threeEq : env three = natSetCode 3) :
    Truth (leastSlotOwnerEntryFormula z P B V owner supports three) env ↔
      env z ∈ leastSlotOwnerGraph (env P) (env B) (env V) (env owner) (env supports) := by
  simp only [leastSlotOwnerEntryFormula, truth_exMem, Truth, truth_orderedPairFormula,
    truth_pairMembershipFormula, truth_leastSlotFormula]
  simp only [extend, Fin.cases_zero, Fin.cases_succ]
  rw [threeEq, leastSlotOwnerGraph, ZFSet.mem_sep]
  refine ⟨fun h => ⟨?_, h⟩, And.right⟩
  obtain ⟨x, hx, j, hj, _, _, equal, _⟩ := h
  rw [equal]
  exact ZFSet.pair_mem_prod.2 ⟨hx, hj⟩

end BoundedFormula
end PartitionPilot.Forcing

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Definability_GroundBoundedExternalBirths
attribute [-instance] _root_.OAI.PartitionPilot.Forcing.GroundMainPrefix.withTopSmall
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PartitionPilot.Forcing

section
universe u
namespace GroundCompressionCompletion
variable {M : TransitiveGround.{u}} {initial : RecursiveStateData.{u}}
variable {I Sources Reps G m one T τ : ZFSet.{u}}
variable (completion : GroundCompressionCompletion M initial I Sources Reps G m one T τ)

noncomputable def externalBoundedCarrier (P r μ A : ZFSet.{u}) : ZFSet.{u} :=
  fixedTopCarrier (completion.externalPointCarrier P r μ A)

noncomputable def externalBoundedOrder (P r μ A : ZFSet.{u}) : ZFSet.{u} :=
  fixedTopOrder (completion.externalPointCarrier P r μ A) (completion.externalPointOrder P r μ A)

noncomputable def externalBoundedMeet (P r μ A : ZFSet.{u}) : ZFSet.{u} :=
  fixedTopMeet (completion.externalPointCarrier P r μ A) (completion.externalPointOrder P r μ A)

end GroundCompressionCompletion

end

open SetFormula
universe u

end PartitionPilot.Forcing

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Forcing_GroundUnionSizeWitnesses
attribute [-instance] _root_.OAI.PartitionPilot.Forcing.GroundMainPrefix.withTopSmall
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PartitionPilot.Forcing
open SetFormula
open scoped ZFSet
universe u

namespace BoundedFormula

theorem truth_belowWitnessEntryFormula {n} (z r k w : Fin n) (env : Fin n → ZFSet.{u}) :
    Truth (belowWitnessEntryFormula z r k w) env ↔
      ∃ A ∈ env r, ∃ β ∈ env k, ∃ f ∈ env w,
        env z = ZFSet.pair A (ZFSet.pair β f) ∧ InjectionCode A β f := by
  simp only [belowWitnessEntryFormula, truth_exMem, Truth,
    truth_orderedRightTripleFormula, truth_injectionFormula]
  rfl

end BoundedFormula

namespace TransitiveGround
variable (M : TransitiveGround.{u})

theorem belowWitnessRelation_mem
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    {R K W : ZFSet.{u}} (hR : R ∈ M.sets) (hK : K ∈ M.sets) (hW : W ∈ M.sets) :
    belowWitnessRelation R K W ∈ M.sets := by
  let params := extend R (extend K (extend W Fin.elim0))
  have selected := M.bounded_separation_mem separation (BoundedFormula.belowWitnessEntryFormula 0 1 2 3)
    params (Fin.cases hR (Fin.cases hK (Fin.cases hW (fun i => Fin.elim0 i))))
    (M.prod_mem pairing unions powers separation hR (M.prod_mem pairing unions powers separation hK hW))
  have equal : ZFSet.sep (fun z => BoundedFormula.Truth
      (BoundedFormula.belowWitnessEntryFormula 0 1 2 3) (extend z params))
      (ZFSet.prod R (ZFSet.prod K W)) = belowWitnessRelation R K W := by
    apply ZFSet.ext
    intro z
    rw [ZFSet.mem_sep, belowWitnessRelation, ZFSet.mem_sep]
    exact and_congr Iff.rfl (BoundedFormula.truth_belowWitnessEntryFormula 0 1 2 3 _)
  exact equal ▸ selected

noncomputable def groundBelowWitnesses (R B K : ZFSet.{u}) : ZFSet.{u} :=
  belowWitnessRelation R K (M.groundRelations B K)

theorem groundBelowWitnesses_mem
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    {R B K : ZFSet.{u}} (hR : R ∈ M.sets) (hB : B ∈ M.sets) (hK : K ∈ M.sets) :
    M.groundBelowWitnesses R B K ∈ M.sets :=
  M.belowWitnessRelation_mem pairing unions powers separation hR hK
    (M.groundRelations_mem pairing unions powers separation hB hK)

theorem groundBelow_iff_boundedWitness {A B K : ZFSet.{u}}
    (subset : A ⊆ B) (transitive : ∀ β ∈ K, β ⊆ K) :
    GroundBelow M A K ↔ ∃ β ∈ K, ∃ f ∈ M.groundRelations B K, InjectionCode A β f := by
  constructor
  · rintro ⟨β, hβ, f, hf, code⟩
    have bound : f ⊆ ZFSet.prod B K := by
      intro z hz
      obtain ⟨x, hx, y, hy, rfl⟩ := ZFSet.mem_prod.1 (code.function.1 hz)
      exact ZFSet.pair_mem_prod.2 ⟨subset hx, transitive β hβ hy⟩
    exact ⟨β, hβ, f, (M.mem_groundRelations B K f).2 ⟨hf, bound⟩, code⟩
  · rintro ⟨β, hβ, f, hf, code⟩
    exact ⟨β, hβ, f, ((M.mem_groundRelations B K f).1 hf).1, code⟩

theorem groundBelowWitnesses_total_iff {R B K : ZFSet.{u}}
    (subsets : ∀ A ∈ R, A ⊆ B) (transitive : ∀ β ∈ K, β ⊆ K) :
    (∀ A ∈ R, ∃ q ∈ ZFSet.prod K (M.groundRelations B K),
      ZFSet.pair A q ∈ M.groundBelowWitnesses R B K) ↔
        ∀ A ∈ R, GroundBelow M A K := by
  constructor
  · intro total A hA
    obtain ⟨q, hq, entry⟩ := total A hA
    obtain ⟨β, hβ, f, hf, rfl⟩ := ZFSet.mem_prod.1 hq
    have code := ((pair_mem_belowWitnessRelation R K (M.groundRelations B K) A β f).1 entry).2.2.2
    exact (M.groundBelow_iff_boundedWitness (subsets A hA) transitive).2 ⟨β, hβ, f, hf, code⟩
  · intro small A hA
    obtain ⟨β, hβ, f, hf, code⟩ :=
      (M.groundBelow_iff_boundedWitness (subsets A hA) transitive).1 (small A hA)
    exact ⟨ZFSet.pair β f, ZFSet.pair_mem_prod.2 ⟨hβ, hf⟩,
      (pair_mem_belowWitnessRelation R K (M.groundRelations B K) A β f).2 ⟨hA, hβ, hf, code⟩⟩

theorem uniform_below_witnesses
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (choice : Realize M.sets SetFormula.choice Fin.elim0)
    {R B K : ZFSet.{u}} (hR : R ∈ M.sets) (hB : B ∈ M.sets) (hK : K ∈ M.sets)
    (subsets : ∀ A ∈ R, A ⊆ B) (transitive : ∀ β ∈ K, β ⊆ K)
    (small : ∀ A ∈ R, GroundBelow M A K) :
    ∃ F ∈ M.sets, ZFSet.IsFunc R (ZFSet.prod K (M.groundRelations B K)) F ∧
      ∀ A q, ZFSet.pair A q ∈ F →
        ∃ β ∈ K, ∃ f ∈ M.sets, q = ZFSet.pair β f ∧ InjectionCode A β f := by
  have hW := M.groundRelations_mem pairing unions powers separation hB hK
  have relation := M.groundBelowWitnesses_mem pairing unions powers separation hR hB hK
  have total := (M.groundBelowWitnesses_total_iff subsets transitive).2 small
  obtain ⟨F, hF, function, selected⟩ := M.uniformize_relation pairing unions powers separation choice
    hR (M.prod_mem pairing unions powers separation hK hW) relation total
  refine ⟨F, hF, function, ?_⟩
  intro A q entry
  have hq := (ZFSet.pair_mem_prod.1 (function.1 entry)).2
  obtain ⟨β, hβ, f, hf, rfl⟩ := ZFSet.mem_prod.1 hq
  have code := ((pair_mem_belowWitnessRelation R K (M.groundRelations B K) A β f).1
    (selected entry)).2.2.2
  exact ⟨β, hβ, f, ((M.mem_groundRelations B K f).1 hf).1, rfl, code⟩

theorem uniform_below_family
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (choice : Realize M.sets SetFormula.choice Fin.elim0)
    {R K : ZFSet.{u}} (hR : R ∈ M.sets) (hK : K ∈ M.sets)
    (transitive : ∀ β ∈ K, β ⊆ K) (small : ∀ A ∈ R, GroundBelow M A K) :
    ∃ F ∈ M.sets, ZFSet.IsFunc R (ZFSet.prod K (M.groundRelations (⋃₀ R) K)) F ∧
      ∀ A q, ZFSet.pair A q ∈ F →
        ∃ β ∈ K, ∃ f ∈ M.sets, q = ZFSet.pair β f ∧ InjectionCode A β f :=
  M.uniform_below_witnesses pairing unions powers separation choice hR (M.union_mem unions hR) hK
    (fun A hA _ hx => ZFSet.mem_sUnion.2 ⟨A, hA, hx⟩) transitive small

end TransitiveGround

namespace GroundRegular
variable {M : TransitiveGround.{u}} {K : ZFSet.{u}} (regular : GroundRegular M K)
variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
variable (unions : Realize M.sets SetFormula.union Fin.elim0)
variable (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
include regular pairing unions powers separation

theorem bound_witnesses {R W F : ZFSet.{u}}
    (hR : R ∈ M.sets) (hK : K ∈ M.sets) (hW : W ∈ M.sets) (hF : F ∈ M.sets)
    (ordinal : ordinalSetProperty K) (small : GroundBelow M R K)
    (family : ZFSet.IsFunc R (ZFSet.prod K W) F)
    (witnesses : ∀ A β f, ZFSet.pair A (ZFSet.pair β f) ∈ F → InjectionCode A β f) :
    ∃ δ ∈ K, ∀ A β f, ZFSet.pair A (ZFSet.pair β f) ∈ F →
      β ∈ δ ∧ InjectionCode A β f ∧ InjectionCode A δ f := by
  obtain ⟨δ, hδ, bounded⟩ := regular.bound_paired pairing unions powers separation hR hK hW hF small family
  refine ⟨δ, hδ, ?_⟩
  intro A β f entry
  have hβ := bounded A β f entry
  have code := witnesses A β f entry
  refine ⟨hβ, code, ⟨⟨?_, code.function.2⟩, code.injective⟩⟩
  intro z hz
  obtain ⟨x, hx, y, hy, rfl⟩ := ZFSet.mem_prod.1 (code.function.1 hz)
  exact ZFSet.pair_mem_prod.2 ⟨hx, (ordinal.2 δ hδ) β hβ y hy⟩

end GroundRegular

namespace TransitiveGround
variable (M : TransitiveGround.{u})

theorem uniform_below_common_bound
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (choice : Realize M.sets SetFormula.choice Fin.elim0)
    {R K : ZFSet.{u}} (hR : R ∈ M.sets) (hK : K ∈ M.sets)
    (ordinal : ordinalSetProperty K) (regular : GroundRegular M K)
    (indices : GroundBelow M R K) (small : ∀ A ∈ R, GroundBelow M A K) :
    ∃ δ ∈ K, ∃ F ∈ M.sets,
      ZFSet.IsFunc R (ZFSet.prod K (M.groundRelations (⋃₀ R) K)) F ∧
      ∀ A β f, ZFSet.pair A (ZFSet.pair β f) ∈ F →
        f ∈ M.sets ∧ β ∈ δ ∧ InjectionCode A β f ∧ InjectionCode A δ f := by
  obtain ⟨F, hF, family, witnesses⟩ := M.uniform_below_family
    pairing unions powers separation choice hR hK ordinal.1 small
  have actual : ∀ A β f, ZFSet.pair A (ZFSet.pair β f) ∈ F →
      f ∈ M.sets ∧ InjectionCode A β f := by
    intro A β f entry
    obtain ⟨β', _, f', hf, equal, code⟩ := witnesses A (ZFSet.pair β f) entry
    obtain ⟨rfl, rfl⟩ := ZFSet.pair_inj.1 equal
    exact ⟨hf, code⟩
  obtain ⟨δ, hδ, bounded⟩ := regular.bound_witnesses pairing unions powers separation hR hK
    (M.groundRelations_mem pairing unions powers separation (M.union_mem unions hR) hK) hF
    ordinal indices family (fun A β f entry => (actual A β f entry).2)
  exact ⟨δ, hδ, F, hF, family, fun A β f entry =>
    ⟨(actual A β f entry).1, bounded A β f entry⟩⟩

end TransitiveGround
end PartitionPilot.Forcing

namespace PartitionPilot.Forcing.TransitiveGround
open SetFormula
open scoped ZFSet
universe u
variable (M : TransitiveGround.{u})
variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
variable (unions : Realize M.sets SetFormula.union Fin.elim0)
variable (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
variable (choice : Realize M.sets SetFormula.choice Fin.elim0)
include M pairing unions powers separation choice

theorem selected_union_embeds_product {R W D F : ZFSet.{u}}
    (hR : R ∈ M.sets) (hW : W ∈ M.sets) (hD : D ∈ M.sets) (hF : F ∈ M.sets)
    (family : ZFSet.IsFunc R W F)
    (codes : ∀ A f, ZFSet.pair A f ∈ F → InjectionCode A D f) :
    M.groundEmbeddable (⋃₀ R) (ZFSet.prod R D) :=
  M.groundEmbeddable_of_partial_surjection pairing unions powers separation choice
    (M.prod_mem pairing unions powers separation hR hD) (M.union_mem unions hR)
    (M.unionSizeRelation_mem pairing unions powers separation (M.union_mem unions hR) hR hW hD hF)
    (unionSizeRelation_partial family codes) (unionSizeRelation_onto family codes)

theorem paired_union_embeds_product {R K W D F : ZFSet.{u}}
    (hR : R ∈ M.sets) (hK : K ∈ M.sets) (hW : W ∈ M.sets)
    (hD : D ∈ M.sets) (hF : F ∈ M.sets)
    (family : ZFSet.IsFunc R (ZFSet.prod K W) F)
    (codes : ∀ A β f, ZFSet.pair A (ZFSet.pair β f) ∈ F → InjectionCode A D f) :
    M.groundEmbeddable (⋃₀ R) (ZFSet.prod R D) := by
  let H := relationCompose R (ZFSet.prod K W) W F (productSecond K W)
  have hH : H ∈ M.sets := M.relationCompose_mem pairing unions powers separation hR
    (M.prod_mem pairing unions powers separation hK hW) hW hF
    (M.productSecond_mem pairing unions powers separation hK hW)
  have selected : ZFSet.IsFunc R W H :=
    relationCompose_function_of_subset family (productSecond_function K W) (fun _ h => h)
  have actual : ∀ A f, ZFSet.pair A f ∈ H → InjectionCode A D f := by
    intro A f entry
    obtain ⟨_, _, q, _, aq, projection⟩ := (pair_mem_relationCompose _ _ _ _ _ A f).1 entry
    obtain ⟨β, _, g, _, equal⟩ := (mem_productSecond K W (ZFSet.pair q f)).1 projection
    obtain ⟨rfl, rfl⟩ := ZFSet.pair_inj.1 equal
    exact codes A β f aq
  exact M.selected_union_embeds_product pairing unions powers separation choice hR hW hD hH selected actual

theorem regular_union_embeds_product {R K : ZFSet.{u}}
    (hR : R ∈ M.sets) (hK : K ∈ M.sets)
    (ordinal : ordinalSetProperty K) (regular : GroundRegular M K)
    (indices : GroundBelow M R K) (small : ∀ A ∈ R, GroundBelow M A K) :
    ∃ D ∈ K, M.groundEmbeddable (⋃₀ R) (ZFSet.prod R D) := by
  obtain ⟨D, hD, F, hF, family, witnesses⟩ := M.uniform_below_common_bound
    pairing unions powers separation choice hR hK ordinal regular indices small
  exact ⟨D, hD, M.paired_union_embeds_product pairing unions powers separation choice hR hK
    (M.groundRelations_mem pairing unions powers separation (M.union_mem unions hR) hK)
    (M.transitive hK hD) hF family (fun A β f entry => (witnesses A β f entry).2.2.2)⟩

end PartitionPilot.Forcing.TransitiveGround

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Geometry_GroundBelowInitialCompression
attribute [-instance] _root_.OAI.PartitionPilot.Forcing.GroundMainPrefix.withTopSmall
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PartitionPilot.Forcing

namespace GroundBelow
open SetFormula
universe u
variable {M : TransitiveGround.{u}}
variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
variable (unions : Realize M.sets SetFormula.union Fin.elim0)
variable (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
variable (choice : Realize M.sets SetFormula.choice Fin.elim0)
include pairing unions powers separation choice

theorem sUnion {R K : ZFSet.{u}} (hR : R ∈ M.sets) (hK : K ∈ M.sets)
    (ordinal : ordinalSetProperty K) (regular : GroundRegular M K) (strong : GroundStrongLimit M K)
    (indices : GroundBelow M R K) (small : ∀ A ∈ R, GroundBelow M A K) :
    GroundBelow M R.sUnion K := by
  obtain ⟨D, hD, witness⟩ := M.regular_union_embeds_product
    pairing unions powers separation choice hR hK ordinal regular indices small
  have hDM := M.transitive hK hD
  have smallD := GroundBelow.of_member pairing unions powers separation hK hD
  have product := GroundBelow.product pairing unions powers separation hR hDM hK ordinal strong indices smallD
  exact product.of_embeddable pairing unions powers separation (M.union_mem unions hR)
    (M.prod_mem pairing unions powers separation hR hDM) hK witness

theorem indexed_sUnion {I Q F K : ZFSet.{u}}
    (hI : I ∈ M.sets) (hQ : Q ∈ M.sets) (hF : F ∈ M.sets) (hK : K ∈ M.sets)
    (ordinal : ordinalSetProperty K) (regular : GroundRegular M K) (strong : GroundStrongLimit M K)
    (indices : GroundBelow M I K) (family : ZFSet.IsFunc I Q F)
    (small : ∀ i A, ZFSet.pair i A ∈ F → GroundBelow M A K) :
    GroundBelow M (relationImage I Q F).sUnion K := by
  have hR := M.relationImage_mem separation hI hQ hF
  have indexImage := indices.function_image pairing unions powers separation choice hI hQ hK hF family
  apply GroundBelow.sUnion pairing unions powers separation choice hR hK ordinal regular strong indexImage
  intro A hA
  obtain ⟨_, i, _, entry⟩ := (mem_relationImage I Q F A).1 hA
  exact small i A entry

end GroundBelow

namespace GroundBelow
open SetFormula
universe u
variable {M : TransitiveGround.{u}} {K : ZFSet.{u}}
variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
variable (unions : Realize M.sets SetFormula.union Fin.elim0)
variable (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
variable (infinite : Realize M.sets infinity Fin.elim0)
variable (choice : Realize M.sets SetFormula.choice Fin.elim0)

theorem of_countable {A : ZFSet.{u}} (omega : ZFSet.omega ∈ K)
    (small : M.groundEmbeddable A ZFSet.omega) : GroundBelow M A K := ⟨ZFSet.omega, omega, small⟩

include pairing unions powers separation infinite

theorem singleton {a : ZFSet.{u}} (hK : K ∈ M.sets) (omega : ZFSet.omega ∈ K)
    (ha : a ∈ M.sets) : GroundBelow M ({a} : ZFSet.{u}) K := by
  have hEmpty := M.empty_mem ⟨K, hK⟩
  apply of_countable omega
  simpa using M.groundEmbeddable_insert pairing unions powers separation infinite hEmpty ha
    (M.empty_groundEmbeddable ZFSet.omega ⟨K, hK⟩)

theorem unorderedPair {a b : ZFSet.{u}} (hK : K ∈ M.sets) (omega : ZFSet.omega ∈ K)
    (ha : a ∈ M.sets) (hb : b ∈ M.sets) : GroundBelow M ({a, b} : ZFSet.{u}) K := by
  have hEmpty := M.empty_mem ⟨K, hK⟩
  have first := M.groundEmbeddable_insert pairing unions powers separation infinite hEmpty hb
    (M.empty_groundEmbeddable ZFSet.omega ⟨K, hK⟩)
  have ground := M.insert_mem pairing unions hb hEmpty
  apply of_countable omega
  simpa using M.groundEmbeddable_insert pairing unions powers separation infinite ground ha first

include choice

theorem binary_union {A B : ZFSet.{u}}
    (hA : A ∈ M.sets) (hB : B ∈ M.sets) (hK : K ∈ M.sets) (omega : ZFSet.omega ∈ K)
    (ordinal : ordinalSetProperty K) (regular : GroundRegular M K) (strong : GroundStrongLimit M K)
    (first : GroundBelow M A K) (second : GroundBelow M B K) : GroundBelow M (A ∪ B) K := by
  have result := sUnion pairing unions powers separation choice (M.unorderedPair_mem pairing hA hB) hK
    ordinal regular strong (unorderedPair pairing unions powers separation infinite hK omega hA hB)
    (fun X hX => (ZFSet.mem_pair.1 hX).elim (fun equal => equal ▸ first) (fun equal => equal ▸ second))
  simpa only [ZFSet.sUnion_pair] using result

theorem insert {A a : ZFSet.{u}}
    (hA : A ∈ M.sets) (ha : a ∈ M.sets) (hK : K ∈ M.sets) (omega : ZFSet.omega ∈ K)
    (ordinal : ordinalSetProperty K) (regular : GroundRegular M K) (strong : GroundStrongLimit M K)
    (small : GroundBelow M A K) : GroundBelow M (Insert.insert a A) K := by
  have hs : ({a} : ZFSet.{u}) ∈ M.sets := by
    simpa only [ZFSet.pair_eq_singleton] using M.unorderedPair_mem pairing ha ha
  have result := binary_union pairing unions powers separation infinite choice hs hA hK omega
    ordinal regular strong (singleton pairing unions powers separation infinite hK omega ha) small
  have equal : ({a} : ZFSet.{u}) ∪ A = Insert.insert a A := by
    apply ZFSet.ext
    intro x
    simp only [ZFSet.mem_union, ZFSet.mem_singleton, ZFSet.mem_insert_iff]
  exact equal ▸ result

end GroundBelow

open SetFormula
universe u

end PartitionPilot.Forcing

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Geometry_GroundBelowExternalPoints
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
namespace GroundBelow
variable {M : TransitiveGround.{u}} {A E K : ZFSet.{u}}

theorem equivalenceClasses
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (hA : A ∈ M.sets) (hE : E ∈ M.sets) (hK : K ∈ M.sets)
    (strong : GroundStrongLimit M K) (small : GroundBelow M A K) :
    GroundBelow M (Forcing.equivalenceClasses A E) K := by
  have included : Forcing.equivalenceClasses A E ⊆ M.groundPower A := by
    intro X hX
    rw [M.equivalenceClasses_eq_sep_groundPower separation hA hE] at hX
    exact (ZFSet.mem_sep.1 hX).1
  exact (strong.power_closed pairing unions powers separation hA hK small).restrict
    separation (M.equivalenceClasses_mem powers separation hA hE) hK included

end GroundBelow

end

end PartitionPilot.Forcing

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Definability_GroundBelowIndexedCarriers
attribute [-instance] _root_.OAI.PartitionPilot.Forcing.GroundMainPrefix.withTopSmall
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PartitionPilot.Forcing.GroundBelow
open SetFormula
universe u
variable {M : TransitiveGround.{u}} {T U A E K : ZFSet.{u}}
variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
variable (unions : Realize M.sets SetFormula.union Fin.elim0)
variable (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
include pairing unions powers separation

theorem indexedCarrierLabels (hT : T ∈ M.sets) (hU : U ∈ M.sets) (hA : A ∈ M.sets)
    (hK : K ∈ M.sets) (ordinal : ordinalSetProperty K) (strong : GroundStrongLimit M K)
    (indices : GroundBelow M T K) (points : GroundBelow M U K) :
    GroundBelow M (Forcing.indexedCarrierLabels T U A) K :=
  (GroundBelow.product pairing unions powers separation hT hU hK ordinal strong indices points).restrict
    separation (M.indexedCarrierLabels_mem pairing unions powers separation hT hU hA) hK
    (indexedCarrierLabels_subset T U A)

theorem indexedCarrierClasses (hT : T ∈ M.sets) (hU : U ∈ M.sets) (hA : A ∈ M.sets)
    (hE : E ∈ M.sets) (hK : K ∈ M.sets)
    (ordinal : ordinalSetProperty K) (strong : GroundStrongLimit M K)
    (indices : GroundBelow M T K) (points : GroundBelow M U K) :
    GroundBelow M (Forcing.equivalenceClasses (Forcing.indexedCarrierLabels T U A) E) K :=
  GroundBelow.equivalenceClasses pairing unions powers separation
    (M.indexedCarrierLabels_mem pairing unions powers separation hT hU hA) hE hK strong
    (GroundBelow.indexedCarrierLabels pairing unions powers separation hT hU hA hK ordinal strong indices points)

end PartitionPilot.Forcing.GroundBelow

end

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Definability_IndexedValueLiftCodes
attribute [-instance] _root_.OAI.PartitionPilot.Forcing.GroundMainPrefix.withTopSmall
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PartitionPilot.Forcing
universe u

namespace BoundedFormula
open SetFormula

theorem truth_indexedValueLiftEntryFormula (env : Fin 9 → ZFSet.{u}) :
    Truth indexedValueLiftEntryFormula env ↔
      ∃ i ∈ env 1, ∃ f ∈ env 7, ∃ e ∈ env 8, ∃ x ∈ env 2, ∃ q ∈ env 3, ∃ v ∈ env 4,
        env 0 = ZFSet.pair q v ∧ ZFSet.pair i f ∈ env 5 ∧ ZFSet.pair i e ∈ env 6 ∧
        ZFSet.pair x q ∈ e ∧ ZFSet.pair x v ∈ f := by
  simp only [indexedValueLiftEntryFormula, truth_exMem, Truth,
    truth_orderedPairFormula, truth_pairMembershipFormula]
  rfl

end BoundedFormula

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

def bottom : ZFSet.{u} := natSetCode 0

end PartitionPilot.Forcing.InitialMainAlgebra

end

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Transfinite_SerializedChronologyCodes
attribute [-instance] _root_.OAI.PartitionPilot.Forcing.GroundMainPrefix.withTopSmall
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PartitionPilot.Forcing
universe u

def ChronologyLayerEntries (T N : ZFSet.{u}) (graphs : Fin 5 → ZFSet.{u})
    (layers : ZFSet.{u}) : Prop :=
  ∀ s ∈ T, ∀ t ∈ T, t = s ∨ t ∈ s → ∀ L r μ birth z,
    ZFSet.pair s L ∈ graphs 0 → ZFSet.pair s r ∈ graphs 1 →
    ZFSet.pair s μ ∈ graphs 2 → ZFSet.pair s birth ∈ graphs 3 →
    ZFSet.pair (ZFSet.pair s t) z ∈ layers →
      GrowthLayerWitnessCode (graphs 0) (graphs 1) (graphs 2) L r μ birth t N z

end PartitionPilot.Forcing

end

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

namespace BoundedFormula

theorem truth_ownerLevelPrefixPointFormula {n} (z P B levels omega : Fin n)
    (env : Fin n → ZFSet.{u}) (omegaEq : env omega = ZFSet.omega) :
    Truth (ownerLevelPrefixPointFormula z P B levels omega) env ↔
      env z ∈ ownerLevelPrefixPoints (env P) (env B) (env levels) := by
  simp only [ownerLevelPrefixPointFormula, truth_exMem, Truth, truth_orderedPairFormula,
    ownerLevelPrefixFormula, truth_disj, truth_pairMembershipFormula]
  simp only [extend, Fin.cases_zero, Fin.cases_succ]
  rw [omegaEq, ownerLevelPrefixPoints, ZFSet.mem_sep]
  simp only [mem_ownerLevelPrefix]
  refine ⟨fun h => ⟨?_, h⟩, And.right⟩
  obtain ⟨n, hn, x, hx, equal, _⟩ := h
  rw [equal]
  exact ZFSet.pair_mem_prod.2 ⟨hn, hx⟩
end BoundedFormula

namespace BoundedFormula

theorem truth_chronologyRestrictionMemberFormula (kind : Fin 3) {n}
    (z P R : Fin n) (env : Fin n → ZFSet.{u}) {f : ZFSet.{u}}
    (bound : env R = ZFSet.sUnion (ZFSet.sUnion f)) (member : env z ∈ f) :
    Truth (chronologyRestrictionMemberFormula kind z P R) env ↔
      env z ∈ chronologyRestriction kind (env P) f := by
  refine Fin.cases ?_ (Fin.cases ?_ (fun _ => ?_)) kind
  · simp only [chronologyRestrictionMemberFormula, chronologyRestriction, Fin.cases_zero,
      truth_productElementFormula, graphRestriction, ZFSet.mem_sep, member, true_and, bound]
  · simp only [chronologyRestrictionMemberFormula, chronologyRestriction, Fin.cases_succ,
      Fin.cases_zero, truth_productElementFormula, heightOrderRestriction, ZFSet.mem_sep, member, true_and]
  · simp only [chronologyRestrictionMemberFormula, chronologyRestriction, Fin.cases_succ,
      truth_exMem, Truth, truth_orderedPairFormula, truth_productElementFormula]
    change (∃ a ∈ env R, ∃ b ∈ env R, env z = ZFSet.pair a b ∧ a ∈ ZFSet.prod (env P) (env P)) ↔ _
    constructor
    · rintro ⟨a, _, b, _, equal, ha⟩
      rw [equal] at member ⊢
      exact pair_mem_graphRestriction.2 ⟨member, ha⟩
    · intro entry
      obtain ⟨a, ha, b, equal, pair⟩ := mem_graphRestriction.1 entry
      exact ⟨a, bound.symm ▸ pair_first_mem_doubleUnion pair,
        b, bound.symm ▸ pair_second_mem_doubleUnion pair, equal, ha⟩

theorem truth_chronologyRestrictionFormula (kind : Fin 3) {n}
    (q P R f : Fin n) (env : Fin n → ZFSet.{u}) (bound : env R = ZFSet.sUnion (ZFSet.sUnion (env f))) :
    Truth (chronologyRestrictionFormula kind q P R f) env ↔
      env q = chronologyRestriction kind (env P) (env f) := by
  have subset : chronologyRestriction kind (env P) (env f) ⊆ env f := by
    exact Fin.cases (graphRestriction_subset _ _)
      (Fin.cases (fun _ hz => (ZFSet.mem_sep.1 hz).1)
        (fun _ => graphRestriction_subset _ _)) kind
  simp only [chronologyRestrictionFormula, Truth, truth_imp]
  constructor
  · rintro ⟨forward, backward⟩
    apply ZFSet.ext
    intro z
    constructor
    · intro hz
      exact (truth_chronologyRestrictionMemberFormula kind 0 P.succ R.succ (extend z env)
        bound (forward z hz).1).1 (forward z hz).2
    · intro hz
      exact backward z (subset hz) ((truth_chronologyRestrictionMemberFormula kind 0 P.succ R.succ
        (extend z env) bound (subset hz)).2 hz)
  · intro equal
    change (∀ z ∈ env q, z ∈ env f ∧ _) ∧ (∀ z ∈ env f, _ → z ∈ env q)
    rw [equal]
    exact ⟨fun z hz => ⟨subset hz, (truth_chronologyRestrictionMemberFormula kind 0 P.succ R.succ
      (extend z env) bound (subset hz)).2 hz⟩,
      fun z hz recognized => (truth_chronologyRestrictionMemberFormula kind 0 P.succ R.succ
        (extend z env) bound hz).1 recognized⟩

theorem truth_chronologyRestrictionFamilyFormula (kind : Fin 3) {n}
    (z I Ps Q R W f : Fin n) (env : Fin n → ZFSet.{u}) (bound : env R = ZFSet.sUnion (ZFSet.sUnion (env f))) :
    Truth (chronologyRestrictionFamilyFormula kind z I Ps Q R W f) env ↔
      ∃ i ∈ env I, ∃ P ∈ env Q, ∃ q ∈ env W, env z = ZFSet.pair i q ∧
        ZFSet.pair i P ∈ env Ps ∧ q = chronologyRestriction kind P (env f) := by
  have meaning (i P q : ZFSet.{u}) :=
    truth_chronologyRestrictionFormula kind 0 1 R.succ.succ.succ f.succ.succ.succ
      (extend q (extend P (extend i env))) bound
  simp only [chronologyRestrictionFamilyFormula, truth_exMem, Truth,
    truth_orderedPairFormula, truth_pairMembershipFormula, meaning]
  rfl

end BoundedFormula

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

namespace BoundedFormula

def productEquationFormula {n} (B C D : Fin n) : BoundedFormula n :=
  .conj (.allMem B (productElementFormula 0 C.succ D.succ))
    (.allMem C (.allMem D.succ (pairMembershipFormula 1 0 B.succ.succ)))

def mainStageLawsFormula {n} (P r μ G m inv one A b t height C D rD : Fin n) :
    BoundedFormula n :=
  .conj (meetOrderFormula P r μ) (.conj (groupFormula G m inv one)
    (.conj (posetActionFormula G P m one r A) (.conj (bottomFormula P r b)
      (.conj (topFormula P r t) (strictLexHeightFormula P C D r height rD)))))

def mainStageWitnessFormula {n}
    (P r μ G m inv one A b t height C D rD B R N f : Fin n) : BoundedFormula n :=
  .conj (mainStageLawsFormula P r μ G m inv one A b t height C D rD)
    (.conj (productEquationFormula B C D)
      (.conj (imageSetFormula R P B height) (injectionFormula R N f)))

end BoundedFormula

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
universe u

namespace BoundedFormula
def serializedChronologyTupleFormula {n} (z history T V : Fin n) (graphs : Fin 5 → Fin n)
    (W layers : Fin n) : BoundedFormula n :=
  .conj (nonemptyTupleFormula 6 history (Fin.cases T (Fin.cases V graphs)))
    (nonemptyTupleFormula 2 z (Fin.cases history (Fin.cases W (fun _ => layers))))

end BoundedFormula

end

section
open SetFormula
universe u v

namespace BoundedFormula

def linkedMainStageTupleFormula {n} (z a t h : Fin n) : BoundedFormula n :=
  nonemptyTupleFormula 2 z (Fin.cases a (Fin.cases t (fun _ => h)))

def linkedTerminalFormula {n} (t T P r μ h : Fin n) (graphs : Fin 5 → Fin n) : BoundedFormula n :=
  .conj (ordinalFormula t) (.conj (successorFormula T t)
    (.conj (pairMembershipFormula t P (graphs 0)) (.conj (pairMembershipFormula t r (graphs 1))
      (.conj (pairMembershipFormula t μ (graphs 2)) (pairMembershipFormula t h (graphs 4))))))

end BoundedFormula

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

namespace BoundedFormula

def linkedTransitionLawsFormula {n} (z points actors sourceBirth targetBirth : Fin n)
    (f g : Fin 24 → Fin n) : BoundedFormula n :=
  .conj (pairMembershipFormula (f 11) sourceBirth (f 17))
    (.conj (pairMembershipFormula (g 11) targetBirth (g 17))
      (coveredChronologicalMainTransitionFormula z (f 0) (g 0) (f 1) (g 1) (f 2) (g 2) (f 3) (g 3) (f 4) (g 4) (f 6) (g 6) (f 7) (g 7) (f 8) (g 8) (f 10) (g 10)
        points actors (f 11) (g 11) sourceBirth targetBirth
          (linkedChronologyGraphs f) (linkedChronologyGraphs g)))

end BoundedFormula

end PartitionPilot.Forcing

end

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

section
open SetFormula
universe u

namespace BoundedFormula

def mainPrefixTupleFormula {n} (z T S E : Fin n) : BoundedFormula n :=
  nonemptyTupleFormula 2 z (Fin.cases T (Fin.cases S (fun _ => E)))

end BoundedFormula

end

end PartitionPilot.Forcing

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Definability_MainLimitCoverageFormulas
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace PartitionPilot.Forcing.BoundedFormula
open SetFormula
universe u

theorem truth_exGraphFields {n} (f : Fin n) (body : BoundedFormula (n + 2))
    (env : Fin n → ZFSet.{u}) :
    Truth (exGraphFields f body) env ↔
      ∃ x y, ZFSet.pair x y ∈ env f ∧ Truth body (extend y (extend x env)) := by
  simp only [exGraphFields, truth_exMem, truth_exPairFields, truth_reindex]
  have rearrange (z x y : ZFSet.{u}) :
      (fun i => extend y (extend x (extend z env))
        (Fin.cases 0 (Fin.cases 1 (fun j => j.succ.succ.succ)) i)) =
        extend y (extend x env) := by
    funext i
    refine Fin.cases ?_ (fun j => Fin.cases ?_ (fun k => ?_) j) i <;> rfl
  simp only [rearrange]
  change (∃ z ∈ env f, ∃ x y, z = ZFSet.pair x y ∧
    Truth body (extend y (extend x env))) ↔ _
  constructor
  · rintro ⟨z, member, x, y, rfl, holds⟩
    exact ⟨x, y, member, holds⟩
  · rintro ⟨x, y, member, holds⟩
    exact ⟨ZFSet.pair x y, member, x, y, rfl, holds⟩

def exLinkedCoverageFields {n} (z : Fin n) (body : BoundedFormula (n + 3)) : BoundedFormula n :=
  exPairFields z (exPairFields 0 (exPairFields 3
    (exPairFields 0 (exPairFields 0 (exPairFields 0
      (.conj (tupleShapeFormula 6 0)
        (reindex (Fin.cases 9 (Fin.cases 1 (Fin.cases 7
          (fun i => i.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ)))) body)))))))





def exMainLimitStageFields {n} (T S : Fin n) (body : BoundedFormula (n + 4)) : BoundedFormula n :=
  exGraphFields S (.conj (.mem 1 T.succ.succ)
    (exLinkedCoverageFields 0 (reindex
      (Fin.cases 0 (Fin.cases 1 (Fin.cases 2 (Fin.cases 4
        (fun i => i.succ.succ.succ.succ.succ))))) body)))

def exMainLimitConeFields {n} (T S row : Fin n) (body : BoundedFormula (n + 6)) : BoundedFormula n :=
  exMainLimitStageFields T S (exGraphFields row.succ.succ.succ.succ
    (.conj (orderedPairFormula 1 T.succ.succ.succ.succ.succ.succ 5)
      (exPairFields 0 (reindex (Fin.cases 0 (Fin.cases 1 (Fin.cases 4 (Fin.cases 5
        (Fin.cases 6 (Fin.cases 7 (fun i => i.succ.succ.succ.succ.succ.succ.succ.succ))))))) body))))

def enumerationGraphEntryAt {n} (j e names g : Fin n) : BoundedFormula n :=
  exGraphFields g (.conj (.equal 1 j.succ.succ)
    (orderedPairFormula 0 e.succ.succ names.succ.succ))





def relativeAntichainFamilyFormula {n} (j A Q order domains : Fin n) : BoundedFormula n :=
  exGraphFields domains (.conj (.equal 1 j.succ.succ)
    (relativeMaximalAntichainFormula Q.succ.succ order.succ.succ 0 A.succ.succ))

theorem truth_assignmentQueryWithinFormula {n} (X T q : Fin n)
    (env : Fin n → ZFSet.{u}) :
    Truth (assignmentQueryWithinFormula X T q) env ↔
      AssignmentQueryWithin (env X) (env T) (env q) := by
  simp only [assignmentQueryWithinFormula, truth_exPairFields,
    truth_stageOneAssignmentsSubsetFormula]
  rfl

def representativeIndexAdditionsMemberFormula {n} (i I T Q c X : Fin n) : BoundedFormula n :=
  .conj (.mem i I) (exMem Q
    (.conj (assignmentQueryWithinFormula X.succ T.succ 0)
      (exGraphFields c.succ (.conj (.equal 1 2)
        (exPairFields 0
          (exMem T.succ.succ.succ.succ.succ
            (exMem T.succ.succ.succ.succ.succ.succ
              (exMem 2 (stageOneAssignmentFormula 0
                i.succ.succ.succ.succ.succ.succ.succ.succ 2 1)))))))))

theorem truth_representativeIndexAdditionsMemberFormula {n} (i I T Q c X : Fin n)
    (env : Fin n → ZFSet.{u}) :
    Truth (representativeIndexAdditionsMemberFormula i I T Q c X) env ↔
      env i ∈ representativeIndexAdditions (env I) (env T) (env Q) (env c) (env X) := by
  simp only [representativeIndexAdditionsMemberFormula, Truth, truth_exMem,
    truth_assignmentQueryWithinFormula, truth_exGraphFields, truth_exPairFields,
    truth_stageOneAssignmentFormula]
  rw [mem_representativeIndexAdditions]
  change (env i ∈ env I ∧ ∃ q ∈ env Q, AssignmentQueryWithin (env X) (env T) q ∧
    ∃ key value, ZFSet.pair key value ∈ env c ∧ key = q ∧
      ∃ row A, value = ZFSet.pair row A ∧ ∃ v ∈ env T, ∃ w ∈ env T,
        ∃ z ∈ A, z = stageOneAssignment (env i) v w) ↔ _
  apply and_congr Iff.rfl
  constructor
  · rintro ⟨q, hq, localQuery, key, value, entry, rfl, row, A, rfl, v, hv, w, hw, z, hz, rfl⟩
    exact ⟨key, hq, localQuery, row, A, entry, v, hv, w, hw, hz⟩
  · rintro ⟨q, hq, localQuery, row, A, entry, v, hv, w, hw, hz⟩
    exact ⟨q, hq, localQuery, q, ZFSet.pair row A, entry, rfl, row, A, rfl,
      v, hv, w, hw, stageOneAssignment (env i) v w, hz, rfl⟩





def supportedCertificateFormula {n}
    (nodes N order R niceEval visibilityEval value F B f : Fin n) : BoundedFormula n :=
  .conj (.allMem F (.mem 0 nodes.succ))
    (.conj (.allMem B (.mem 0 F.succ))
      (.conj (.allMem F (exMem B.succ (pairMembershipFormula 0 1 order.succ.succ)))
        (.conj (functionFormula B N f)
          (.conj
            (.neg (exGraphFields visibilityEval
              (.conj (.mem 1 nodes.succ.succ)
                (.neg (.conj (imp (.mem value.succ.succ 0) (.mem 1 F.succ.succ))
                  (imp (.mem 1 F.succ.succ) (.mem value.succ.succ 0)))))))
            (.allMem B (.allMem N.succ
              (imp (pairMembershipFormula 1 0 f.succ.succ)
                (.conj (pairMembershipFormula 1 0 R.succ.succ)
                  (pairMembershipFormula 0 value.succ.succ niceEval.succ.succ)))))))))

def supportedCertificateEntryFormula {n}
    (entry J PF PB WF nodes N order R inputEval niceEval visibilityEval : Fin n) :
    BoundedFormula n :=
  exPairFields entry (exPairFields 0 (exPairFields 0
    (.conj (.mem 5 J.succ.succ.succ.succ.succ.succ)
      (.conj (.mem 3 PF.succ.succ.succ.succ.succ.succ)
        (.conj (.mem 1 PB.succ.succ.succ.succ.succ.succ)
          (.conj (.mem 0 WF.succ.succ.succ.succ.succ.succ)
            (exGraphFields inputEval.succ.succ.succ.succ.succ.succ
              (.conj (.equal 1 7)
                (supportedCertificateFormula
                  nodes.succ.succ.succ.succ.succ.succ.succ.succ
                  N.succ.succ.succ.succ.succ.succ.succ.succ
                  order.succ.succ.succ.succ.succ.succ.succ.succ
                  R.succ.succ.succ.succ.succ.succ.succ.succ
                  niceEval.succ.succ.succ.succ.succ.succ.succ.succ
                  visibilityEval.succ.succ.succ.succ.succ.succ.succ.succ
                  0 5 3 2)))))))))





def exMainLimitImageFields {n} (actor : Bool) (T S row : Fin n)
    (body : BoundedFormula (n + 1)) : BoundedFormula n :=
  exMainLimitConeFields T S row (exGraphFields (if actor then 0 else 1)
    (.conj (.mem 1 (if actor then 5 else 6))
      (reindex (Fin.cases 0 (fun i => i.succ.succ.succ.succ.succ.succ.succ.succ)) body)))

def mainLimitImageFormula {n} (actor : Bool) (T S row x : Fin n) : BoundedFormula n :=
  exMainLimitImageFields actor T S row (.equal 0 x.succ)

def mainLimitOldCutoffFormula {n} (T S t : Fin n) : BoundedFormula n :=
  exMainLimitStageFields T S (disj (.equal t.succ.succ.succ.succ 0)
    (.mem t.succ.succ.succ.succ 0))





def mainLimitPointCoverageFormula {n} (T S row Q top : Fin n) : BoundedFormula n :=
  .conj (.allMem Q (imp (.neg (.equal 0 top.succ))
    (mainLimitImageFormula false T.succ S.succ row.succ 0)))
    (.neg (exMainLimitImageFields false T S row
      (.neg (.conj (.mem 0 Q.succ) (.neg (.equal 0 top.succ))))))

def mainLimitActorCoverageFormula {n} (T S row H : Fin n) : BoundedFormula n :=
  .conj (.allMem H (mainLimitImageFormula true T.succ S.succ row.succ 0))
    (.neg (exMainLimitImageFields true T S row (.neg (.mem 0 H.succ))))

def mainLimitStrictTopFormula {n} (T S row R top : Fin n) : BoundedFormula n :=
  .neg (exMainLimitConeFields T S row (exGraphFields 1 (.neg
    (.conj (pairMembershipFormula 0 top.succ.succ.succ.succ.succ.succ.succ.succ
      R.succ.succ.succ.succ.succ.succ.succ.succ)
      (.neg (pairMembershipFormula top.succ.succ.succ.succ.succ.succ.succ.succ 0
        R.succ.succ.succ.succ.succ.succ.succ.succ))))))

def mainLimitCutoffFormula {n} (T S cutoff : Fin n) : BoundedFormula n :=
  .conj (.allMem cutoff (mainLimitOldCutoffFormula T.succ S.succ 0))
    (.neg (exMainLimitStageFields T S (.neg
      (.conj (.mem 0 cutoff.succ.succ.succ.succ)
        (.allMem 0 (.mem 0 cutoff.succ.succ.succ.succ.succ))))))

def mainLimitTopBirthFormula {n} (top cutoff birth : Fin n) : BoundedFormula n :=
  .conj (pairMembershipFormula top cutoff birth)
    (.neg (exGraphFields birth (.conj (.equal 0 cutoff.succ.succ)
      (.neg (.equal 1 top.succ.succ)))))

def mainLimitCoverageFormula {n} (T S row Q H R top cutoff birth : Fin n) : BoundedFormula n :=
  .conj (mainLimitPointCoverageFormula T S row Q top)
    (.conj (mainLimitActorCoverageFormula T S row H)
      (.conj (mainLimitStrictTopFormula T S row R top)
        (.conj (mainLimitCutoffFormula T S cutoff) (mainLimitTopBirthFormula top cutoff birth))))

end PartitionPilot.Forcing.BoundedFormula

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
namespace BoundedFormula
open SetFormula

theorem truth_indexedRelationLiftEntryFormula (env : Fin 8 → ZFSet.{u}) :
    Truth indexedRelationLiftEntryFormula env ↔
      ∃ p ∈ env 3, ∃ q ∈ env 3, ∃ i ∈ env 1,
        ∃ r ∈ env 6, ∃ e ∈ env 7, ∃ x ∈ env 2, ∃ y ∈ env 2,
          env 0 = ZFSet.pair p q ∧ ZFSet.pair i r ∈ env 4 ∧
          ZFSet.pair i e ∈ env 5 ∧ ZFSet.pair x p ∈ e ∧
          ZFSet.pair y q ∈ e ∧ ZFSet.pair x y ∈ r := by
  simp only [indexedRelationLiftEntryFormula, truth_exMem, Truth,
    truth_orderedPairFormula, truth_pairMembershipFormula]
  rfl

def indexedBinaryLiftEntryFormula : BoundedFormula 8 :=
  exMem 3 (exMem 4 (exMem 5 (exMem 4 (exMem 10 (exMem 12 (exMem 8 (exMem 9 (exMem 10
    (.conj (orderedTripleFormula 9 8 7 6)
      (.conj (pairMembershipFormula 5 4 13)
        (.conj (pairMembershipFormula 5 3 14)
          (.conj (pairMembershipFormula 2 8 3)
            (.conj (pairMembershipFormula 1 7 3)
              (.conj (pairMembershipFormula 0 6 3)
                (tripleMembershipFormula 2 1 0 4)))))))))))))))

theorem truth_indexedBinaryLiftEntryFormula (env : Fin 8 → ZFSet.{u}) :
    Truth indexedBinaryLiftEntryFormula env ↔
      ∃ p ∈ env 3, ∃ q ∈ env 3, ∃ v ∈ env 3, ∃ i ∈ env 1,
        ∃ b ∈ env 6, ∃ e ∈ env 7, ∃ x ∈ env 2, ∃ y ∈ env 2, ∃ z ∈ env 2,
          env 0 = ZFSet.pair (ZFSet.pair p q) v ∧ ZFSet.pair i b ∈ env 4 ∧
          ZFSet.pair i e ∈ env 5 ∧ ZFSet.pair x p ∈ e ∧
          ZFSet.pair y q ∈ e ∧ ZFSet.pair z v ∈ e ∧
          ZFSet.pair (ZFSet.pair x y) z ∈ b := by
  simp only [indexedBinaryLiftEntryFormula, truth_exMem, Truth,
    truth_orderedTripleFormula, truth_pairMembershipFormula, truth_tripleMembershipFormula]
  rfl

end BoundedFormula

end PartitionPilot.Forcing

end

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Transfinite_GroundMainPrefixLimitGroupLaws
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open scoped ZFSet

namespace PartitionPilot.Forcing
universe u

theorem pair_mem_directLimitRelation (T U F L i x j y : ZFSet.{u}) :
    ZFSet.pair (ZFSet.pair i x) (ZFSet.pair j y) ∈ directLimitRelation T U F L ↔
      ZFSet.pair i x ∈ L ∧ ZFSet.pair j y ∈ L ∧
      i ∈ T ∧ x ∈ U ∧ j ∈ T ∧ y ∈ U ∧
      ∃ k ∈ T, ∃ w ∈ U, ∃ f g,
        ZFSet.pair (ZFSet.pair k i) f ∈ F ∧ ZFSet.pair (ZFSet.pair k j) g ∈ F ∧
        ZFSet.pair x w ∈ f ∧ ZFSet.pair y w ∈ g := by
  rw [directLimitRelation, ZFSet.mem_sep]
  constructor
  · rintro ⟨shape, a, ha, b, hb, c, hc, d, hd, k, hk, w, hw, f, _, g, _, equal, first, second, left, right⟩
    obtain ⟨ab, cd⟩ := ZFSet.pair_inj.1 equal
    obtain ⟨rfl, rfl⟩ := ZFSet.pair_inj.1 ab
    obtain ⟨rfl, rfl⟩ := ZFSet.pair_inj.1 cd
    exact ⟨(ZFSet.pair_mem_prod.1 shape).1, (ZFSet.pair_mem_prod.1 shape).2,
      ha, hb, hc, hd, k, hk, w, hw, f, g, first, second, left, right⟩
  · rintro ⟨leftLabel, rightLabel, hi, hx, hj, hy, k, hk, w, hw, f, g, first, second, left, right⟩
    exact ⟨ZFSet.pair_mem_prod.2 ⟨leftLabel, rightLabel⟩,
      i, hi, x, hx, j, hj, y, hy, k, hk, w, hw,
      f, pair_second_mem_doubleUnion first, g, pair_second_mem_doubleUnion second,
      rfl, first, second, left, right⟩

namespace BoundedFormula
open SetFormula

theorem truth_directLimitRelationEntryFormula (env : Fin 5 → ZFSet.{u}) :
    Truth directLimitRelationEntryFormula env ↔
      ∃ i ∈ env 1, ∃ x ∈ env 2, ∃ j ∈ env 1, ∃ y ∈ env 2,
        ∃ k ∈ env 1, ∃ w ∈ env 2, ∃ f ∈ env 3, ∃ g ∈ env 3,
          env 0 = ZFSet.pair (ZFSet.pair i x) (ZFSet.pair j y) ∧
          ZFSet.pair (ZFSet.pair k i) f ∈ env 4 ∧ ZFSet.pair (ZFSet.pair k j) g ∈ env 4 ∧
          ZFSet.pair x w ∈ f ∧ ZFSet.pair y w ∈ g := by
  simp only [directLimitRelationEntryFormula, truth_exMem, Truth,
    truth_pairOfPairsFormula, truth_tripleMembershipFormula, truth_pairMembershipFormula]
  rfl

end BoundedFormula

end PartitionPilot.Forcing

namespace PartitionPilot.Forcing.CodedDirectPresentation
universe u v
variable {I : Type v} [Small.{u} I] [Preorder I] {system : CodedDirectSystem.{u} I}
variable {T U A F : ZFSet.{u}} (p : CodedDirectPresentation system T U A F)

theorem relation_iff (i : I) (x : ZFSet.{u}) (j : I) (y : ZFSet.{u}) :
    ZFSet.pair (ZFSet.pair (p.key i) x) (ZFSet.pair (p.key j) y) ∈
        directLimitRelation T U F (indexedCarrierLabels T U A) ↔ system.Related i x j y := by
  rw [pair_mem_directLimitRelation]
  constructor
  · rintro ⟨_, _, _, _, _, _, k, hk, w, _, f, g, first, second, left, right⟩
    obtain ⟨k, rfl⟩ := p.exists_key hk
    obtain ⟨before, rfl⟩ := p.map_lookup first
    obtain ⟨after, rfl⟩ := p.map_lookup second
    exact ⟨k, before, after, w, left, right⟩
  · rintro ⟨k, first, second, w, left, right⟩
    have leftBounds := system.map_entry_bounds first left
    have rightBounds := system.map_entry_bounds second right
    exact ⟨(p.label_mem i x).2 leftBounds.1, (p.label_mem j y).2 rightBounds.1,
      p.key_mem i, p.carrier_bound i leftBounds.1, p.key_mem j, p.carrier_bound j rightBounds.1,
      p.key k, p.key_mem k, w, p.carrier_bound k leftBounds.2,
      system.map first, system.map second, p.map_entry first, p.map_entry second, left, right⟩

include p in
theorem relation_equivalence : EquivalenceRelationCode (indexedCarrierLabels T U A)
    (directLimitRelation T U F (indexedCarrierLabels T U A)) := by
  refine ⟨directLimitRelation_subset _ _ _ _, ?_, ?_, ?_⟩
  · intro x hx
    obtain ⟨i, x, member, rfl⟩ := p.label_cases hx
    exact (p.relation_iff i x i x).2 (system.related_refl member)
  · intro x y related
    obtain ⟨hx, hy⟩ := ZFSet.pair_mem_prod.1 (directLimitRelation_subset _ _ _ _ related)
    obtain ⟨i, x, _, rfl⟩ := p.label_cases hx
    obtain ⟨j, y, _, rfl⟩ := p.label_cases hy
    exact (p.relation_iff j y i x).2 (system.related_symm ((p.relation_iff i x j y).1 related))
  · intro x y z first second
    obtain ⟨hx, hy⟩ := ZFSet.pair_mem_prod.1 (directLimitRelation_subset _ _ _ _ first)
    have hz := (ZFSet.pair_mem_prod.1 (directLimitRelation_subset _ _ _ _ second)).2
    obtain ⟨i, x, _, rfl⟩ := p.label_cases hx
    obtain ⟨j, y, _, rfl⟩ := p.label_cases hy
    obtain ⟨k, z, _, rfl⟩ := p.label_cases hz
    exact (p.relation_iff i x k z).2
      (system.related_trans ((p.relation_iff i x j y).1 first) ((p.relation_iff j y k z).1 second))

end PartitionPilot.Forcing.CodedDirectPresentation

namespace PartitionPilot.Forcing
universe u v

noncomputable def directLimitInclusion (T U A F k : ZFSet.{u}) : ZFSet.{u} :=
  indexedClassInclusion U (indexedCarrierLabels T U A)
    (directLimitRelation T U F (indexedCarrierLabels T U A)) k

namespace CodedDirectPresentation
variable {I : Type v} [Small.{u} I] [Preorder I] {system : CodedDirectSystem.{u} I}
variable {T U A F : ZFSet.{u}} (p : CodedDirectPresentation system T U A F)

noncomputable def limitPoint (i : I) (x : ZFSet.{u}) : ZFSet.{u} :=
  equivalenceClass (indexedCarrierLabels T U A)
    (directLimitRelation T U F (indexedCarrierLabels T U A)) (ZFSet.pair (p.key i) x)

theorem limitPoint_mem {i : I} {x : ZFSet.{u}} (member : x ∈ system.carrier i) :
    p.limitPoint i x ∈ directLimitCarrier T U A F :=
  equivalenceClass_mem ((p.label_mem i x).2 member)

theorem limitPoint_eq_iff_related {i j : I} {x y : ZFSet.{u}}
    (hx : x ∈ system.carrier i) (hy : y ∈ system.carrier j) :
    p.limitPoint i x = p.limitPoint j y ↔ system.Related i x j y :=
  (p.relation_equivalence.class_eq_iff ((p.label_mem i x).2 hx) ((p.label_mem j y).2 hy)).trans
    (p.relation_iff i x j y)

theorem limitPoint_same_iff {i : I} {x y : ZFSet.{u}}
    (hx : x ∈ system.carrier i) (hy : y ∈ system.carrier i) :
    p.limitPoint i x = p.limitPoint i y ↔ x = y :=
  (p.limitPoint_eq_iff_related hx hy).trans (system.related_same_iff_eq hx)

theorem limitPoint_transition {i j : I} (before : i ≤ j) {x y : ZFSet.{u}}
    (entry : ZFSet.pair x y ∈ system.map before) :
    p.limitPoint i x = p.limitPoint j y :=
  (p.limitPoint_eq_iff_related (system.map_entry_bounds before entry).1
    (system.map_entry_bounds before entry).2).2 (system.related_of_entry before entry)

theorem inclusion_entry (i : I) (x y : ZFSet.{u}) :
    ZFSet.pair x y ∈ directLimitInclusion T U A F (p.key i) ↔
      x ∈ system.carrier i ∧ y = p.limitPoint i x :=
  pair_mem_indexedClassInclusion_of_entry p.carrier_function (p.carrier_entry i) (p.carrier_bound i)

theorem inclusion_injection (i : I) :
    InjectionCode (system.carrier i) (directLimitCarrier T U A F)
      (directLimitInclusion T U A F (p.key i)) := by
  refine ⟨indexedClassInclusion_function p.carrier_function (p.carrier_entry i) (p.carrier_bound i), ?_⟩
  intro x y z first second
  obtain ⟨hx, left⟩ := (p.inclusion_entry i x z).1 first
  obtain ⟨hy, right⟩ := (p.inclusion_entry i y z).1 second
  exact (p.limitPoint_same_iff hx hy).1 (left.symm.trans right)

theorem inclusion_comp {i j : I} (before : i ≤ j) :
    relationCompose (system.carrier i) (system.carrier j) (directLimitCarrier T U A F)
      (system.map before) (directLimitInclusion T U A F (p.key j)) =
      directLimitInclusion T U A F (p.key i) := by
  apply ZFSet.ext
  intro z
  constructor
  · intro entry
    obtain ⟨x, hx, y, _, w, _, rfl, xy, yw⟩ := (mem_relationCompose _ _ _ _ _ z).1 entry
    obtain ⟨_, equal⟩ := (p.inclusion_entry j y w).1 yw
    exact (p.inclusion_entry i x w).2 ⟨hx, equal.trans (p.limitPoint_transition before xy).symm⟩
  · intro entry
    obtain ⟨x, _, w, _, rfl⟩ := ZFSet.mem_prod.1 ((p.inclusion_injection i).function.1 entry)
    obtain ⟨hx, rfl⟩ := (p.inclusion_entry i x w).1 entry
    obtain ⟨y, xy⟩ := system.map_entry_total before hx
    have hy := (system.map_entry_bounds before xy).2
    exact (pair_mem_relationCompose _ _ _ _ _ _ _).2
      ⟨hx, p.limitPoint_mem hx, y, hy, xy,
        (p.inclusion_entry j y (p.limitPoint i x)).2 ⟨hy, p.limitPoint_transition before xy⟩⟩

end CodedDirectPresentation

end PartitionPilot.Forcing

namespace PartitionPilot.Forcing.CodedDirectPresentation
universe u v
variable {I : Type v} [Small.{u} I] [Preorder I]
variable {system : CodedDirectSystem.{u} I} {T U A F : ZFSet.{u}}
variable (p : CodedDirectPresentation system T U A F)

theorem limitPoint_coverage {z : ZFSet.{u}} (member : z ∈ directLimitCarrier T U A F) :
    ∃ i x, x ∈ system.carrier i ∧ z = p.limitPoint i x := by
  obtain ⟨label, labelMember, rfl⟩ := (mem_equivalenceClasses _ _ z).1 member
  obtain ⟨i, x, hx, rfl⟩ := p.label_cases labelMember
  exact ⟨i, x, hx, rfl⟩

theorem mixed_pair_coverage {other : CodedDirectSystem.{u} I} {T' U' A' F' : ZFSet.{u}}
    (q : CodedDirectPresentation other T' U' A' F') {z w : ZFSet.{u}}
    (hz : z ∈ directLimitCarrier T U A F) (hw : w ∈ directLimitCarrier T' U' A' F') :
    ∃ k x y, x ∈ system.carrier k ∧ y ∈ other.carrier k ∧
      z = p.limitPoint k x ∧ w = q.limitPoint k y := by
  obtain ⟨i, x, hx, rfl⟩ := p.limitPoint_coverage hz
  obtain ⟨j, y, hy, rfl⟩ := q.limitPoint_coverage hw
  obtain ⟨k, ik, jk⟩ := system.common_upper i j
  obtain ⟨x', xx'⟩ := system.map_entry_total ik hx
  obtain ⟨y', yy'⟩ := other.map_entry_total jk hy
  exact ⟨k, x', y', (system.map_entry_bounds ik xx').2, (other.map_entry_bounds jk yy').2,
    p.limitPoint_transition ik xx', q.limitPoint_transition jk yy'⟩

theorem mixed_triple_coverage {other third : CodedDirectSystem.{u} I}
    {T' U' A' F' T'' U'' A'' F'' : ZFSet.{u}}
    (q : CodedDirectPresentation other T' U' A' F')
    (r : CodedDirectPresentation third T'' U'' A'' F'') {z w v : ZFSet.{u}}
    (hz : z ∈ directLimitCarrier T U A F) (hw : w ∈ directLimitCarrier T' U' A' F')
    (hv : v ∈ directLimitCarrier T'' U'' A'' F'') :
    ∃ k x y a, x ∈ system.carrier k ∧ y ∈ other.carrier k ∧ a ∈ third.carrier k ∧
      z = p.limitPoint k x ∧ w = q.limitPoint k y ∧ v = r.limitPoint k a := by
  obtain ⟨i, x, y, hx, hy, rfl, rfl⟩ := p.mixed_pair_coverage q hz hw
  obtain ⟨j, a, ha, rfl⟩ := r.limitPoint_coverage hv
  obtain ⟨k, ik, jk⟩ := system.common_upper i j
  obtain ⟨x', xx'⟩ := system.map_entry_total ik hx
  obtain ⟨y', yy'⟩ := other.map_entry_total ik hy
  obtain ⟨a', aa'⟩ := third.map_entry_total jk ha
  exact ⟨k, x', y', a', (system.map_entry_bounds ik xx').2, (other.map_entry_bounds ik yy').2,
    (third.map_entry_bounds jk aa').2, p.limitPoint_transition ik xx',
    q.limitPoint_transition ik yy', r.limitPoint_transition jk aa'⟩

theorem pair_coverage {z w : ZFSet.{u}}
    (hz : z ∈ directLimitCarrier T U A F) (hw : w ∈ directLimitCarrier T U A F) :
    ∃ k x y, x ∈ system.carrier k ∧ y ∈ system.carrier k ∧
      z = p.limitPoint k x ∧ w = p.limitPoint k y :=
  p.mixed_pair_coverage p hz hw

theorem triple_coverage {z w v : ZFSet.{u}}
    (hz : z ∈ directLimitCarrier T U A F) (hw : w ∈ directLimitCarrier T U A F)
    (hv : v ∈ directLimitCarrier T U A F) :
    ∃ k x y a, x ∈ system.carrier k ∧ y ∈ system.carrier k ∧ a ∈ system.carrier k ∧
      z = p.limitPoint k x ∧ w = p.limitPoint k y ∧ v = p.limitPoint k a :=
  p.mixed_triple_coverage p p hz hw hv

end PartitionPilot.Forcing.CodedDirectPresentation

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
namespace BoundedFormula

def pairedTransitionEntryFormula {n} (i j p a E : Fin n) : BoundedFormula n :=
  exMem E (exMem 0 (exMem 0 (.conj
    (orderedPairFormula 0 p.succ.succ.succ a.succ.succ.succ)
    (orderedTripleFormula 2 j.succ.succ.succ i.succ.succ.succ 0))))

end BoundedFormula

end PartitionPilot.Forcing

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Definability_TaskCapFamilyCodes
attribute [-instance] _root_.OAI.PartitionPilot.Forcing.GroundMainPrefix.withTopSmall
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PartitionPilot.Forcing.BoundedFormula
open SetFormula
universe u

def imageInsertionProfileFormula {n} (Q R ν c E K F e : Fin n) : BoundedFormula n :=
  .allMem Q (imp (pairMembershipFormula E.succ 0 R.succ)
    (.conj
      (imp (imageProfilePositiveFormula F.succ Q.succ e.succ R.succ 0)
        (pairMembershipFormula K.succ 0 R.succ))
      (imp (.neg (imageProfilePositiveFormula F.succ Q.succ e.succ R.succ 0))
        (tripleMembershipFormula K.succ 0 c.succ ν.succ))))

def imageCapProfileFormula {n} (Q R ν c E K F e : Fin n) : BoundedFormula n :=
  .conj (.mem c Q) (.conj (.mem E Q) (.conj (.mem K Q)
    (.conj (.exMem Q (.exMem F.succ (pairMembershipFormula 0 1 e.succ.succ)))
      (.conj (imageInsertionProfileFormula Q R ν c E K F e)
        (.conj (pairMembershipFormula c K R)
          (.conj (.neg (pairMembershipFormula K c R)) (.neg (pairMembershipFormula E K R))))))))

end PartitionPilot.Forcing.BoundedFormula

namespace PartitionPilot.Forcing
universe u

namespace BoundedFormula
open SetFormula

def oldProfilePreservationFormula {n} (P r μ Q R ν e Filters : Fin n) : BoundedFormula n :=
  let lift (j : Fin n) := j.succ.succ.succ.succ.succ.succ.succ
  .allMem Filters (.allMem P.succ (.allMem P.succ.succ (.allMem P.succ.succ.succ
    (imp (codedCapProfileFormula P.succ.succ.succ.succ r.succ.succ.succ.succ
      μ.succ.succ.succ.succ 2 1 0 3)
      (.allMem Q.succ.succ.succ.succ (.allMem Q.succ.succ.succ.succ.succ
        (.allMem Q.succ.succ.succ.succ.succ.succ
          (imp (pairMembershipFormula 5 2 (lift e))
            (imp (pairMembershipFormula 4 1 (lift e))
              (imp (pairMembershipFormula 3 0 (lift e))
                (imageCapProfileFormula (lift Q) (lift R) (lift ν) 2 1 0 6 (lift e))))))))))))

end BoundedFormula

namespace BoundedFormula

def taskCapProfilesFormula {n}
    (I P Q R ν e Targets Separators Filters Families Caps : Fin n) : BoundedFormula n :=
  let lift (j : Fin n) := j.succ.succ.succ.succ.succ.succ.succ
  .allMem I (.allMem P.succ (.allMem P.succ.succ (.allMem Families.succ.succ.succ
    (.allMem Q.succ.succ.succ.succ (.allMem Q.succ.succ.succ.succ.succ
      (.allMem Q.succ.succ.succ.succ.succ.succ
        (imp (pairMembershipFormula 6 5 (lift Targets))
          (imp (pairMembershipFormula 6 4 (lift Separators))
            (imp (pairMembershipFormula 6 3 (lift Filters))
              (imp (pairMembershipFormula 6 2 (lift Caps))
                (imp (pairMembershipFormula 5 1 (lift e))
                  (imp (pairMembershipFormula 4 0 (lift e))
                    (imageCapProfileFormula (lift Q) (lift R) (lift ν) 1 0 2 3 (lift e))))))))))))))

def taskCapFamilyFormula {n}
    (I P Q R ν e Targets Separators Filters Families Caps : Fin n) : BoundedFormula n :=
  .conj (functionFormula I Q Caps)
    (.conj (taskCapProfilesFormula I P Q R ν e Targets Separators Filters Families Caps)
      (commonTargetCapMeetFormula I P Q ν e Targets Caps))

end BoundedFormula

end PartitionPilot.Forcing

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

namespace BoundedFormula
open SetFormula

def separatedActorsFormula : BoundedFormula 7 :=
  exMem 4 (exMem 5 (exMem 5 (exMem 6
    (.conj (orderedPairFormula 4 3 2)
      (.conj (tripleMembershipFormula 3 5 1 9)
        (.conj (tripleMembershipFormula 2 5 0 9) (tripleMembershipFormula 1 0 6 10)))))))

end BoundedFormula

end PartitionPilot.Forcing

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
namespace BoundedFormula
open SetFormula

def indexedMixedBinaryLiftEntryFormula : BoundedFormula 12 :=
  exMem 4 <| exMem 6 <| exMem 7 <| exMem 4 <| exMem 13 <|
    exMem 15 <| exMem 17 <| exMem 9 <| exMem 11 <| exMem 12 <|
      .conj (orderedTripleFormula 10 9 8 7) <|
        .conj (pairMembershipFormula 6 5 16) <|
          .conj (pairMembershipFormula 6 4 17) <|
            .conj (pairMembershipFormula 6 3 18) <|
              .conj (pairMembershipFormula 2 9 4) <|
                .conj (pairMembershipFormula 1 8 3) <|
                  .conj (pairMembershipFormula 0 7 3) (tripleMembershipFormula 2 1 0 5)

theorem truth_indexedMixedBinaryLiftEntryFormula (env : Fin 12 → ZFSet.{u}) :
    Truth indexedMixedBinaryLiftEntryFormula env ↔
      ∃ g ∈ env 4, ∃ p ∈ env 5, ∃ q ∈ env 5, ∃ i ∈ env 1,
        ∃ a ∈ env 9, ∃ eG ∈ env 10, ∃ eP ∈ env 11,
          ∃ u ∈ env 2, ∃ x ∈ env 3, ∃ y ∈ env 3,
            env 0 = ZFSet.pair (ZFSet.pair g p) q ∧
              ZFSet.pair i a ∈ env 6 ∧ ZFSet.pair i eG ∈ env 7 ∧ ZFSet.pair i eP ∈ env 8 ∧
              ZFSet.pair u g ∈ eG ∧ ZFSet.pair x p ∈ eP ∧ ZFSet.pair y q ∈ eP ∧
              ZFSet.pair (ZFSet.pair u x) y ∈ a := by
  simp only [indexedMixedBinaryLiftEntryFormula, truth_exMem, Truth,
    truth_orderedTripleFormula, truth_pairMembershipFormula, truth_tripleMembershipFormula]
  rfl

end BoundedFormula

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

namespace BoundedFormula

def mainSuccessorOutputFormula {n} (f : Fin 30 → Fin n) : BoundedFormula n :=
  .conj (mainTransitionLawsFormula (f 0) (f 1) (f 2) (f 3) (f 4) (f 5) (f 6) (f 7)
    (f 8) (f 9) (f 10) (f 11) (f 12) (f 13) (f 14) (f 15) (f 16) (f 17) (f 18) (f 19))
    (.conj (strictSuccessorTopFormula (f 0) (f 1) (f 3) (f 18) (f 29))
      (.conj (separationFulfillmentFormula (f 0) (f 2) (f 1) (f 3) (f 5) (f 7) (f 13) (f 18))
        (.conj (rectangleFulfillmentFormula (f 0) (f 6) (f 2) (f 4) (f 12)
          (f 1) (f 7) (f 3) (f 5) (f 13) (f 18) (f 19))
          (.conj (oldProfilePreservationFormula (f 0) (f 2) (f 4) (f 1) (f 3) (f 5) (f 18) (f 26))
            (.conj (taskCapFamilyFormula (f 21) (f 0) (f 1) (f 3) (f 5) (f 18)
              (f 23) (f 24) (f 25) (f 26) (f 28))
              (compressionActorFulfillmentFormula (f 21) (f 0) (f 6) (f 1) (f 7)
                (f 3) (f 13) (f 18) (f 19) (f 22) (f 27) (f 20) (f 28)))))))

end BoundedFormula

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

namespace BoundedFormula
open SetFormula
universe u

def nonzeroLimitOrdinalFormula {n} (T : Fin n) : BoundedFormula n :=
  .conj (.neg (emptyFormula T)) (.allMem T (exMem T.succ (.mem 1 0)))

end BoundedFormula

open SetFormula
universe u

namespace BoundedFormula
def mainPrefixFieldExtensionFormula {n} (T S E T' S' E' : Fin n) : BoundedFormula n :=
  .conj (subsetFormula T T') (.conj (subsetFormula S S') (subsetFormula E E'))

end BoundedFormula

namespace BoundedFormula
def mainPrefixSelectedStepBody {n} (f old next : Fin n) (v : Fin 10 → Fin n) : BoundedFormula n :=
  .conj (successorFormula (v 8) (v 0))
  (.conj (successorFormula (v 9) (v 8))
  (.conj (mainPrefixTupleFormula old (v 8) (v 1) (v 2))
  (.conj (mainPrefixTupleFormula next (v 9) (v 3) (v 4))
  (.conj (mainPrefixFieldExtensionFormula (v 8) (v 1) (v 2) (v 9) (v 3) (v 4))
  (.conj (pairMembershipFormula (v 0) (v 5) (v 1))
  (.conj (rightTripleMembershipFormula (v 5) (v 6) (v 7) f)
  (.conj (pairMembershipFormula (v 8) (v 6) (v 3))
    (tripleMembershipFormula (v 8) (v 0) (v 7) (v 4)))))))))

end BoundedFormula

end PartitionPilot.Forcing

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

namespace BoundedFormula

def rowAssignmentOrderFormula {n} (z C B r : Fin n) : BoundedFormula n :=
  let lift (i : Fin n) := i.succ.succ.succ.succ
  exMem C (exMem B.succ (exMem C.succ.succ (exMem B.succ.succ.succ
    (.conj (pairOfPairsFormula (lift z) 3 2 1 0)
      (.conj (pairMembershipFormula 3 1 (lift r)) (subsetFormula 0 2))))))

theorem truth_rowAssignmentOrderFormula {n} (z C B r : Fin n) (env : Fin n → ZFSet.{u}) :
    Truth (rowAssignmentOrderFormula z C B r) env ↔
      ∃ q ∈ env C, ∃ A ∈ env B, ∃ p ∈ env C, ∃ D ∈ env B,
        env z = ZFSet.pair (ZFSet.pair q A) (ZFSet.pair p D) ∧
          ZFSet.pair q p ∈ env r ∧ D ⊆ A := by
  simp only [rowAssignmentOrderFormula, truth_exMem, Truth,
    truth_pairOfPairsFormula, truth_pairMembershipFormula, truth_subsetFormula]
  rfl

end BoundedFormula

end PartitionPilot.Forcing

end

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Geometry_GroundVisibilitySupportIncidence
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section



namespace PartitionPilot.Forcing.BoundedFormula
open SetFormula
universe u

def visibilitySupportAt {n} (node tau nodes names visibility top : Fin n) : BoundedFormula n :=
  .conj (.mem node nodes) (.conj (.mem tau names)
    (exGraphFields visibility (.conj (.equal 1 node.succ.succ)
      (pairMembershipFormula tau.succ.succ top.succ.succ 0))))

end PartitionPilot.Forcing.BoundedFormula

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
open SetFormula
universe u
namespace BoundedFormula

noncomputable def refinementDataHistoryFieldFormula {n : Nat}
    (stages history z : Fin n) (j : Fin 15) : BoundedFormula n :=
  exPairFields z (.conj (.mem 1 stages.succ.succ)
    (exGraphFields history.succ.succ
      (.conj (.equal 1 3) (tupleFieldFormula 14 0 2 j))))

theorem truth_refinementDataHistoryFieldFormula {n : Nat}
    (stages history z : Fin n) (j : Fin 15) (env : Fin n → ZFSet.{u}) :
    Truth (refinementDataHistoryFieldFormula stages history z j) env ↔
      ∃ alpha ∈ env stages, ∃ d : Fin 15 → ZFSet.{u},
        ZFSet.pair alpha (refinementFormulaDataCode d) ∈ env history ∧
          env z = ZFSet.pair alpha (d j) := by
  simp only [refinementDataHistoryFieldFormula, truth_exPairFields, Truth,
    truth_exGraphFields, truth_tupleFieldFormula]
  change (∃ alpha y, env z = ZFSet.pair alpha y ∧ alpha ∈ env stages ∧
    ∃ key data, ZFSet.pair key data ∈ env history ∧ key = alpha ∧
      ∃ d : Fin 15 → ZFSet.{u}, data = refinementFormulaDataCode d ∧ y = d j) ↔ _
  constructor
  · rintro ⟨alpha, y, pair, halpha, key, data, entry, rfl, d, rfl, rfl⟩
    exact ⟨key, halpha, d, entry, pair⟩
  · rintro ⟨alpha, halpha, d, entry, equal⟩
    exact ⟨alpha, d j, equal, halpha, alpha, refinementFormulaDataCode d, entry, rfl, d, rfl, rfl⟩

end BoundedFormula

end PartitionPilot.Forcing



namespace PartitionPilot.Forcing
universe u

noncomputable def refinementDataHistoryIndices (stages history : ZFSet.{u}) : ZFSet.{u} :=
  refinementHistoryIndices stages (refinementDataHistoryField stages history 0)

end PartitionPilot.Forcing



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

theorem mem_refinementDataHistoryIndices (stages history x : ZFSet.{u}) :
    x ∈ refinementDataHistoryIndices stages history ↔
      ∃ alpha ∈ stages, ∃ d : Fin 15 → ZFSet.{u},
        ZFSet.pair alpha (refinementFormulaDataCode d) ∈ history ∧ x ∈ d 0 := by
  rw [refinementDataHistoryIndices, mem_refinementHistoryIndices]
  constructor
  · rintro ⟨alpha, halpha, I, entry, member⟩
    obtain ⟨_, d, stored, rfl⟩ := (pair_mem_refinementDataHistoryField _ _ _ _ _).1 entry
    exact ⟨alpha, halpha, d, stored, member⟩
  · rintro ⟨alpha, halpha, d, entry, member⟩
    exact ⟨alpha, halpha, d 0,
      (pair_mem_refinementDataHistoryField _ _ _ _ _).2 ⟨halpha, d, entry, rfl⟩, member⟩

namespace BoundedFormula
noncomputable def refinementDataHistoryIndicesEntryFormula {n : Nat}
    (stages history x : Fin n) : BoundedFormula n :=
  exGraphFields history (.conj (.mem 1 stages.succ.succ)
    (exPairFields 0 (.conj (tupleShapeFormula 13 0) (.mem x.succ.succ.succ.succ 1))))

theorem truth_refinementDataHistoryIndicesEntryFormula {n : Nat}
    (stages history x : Fin n) (env : Fin n → ZFSet.{u}) :
    Truth (refinementDataHistoryIndicesEntryFormula stages history x) env ↔
      env x ∈ refinementDataHistoryIndices (env stages) (env history) := by
  rw [mem_refinementDataHistoryIndices]
  simp only [refinementDataHistoryIndicesEntryFormula, truth_exGraphFields, Truth,
    truth_exPairFields, truth_tupleShapeFormula]
  change (∃ alpha data, ZFSet.pair alpha data ∈ env history ∧ alpha ∈ env stages ∧
    ∃ I tail, data = ZFSet.pair I tail ∧ (∃ fields : Fin 14 → ZFSet.{u},
      tail = nonemptyTupleCode 13 fields) ∧ env x ∈ I) ↔ _
  constructor
  · rintro ⟨alpha, data, entry, halpha, I, tail, pair, ⟨fields, tuple⟩, member⟩
    let d : Fin 15 → ZFSet.{u} := Fin.cases I fields
    refine ⟨alpha, halpha, d, ?_, member⟩
    have equal : data = refinementFormulaDataCode d := pair.trans (congrArg (ZFSet.pair I) tuple)
    exact equal ▸ entry
  · rintro ⟨alpha, halpha, d, entry, member⟩
    exact ⟨alpha, refinementFormulaDataCode d, entry, halpha, d 0,
      nonemptyTupleCode 13 (fun i => d i.succ), rfl,
      ⟨fun i => d i.succ, rfl⟩, member⟩

noncomputable def refinementDataHistoryLevelsEntryFormula {n : Nat}
    (stages history T z : Fin n) : BoundedFormula n :=
  let lift (i : Fin n) := i.succ.succ.succ.succ.succ.succ
  exPairFields z (exPairFields 1 (exPairFields 0
    (.conj (refinementDataHistoryIndicesEntryFormula (lift stages) (lift history) 3)
      (.conj (.mem 1 (lift T)) (.conj (.mem 0 (lift T))
        (.conj (.mem 4 (lift stages)) (tupleFieldFormula 5 3 4 0)))))))

end BoundedFormula

end PartitionPilot.Forcing

end

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Geometry_GroundFairPreparationMonotonicity
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace PartitionPilot.Forcing
universe u

namespace BoundedFormula
open SetFormula

def exFairStateFields {n} (state : Fin n) (body : BoundedFormula (n + 4)) : BoundedFormula n :=
  exPairFields state (exPairFields 0 (exPairFields 0
    (reindex (Fin.cases 0 (Fin.cases 1 (Fin.cases 3 (Fin.cases 5
      (fun j => j.succ.succ.succ.succ.succ.succ))))) body)))

def fairPreparationStateFormula {n} (omega E0 enumSelector state : Fin n) : BoundedFormula n :=
  let old := fun j : Fin n => j.succ.succ.succ.succ
  exFairStateFields state (.conj (.mem 3 (old omega))
    (exMem (old omega) (.conj (successorFormula 0 4)
      (.conj (functionFormula 0 (old E0).succ 2)
        (exMem (old E0).succ (.conj
          (pairMembershipFormula 4 0 (old enumSelector).succ.succ)
          (pairMembershipFormula 5 0 3)))))))

end BoundedFormula






namespace BoundedFormula
open SetFormula

def insertPairFormula {n} (output graph x y : Fin n) : BoundedFormula n :=
  .conj (.allMem output (disj (.mem 0 graph.succ) (orderedPairFormula 0 x.succ y.succ)))
    (.conj (subsetFormula graph output) (pairMembershipFormula x y output))

def activePreparationFormula {n}
    (stages U e j p q event prepSelector : Fin n) : BoundedFormula n :=
  let old := fun i : Fin n => i.succ.succ.succ.succ
  exMem stages (exMem U.succ (exPairFields 0
    (.conj (.equal 1 (old q))
      (.conj (pairMembershipFormula (old j) 3 (old e))
        (.conj (tripleMembershipFormula 3 (old p) 2 (old prepSelector))
          (orderedPairFormula (old event) 3 2))))))

def fairStepFieldsFormula {arity}
    (omega E0 stages U enumSelector prepSelector gridGraph n p births m q nextBirths event : Fin arity) :
    BoundedFormula arity :=
  let old := fun i : Fin arity => i.succ.succ.succ.succ
  .conj (successorFormula m n)
    (exMem omega (exMem omega.succ (exMem E0.succ.succ (exMem E0.succ.succ.succ
      (.conj (rightTripleMembershipFormula (old n) 3 2 (old gridGraph))
        (.conj (pairMembershipFormula 3 1 (old births))
          (.conj (pairMembershipFormula (old q) 0 (old enumSelector))
            (.conj (insertPairFormula (old nextBirths) (old births) (old m) 0)
              (disj (.conj (emptyFormula 1) (.conj (.equal (old q) (old p)) (emptyFormula (old event))))
                (activePreparationFormula (old stages) (old U) 1 2 (old p) (old q)
                  (old event) (old prepSelector)))))))))))

def fairPreparationStepFormula {n}
    (omega E0 stages U enumSelector prepSelector gridGraph state next : Fin n) : BoundedFormula n :=
  let old := fun i : Fin n => i.succ.succ.succ.succ.succ.succ.succ.succ
  exFairStateFields state (exFairStateFields next.succ.succ.succ.succ
    (fairStepFieldsFormula (old omega) (old E0) (old stages) (old U) (old enumSelector)
      (old prepSelector) (old gridGraph) 7 6 5 3 2 1 0))

end BoundedFormula

end PartitionPilot.Forcing




end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Forcing_GroundStoredPreparedFamilyActions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace PartitionPilot.Forcing
open SetFormula
universe u

namespace BoundedFormula

def preparationEventSupportFormula {n} (v event : Fin n) : BoundedFormula n :=
  exPairFields event (exPairFields 0 (exPairFields 0
    (certificateBasisMemberFormula v.succ.succ.succ.succ.succ.succ 1)))

end BoundedFormula






end PartitionPilot.Forcing



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

namespace PartitionPilot.Forcing.BoundedFormula
open SetFormula

def separationWitnessBody : BoundedFormula 12 :=
  .conj (.mem 1 6) (.conj (tripleMembershipFormula 1 3 0 10)
    (.conj (pairMembershipFormula 2 0 11)
      (.conj (pairMembershipFormula 1 4 7) (pairMembershipFormula 1 5 7))))

def separationWitnessFormula : BoundedFormula 10 :=
  exMem 7 (exMem 7 separationWitnessBody)

end PartitionPilot.Forcing.BoundedFormula

end


end OAI
end


