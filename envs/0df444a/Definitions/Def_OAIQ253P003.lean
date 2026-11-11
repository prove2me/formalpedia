-- Prove2me | Definitions.Def_OAIQ253P003
-- name    : OAIQ253P003
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-11T05:47:17.537193+00:00
-- url     : https://prove2.me/theorems/d4688111-2dd4-4243-af6b-cdc6f761b29d
-- title:
--   Definitions bundle OAIQ253P003 of the split of OpenAI, The Partition Principle does not imply Choice
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.PartitionPilot.Forcing.TransitiveGround.exists_model_partitionPrinciple_without_choice`, carved from OpenAI's openai/math development (OpenAI, *The Partition Principle does not imply Choice*, OpenAI Math Release, September 24, 2026, result family 244, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 724 declarations of OpenAI's Lean: 296 definitions, 19 inductive types or structures, 5 instances and 404 theorems. The definitions and types are `OAI.PartitionPilot.Forcing.BoundedFormula.coveringPositionFormula`, `OAI.PartitionPilot.Forcing.GroundChronologicalHistory`, `OAI.PartitionPilot.Forcing.GroundChronologyFields`, `OAI.PartitionPilot.Forcing.GroundChronologyFields.code`, `OAI.PartitionPilot.Forcing.GroundChronologyFields.codeFields`, `OAI.PartitionPilot.Forcing.GroundChronologyFields.layerRelationParams`, `OAI.PartitionPilot.Forcing.GroundChronologyFields.ofGraphs`, `OAI.PartitionPilot.Forcing.GroundCumulativeHierarchyCode`, `OAI.PartitionPilot.Forcing.GroundDefinableFunction.congr`, `OAI.PartitionPilot.Forcing.GroundDefinableFunction.graph`, `OAI.PartitionPilot.Forcing.GroundMainFinalGeometry`, `OAI.PartitionPilot.Forcing.GroundMainFinalGeometry.code`, `OAI.PartitionPilot.Forcing.GroundMainFinalGeometry.decodedBottom`, `OAI.PartitionPilot.Forcing.GroundMainFinalGeometry.fields`, `OAI.PartitionPilot.Forcing.GroundMainStage.code`, `OAI.PartitionPilot.Forcing.GroundMainStage.field`, `OAI.PartitionPilot.Forcing.GroundMainTransition`, `OAI.PartitionPilot.Forcing.GroundMainTransition.code`, `OAI.PartitionPilot.Forcing.GroundOrdinalStepClosure`, `OAI.PartitionPilot.Forcing.GroundSequenceReflection`, `OAI.PartitionPilot.Forcing.GroundSetTerm`, `OAI.PartitionPilot.Forcing.GroundSetTerm.var`, `OAI.PartitionPilot.Forcing.HereditarilySymmetric`, `OAI.PartitionPilot.Forcing.IdealEmbeddingCode`, `OAI.PartitionPilot.Forcing.InitialMainAlgebra.actors`, `OAI.PartitionPilot.Forcing.InitialMainAlgebra.carrier`, `OAI.PartitionPilot.Forcing.InitialMainAlgebra.top`, `OAI.PartitionPilot.Forcing.InternallyCountablyClosed`, `OAI.PartitionPilot.Forcing.IntervalEmbeddingFamilyInputs`, `OAI.PartitionPilot.Forcing.IsName`, `OAI.PartitionPilot.Forcing.LinkedCoverageFieldsCode`, `OAI.PartitionPilot.Forcing.LinkedTransitionLawsCode`, `OAI.PartitionPilot.Forcing.MainLimitConeEntryCode`, `OAI.PartitionPilot.Forcing.MainLimitCoverageGraphCode`, `OAI.PartitionPilot.Forcing.MainLimitOldActorImageCode`, `OAI.PartitionPilot.Forcing.MainLimitOldCutoffCode`, `OAI.PartitionPilot.Forcing.MainLimitOldPointImageCode`, `OAI.PartitionPilot.Forcing.MainPrefixAtIndex`, `OAI.PartitionPilot.Forcing.MainPrefixExtends`, `OAI.PartitionPilot.Forcing.MainPrefixHistoryExtends` and 275 more.
--
--   **Sources.** They come from these modules of lean/OAI/SetTheory, in whole or in part: `PartitionPrinciple_Definability_BatchGraphSetFormulas`, `PartitionPrinciple_Definability_BoundedAtomicEquality`, `PartitionPrinciple_Definability_CodedEqualityRelations`, `PartitionPrinciple_Definability_CompressionExternalStepRealization`, `PartitionPrinciple_Definability_CountableSetFormulas`, `PartitionPrinciple_Definability_DecodedFunctionGraphs`, `PartitionPrinciple_Definability_DepthSlotCodes`, `PartitionPrinciple_Definability_EqualityStepSyntax`, `PartitionPrinciple_Definability_ExternalSlotCopyGraphs`, `PartitionPrinciple_Definability_FiniteWordMapCodes`, `PartitionPrinciple_Definability_FixedTopCodes`, `PartitionPrinciple_Definability_FlatCopyGraphRealization`, `PartitionPrinciple_Definability_ForcingHistoryOutputFormulas`, `PartitionPrinciple_Definability_FormulaSymmetry`, `PartitionPrinciple_Definability_GroundBinaryRowSets`, `PartitionPrinciple_Definability_GroundCompositionFamilyFormulas`, `PartitionPrinciple_Definability_GroundDefinableRelationProducts`, `PartitionPrinciple_Definability_GroundFlatCopyGraphs`, `PartitionPrinciple_Definability_GroundFlatCopyPresentation`, `PartitionPrinciple_Definability_GroundFunctionRangeFamilies`, `PartitionPrinciple_Definability_GroundLiftedRowTupleProvenance`, `PartitionPrinciple_Definability_GroundMainTransitionCodes`, `PartitionPrinciple_Definability_GroundNiceVisibilityGraphs`, `PartitionPrinciple_Definability_GroundPairCompositions`, `PartitionPrinciple_Definability_GroundPartialFunctionSpaces`, `PartitionPrinciple_Definability_GroundPrincipalNiceSupportCodes`, `PartitionPrinciple_Definability_GroundPushFilterFamilyFormulas`, `PartitionPrinciple_Definability_GroundRefinementPairClassGraphs`, `PartitionPrinciple_Definability_GroundSelectedSupportTupleFamilies`, `PartitionPrinciple_Definability_GroundSeparatorFamilyFormulas`, `PartitionPrinciple_Definability_GroundStrongLimitFormulas`, `PartitionPrinciple_Definability_GroundVaryingPreparationRelations`, `PartitionPrinciple_Definability_HistoryFieldFormulas`, `PartitionPrinciple_Definability_IndexedMixedOperationLiftCodes`, `PartitionPrinciple_Definability_IndexedOperationLiftCodes`, `PartitionPrinciple_Definability_IndexedValueLiftCodes`, `PartitionPrinciple_Definability_InitialMainAlgebraCodes`, `PartitionPrinciple_Definability_LeastSlotOwnerCodes`, `PartitionPrinciple_Definability_LinkedMainTransitionRawCodes`, `PartitionPrinciple_Definability_MainTransitionValidityCodes`, `PartitionPrinciple_Definability_NatUnionCodes`, `PartitionPrinciple_Definability_NaturalSetCodes`, `PartitionPrinciple_Definability_NaturalStepFormulas`, `PartitionPrinciple_Definability_NonemptyTupleFields`, `PartitionPrinciple_Definability_OrbitImageFormulas`, `PartitionPrinciple_Definability_PresentedGroupCodes`, `PartitionPrinciple_Definability_PresentedRowAssignmentGraphs`, `PartitionPrinciple_Definability_RationalCodeLaws`, `PartitionPrinciple_Definability_RawCheckFormulas`, `PartitionPrinciple_Definability_RawRenameFormulas`, `PartitionPrinciple_Definability_RecursivePrimitiveFormulas`, `PartitionPrinciple_Definability_RowAssignmentTransitionFormulas`, `PartitionPrinciple_Definability_SerializedChronologyFormulas`, `PartitionPrinciple_Definability_SmallFunctionActionFormulas`, `PartitionPrinciple_Definability_StructuralAssignmentActionFormulas`, `PartitionPrinciple_Definability_TaggedExtensionCodes`, `PartitionPrinciple_Definability_TaggedSumPresentations`, `PartitionPrinciple_Definability_TaskCapFamilyCodes`, `PartitionPrinciple_Definability_TupleRelationProducts`, `PartitionPrinciple_Definability_UnionEntryFormula`, `PartitionPrinciple_Definability_VisibilityProfileFormulas`, `PartitionPrinciple_Forcing_ActionPostcompositionCodes`, `PartitionPrinciple_Forcing_ActiveNameImageSymmetry`, `PartitionPrinciple_Forcing_AllSupportFamilies`, `PartitionPrinciple_Forcing_AtomicTruth`, `PartitionPrinciple_Forcing_ConditionQuantifiers`, `PartitionPrinciple_Forcing_EvaluatedDomains`, `PartitionPrinciple_Forcing_FinitePrincipalNameSupports`, `PartitionPrinciple_Forcing_GeneratedMeetFilters`, `PartitionPrinciple_Forcing_GroundBinaryRowNames`, `PartitionPrinciple_Forcing_GroundCompleteProjectionGenericity`, `PartitionPrinciple_Forcing_GroundDefinableRefinementNameGraphs`, `PartitionPrinciple_Forcing_GroundFixedPoints`, `PartitionPrinciple_Forcing_GroundFixedTopStep`, `PartitionPrinciple_Forcing_GroundFlatSuccessorFullActionGraph`, `PartitionPrinciple_Forcing_GroundGraphValueDescendantWitnesses`, `PartitionPrinciple_Forcing_GroundIdealProjections`, `PartitionPrinciple_Forcing_GroundIndexedGraphNameFamilies`, `PartitionPrinciple_Forcing_GroundMainFinalStructuralCommonSupportInduction`, `PartitionPrinciple_Forcing_GroundMixtureNames`, `PartitionPrinciple_Forcing_GroundNameSequenceForcingWitness`, `PartitionPrinciple_Forcing_GroundNameSequenceValues`, `PartitionPrinciple_Forcing_GroundNiceNameGraphs`, `PartitionPrinciple_Forcing_GroundNiceNameNormalization`, `PartitionPrinciple_Forcing_GroundPairNameFamilies`, `PartitionPrinciple_Forcing_GroundPreparationForcing`, `PartitionPrinciple_Forcing_GroundProductActions`, `PartitionPrinciple_Forcing_GroundProjectedRowChooserWitnesses`, `PartitionPrinciple_Forcing_GroundRawRefinementStageWitnesses`, `PartitionPrinciple_Forcing_GroundRawRowAssignmentActions`, `PartitionPrinciple_Forcing_GroundRecursiveActions`, `PartitionPrinciple_Forcing_GroundRefinementAssignmentActionFamilies`, `PartitionPrinciple_Forcing_GroundRowAssignmentActions`, `PartitionPrinciple_Forcing_GroundRowGenerics`, `PartitionPrinciple_Forcing_GroundSmallFunctionPermutations`, `PartitionPrinciple_Forcing_GroundStructuralForcingHistoryConstruction`, `PartitionPrinciple_Forcing_GroundTestedMeetFilters`, `PartitionPrinciple_Forcing_IndexedTupleNames`, `PartitionPrinciple_Forcing_MeetOrderPosetActions`, `PartitionPrinciple_Forcing_NameFamilySetTransport`, `PartitionPrinciple_Forcing_NameMixingRanks`, `PartitionPrinciple_Forcing_NameOrbitBounds`, `PartitionPrinciple_Forcing_NamePresentationEquivalences`, `PartitionPrinciple_Forcing_NameRenameSteps`, `PartitionPrinciple_Forcing_OrbitPairGraphNames`, `PartitionPrinciple_Forcing_PairFamilyEvaluation`, `PartitionPrinciple_Forcing_PresentedMeetActionCodes`, `PartitionPrinciple_Forcing_RefinementAssignmentLabelNames`, `PartitionPrinciple_Forcing_RefinementCoarseImageNames`, `PartitionPrinciple_Forcing_RelationActionFamilies`, `PartitionPrinciple_Forcing_RenamedPairNameFamilies`, `PartitionPrinciple_Forcing_UniformGroundNames`, `PartitionPrinciple_Geometry_AtomicEqualitySteps`, `PartitionPrinciple_Geometry_AtomicSoundness`, `PartitionPrinciple_Geometry_CheckCertificates`, `PartitionPrinciple_Geometry_Compression`, `PartitionPrinciple_Geometry_DecodedGroundGroups`, `PartitionPrinciple_Geometry_FiniteIterationTraces`, `PartitionPrinciple_Geometry_FiniteWordOperations`, `PartitionPrinciple_Geometry_GroundAssignmentIndexLevels`, `PartitionPrinciple_Geometry_GroundBatchEmbeddingRecognition`, `PartitionPrinciple_Geometry_GroundBinaryRows`, `PartitionPrinciple_Geometry_GroundCantorDiagonal`, `PartitionPrinciple_Geometry_GroundCompressionHeightSteps`, `PartitionPrinciple_Geometry_GroundCompressionStampBounds`, `PartitionPrinciple_Geometry_GroundCompressionStarIncidence`, `PartitionPrinciple_Geometry_GroundCumulativeHierarchyLevels`, `PartitionPrinciple_Geometry_GroundDefinableIndexBounds`, `PartitionPrinciple_Geometry_GroundDefinableRowAssignmentOrders`, `PartitionPrinciple_Geometry_GroundExternalGenerators`, `PartitionPrinciple_Geometry_GroundExternalGroupEmbeddings`, `PartitionPrinciple_Geometry_GroundExternalTileSlotSupports`, `PartitionPrinciple_Geometry_GroundFamilyValueUnions`, `PartitionPrinciple_Geometry_GroundFiniteWordLaws`, `PartitionPrinciple_Geometry_GroundFiniteWordLength`, `PartitionPrinciple_Geometry_GroundFixedTopOrders`, `PartitionPrinciple_Geometry_GroundGrowthLayerRecognition`, `PartitionPrinciple_Geometry_GroundHeightPushforward`, `PartitionPrinciple_Geometry_GroundIndexedClassInclusions`, `PartitionPrinciple_Geometry_GroundInitialCompressionOrigin`, `PartitionPrinciple_Geometry_GroundLiteralTaskFieldRecognition`, `PartitionPrinciple_Geometry_GroundMainFinalSeparatedActors`, `PartitionPrinciple_Geometry_GroundMainTransitionLaws`, `PartitionPrinciple_Geometry_GroundMixtureDensityRecovery`, `PartitionPrinciple_Geometry_GroundMixtureTermBounds`, `PartitionPrinciple_Geometry_GroundNaturalFamilyShift`, `PartitionPrinciple_Geometry_GroundNiceRefinementVisibility`, `PartitionPrinciple_Geometry_GroundNormalizedRefinementOutputs`, `PartitionPrinciple_Geometry_GroundOrdinarySubmodelReflection`, `PartitionPrinciple_Geometry_GroundRowAssignmentCuts`, `PartitionPrinciple_Geometry_GroundRowDistinguishing`, `PartitionPrinciple_Geometry_GroundTaskRepresentativeRecognition`, `PartitionPrinciple_Geometry_GroundTileStarIncidence`, `PartitionPrinciple_Geometry_GroundTwoPointHeights`, `PartitionPrinciple_Geometry_IntervalEmbeddingFamilyCodes`, `PartitionPrinciple_Geometry_PresentedRowAssignmentTotality`, `PartitionPrinciple_Geometry_RawEqualitySteps`, `PartitionPrinciple_Geometry_RectangleFulfillmentAtBound`, `PartitionPrinciple_Geometry_RepresentativeIndexSteps`, `PartitionPrinciple_Geometry_RowAssignmentOrderLaws`, `PartitionPrinciple_Geometry_RowCopyRefinements`, `PartitionPrinciple_Geometry_RowPositionBounds`, `PartitionPrinciple_Geometry_TaggedGrowthLayerRanks`, `PartitionPrinciple_Geometry_TemplateHeightRangeCodes`, `PartitionPrinciple_Geometry_UniformAtomicEquality`, `PartitionPrinciple_Models_GroundCountableQuotients`, `PartitionPrinciple_Models_GroundOrdinalPartitionInjectionAssembly`, `PartitionPrinciple_Models_GroundQuotientBinaryOperations`, `PartitionPrinciple_Models_GroundRefinementQuotientNames`, `PartitionPrinciple_Models_LiteralQuotientRankBounds`, `PartitionPrinciple_Transfinite_CodedMainPrefixSystems`, `PartitionPrinciple_Transfinite_ExternalChronologyStageLaws`, `PartitionPrinciple_Transfinite_FiniteFlatHistoryCoherence`, `PartitionPrinciple_Transfinite_GroundBatchBirths`, `PartitionPrinciple_Transfinite_GroundChronologicalBasis`, `PartitionPrinciple_Transfinite_GroundChronologyFieldAppend`, `PartitionPrinciple_Transfinite_GroundChronologyLayerRelation`, `PartitionPrinciple_Transfinite_GroundCoinitialOperations`, `PartitionPrinciple_Transfinite_GroundCompressionBirths`, `PartitionPrinciple_Transfinite_GroundCompressionPrefixGraphs`, `PartitionPrinciple_Transfinite_GroundCountableFunctionClosure`, `PartitionPrinciple_Transfinite_GroundCountableRelationSelections`, `PartitionPrinciple_Transfinite_GroundInitialCompressionHistory`, `PartitionPrinciple_Transfinite_GroundIntervalRecursion`, `PartitionPrinciple_Transfinite_GroundLinkedMainStageCodeLaws`, `PartitionPrinciple_Transfinite_GroundMainPrefixDecoding`, `PartitionPrinciple_Transfinite_GroundMainPrefixLimitCoverageGraph`, `PartitionPrinciple_Transfinite_GroundMainPrefixSelectedStepTotality`, `PartitionPrinciple_Transfinite_GroundMainStageCandidates`, `PartitionPrinciple_Transfinite_GroundMainStageFromCodes`, `PartitionPrinciple_Transfinite_GroundSerializedChronologyTimeEquality`, `PartitionPrinciple_Transfinite_MainPrefixHistoryUnionRecognition`, `PartitionPrinciple_Transfinite_NonzeroLimitOrdinalCodes`, `PartitionPrinciple_Transfinite_OrdinalRecursionTraces`, `PartitionPrinciple_Transfinite_OwnerBirthLayers`, `PartitionPrinciple_Transfinite_RecursiveStateFieldEnvironments`, `PartitionPrinciple_Transfinite_StageOneDataBoundLaws`.
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
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Definability_TaggedExtensionCodes
attribute [-instance] _root_.OAI.PartitionPilot.Forcing.GroundMainPrefix.withTopSmall
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PartitionPilot.Forcing

universe u

theorem taggedExtension_disjoint (P N : ZFSet.{u}) :
    ∀ z ∈ P, z ∉ ZFSet.prod {P} N := by
  intro z hz tagged
  obtain ⟨p, hp, q, _, eq⟩ := ZFSet.mem_prod.1 tagged
  have same : z = ZFSet.pair P q := (ZFSet.mem_singleton.1 hp) ▸ eq
  exact pair_tag_not_mem P q (same ▸ hz)

end PartitionPilot.Forcing

end

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Forcing_EvaluatedDomains
attribute [-instance] _root_.OAI.PartitionPilot.Forcing.GroundMainPrefix.withTopSmall
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace PartitionPilot.Forcing

section

open SetRealization
universe u v
variable {P : Type u}

inductive IsName (s : Presentation P) : ZFSet.{u} → Prop
  | mk {x} : (∀ z ∈ x, ∃ y p, z = ZFSet.pair y (s.encode p)) →
      (∀ y p, ZFSet.pair y (s.encode p) ∈ x → IsName s y) → IsName s x

def Name (s : Presentation P) := {x : ZFSet.{u} // IsName s x}

namespace Name
variable {s : Presentation P}

def Entry (σ τ : Name s) (p : P) : Prop :=
  ZFSet.pair σ.val (s.encode p) ∈ τ.val

theorem entries_cover (τ : Name s) {z : ZFSet.{u}} (hz : z ∈ τ.val) :
    ∃ σ : Name s, ∃ p, z = ZFSet.pair σ.val (s.encode p) := by
  obtain ⟨x, hx⟩ := τ
  cases hx with
  | mk h children =>
    obtain ⟨y, p, eq⟩ := h z hz
    exact ⟨⟨y, children y p (eq ▸ hz)⟩, p, eq⟩

theorem ext {τ ν : Name s} (h : ∀ σ p, Entry σ τ p ↔ Entry σ ν p) : τ = ν := by
  apply Subtype.ext
  apply ZFSet.ext
  intro z
  constructor
  · intro hz
    obtain ⟨σ, p, rfl⟩ := entries_cover τ hz
    exact (h σ p).1 hz
  · intro hz
    obtain ⟨σ, p, rfl⟩ := entries_cover ν hz
    exact (h σ p).2 hz

theorem entry_rank_lt {σ τ : Name s} {p : P} (h : Entry σ τ p) :
    ZFSet.rank σ.val < ZFSet.rank τ.val := by
  have h₁ : σ.val ∈ ({σ.val} : ZFSet) := ZFSet.mem_singleton.2 rfl
  have h₂ : ({σ.val} : ZFSet) ∈ ZFSet.pair σ.val (s.encode p) := by
    exact ZFSet.mem_pair.2 (Or.inl rfl)
  exact (ZFSet.rank_lt_of_mem h₁).trans
    ((ZFSet.rank_lt_of_mem h₂).trans (ZFSet.rank_lt_of_mem h))

theorem inductionOn {motive : Name s → Prop} (τ : Name s)
    (step : ∀ ν, (∀ σ p, Entry σ ν p → motive σ) → motive ν) : motive τ := by
  apply (InvImage.wf (fun ν : Name s => ZFSet.rank ν.val) wellFounded_lt).induction τ
  intro ν ih
  exact step ν (fun σ p h => ih σ (entry_rank_lt h))

def Entries (τ : Name s) := {a : Name s × P // Entry a.1 τ a.2}

instance entries_small (τ : Name s) : Small.{u} (Entries τ) := by
  let f : Entries τ → τ.val :=
    fun a => ⟨ZFSet.pair a.val.1.val (s.encode a.val.2), a.property⟩
  apply small_of_injective (f := f)
  intro a b eq
  have parts := ZFSet.pair_inj.1 (congrArg Subtype.val eq)
  apply Subtype.ext
  exact Prod.ext (Subtype.ext parts.1) (s.injective parts.2)

noncomputable def assemble {α : Type v} [Small.{u} α]
    (names : α → Name s) (conditions : α → P) : Name s := by
  refine ⟨ZFSet.range (fun i => ZFSet.pair (names i).val (s.encode (conditions i))),
    IsName.mk ?_ ?_⟩
  · intro z hz
    obtain ⟨i, rfl⟩ := ZFSet.mem_range.1 hz
    exact ⟨(names i).val, conditions i, rfl⟩
  · intro y p hp
    obtain ⟨i, eq⟩ := ZFSet.mem_range.1 hp
    have eqy := (ZFSet.pair_inj.1 eq).1
    exact eqy ▸ (names i).property

theorem entry_assemble {α : Type v} [Small.{u} α]
    (names : α → Name s) (conditions : α → P) (σ : Name s) (p : P) :
    Entry σ (assemble names conditions) p ↔ ∃ i, names i = σ ∧ conditions i = p := by
  change ZFSet.pair σ.val (s.encode p) ∈ ZFSet.range _ ↔ _
  rw [ZFSet.mem_range]
  constructor
  · rintro ⟨i, eq⟩
    have parts := ZFSet.pair_inj.1 eq
    exact ⟨i, Subtype.ext parts.1, s.injective parts.2⟩
  · rintro ⟨i, rfl, rfl⟩
    exact ⟨i, rfl⟩

def empty (s : Presentation P) : Name s :=
  ⟨∅, IsName.mk (by intro z hz; exact False.elim (ZFSet.notMem_empty z hz))
    (by intro y p hp; exact False.elim (ZFSet.notMem_empty _ hp))⟩

end Name
end



namespace Name

open SetRealization
universe u v
variable {P : Type u} {s : Presentation P}

noncomputable def eval (H : Set P) (τ : Name s) : ZFSet.{u} :=
  ZFSet.range (fun a : {a : Entries τ // a.val.2 ∈ H} => eval H a.val.val.1)
termination_by ZFSet.rank τ.val
decreasing_by exact entry_rank_lt a.val.property

theorem mem_eval (H : Set P) (τ : Name s) (x : ZFSet.{u}) :
    x ∈ eval H τ ↔ ∃ σ p, Entry σ τ p ∧ p ∈ H ∧ eval H σ = x := by
  rw [eval, ZFSet.mem_range]
  constructor
  · rintro ⟨a, eq⟩
    exact ⟨a.val.val.1, a.val.val.2, a.val.property, a.property, eq⟩
  · rintro ⟨σ, p, h, hp, eq⟩
    exact ⟨⟨⟨(σ, p), h⟩, hp⟩, eq⟩

end Name



namespace Name

open SetRealization
universe u
variable {P : Type u} [Preorder P] {s : Presentation P}

noncomputable def ForcesEq (p : P) (σ τ : Name s) : Prop :=
  (∀ ρ r, Entry ρ σ r → ∀ q, q ≤ p → q ≤ r →
    ∃ t, t ≤ q ∧ ∃ ν k, Entry ν τ k ∧ t ≤ k ∧ ForcesEq t ρ ν) ∧
  (∀ ν k, Entry ν τ k → ∀ q, q ≤ p → q ≤ k →
    ∃ t, t ≤ q ∧ ∃ ρ r, ∃ _ : Entry ρ σ r, t ≤ r ∧ ForcesEq t ρ ν)
termination_by ZFSet.rank σ.val
decreasing_by all_goals exact entry_rank_lt ‹Entry _ σ _›

theorem forcesEq_mono {p q : P} {σ τ : Name s} (h : ForcesEq p σ τ) (qp : q ≤ p) :
    ForcesEq q σ τ := by
  rw [ForcesEq] at h ⊢
  exact ⟨fun ρ r hr t tq tr => h.1 ρ r hr t (tq.trans qp) tr,
    fun ν k hk t tq tk => h.2 ν k hk t (tq.trans qp) tk⟩

theorem forcesEq_symm {p : P} {σ τ : Name s} (h : ForcesEq p σ τ) : ForcesEq p τ σ := by
  induction σ using inductionOn generalizing p τ with
  | step σ ih =>
    rw [ForcesEq] at h ⊢
    constructor
    · intro ν k hk q qp qk
      obtain ⟨t, tq, ρ, r, hr, tr, eq⟩ := h.2 ν k hk q qp qk
      exact ⟨t, tq, ρ, r, hr, tr, ih ρ r hr eq⟩
    · intro ρ r hr q qp qr
      obtain ⟨t, tq, ν, k, hk, tk, eq⟩ := h.1 ρ r hr q qp qr
      exact ⟨t, tq, ν, k, hk, tk, ih ρ r hr eq⟩

theorem forcesEq_of_dense {p : P} {σ τ : Name s}
    (dense : DenseBelow p {q | ForcesEq q σ τ}) : ForcesEq p σ τ := by
  rw [ForcesEq]
  constructor
  · intro ρ r hr q qp qr
    obtain ⟨t, tq, ht⟩ := dense q qp
    change ForcesEq t σ τ at ht
    rw [ForcesEq] at ht
    obtain ⟨v, vt, ν, k, hk, vk, eq⟩ := ht.1 ρ r hr t le_rfl (tq.trans qr)
    exact ⟨v, vt.trans tq, ν, k, hk, vk, eq⟩
  · intro ν k hk q qp qk
    obtain ⟨t, tq, ht⟩ := dense q qp
    change ForcesEq t σ τ at ht
    rw [ForcesEq] at ht
    obtain ⟨v, vt, ρ, r, hr, vr, eq⟩ := ht.2 ν k hk t le_rfl (tq.trans qk)
    exact ⟨v, vt.trans tq, ρ, r, hr, vr, eq⟩

def MemWitness (σ τ : Name s) : Set P :=
  {p | ∃ ν r, Entry ν τ r ∧ p ≤ r ∧ ForcesEq p σ ν}

def ForcesMem (p : P) (σ τ : Name s) : Prop := DenseBelow p (MemWitness σ τ)

theorem forcesMem_mono {p q : P} {σ τ : Name s} (h : ForcesMem p σ τ) (qp : q ≤ p) :
    ForcesMem q σ τ := fun r rq => h r (rq.trans qp)

theorem forcesMem_of_witness {p : P} {σ τ : Name s} (h : p ∈ MemWitness σ τ) :
    ForcesMem p σ τ := by
  obtain ⟨ν, r, entry, pr, eq⟩ := h
  intro q qp
  exact ⟨q, le_rfl, ν, r, entry, qp.trans pr, forcesEq_mono eq qp⟩

theorem forcesMem_of_dense {p : P} {σ τ : Name s}
    (dense : DenseBelow p {q | ForcesMem q σ τ}) : ForcesMem p σ τ := by
  intro q qp
  obtain ⟨r, rq, hr⟩ := dense q qp
  obtain ⟨t, tr, ht⟩ := hr r le_rfl
  exact ⟨t, tr.trans rq, ht⟩

theorem forcesEq_left {p q r : P} {σ τ ρ : Name s}
    (eq : ForcesEq p σ τ) (entry : Entry ρ σ r) (qp : q ≤ p) (qr : q ≤ r) :
    ForcesMem q ρ τ := by
  rw [ForcesEq] at eq
  intro t tq
  exact eq.1 ρ r entry t (tq.trans qp) (tq.trans qr)

theorem forcesEq_right {p q r : P} {σ τ ρ : Name s}
    (eq : ForcesEq p σ τ) (entry : Entry ρ τ r) (qp : q ≤ p) (qr : q ≤ r) :
    ForcesMem q ρ σ := forcesEq_left (forcesEq_symm eq) entry qp qr

theorem forcesEq_iff (p : P) (σ τ : Name s) : ForcesEq p σ τ ↔
    (∀ ρ r, Entry ρ σ r → ∀ q, q ≤ p → q ≤ r → ForcesMem q ρ τ) ∧
    (∀ ν k, Entry ν τ k → ∀ q, q ≤ p → q ≤ k → ForcesMem q ν σ) := by
  constructor
  · intro eq
    exact ⟨fun _ _ entry _ qp qr => forcesEq_left eq entry qp qr,
      fun _ _ entry _ qp qr => forcesEq_right eq entry qp qr⟩
  · rintro ⟨left, right⟩
    rw [ForcesEq]
    constructor
    · intro ρ r hr q qp qr
      exact left ρ r hr q qp qr q le_rfl
    · intro ν k hk q qp qk
      obtain ⟨t, tq, ρ, r, hr, tr, eq⟩ := right ν k hk q qp qk q le_rfl
      exact ⟨t, tq, ρ, r, hr, tr, forcesEq_symm eq⟩

end Name



namespace Name

open SetRealization
universe u
variable {P : Type u} {s : Presentation P}

noncomputable def check (s : Presentation P) (one : P) (x : ZFSet.{u}) : Name s :=
  assemble (fun y : x => check s one y.val) (fun _ => one)
termination_by ZFSet.rank x
decreasing_by exact ZFSet.rank_lt_of_mem y.property

theorem entry_check (one : P) (x : ZFSet.{u}) (σ : Name s) (p : P) :
    Entry σ (check s one x) p ↔ ∃ y ∈ x, check s one y = σ ∧ one = p := by
  rw [check, entry_assemble]
  constructor
  · rintro ⟨y, eq, hp⟩
    exact ⟨y.val, y.property, eq, hp⟩
  · rintro ⟨y, hy, eq, hp⟩
    exact ⟨⟨y, hy⟩, eq, hp⟩

noncomputable def singleton (one : P) (σ : Name s) : Name s :=
  assemble (fun _ : Unit => σ) (fun _ => one)

noncomputable def unorderedPair (one : P) (σ τ : Name s) : Name s :=
  assemble (fun b : Bool => if b then σ else τ) (fun _ => one)

noncomputable def orderedPair (one : P) (σ τ : Name s) : Name s :=
  unorderedPair one (singleton one σ) (unorderedPair one σ τ)

end Name



namespace Name

open SetRealization
universe u
variable {P : Type u} [Preorder P] {s : Presentation P}

structure NameDomain (s : Presentation P) where
  names : Set (Name s)
  children : ∀ {σ τ : Name s} {p : P}, τ ∈ names → Entry σ τ p → σ ∈ names

def ForcesNotMem (p : P) (σ τ : Name s) : Prop :=
  ∀ q, q ≤ p → ¬ ForcesMem q σ τ

theorem not_forcesMem_refine {p : P} {σ τ : Name s} (bad : ¬ ForcesMem p σ τ) :
    ∃ q, q ≤ p ∧ ForcesNotMem q σ τ := by
  classical
  change ¬ ∀ q, q ≤ p → ∃ r, r ≤ q ∧ r ∈ MemWitness σ τ at bad
  push Not at bad
  obtain ⟨q, qp, hq⟩ := bad
  refine ⟨q, qp, ?_⟩
  intro r rq hr
  obtain ⟨t, tr, ht⟩ := hr r le_rfl
  exact hq t (tr.trans rq) ht

def EqDecisionWitness (σ τ : Name s) : Set P :=
  {p | ForcesEq p σ τ ∨
    (∃ ρ r, Entry ρ σ r ∧ p ≤ r ∧ ForcesNotMem p ρ τ) ∨
    ∃ ν k, Entry ν τ k ∧ p ≤ k ∧ ForcesNotMem p ν σ}

theorem eqDecisionWitness_dense (σ τ : Name s) : Dense (EqDecisionWitness σ τ) := by
  classical
  intro p
  by_cases eq : ForcesEq p σ τ
  · exact ⟨p, le_rfl, Or.inl eq⟩
  · rw [forcesEq_iff] at eq
    obtain bad | bad := not_and_or.mp eq
    · push Not at bad
      obtain ⟨ρ, r, entry, q, qp, qr, nmem⟩ := bad
      obtain ⟨t, tq, neg⟩ := not_forcesMem_refine nmem
      exact ⟨t, tq.trans qp, Or.inr (Or.inl ⟨ρ, r, entry, tq.trans qr, neg⟩)⟩
    · push Not at bad
      obtain ⟨ν, k, entry, q, qp, qk, nmem⟩ := bad
      obtain ⟨t, tq, neg⟩ := not_forcesMem_refine nmem
      exact ⟨t, tq.trans qp, Or.inr (Or.inr ⟨ν, k, entry, tq.trans qk, neg⟩)⟩

def atomicFamily (D : NameDomain s) : Set (Set P) :=
  {E | (∃ p σ τ, σ ∈ D.names ∧ τ ∈ D.names ∧ E = Localized p (MemWitness σ τ)) ∨
    ∃ σ τ, σ ∈ D.names ∧ τ ∈ D.names ∧ E = EqDecisionWitness σ τ}

theorem generic_mem_witness (D : NameDomain s) (H : ConditionFilter P)
    (generic : H.GenericFor (atomicFamily D)) {σ τ : Name s}
    (hσ : σ ∈ D.names) (hτ : τ ∈ D.names) {p : P} (hp : H.mem p)
    (h : ForcesMem p σ τ) : H.Meets (MemWitness σ τ) :=
  H.meets_below generic hp (Or.inl ⟨p, σ, τ, hσ, hτ, rfl⟩) h

end Name



namespace Name.NameDomain

open SetRealization
universe u
variable {P : Type u} {s : Presentation P}

def values (D : NameDomain s) (H : Set P) : Set ZFSet.{u} :=
  Set.range (fun τ : D.names => eval H τ.val)

theorem mem_values (D : NameDomain s) (H : Set P) (x : ZFSet.{u}) :
    x ∈ D.values H ↔ ∃ τ ∈ D.names, eval H τ = x := by
  constructor
  · rintro ⟨τ, eq⟩
    exact ⟨τ.val, τ.property, eq⟩
  · rintro ⟨τ, hτ, eq⟩
    exact ⟨⟨τ, hτ⟩, eq⟩

theorem values_transitive (D : NameDomain s) (H : Set P)
    {x y : ZFSet.{u}} (hx : x ∈ D.values H) (hy : y ∈ x) : y ∈ D.values H := by
  obtain ⟨τ, hτ, rfl⟩ := (D.mem_values H x).1 hx
  obtain ⟨σ, p, entry, _, eq⟩ := (mem_eval H τ y).1 hy
  exact (D.mem_values H y).2 ⟨σ, D.children hτ entry, eq⟩

end Name.NameDomain

end PartitionPilot.Forcing

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Geometry_AtomicSoundness
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
variable {P : Type u} [Preorder P] {s : Presentation P}

theorem forcesEq_sound (D : NameDomain s) (H : ConditionFilter P)
    (generic : H.GenericFor (atomicFamily D)) :
    ∀ σ ∈ D.names, ∀ τ ∈ D.names, ∀ p, H.mem p → ForcesEq p σ τ →
      eval {q | H.mem q} σ = eval {q | H.mem q} τ := by
  intro σ
  induction σ using inductionOn with
  | step σ ih =>
    intro hσ τ hτ p hp eq
    apply ZFSet.ext
    intro value
    constructor
    · intro hv
      obtain ⟨ρ, r, entry, hr, old⟩ := (mem_eval {q | H.mem q} σ value).1 hv
      obtain ⟨q, hq, qp, qr⟩ := H.directed hp hr
      have hρ := D.children hσ entry
      obtain ⟨t, ht, ν, k, target, tk, childEq⟩ := generic_mem_witness D H generic hρ hτ hq
        (forcesEq_left eq entry qp qr)
      have values := ih ρ r entry hρ ν (D.children hτ target) t ht childEq
      exact (mem_eval {q | H.mem q} τ value).2
        ⟨ν, k, target, H.upward ht tk, values.symm.trans old⟩
    · intro hv
      obtain ⟨ν, k, entry, hk, old⟩ := (mem_eval {q | H.mem q} τ value).1 hv
      obtain ⟨q, hq, qp, qk⟩ := H.directed hp hk
      have hν := D.children hτ entry
      obtain ⟨t, ht, ρ, r, target, tr, childEq⟩ := generic_mem_witness D H generic hν hσ hq
        (forcesEq_right eq entry qp qk)
      have values := ih ρ r target (D.children hσ target) ν hν t ht (forcesEq_symm childEq)
      exact (mem_eval {q | H.mem q} σ value).2
        ⟨ρ, r, target, H.upward ht tr, values.trans old⟩

theorem forcesMem_sound (D : NameDomain s) (H : ConditionFilter P)
    (generic : H.GenericFor (atomicFamily D)) {σ τ : Name s}
    (hσ : σ ∈ D.names) (hτ : τ ∈ D.names) {p : P} (hp : H.mem p)
    (h : ForcesMem p σ τ) : eval {q | H.mem q} σ ∈ eval {q | H.mem q} τ := by
  obtain ⟨q, hq, ν, r, entry, qr, eq⟩ := generic_mem_witness D H generic hσ hτ hp h
  have values := forcesEq_sound D H generic σ hσ ν (D.children hτ entry) q hq eq
  exact (mem_eval {q | H.mem q} τ _).2 ⟨ν, r, entry, H.upward hq qr, values.symm⟩

end PartitionPilot.Forcing.Name

end

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Forcing_AtomicTruth
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
variable {P : Type u} [Preorder P] {s : Presentation P}

def EqTruth (H : ConditionFilter P) (σ τ : Name s) : Prop :=
  eval {q | H.mem q} σ = eval {q | H.mem q} τ → ∃ p, H.mem p ∧ ForcesEq p σ τ

def MemTruth (H : ConditionFilter P) (σ τ : Name s) : Prop :=
  eval {q | H.mem q} σ ∈ eval {q | H.mem q} τ → ∃ p, H.mem p ∧ ForcesMem p σ τ

theorem memTruth_of_children (H : ConditionFilter P) (σ τ : Name s)
    (children : ∀ ν r, Entry ν τ r → EqTruth H σ ν) : MemTruth H σ τ := by
  intro hv
  obtain ⟨ν, r, entry, hr, values⟩ := (mem_eval {q | H.mem q} τ _).1 hv
  obtain ⟨p, hp, eq⟩ := children ν r entry values.symm
  obtain ⟨q, hq, qp, qr⟩ := H.directed hp hr
  exact ⟨q, hq, forcesMem_of_witness ⟨ν, r, entry, qr, forcesEq_mono eq qp⟩⟩

theorem eqTruth_of_children (D : NameDomain s) (H : ConditionFilter P)
    (generic : H.GenericFor (atomicFamily D)) (σ τ : Name s)
    (hσ : σ ∈ D.names) (hτ : τ ∈ D.names)
    (left : ∀ ρ r, Entry ρ σ r → MemTruth H ρ τ)
    (right : ∀ ν k, Entry ν τ k → MemTruth H ν σ) : EqTruth H σ τ := by
  intro values
  obtain ⟨p, hp, eq | bad | bad⟩ := generic (EqDecisionWitness σ τ)
    (Or.inr ⟨σ, τ, hσ, hτ, rfl⟩) (eqDecisionWitness_dense σ τ)
  · exact ⟨p, hp, eq⟩
  · obtain ⟨ρ, r, entry, pr, neg⟩ := bad
    have member : eval {q | H.mem q} ρ ∈ eval {q | H.mem q} τ := by
      rw [← values]
      exact (mem_eval {q | H.mem q} σ _).2 ⟨ρ, r, entry, H.upward hp pr, rfl⟩
    obtain ⟨q, hq, mem⟩ := left ρ r entry member
    obtain ⟨t, _, tp, tq⟩ := H.directed hp hq
    exact False.elim (neg t tp (forcesMem_mono mem tq))
  · obtain ⟨ν, k, entry, pk, neg⟩ := bad
    have member : eval {q | H.mem q} ν ∈ eval {q | H.mem q} σ := by
      rw [values]
      exact (mem_eval {q | H.mem q} τ _).2 ⟨ν, k, entry, H.upward hp pk, rfl⟩
    obtain ⟨q, hq, mem⟩ := right ν k entry member
    obtain ⟨t, _, tp, tq⟩ := H.directed hp hq
    exact False.elim (neg t tp (forcesMem_mono mem tq))

theorem atomic_truth (D : NameDomain s) (H : ConditionFilter P)
    (generic : H.GenericFor (atomicFamily D)) :
    ∀ σ ∈ D.names, ∀ τ ∈ D.names, EqTruth H σ τ ∧ MemTruth H σ τ ∧ MemTruth H τ σ := by
  intro σ
  induction σ using inductionOn with
  | step σ outer =>
    intro hσ τ
    induction τ using inductionOn with
    | step τ inner =>
      intro hτ
      have eq : EqTruth H σ τ := eqTruth_of_children D H generic σ τ hσ hτ
        (fun ρ r entry => (outer ρ r entry (D.children hσ entry) τ hτ).2.1)
        (fun ν k entry => (inner ν k entry (D.children hτ entry)).2.2)
      have mem : MemTruth H σ τ := memTruth_of_children H σ τ
        (fun ν k entry => (inner ν k entry (D.children hτ entry)).1)
      have reverse : MemTruth H τ σ := memTruth_of_children H τ σ (by
        intro ρ r entry values
        obtain ⟨p, hp, eq⟩ := (outer ρ r entry (D.children hσ entry) τ hτ).1 values.symm
        exact ⟨p, hp, forcesEq_symm eq⟩)
      exact ⟨eq, mem, reverse⟩

theorem eval_eq_iff_forcesEq (D : NameDomain s) (H : ConditionFilter P)
    (generic : H.GenericFor (atomicFamily D)) {σ τ : Name s}
    (hσ : σ ∈ D.names) (hτ : τ ∈ D.names) :
    eval {q | H.mem q} σ = eval {q | H.mem q} τ ↔ ∃ p, H.mem p ∧ ForcesEq p σ τ := by
  constructor
  · exact (atomic_truth D H generic σ hσ τ hτ).1
  · rintro ⟨p, hp, eq⟩
    exact forcesEq_sound D H generic σ hσ τ hτ p hp eq

theorem eval_mem_iff_forcesMem (D : NameDomain s) (H : ConditionFilter P)
    (generic : H.GenericFor (atomicFamily D)) {σ τ : Name s}
    (hσ : σ ∈ D.names) (hτ : τ ∈ D.names) :
    eval {q | H.mem q} σ ∈ eval {q | H.mem q} τ ↔ ∃ p, H.mem p ∧ ForcesMem p σ τ := by
  constructor
  · exact (atomic_truth D H generic σ hσ τ hτ).2.1
  · rintro ⟨p, hp, mem⟩
    exact forcesMem_sound D H generic hσ hτ hp mem

end PartitionPilot.Forcing.Name

end

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Geometry_Compression
attribute [-instance] _root_.OAI.PartitionPilot.Compression.RecursiveMaps.TileRequests.Family.child_countable _root_.OAI.PartitionPilot.Compression.RecursiveMaps.TileRequests.Request.child_countable _root_.OAI.PartitionPilot.Forcing.GroundMainPrefix.withTopSmall
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace PartitionPilot

section

universe u v

def HasOldShadow {α : Type u} {β : Type v}
    {P : MeetOrder α} {Q : MeetOrder β}
    (i : MeetEmbedding P Q) (x : β) : Prop :=
  ∃ l,
    (∀ a, Q.le (i.toFun a) x ↔ P.le a l) ∧
    (∀ a, ¬ Q.le x (i.toFun a) →
      Q.meet x (i.toFun a) = i.toFun (P.meet l a))

def IsGreatest {β : Type v} (Q : MeetOrder β) (x : β) : Prop :=
  ∀ y, Q.le y x

def PermittedExtension {α : Type u} {β : Type v}
    {P : MeetOrder α} {Q : MeetOrder β}
    (i : MeetEmbedding P Q) : Prop :=
  ∀ x, (∃ a, i.toFun a = x) ∨ HasOldShadow i x ∨ IsGreatest Q x

end




universe u v w

end PartitionPilot

end OAI
end

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

open SetRealization
universe u
variable {P : Type u} [Preorder P] {s : Presentation P}

abbrev Assignment (D : Name.NameDomain s) (n : Nat) := Fin n → D.names

def Forces (D : Name.NameDomain s) : {n : Nat} → SetFormula n → Assignment D n → P → Prop
  | _, .equal i j, env, p => Name.ForcesEq p (env i).val (env j).val
  | _, .mem i j, env, p => Name.ForcesMem p (env i).val (env j).val
  | _, .neg φ, env, p => ∀ q, q ≤ p → ¬ Forces D φ env q
  | _, .conj φ ψ, env, p => Forces D φ env p ∧ Forces D ψ env p
  | _, .all φ, env, p => ∀ τ : D.names, Forces D φ (extend τ env) p

theorem forces_mono (D : Name.NameDomain s) {n : Nat} (φ : SetFormula n)
    (env : Assignment D n) {p q : P} (h : Forces D φ env p) (qp : q ≤ p) :
    Forces D φ env q := by
  induction φ generalizing p q with
  | equal i j => exact Name.forcesEq_mono h qp
  | mem i j => exact Name.forcesMem_mono h qp
  | neg φ _ => exact fun r rq => h r (rq.trans qp)
  | conj φ ψ ihφ ihψ => exact ⟨ihφ env h.1 qp, ihψ env h.2 qp⟩
  | all φ ih => exact fun τ => ih (extend τ env) (h τ) qp

theorem forces_of_dense (D : Name.NameDomain s) {n : Nat} (φ : SetFormula n)
    (env : Assignment D n) {p : P} (dense : DenseBelow p {q | Forces D φ env q}) :
    Forces D φ env p := by
  induction φ generalizing p with
  | equal i j => exact Name.forcesEq_of_dense dense
  | mem i j => exact Name.forcesMem_of_dense dense
  | neg φ _ =>
    intro q qp hq
    obtain ⟨r, rq, hr⟩ := dense q qp
    exact hr r le_rfl (forces_mono D φ env hq rq)
  | conj φ ψ ihφ ihψ =>
    exact ⟨ihφ env (denseBelow_mono dense (fun _ h => h.1)),
      ihψ env (denseBelow_mono dense (fun _ h => h.2))⟩
  | all φ ih =>
    exact fun τ => ih (extend τ env) (denseBelow_mono dense (fun _ h => h τ))

theorem not_forces_refine_neg (D : Name.NameDomain s) {n : Nat} (φ : SetFormula n)
    (env : Assignment D n) {p : P} (bad : ¬ Forces D φ env p) :
    ∃ q, q ≤ p ∧ Forces D (.neg φ) env q := by
  classical
  have missing : ¬ DenseBelow p {q | Forces D φ env q} := fun h => bad (forces_of_dense D φ env h)
  change ¬ ∀ q, q ≤ p → ∃ r, r ≤ q ∧ Forces D φ env r at missing
  push Not at missing
  exact missing

noncomputable def evalAssignment (H : Set P) {D : Name.NameDomain s} {n : Nat}
    (env : Assignment D n) : Fin n → ZFSet.{u} := fun i => Name.eval H (env i).val

omit [Preorder P] in
theorem evalAssignment_extend (H : Set P) {D : Name.NameDomain s} {n : Nat}
    (τ : D.names) (env : Assignment D n) :
    evalAssignment H (extend τ env) = extend (Name.eval H τ.val) (evalAssignment H env) :=
  map_extend (fun τ : D.names => Name.eval H τ.val) τ env

end SetFormula



namespace SetFormula

open SetRealization
universe u
variable {P : Type u} [Preorder P] {s : Presentation P}

def DecisionWitness (D : Name.NameDomain s) {n : Nat} (φ : SetFormula n)
    (env : Assignment D n) : Set P := {p | Forces D φ env p ∨ Forces D (.neg φ) env p}

theorem decisionWitness_dense (D : Name.NameDomain s) {n : Nat} (φ : SetFormula n)
    (env : Assignment D n) : Dense (DecisionWitness D φ env) := by
  classical
  intro p
  by_cases possible : ∃ q, q ≤ p ∧ Forces D φ env q
  · obtain ⟨q, qp, hq⟩ := possible
    exact ⟨q, qp, Or.inl hq⟩
  · exact ⟨p, le_rfl, Or.inr (fun q qp hq => possible ⟨q, qp, hq⟩)⟩

def AllDecisionWitness (D : Name.NameDomain s) {n : Nat} (φ : SetFormula (n + 1))
    (env : Assignment D n) : Set P :=
  {p | Forces D (.all φ) env p ∨ ∃ τ : D.names, Forces D (.neg φ) (extend τ env) p}

theorem allDecisionWitness_dense (D : Name.NameDomain s) {n : Nat}
    (φ : SetFormula (n + 1)) (env : Assignment D n) : Dense (AllDecisionWitness D φ env) := by
  classical
  intro p
  by_cases h : Forces D (.all φ) env p
  · exact ⟨p, le_rfl, Or.inl h⟩
  · change ¬ ∀ τ : D.names, Forces D φ (extend τ env) p at h
    push Not at h
    obtain ⟨τ, bad⟩ := h
    obtain ⟨q, qp, neg⟩ := not_forces_refine_neg D φ (extend τ env) bad
    exact ⟨q, qp, Or.inr ⟨τ, neg⟩⟩

def formulaFamily (D : Name.NameDomain s) : Set (Set P) :=
  Name.atomicFamily D ∪ {E |
    (∃ (n : Nat) (φ : SetFormula n) (env : Assignment D n), E = DecisionWitness D φ env) ∨
    ∃ (n : Nat) (φ : SetFormula (n + 1)) (env : Assignment D n), E = AllDecisionWitness D φ env}

end SetFormula



namespace SetFormula

universe u v

theorem realize_exBlock (U : Set ZFSet.{u}) {n : Nat} (k : Nat)
    (body : SetFormula (n + k)) (env : Fin n → ZFSet.{u}) :
    Realize U (exBlock k body) env ↔
      ∃ fields : Fin k → ZFSet.{u}, (∀ i, fields i ∈ U) ∧
        Realize U body (extendMany k fields env) := by
  induction k with
  | zero =>
    constructor
    · intro value
      exact ⟨Fin.elim0, fun i => Fin.elim0 i, value⟩
    · rintro ⟨_, _, value⟩
      exact value
  | succ k ih =>
    rw [exBlock, ih]
    constructor
    · rintro ⟨fields, members, rest⟩
      obtain ⟨first, hfirst, value⟩ := (realize_ex U _ _).1 rest
      let combined : Fin (k + 1) → ZFSet.{u} := Fin.cases first fields
      refine ⟨combined, ?_, ?_⟩
      · intro i
        exact Fin.cases hfirst members i
      · exact value
    · rintro ⟨fields, members, value⟩
      refine ⟨fun i => fields i.succ, fun i => members i.succ, ?_⟩
      exact (realize_ex U _ _).2 ⟨fields 0, members 0, value⟩

end SetFormula



namespace SetFormula

open SetRealization
universe u
variable {P : Type u} [Preorder P] {s : Presentation P}

theorem forcing_truth (D : Name.NameDomain s) (H : ConditionFilter P)
    (generic : H.GenericFor (formulaFamily D)) {n : Nat} (φ : SetFormula n)
    (env : Assignment D n) :
    Realize (D.values {p | H.mem p}) φ (evalAssignment {p | H.mem p} env) ↔
      ∃ p, H.mem p ∧ Forces D φ env p := by
  have atoms : H.GenericFor (Name.atomicFamily D) := fun E hE dense => generic E (Or.inl hE) dense
  induction φ with
  | equal i j => exact Name.eval_eq_iff_forcesEq D H atoms (env i).property (env j).property
  | mem i j => exact Name.eval_mem_iff_forcesMem D H atoms (env i).property (env j).property
  | neg φ ih =>
    constructor
    · intro notTrue
      obtain ⟨p, hp, good | bad⟩ := generic (DecisionWitness D φ env)
        (Or.inr (Or.inl ⟨_, φ, env, rfl⟩)) (decisionWitness_dense D φ env)
      · exact False.elim (notTrue ((ih env).2 ⟨p, hp, good⟩))
      · exact ⟨p, hp, bad⟩
    · rintro ⟨p, hp, neg⟩ truth
      obtain ⟨q, hq, hφ⟩ := (ih env).1 truth
      obtain ⟨r, _, rp, rq⟩ := H.directed hp hq
      exact neg r rp (forces_mono D φ env hφ rq)
  | conj φ ψ ihφ ihψ =>
    constructor
    · rintro ⟨hφ, hψ⟩
      obtain ⟨p, hp, fp⟩ := (ihφ env).1 hφ
      obtain ⟨q, hq, fq⟩ := (ihψ env).1 hψ
      obtain ⟨r, hr, rp, rq⟩ := H.directed hp hq
      exact ⟨r, hr, forces_mono D φ env fp rp, forces_mono D ψ env fq rq⟩
    · rintro ⟨p, hp, hφ, hψ⟩
      exact ⟨(ihφ env).2 ⟨p, hp, hφ⟩, (ihψ env).2 ⟨p, hp, hψ⟩⟩
  | all φ ih =>
    constructor
    · intro allTrue
      obtain ⟨p, hp, good | bad⟩ := generic (AllDecisionWitness D φ env)
        (Or.inr (Or.inr ⟨_, φ, env, rfl⟩)) (allDecisionWitness_dense D φ env)
      · exact ⟨p, hp, good⟩
      · obtain ⟨τ, neg⟩ := bad
        have truth := allTrue (Name.eval {q | H.mem q} τ.val) ⟨τ, rfl⟩
        rw [← evalAssignment_extend] at truth
        obtain ⟨q, hq, hφ⟩ := (ih (extend τ env)).1 truth
        obtain ⟨r, _, rp, rq⟩ := H.directed hp hq
        exact False.elim (neg r rp (forces_mono D φ (extend τ env) hφ rq))
    · rintro ⟨p, hp, allForced⟩ x hx
      obtain ⟨τ, rfl⟩ := hx
      have truth := (ih (extend τ env)).2 ⟨p, hp, allForced τ⟩
      rw [evalAssignment_extend] at truth
      exact truth

theorem forces_sound (D : Name.NameDomain s) (H : ConditionFilter P)
    (generic : H.GenericFor (formulaFamily D)) {n : Nat} (φ : SetFormula n)
    (env : Assignment D n) {p : P} (hp : H.mem p) (h : Forces D φ env p) :
    Realize (D.values {q | H.mem q}) φ (evalAssignment {q | H.mem q} env) :=
  (forcing_truth D H generic φ env).2 ⟨p, hp, h⟩

end SetFormula



namespace SetFormula

open Compression.RecursiveMaps

def natCode : {n : Nat} → SetFormula n → Nat
  | _, .equal i j => natPair 0 (natPair i.val j.val)
  | _, .mem i j => natPair 1 (natPair i.val j.val)
  | _, .neg φ => natPair 2 (natCode φ)
  | _, .conj φ ψ => natPair 3 (natPair (natCode φ) (natCode ψ))
  | _, .all φ => natPair 4 (natCode φ)

end SetFormula

end PartitionPilot.Forcing

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Definability_NatUnionCodes
attribute [-instance] _root_.OAI.PartitionPilot.Forcing.GroundMainPrefix.withTopSmall _root_.OAI.PartitionPilot.Forcing.Name.entries_small
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI



namespace PartitionPilot.SetRealization.Presentation
universe u
variable {A B : Type u} (s : Presentation A) (e : B ≃ A)

def reindex : Presentation B where
  carrier := s.carrier
  encode b := s.encode (e b)
  injective := s.injective.comp e.injective
  mem_carrier x := by
    rw [s.mem_carrier]
    exact ⟨fun ⟨a, eq⟩ => ⟨e.symm a, by simpa only [e.apply_symm_apply] using eq⟩,
      fun ⟨b, eq⟩ => ⟨e b, eq⟩⟩

theorem graph_reindex {C : Type u} (t : Presentation C) (f : C → B) :
    t.graph (s.reindex e) f = t.graph s (fun x => e (f x)) := by
  apply ZFSet.ext
  intro z
  rw [mem_graph, mem_graph]
  rfl

end PartitionPilot.SetRealization.Presentation



end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Forcing_OrbitPairGraphNames
attribute [-instance] _root_.OAI.PartitionPilot.Forcing.GroundMainPrefix.withTopSmall
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace PartitionPilot.Forcing.Name

open SetRealization
universe u v
variable {P Q R : Type u} {s : Presentation P}

noncomputable def rename (t : Presentation Q) (f : P → Q) (τ : Name s) : Name t :=
  assemble (fun a : Entries τ => rename t f a.val.1) (fun a => f a.val.2)
termination_by ZFSet.rank τ.val
decreasing_by exact entry_rank_lt a.property

theorem entry_rename (t : Presentation Q) (f : P → Q) (τ : Name s)
    (σ : Name t) (q : Q) :
    Entry σ (rename t f τ) q ↔
      ∃ ν p, Entry ν τ p ∧ rename t f ν = σ ∧ f p = q := by
  rw [rename, entry_assemble]
  constructor
  · rintro ⟨a, eq, hp⟩
    exact ⟨a.val.1, a.val.2, a.property, eq, hp⟩
  · rintro ⟨ν, p, h, eq, hp⟩
    exact ⟨⟨(ν, p), h⟩, eq, hp⟩

theorem rename_assemble (t : Presentation Q) (f : P → Q)
    {α : Type v} [Small.{u} α] (names : α → Name s) (conditions : α → P) :
    rename t f (assemble names conditions) =
      assemble (fun i => rename t f (names i)) (fun i => f (conditions i)) := by
  apply ext
  intro σ q
  rw [entry_rename, entry_assemble]
  constructor
  · rintro ⟨ν, p, h, eq, hp⟩
    obtain ⟨i, rfl, rfl⟩ := (entry_assemble names conditions ν p).1 h
    exact ⟨i, eq, hp⟩
  · rintro ⟨i, eq, hp⟩
    exact ⟨names i, conditions i,
      (entry_assemble names conditions _ _).2 ⟨i, rfl, rfl⟩, eq, hp⟩

theorem rename_id (τ : Name s) : rename s id τ = τ := by
  induction τ using inductionOn with
  | step τ ih =>
    apply ext
    intro σ p
    rw [entry_rename]
    constructor
    · rintro ⟨ν, q, h, eq, hp⟩
      rw [ih ν q h] at eq
      simpa only [id_eq, ← eq, ← hp] using h
    · intro h
      exact ⟨σ, p, h, ih σ p h, rfl⟩

theorem rename_comp (t : Presentation Q) (r : Presentation R)
    (f : P → Q) (g : Q → R) (τ : Name s) :
    rename r g (rename t f τ) = rename r (g ∘ f) τ := by
  induction τ using inductionOn with
  | step τ ih =>
    apply ext
    intro σ q
    rw [entry_rename, entry_rename]
    constructor
    · rintro ⟨ν, p, h, eq, hp⟩
      obtain ⟨χ, a, ha, rfl, rfl⟩ := (entry_rename t f τ ν p).1 h
      exact ⟨χ, a, ha, (ih χ a ha).symm.trans eq, hp⟩
    · rintro ⟨χ, a, ha, eq, hp⟩
      exact ⟨rename t f χ, f a, (entry_rename t f τ _ _).2 ⟨χ, a, ha, rfl, rfl⟩,
        (ih χ a ha).trans eq, hp⟩

theorem rename_singleton (t : Presentation Q) (f : P → Q) (one : P) (σ : Name s) :
    rename t f (singleton one σ) = singleton (f one) (rename t f σ) := by
  rw [singleton, rename_assemble]
  rfl

theorem rename_unorderedPair (t : Presentation Q) (f : P → Q)
    (one : P) (σ τ : Name s) :
    rename t f (unorderedPair one σ τ) =
      unorderedPair (f one) (rename t f σ) (rename t f τ) := by
  rw [unorderedPair, rename_assemble, unorderedPair]
  apply congrArg (fun names : Bool → Name t => assemble names (fun _ => f one))
  funext b
  cases b <;> rfl

theorem rename_orderedPair (t : Presentation Q) (f : P → Q)
    (one : P) (σ τ : Name s) :
    rename t f (orderedPair one σ τ) =
      orderedPair (f one) (rename t f σ) (rename t f τ) := by
  rw [orderedPair, rename_unorderedPair, rename_singleton, rename_unorderedPair]
  rfl

end PartitionPilot.Forcing.Name



namespace PartitionPilot.Forcing

open SetRealization Compression.RecursiveMaps.CosetGeometry.OrderAction
universe u v

namespace PosetAction
variable {G : Type v} [Group G] {P : Type u} [PartialOrder P]
variable (a : PosetAction G P) (s : Presentation P)

noncomputable def act (g : G) (τ : Name s) : Name s := Name.rename s (a.iso g) τ

theorem act_one (τ : Name s) : a.act s 1 τ = τ := by
  have eq : (a.iso 1 : P → P) = id := funext a.one
  change Name.rename s (a.iso 1) τ = τ
  rw [eq, Name.rename_id]

theorem act_mul (g h : G) (τ : Name s) :
    a.act s (g * h) τ = a.act s g (a.act s h τ) := by
  have eq : (a.iso (g * h) : P → P) = (a.iso g : P → P) ∘ a.iso h :=
    funext (a.mul g h)
  change Name.rename s (a.iso (g * h)) τ =
    Name.rename s (a.iso g) (Name.rename s (a.iso h) τ)
  rw [Name.rename_comp, eq]

theorem act_inv_left (g : G) (τ : Name s) : a.act s g⁻¹ (a.act s g τ) = τ := by
  rw [← act_mul, inv_mul_cancel, act_one]

theorem act_inv_right (g : G) (τ : Name s) : a.act s g (a.act s g⁻¹ τ) = τ := by
  rw [← act_mul, mul_inv_cancel, act_one]

noncomputable def nameEquiv (g : G) : Name s ≃ Name s where
  toFun := a.act s g
  invFun := a.act s g⁻¹
  left_inv := a.act_inv_left s g
  right_inv := a.act_inv_right s g

theorem entry_act (g : G) (σ τ : Name s) (p : P) :
    Name.Entry (a.act s g σ) (a.act s g τ) (a.iso g p) ↔ Name.Entry σ τ p := by
  change Name.Entry (a.act s g σ) (Name.rename s (a.iso g) τ) (a.iso g p) ↔ _
  rw [Name.entry_rename]
  constructor
  · rintro ⟨ν, q, h, eq, hp⟩
    have eqν : ν = σ := (a.nameEquiv s g).injective eq
    have eqp : q = p := (a.iso g).injective hp
    simpa only [← eqν, ← eqp] using h
  · intro h
    exact ⟨σ, p, h, rfl, rfl⟩

def stabilizer (τ : Name s) : Subgroup G where
  carrier := {g | a.act s g τ = τ}
  one_mem' := a.act_one s τ
  mul_mem' {g h} hg hh := by
    change a.act s (g * h) τ = τ
    change a.act s g τ = τ at hg
    change a.act s h τ = τ at hh
    rw [a.act_mul, hh, hg]
  inv_mem' {g} hg := by
    have eq := a.act_inv_left s g τ
    rw [hg] at eq
    exact eq

end PosetAction
end PartitionPilot.Forcing



namespace PartitionPilot.Forcing.PosetAction

open SetRealization
universe u v
variable {G : Type v} [Group G] {P : Type u} [PartialOrder P]
variable (a : PosetAction G P) (s : Presentation P)

theorem forcesEq_act (g : G) {p : P} {σ τ : Name s} (eq : Name.ForcesEq p σ τ) :
    Name.ForcesEq (a.iso g p) (a.act s g σ) (a.act s g τ) := by
  induction σ using Name.inductionOn generalizing p τ with
  | step σ ih =>
    rw [Name.ForcesEq] at eq ⊢
    constructor
    · intro ρ r entry q qp qr
      change Name.Entry ρ (Name.rename s (a.iso g) σ) r at entry
      obtain ⟨ρ₀, r₀, old, rfl, rfl⟩ := (Name.entry_rename s (a.iso g) σ ρ r).1 entry
      have oldp : (a.iso g).symm q ≤ p := by simpa using (a.iso g).symm.monotone qp
      have oldr : (a.iso g).symm q ≤ r₀ := by simpa using (a.iso g).symm.monotone qr
      obtain ⟨t, tq, ν, k, target, tk, childEq⟩ := eq.1 ρ₀ r₀ old _ oldp oldr
      refine ⟨a.iso g t, ?_, a.act s g ν, a.iso g k,
        (a.entry_act s g ν τ k).2 target, (a.iso g).monotone tk, ih ρ₀ r₀ old childEq⟩
      simpa using (a.iso g).monotone tq
    · intro ν k entry q qp qk
      change Name.Entry ν (Name.rename s (a.iso g) τ) k at entry
      obtain ⟨ν₀, k₀, old, rfl, rfl⟩ := (Name.entry_rename s (a.iso g) τ ν k).1 entry
      have oldp : (a.iso g).symm q ≤ p := by simpa using (a.iso g).symm.monotone qp
      have oldk : (a.iso g).symm q ≤ k₀ := by simpa using (a.iso g).symm.monotone qk
      obtain ⟨t, tq, ρ, r, target, tr, childEq⟩ := eq.2 ν₀ k₀ old _ oldp oldk
      refine ⟨a.iso g t, ?_, a.act s g ρ, a.iso g r,
        (a.entry_act s g ρ σ r).2 target, (a.iso g).monotone tr, ih ρ r target childEq⟩
      simpa using (a.iso g).monotone tq

theorem forcesEq_act_iff (g : G) (p : P) (σ τ : Name s) :
    Name.ForcesEq (a.iso g p) (a.act s g σ) (a.act s g τ) ↔ Name.ForcesEq p σ τ := by
  constructor
  · intro eq
    have old := a.forcesEq_act s g⁻¹ eq
    rw [← a.mul, inv_mul_cancel, a.one, a.act_inv_left, a.act_inv_left] at old
    exact old
  · exact a.forcesEq_act s g

theorem forcesMem_act (g : G) {p : P} {σ τ : Name s} (mem : Name.ForcesMem p σ τ) :
    Name.ForcesMem (a.iso g p) (a.act s g σ) (a.act s g τ) := by
  intro q qp
  have oldp : (a.iso g).symm q ≤ p := by simpa using (a.iso g).symm.monotone qp
  obtain ⟨t, tq, ν, r, entry, tr, eq⟩ := mem _ oldp
  refine ⟨a.iso g t, ?_, a.act s g ν, a.iso g r,
    (a.entry_act s g ν τ r).2 entry, (a.iso g).monotone tr, a.forcesEq_act s g eq⟩
  simpa using (a.iso g).monotone tq

theorem forcesMem_act_iff (g : G) (p : P) (σ τ : Name s) :
    Name.ForcesMem (a.iso g p) (a.act s g σ) (a.act s g τ) ↔ Name.ForcesMem p σ τ := by
  constructor
  · intro mem
    have old := a.forcesMem_act s g⁻¹ mem
    rw [← a.mul, inv_mul_cancel, a.one, a.act_inv_left, a.act_inv_left] at old
    exact old
  · exact a.forcesMem_act s g

end PartitionPilot.Forcing.PosetAction



namespace PartitionPilot.Forcing.PosetAction
open SetRealization
universe u v
variable {P Q : Type u} {G : Type v} [Group G]
variable [PartialOrder P] [PartialOrder Q]
variable (a : PosetAction G P) (e : PosetAction G Q)
variable (s : Presentation P) (t : Presentation Q) (f : P → Q)
variable (equivariant : ∀ g p, f (a.iso g p) = e.iso g (f p))

include equivariant

theorem act_rename_of_equivariant (g : G) (τ : Name s) :
    e.act t g (Name.rename t f τ) = Name.rename t f (a.act s g τ) := by
  change Name.rename t (e.iso g) (Name.rename t f τ) =
    Name.rename t f (Name.rename s (a.iso g) τ)
  rw [Name.rename_comp, Name.rename_comp]
  have equal : (e.iso g : Q → Q) ∘ f = f ∘ a.iso g :=
    funext (fun p => (equivariant g p).symm)
  rw [equal]

theorem stabilizer_le_rename (τ : Name s) :
    a.stabilizer s τ ≤ e.stabilizer t (Name.rename t f τ) := by
  intro g fixed
  change e.act t g (Name.rename t f τ) = Name.rename t f τ
  change a.act s g τ = τ at fixed
  rw [a.act_rename_of_equivariant e s t f equivariant, fixed]

end PartitionPilot.Forcing.PosetAction



namespace PartitionPilot.Forcing

open SetRealization Compression.RecursiveMaps
universe u v w
variable {G : Type v} [Group G] {P : Type u} [PartialOrder P]

inductive HereditarilySymmetric (a : PosetAction G P) (s : Presentation P)
    (F : NormalSubgroupFamily G) : Name s → Prop
  | mk {τ} : F.mem (a.stabilizer s τ) →
      (∀ σ p, Name.Entry σ τ p → HereditarilySymmetric a s F σ) →
      HereditarilySymmetric a s F τ

namespace HereditarilySymmetric
variable {a : PosetAction G P} {s : Presentation P} {F : NormalSubgroupFamily G}

theorem symmetric {τ : Name s} (h : HereditarilySymmetric a s F τ) :
    F.mem (a.stabilizer s τ) := by
  cases h with
  | mk hs _ => exact hs

theorem member {τ σ : Name s} (h : HereditarilySymmetric a s F τ)
    {p : P} (entry : Name.Entry σ τ p) : HereditarilySymmetric a s F σ := by
  cases h with
  | mk _ children => exact children σ p entry

end HereditarilySymmetric
end PartitionPilot.Forcing


namespace PartitionPilot.Forcing.HereditarilySymmetric
open SetRealization Compression.RecursiveMaps
universe u v
variable {P Q : Type u} [PartialOrder P] [PartialOrder Q]
variable {G : Type v} [Group G]
variable {a : PosetAction G P} {s : Presentation P}
variable (e : PosetAction G Q) (t : Presentation Q) (f : P → Q)
variable (equivariant : ∀ g p, f (a.iso g p) = e.iso g (f p))
variable {F : NormalSubgroupFamily G}
include equivariant

theorem rename {τ : Name s} (hs : HereditarilySymmetric a s F τ) :
    HereditarilySymmetric e t F (Name.rename t f τ) := by
  induction τ using Name.inductionOn with
  | step τ ih =>
    refine .mk ?_ ?_
    · exact F.upward hs.symmetric (a.stabilizer_le_rename e s t f equivariant τ)
    · intro ν q entry
      obtain ⟨σ, p, old, rfl, _⟩ := (Name.entry_rename t f τ ν q).1 entry
      exact ih σ p old (hs.member old)

end PartitionPilot.Forcing.HereditarilySymmetric



namespace PartitionPilot.Forcing.Name
open SetRealization Compression.RecursiveMaps
universe u
variable {G P : Type u} [Group G] [PartialOrder P] [OrderTop P]
variable (a : PosetAction G P) (s : Presentation P)

noncomputable def orbitPairGraph (tuple tau : Name s) : Name s :=
  assemble (fun g : G => orderedPair ⊤ (a.act s g tuple) (a.act s g tau)) (fun _ => ⊤)

end PartitionPilot.Forcing.Name



namespace PartitionPilot.Forcing

open SetRealization
universe u

namespace TransitiveGround

variable (M : TransitiveGround.{u}) {P : Type u} (s : Presentation P)

def nameDomain : Name.NameDomain s where
  names := {τ | τ.val ∈ M.sets}
  children hτ entry := M.pair_left (M.transitive hτ entry)

end TransitiveGround
end PartitionPilot.Forcing

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Definability_FormulaSymmetry
attribute [-instance] _root_.OAI.PartitionPilot.Forcing.GroundMainPrefix.withTopSmall
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PartitionPilot.Forcing.PosetAction

open SetRealization SetFormula
universe u v
variable {G : Type v} [Group G] {P : Type u} [PartialOrder P]
variable (a : PosetAction G P) (s : Presentation P)

noncomputable def domainEquiv (D : Name.NameDomain s)
    (closed : ∀ g τ, τ ∈ D.names → a.act s g τ ∈ D.names) (g : G) : D.names ≃ D.names where
  toFun τ := ⟨a.act s g τ.val, closed g τ.val τ.property⟩
  invFun τ := ⟨a.act s g⁻¹ τ.val, closed g⁻¹ τ.val τ.property⟩
  left_inv τ := Subtype.ext (a.act_inv_left s g τ.val)
  right_inv τ := Subtype.ext (a.act_inv_right s g τ.val)

noncomputable def actAssignment (D : Name.NameDomain s)
    (closed : ∀ g τ, τ ∈ D.names → a.act s g τ ∈ D.names) (g : G)
    {n : Nat} (env : Assignment D n) : Assignment D n := fun i => a.domainEquiv s D closed g (env i)

theorem actAssignment_extend (D : Name.NameDomain s)
    (closed : ∀ g τ, τ ∈ D.names → a.act s g τ ∈ D.names) (g : G)
    {n : Nat} (τ : D.names) (env : Assignment D n) :
    a.actAssignment s D closed g (extend τ env) =
      extend (a.domainEquiv s D closed g τ) (a.actAssignment s D closed g env) :=
  map_extend (a.domainEquiv s D closed g) τ env

theorem formula_forces_act_iff (D : Name.NameDomain s)
    (closed : ∀ g τ, τ ∈ D.names → a.act s g τ ∈ D.names) (g : G)
    {n : Nat} (φ : SetFormula n) (env : Assignment D n) (p : P) :
    Forces D φ (a.actAssignment s D closed g env) (a.iso g p) ↔ Forces D φ env p := by
  induction φ generalizing p with
  | equal i j => exact a.forcesEq_act_iff s g p (env i).val (env j).val
  | mem i j => exact a.forcesMem_act_iff s g p (env i).val (env j).val
  | neg φ ih =>
    constructor
    · intro h q qp hφ
      exact h (a.iso g q) ((a.iso g).monotone qp) ((ih env q).2 hφ)
    · intro h q qp hφ
      have oldp : (a.iso g).symm q ≤ p := by simpa using (a.iso g).symm.monotone qp
      have oldφ := (ih env ((a.iso g).symm q)).1 (by simpa using hφ)
      exact h _ oldp oldφ
  | conj φ ψ ihφ ihψ => exact and_congr (ihφ env p) (ihψ env p)
  | all φ ih =>
    constructor
    · intro h τ
      apply (ih (extend τ env) p).1
      rw [a.actAssignment_extend]
      exact h (a.domainEquiv s D closed g τ)
    · intro h ν
      obtain ⟨τ, rfl⟩ := (a.domainEquiv s D closed g).surjective ν
      have forced := (ih (extend τ env) p).2 (h τ)
      rw [a.actAssignment_extend] at forced
      exact forced

end PartitionPilot.Forcing.PosetAction

end

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Forcing_NameMixingRanks
attribute [-instance] _root_.OAI.PartitionPilot.Forcing.GroundMainPrefix.withTopSmall
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace PartitionPilot.Forcing.Name

open SetRealization
universe u
variable {P Q : Type u} {s : Presentation P}

noncomputable def nameRank (τ : Name s) : Ordinal.{u} := ZFSet.rank (eval Set.univ τ)

end PartitionPilot.Forcing.Name


section

namespace PartitionPilot.Forcing.Name

open SetRealization
universe u
variable {P : Type u} [Preorder P] {s : Presentation P}

noncomputable def selectName (R : Name s → P → Prop) (τ : Name s) : Name s :=
  assemble (fun z : {z : Entries τ × P // z.2 ≤ z.1.val.2 ∧ R z.1.val.1 z.2} => z.val.1.val.1)
    (fun z => z.val.2)

theorem entry_selectName (R : Name s → P → Prop) (τ σ : Name s) (p : P) :
    Entry σ (selectName R τ) p ↔ ∃ r, Entry σ τ r ∧ p ≤ r ∧ R σ p := by
  rw [selectName, entry_assemble]
  constructor
  · rintro ⟨z, rfl, rfl⟩
    exact ⟨z.val.1.val.2, z.val.1.property, z.property⟩
  · rintro ⟨r, entry, pr, hR⟩
    exact ⟨⟨(⟨(σ, r), entry⟩, p), pr, hR⟩, rfl, rfl⟩

end PartitionPilot.Forcing.Name

namespace PartitionPilot.Forcing.PosetAction

open SetRealization
universe u v
variable {G : Type v} [Group G] {P : Type u} [PartialOrder P]
variable (a : PosetAction G P) (s : Presentation P)

theorem act_selectName (g : G) (R R' : Name s → P → Prop)
    (transport : ∀ σ p, R' (a.act s g σ) (a.iso g p) ↔ R σ p) (τ : Name s) :
    a.act s g (Name.selectName R τ) = Name.selectName R' (a.act s g τ) := by
  apply Name.ext
  intro σ p
  obtain ⟨σ, rfl⟩ := (a.nameEquiv s g).surjective σ
  obtain ⟨p, rfl⟩ := (a.iso g).surjective p
  change Name.Entry (a.act s g σ) (a.act s g (Name.selectName R τ)) (a.iso g p) ↔
    Name.Entry (a.act s g σ) (Name.selectName R' (a.act s g τ)) (a.iso g p)
  rw [a.entry_act, Name.entry_selectName, Name.entry_selectName]
  constructor
  · rintro ⟨r, entry, pr, hR⟩
    exact ⟨a.iso g r, (a.entry_act s g σ τ r).2 entry,
      (a.iso g).monotone pr, (transport σ p).2 hR⟩
  · rintro ⟨r, entry, pr, hR⟩
    obtain ⟨r, rfl⟩ := (a.iso g).surjective r
    exact ⟨r, (a.entry_act s g σ τ r).1 entry, (a.iso g).le_iff_le.1 pr, (transport σ p).1 hR⟩

end PartitionPilot.Forcing.PosetAction

end


namespace PartitionPilot.Forcing.Name

open SetRealization SetFormula
universe u
variable {P : Type u} [Preorder P] {s : Presentation P}

def separationPredicate (D : NameDomain s) {n : Nat} (φ : SetFormula (n + 1))
    (env : Assignment D n) (σ : Name s) (p : P) : Prop :=
  ∃ h : σ ∈ D.names, Forces D φ (extend ⟨σ, h⟩ env) p

noncomputable def separationName (D : NameDomain s) {n : Nat} (φ : SetFormula (n + 1))
    (env : Assignment D n) (τ : Name s) : Name s := selectName (separationPredicate D φ env) τ

theorem entry_separationName (D : NameDomain s) {n : Nat} (φ : SetFormula (n + 1))
    (env : Assignment D n) (τ σ : Name s) (p : P) :
    Entry σ (separationName D φ env τ) p ↔
      ∃ r, Entry σ τ r ∧ p ≤ r ∧ ∃ h : σ ∈ D.names, Forces D φ (extend ⟨σ, h⟩ env) p := by
  rw [separationName, entry_selectName]
  rfl

theorem eval_separationName (D : NameDomain s) (H : ConditionFilter P)
    (generic : H.GenericFor (formulaFamily D)) {n : Nat} (φ : SetFormula (n + 1))
    (env : Assignment D n) {τ : Name s} (hτ : τ ∈ D.names) :
    eval {p | H.mem p} (separationName D φ env τ) =
      ZFSet.sep (fun x => Realize (D.values {p | H.mem p}) φ
        (extend x (evalAssignment {p | H.mem p} env))) (eval {p | H.mem p} τ) := by
  apply ZFSet.ext
  intro x
  rw [mem_eval, ZFSet.mem_sep]
  constructor
  · rintro ⟨σ, p, entry, hp, value⟩
    obtain ⟨r, old, pr, hσ, forced⟩ := (entry_separationName D φ env τ σ p).1 entry
    have truth := forces_sound D H generic φ (extend ⟨σ, hσ⟩ env) hp forced
    rw [evalAssignment_extend, value] at truth
    exact ⟨(mem_eval _ τ x).2 ⟨σ, r, old, H.upward hp pr, value⟩, truth⟩
  · rintro ⟨member, truth⟩
    obtain ⟨σ, r, entry, hr, value⟩ := (mem_eval _ τ x).1 member
    have hσ := D.children hτ entry
    have instanceTruth : Realize (D.values {p | H.mem p}) φ
        (evalAssignment {p | H.mem p} (extend ⟨σ, hσ⟩ env)) := by
      rw [evalAssignment_extend, value]
      exact truth
    obtain ⟨q, hq, forced⟩ := (forcing_truth D H generic φ (extend ⟨σ, hσ⟩ env)).1 instanceTruth
    obtain ⟨p, hp, pr, pq⟩ := H.directed hr hq
    exact ⟨σ, p, (entry_separationName D φ env τ σ p).2
      ⟨r, entry, pr, hσ, forces_mono D φ (extend ⟨σ, hσ⟩ env) forced pq⟩, hp, value⟩

end PartitionPilot.Forcing.Name



namespace PartitionPilot.Forcing.PosetAction

open SetRealization Compression.RecursiveMaps
universe u v
variable {G : Type v} [Group G] [Small.{u} G] {P : Type u} [PartialOrder P]
variable (a : PosetAction G P) (s : Presentation P)

def MixIndices (K : Subgroup G) (p : P) (τ : Name s) :=
  {z : K × Name.Entries τ × P //
    z.2.2 ≤ a.iso z.1.val p ∧ z.2.2 ≤ a.iso z.1.val z.2.1.val.2}

instance mixIndices_small (K : Subgroup G) (p : P) (τ : Name s) :
    Small.{u} (a.MixIndices s K p τ) := by
  unfold MixIndices
  infer_instance

noncomputable def mix (K : Subgroup G) (p : P) (τ : Name s) : Name s :=
  Name.assemble (fun z : a.MixIndices s K p τ => a.act s z.val.1.val z.val.2.1.val.1)
    (fun z => z.val.2.2)

end PartitionPilot.Forcing.PosetAction


section

namespace PartitionPilot.Forcing.Name

open SetRealization
universe u
variable {P : Type u} [Preorder P] {s : Presentation P}

def UnionIndices (τ : Name s) :=
  {z : (Σ e : Entries τ, Entries e.val.1) × P //
    z.2 ≤ z.1.1.val.2 ∧ z.2 ≤ z.1.2.val.2}

instance unionIndices_small (τ : Name s) : Small.{u} (UnionIndices τ) := by
  unfold UnionIndices
  infer_instance

noncomputable def unionName (τ : Name s) : Name s :=
  assemble (fun z : UnionIndices τ => z.val.1.2.val.1) (fun z => z.val.2)

end PartitionPilot.Forcing.Name



namespace PartitionPilot.Forcing.Name

open SetRealization SetFormula
universe u
variable {P : Type u} [Preorder P] {s : Presentation P}

noncomputable def envelope (τ : Name s) : Name s := selectName (fun _ _ => True) τ

end PartitionPilot.Forcing.Name

end


end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Forcing_NameOrbitBounds
attribute [-instance] _root_.OAI.PartitionPilot.Forcing.GroundMainPrefix.withTopSmall
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace PartitionPilot.Forcing.PosetAction

open SetRealization Compression.RecursiveMaps SetFormula
universe u v
variable {G : Type v} [Group G] {P : Type u} [PartialOrder P]
variable (a : PosetAction G P) (s : Presentation P)

theorem separationPredicate_act (D : Name.NameDomain s)
    (closed : ∀ g τ, τ ∈ D.names → a.act s g τ ∈ D.names)
    (g : G) {n : Nat} (φ : SetFormula (n + 1)) (env : Assignment D n) (σ : Name s) (p : P) :
    Name.separationPredicate D φ (a.actAssignment s D closed g env) (a.act s g σ) (a.iso g p) ↔
      Name.separationPredicate D φ env σ p := by
  constructor
  · rintro ⟨movedMem, forced⟩
    have oldMem : σ ∈ D.names := by
      have h := closed g⁻¹ (a.act s g σ) movedMem
      simpa only [a.act_inv_left] using h
    refine ⟨oldMem, (a.formula_forces_act_iff s D closed g φ (extend ⟨σ, oldMem⟩ env) p).1 ?_⟩
    rw [a.actAssignment_extend]
    exact forced
  · rintro ⟨hσ, forced⟩
    refine ⟨closed g σ hσ, ?_⟩
    have h := (a.formula_forces_act_iff s D closed g φ (extend ⟨σ, hσ⟩ env) p).2 forced
    rw [a.actAssignment_extend] at h
    exact h

theorem act_separationName (D : Name.NameDomain s)
    (closed : ∀ g τ, τ ∈ D.names → a.act s g τ ∈ D.names)
    (g : G) {n : Nat} (φ : SetFormula (n + 1)) (env : Assignment D n) (τ : Name s) :
    a.act s g (Name.separationName D φ env τ) =
      Name.separationName D φ (a.actAssignment s D closed g env) (a.act s g τ) :=
  a.act_selectName s g (Name.separationPredicate D φ env)
    (Name.separationPredicate D φ (a.actAssignment s D closed g env))
    (a.separationPredicate_act s D closed g φ env) τ

end PartitionPilot.Forcing.PosetAction



namespace PartitionPilot.Forcing.PosetAction

open SetRealization Compression.RecursiveMaps
universe u v
variable {G : Type v} [Group G] {P : Type u} [PartialOrder P]
variable (a : PosetAction G P) (s : Presentation P)

def symmetricDomain (D : Name.NameDomain s) (F : NormalSubgroupFamily G) : Name.NameDomain s where
  names := {τ | τ ∈ D.names ∧ HereditarilySymmetric a s F τ}
  children h entry := ⟨D.children h.1 entry, h.2.member entry⟩

end PartitionPilot.Forcing.PosetAction


section

namespace PartitionPilot.Forcing.Name

open SetRealization
universe u
variable {P : Type u} [Preorder P] {s : Presentation P}

def BoundedNames (D : NameDomain s) (W : ZFSet.{u}) := {σ : D.names // σ.val.val ∈ W}

instance boundedNames_small (D : NameDomain s) (W : ZFSet.{u}) : Small.{u} (BoundedNames D W) := by
  let f : BoundedNames D W → W := fun σ => ⟨σ.val.val.val, σ.property⟩
  apply small_of_injective.{u} (f := f)
  intro σ τ eq
  have raw : σ.val.val.val = τ.val.val.val := congrArg (fun z : W => z.val) eq
  exact Subtype.ext (Subtype.ext (Subtype.ext raw))

noncomputable def codedPower [OrderTop P] (D : NameDomain s) (W : ZFSet.{u}) : Name s :=
  assemble (fun σ : BoundedNames D W => σ.val.val) (fun _ => ⊤)

end PartitionPilot.Forcing.Name

end



namespace PartitionPilot.Forcing.PosetAction

open SetRealization Compression.RecursiveMaps
universe u
variable {G P : Type u} [Group G] [PartialOrder P]
variable (a : PosetAction G P) (s : Presentation P)

noncomputable def orbitCodes (D : Name.NameDomain s) (W : ZFSet.{u}) : ZFSet.{u} :=
  ZFSet.range (fun i : G × Name.BoundedNames D W => (a.act s i.1 i.2.val.val).val)

end PartitionPilot.Forcing.PosetAction

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Definability_UnionEntryFormula
attribute [-instance] _root_.OAI.PartitionPilot.Forcing.GroundMainPrefix.withTopSmall
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI



namespace PartitionPilot.Forcing.TransitiveGround

open SetRealization SetFormula Compression.RecursiveMaps
universe u v
variable (M : TransitiveGround.{u})

variable {P : Type u} (s : Presentation P)

theorem pairName_code (one : P) (σ τ : Name s) :
    (Name.unorderedPair one σ τ).val =
      ({ZFSet.pair σ.val (s.encode one), ZFSet.pair τ.val (s.encode one)} : ZFSet.{u}) := by
  apply ZFSet.ext
  intro z
  change z ∈ ZFSet.range (fun b : Bool => ZFSet.pair (if b then σ else τ).val (s.encode one)) ↔ _
  rw [ZFSet.mem_range, ZFSet.mem_pair]
  constructor
  · rintro ⟨b, eq⟩
    cases b with
    | false => exact Or.inr eq.symm
    | true => exact Or.inl eq.symm
  · rintro (eq | eq)
    · exact ⟨true, eq.symm⟩
    · exact ⟨false, eq.symm⟩

end PartitionPilot.Forcing.TransitiveGround


section

namespace PartitionPilot.Forcing.TransitiveGround

open SetFormula
universe u
variable (M : TransitiveGround.{u})

theorem realize_unorderedPairFormula {n : Nat} (z x y : Fin n)
    (env : Fin n → ZFSet.{u}) (hz : env z ∈ M.sets) (hx : env x ∈ M.sets)
    (hy : env y ∈ M.sets) :
    Realize M.sets (unorderedPairFormula z x y) env ↔ env z = ({env x, env y} : ZFSet.{u}) := by
  simp only [unorderedPairFormula, realize_imp, realize_disj, Realize]
  constructor
  · intro spec
    apply ZFSet.ext
    intro w
    rw [ZFSet.mem_pair]
    constructor
    · intro hw
      exact (spec w (M.transitive hz hw)).1 hw
    · intro hw
      have hwM : w ∈ M.sets := by
        rcases hw with rfl | rfl
        · exact hx
        · exact hy
      exact (spec w hwM).2 hw
  · intro eq w _
    change (w ∈ env z → w = env x ∨ w = env y) ∧
      ((w = env x ∨ w = env y) → w ∈ env z)
    rw [eq]
    exact ⟨ZFSet.mem_pair.1, ZFSet.mem_pair.2⟩

theorem realize_orderedPairFormula
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    {n : Nat} (z x y : Fin n) (env : Fin n → ZFSet.{u})
    (hz : env z ∈ M.sets) (hx : env x ∈ M.sets) (hy : env y ∈ M.sets) :
    Realize M.sets (orderedPairFormula z x y) env ↔ env z = ZFSet.pair (env x) (env y) := by
  simp only [orderedPairFormula, realize_ex]
  constructor
  · rintro ⟨a, ha, b, hb, shape, left, right⟩
    have hzab := (M.realize_unorderedPairFormula z.succ.succ 1 0 _ hz ha hb).1 shape
    have haeq := (M.realize_unorderedPairFormula 1 x.succ.succ x.succ.succ _ ha hx hx).1 left
    have hbeq := (M.realize_unorderedPairFormula 0 x.succ.succ y.succ.succ _ hb hx hy).1 right
    change env z = ({a, b} : ZFSet.{u}) at hzab
    change a = ({env x, env x} : ZFSet.{u}) at haeq
    change b = ({env x, env y} : ZFSet.{u}) at hbeq
    rw [haeq, hbeq, ZFSet.pair_eq_singleton] at hzab
    exact hzab
  · intro eq
    have ha := M.unorderedPair_mem pairing hx hx
    have hb := M.unorderedPair_mem pairing hx hy
    refine ⟨{env x, env x}, ha, {env x, env y}, hb, ?_, ?_, ?_⟩
    · apply (M.realize_unorderedPairFormula z.succ.succ 1 0 _ hz ha hb).2
      change env z = ({{env x, env x}, {env x, env y}} : ZFSet.{u})
      simpa only [ZFSet.pair, ZFSet.pair_eq_singleton] using eq
    · exact (M.realize_unorderedPairFormula 1 x.succ.succ x.succ.succ _ ha hx hx).2 rfl
    · exact (M.realize_unorderedPairFormula 0 x.succ.succ y.succ.succ _ hb hx hy).2 rfl

theorem realize_pairMembershipFormula
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    {n : Nat} (x y z : Fin n) (env : Fin n → ZFSet.{u})
    (hx : env x ∈ M.sets) (hy : env y ∈ M.sets) (hz : env z ∈ M.sets) :
    Realize M.sets (pairMembershipFormula x y z) env ↔ ZFSet.pair (env x) (env y) ∈ env z := by
  simp only [pairMembershipFormula, realize_ex]
  constructor
  · rintro ⟨w, hw, shape, member⟩
    have eq := (M.realize_orderedPairFormula pairing 0 x.succ y.succ _ hw hx hy).1 shape
    change w = ZFSet.pair (env x) (env y) at eq
    change w ∈ env z at member
    exact eq ▸ member
  · intro member
    have hw := M.transitive hz member
    exact ⟨ZFSet.pair (env x) (env y), hw,
      (M.realize_orderedPairFormula pairing 0 x.succ y.succ _ hw hx hy).2 rfl, member⟩

end PartitionPilot.Forcing.TransitiveGround

end



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

instance omegaMembers_countable : Countable (SetRealization.SetMembers ZFSet.omega.{u}) := by
  let f (n : Nat) := SetRealization.SetMembers.ofMem (natSetCode n) (natSetCode_mem_omega n)
  have onto : Function.Surjective f := by
    intro x
    obtain ⟨n, eq⟩ := (mem_omega_iff_natSetCode _).1 (SetRealization.SetMembers.raw_mem x)
    refine ⟨n, SetRealization.SetMembers.raw_injective _ ?_⟩
    exact (SetRealization.SetMembers.raw_ofMem _ _).trans eq.symm
  exact onto.countable

end PartitionPilot.Forcing

end

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

section

namespace PartitionPilot.SetRealization

universe u

theorem ordinalCode_nat (n : Nat) : ordinalCode (n : Ordinal.{u}) = Forcing.natSetCode n := by
  induction n with
  | zero => exact ordinalCode_zero
  | succ n ih =>
    rw [Nat.cast_add_one, ← Order.succ_eq_add_one, ordinalCode_succ, ih]
    rfl

theorem ordinalCode_omega : ordinalCode Ordinal.omega0 = ZFSet.omega.{u} := by
  apply ZFSet.ext
  intro x
  rw [mem_ordinalCode, Forcing.mem_omega_iff_natSetCode]
  constructor
  · rintro ⟨o, ho, eq⟩
    obtain ⟨n, rfl⟩ := Ordinal.lt_omega0.1 ho
    exact ⟨n, eq.symm.trans (ordinalCode_nat n)⟩
  · rintro ⟨n, rfl⟩
    exact ⟨n, Ordinal.natCast_lt_omega0 n, ordinalCode_nat n⟩

end PartitionPilot.SetRealization

end



namespace PartitionPilot.Forcing

open scoped ZFSet
universe u

def OrdinalRecursionTrace (R : ZFSet.{u} → ZFSet.{u} → ZFSet.{u} → Prop)
    (A f : ZFSet.{u}) : Prop :=
  FunctionGraphOn A f ∧ ∀ β ∈ A, ∀ y, ZFSet.pair β y ∈ f → R β (graphRestriction β f) y

end PartitionPilot.Forcing

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



namespace PartitionPilot.Forcing

universe u

namespace TransitiveGround

open SetFormula
variable (M : TransitiveGround.{u})

theorem realize_exactSetFormula {n} (output : Fin n) (entry : SetFormula (n + 1))
    (env : Fin n → ZFSet.{u}) {target : ZFSet.{u}}
    (hOutput : env output ∈ M.sets) (elements : ∀ z ∈ target, z ∈ M.sets)
    (meaning : ∀ z ∈ M.sets, Realize M.sets entry (extend z env) ↔ z ∈ target) :
    Realize M.sets (exactSetFormula output entry) env ↔ env output = target := by
  change (∀ z ∈ M.sets, Realize M.sets
    (.conj (imp (.mem 0 output.succ) entry) (imp entry (.mem 0 output.succ))) (extend z env)) ↔ _
  simp only [Realize, realize_imp]
  change (∀ z ∈ M.sets, (z ∈ env output → Realize M.sets entry (extend z env)) ∧
    (Realize M.sets entry (extend z env) → z ∈ env output)) ↔ _
  constructor
  · intro correct
    apply ZFSet.ext
    intro z
    constructor
    · intro member
      have hz := M.transitive hOutput member
      exact (meaning z hz).1 ((correct z hz).1 member)
    · intro member
      have hz := elements z member
      exact (correct z hz).2 ((meaning z hz).2 member)
  · intro equal z hz
    exact ⟨fun member => (meaning z hz).2 (equal ▸ member),
      fun predicate => equal.symm ▸ (meaning z hz).1 predicate⟩

end TransitiveGround

end PartitionPilot.Forcing



end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Definability_DecodedFunctionGraphs
attribute [-instance] _root_.OAI.PartitionPilot.Forcing.GroundMainPrefix.withTopSmall
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PartitionPilot.SetRealization.Presentation

universe u
variable {A B : Type u} (s : Presentation A) (t : Presentation B)

theorem graph_decodeFunction (f : ZFSet.{u}) (h : ZFSet.IsFunc s.carrier t.carrier f) :
    s.graph t (s.decodeFunction t f h) = f := by
  apply ZFSet.ext
  intro z
  constructor
  · intro hz
    obtain ⟨a, eq⟩ := (s.mem_graph t (s.decodeFunction t f h) z).1 hz
    exact eq ▸ s.decodeFunction_mem t f h a
  · intro hz
    obtain ⟨x, hx, y, hy, eq⟩ := ZFSet.mem_prod.1 (h.1 hz)
    obtain ⟨a, rfl⟩ := (s.mem_carrier x).1 hx
    obtain ⟨b, rfl⟩ := (t.mem_carrier y).1 hy
    rw [eq, s.pair_mem_graph]
    exact (s.decodeFunction_iff t f h a b).2 (eq ▸ hz)

end PartitionPilot.SetRealization.Presentation

end

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

noncomputable def definable_product
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets) :
    GroundDefinableFunction M (fun env : Fin 2 → ZFSet.{u} => ZFSet.prod (env 0) (env 1)) where
  formula := exactSetFormula 0 (BoundedFormula.productElementFormula 0 2 3).toFormula
  closed := fun _ members => M.prod_mem pairing unions powers separation (members 0) (members 1)
  correct := by
    intro env members z hz
    have ground := M.prod_mem pairing unions powers separation (members 0) (members 1)
    apply M.realize_exactSetFormula 0 _ (extend z env) hz (fun _ h => M.transitive ground h)
    intro w hw
    exact (BoundedFormula.realize_toFormula M _ _ (Fin.cases hw (Fin.cases hz members))).trans
      (BoundedFormula.truth_productElementFormula 0 2 3 _)

end PartitionPilot.Forcing.TransitiveGround



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

theorem nonemptyTupleCode_injective (k : Nat) : Function.Injective (nonemptyTupleCode.{u} k) := by
  induction k with
  | zero =>
    intro fields fields' equal
    funext i
    exact Fin.cases equal (fun j => Fin.elim0 j) i
  | succ k ih =>
    intro fields fields' equal
    obtain ⟨head, tail⟩ := ZFSet.pair_inj.1 equal
    have same := ih tail
    funext i
    exact Fin.cases head (fun j => congrFun same j) i

namespace TransitiveGround

open SetFormula
variable (M : TransitiveGround.{u})

theorem nonemptyTupleCode_mem (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (k : Nat) (fields : Fin (k + 1) → ZFSet.{u}) (ground : ∀ i, fields i ∈ M.sets) :
    nonemptyTupleCode k fields ∈ M.sets := by
  induction k with
  | zero => exact ground 0
  | succ k ih => exact M.orderedPair_mem pairing (ground 0) (ih _ (fun i => ground i.succ))

theorem nonemptyTupleCode_field_mem (k : Nat) (fields : Fin (k + 1) → ZFSet.{u})
    (ground : nonemptyTupleCode k fields ∈ M.sets) : ∀ i, fields i ∈ M.sets := by
  induction k with
  | zero => exact Fin.cases ground (fun i => Fin.elim0 i)
  | succ k ih =>
    have pairGround : ZFSet.pair (fields 0) (nonemptyTupleCode k (fun i => fields i.succ)) ∈ M.sets := ground
    have both : ({fields 0, nonemptyTupleCode k (fun i => fields i.succ)} : ZFSet.{u}) ∈ M.sets :=
      M.transitive pairGround (ZFSet.mem_pair.2 (Or.inr rfl))
    have head := M.transitive both (ZFSet.mem_pair.2 (Or.inl rfl))
    have tail := M.transitive both (ZFSet.mem_pair.2 (Or.inr rfl))
    exact Fin.cases head (ih _ tail)

end TransitiveGround

end PartitionPilot.Forcing



namespace PartitionPilot.Forcing.TransitiveGround
open SetFormula
universe u
variable (M : TransitiveGround.{u})

theorem refinementIndexBound_mem (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    {L P V W : ZFSet.{u}} (hL : L ∈ M.sets) (hP : P ∈ M.sets)
    (hV : V ∈ M.sets) (hW : W ∈ M.sets) : refinementIndexBound L P V W ∈ M.sets :=
  M.prod_mem pairing unions powers separation hL
    (M.prod_mem pairing unions powers separation hP
      (M.prod_mem pairing unions powers separation hP
        (M.prod_mem pairing unions powers separation hV
          (M.prod_mem pairing unions powers separation hW hW))))

end PartitionPilot.Forcing.TransitiveGround



namespace PartitionPilot.Forcing
open SetFormula
universe u

noncomputable def refinementIndexFieldGraph (I B : ZFSet.{u}) (j : Fin 6) : ZFSet.{u} :=
  ZFSet.sep (fun z => ∃ fields : Fin 6 → ZFSet.{u},
    nonemptyTupleCode 5 fields ∈ I ∧ z = ZFSet.pair (nonemptyTupleCode 5 fields) (fields j))
      (ZFSet.prod I B)

theorem pair_mem_refinementIndexFieldGraph (I B x y : ZFSet.{u}) (j : Fin 6) :
    ZFSet.pair x y ∈ refinementIndexFieldGraph I B j ↔
      x ∈ I ∧ y ∈ B ∧ ∃ fields : Fin 6 → ZFSet.{u}, x = nonemptyTupleCode 5 fields ∧ y = fields j := by
  rw [refinementIndexFieldGraph, ZFSet.mem_sep, ZFSet.pair_mem_prod]
  constructor
  · rintro ⟨⟨hx, hy⟩, fields, _, eq⟩
    exact ⟨hx, hy, fields, ZFSet.pair_inj.1 eq⟩
  · rintro ⟨hx, hy, fields, rfl, rfl⟩
    exact ⟨⟨hx, hy⟩, fields, hx, rfl⟩

theorem refinementIndexFieldGraph_entry (I B : ZFSet.{u}) (fields : Fin 6 → ZFSet.{u})
    (j : Fin 6) (y : ZFSet.{u}) :
    ZFSet.pair (nonemptyTupleCode 5 fields) y ∈ refinementIndexFieldGraph I B j ↔
      nonemptyTupleCode 5 fields ∈ I ∧ y ∈ B ∧ y = fields j := by
  rw [pair_mem_refinementIndexFieldGraph]
  constructor
  · rintro ⟨hi, hy, fields', equal, value⟩
    have same := nonemptyTupleCode_injective 5 equal
    exact ⟨hi, hy, value.trans (congrFun same j).symm⟩
  · rintro ⟨hi, hy, value⟩
    exact ⟨hi, hy, fields, rfl, value⟩

theorem refinementIndexFieldGraph_function (I B : ZFSet.{u}) (j : Fin 6)
    (fields : ∀ x ∈ I, ∃ v : Fin 6 → ZFSet.{u}, x = nonemptyTupleCode 5 v ∧ v j ∈ B) :
    ZFSet.IsFunc I B (refinementIndexFieldGraph I B j) := by
  refine ⟨fun _ hz => (ZFSet.mem_sep.1 hz).1, ?_⟩
  intro x hx
  obtain ⟨v, rfl, hv⟩ := fields x hx
  refine ⟨v j, (refinementIndexFieldGraph_entry I B v j _).2 ⟨hx, hv, rfl⟩, ?_⟩
  intro y hy
  exact ((refinementIndexFieldGraph_entry I B v j y).1 hy).2.2

namespace SetFormula

def refinementIndexFieldFormula {n} (z I : Fin n) (j : Fin 6) : SetFormula n :=
  let old := suffixIndex n 7
  let w := prefixIndex n 7
  exBlock 7 (.conj (.mem (w 0) (old I))
    (.conj (BoundedFormula.nonemptyTupleFormula 5 (w 0) (fun k => w k.succ)).toFormula
      (BoundedFormula.orderedPairFormula (old z) (w 0) (w j.succ)).toFormula))

end SetFormula

end PartitionPilot.Forcing



namespace PartitionPilot.Forcing
open SetFormula
open scoped ZFSet
universe u

namespace TransitiveGround
variable (M : TransitiveGround.{u})
theorem tupleFieldBound_mem
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (k : Nat) {B : ZFSet.{u}} (ground : B ∈ M.sets) : tupleFieldBound k B ∈ M.sets := by
  induction k generalizing B with
  | zero => exact ground
  | succ k ih =>
    have hB := M.union_mem unions (M.union_mem unions ground)
    exact M.binary_union_mem pairing unions hB (ih hB)

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





namespace SetFormula
def relationCompositionCodeFormula : SetFormula 6 :=
  exactSetFormula 0 (BoundedFormula.composeEntryFormula 0 2 3 4 5 6).toFormula

end SetFormula

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



namespace PartitionPilot.Forcing

universe u v w

theorem pair_mem_constantFamilyGraph (I x i y : ZFSet.{u}) :
    ZFSet.pair i y ∈ constantFamilyGraph I x ↔ i ∈ I ∧ y = x := by
  rw [constantFamilyGraph, ZFSet.pair_mem_prod, ZFSet.mem_singleton]

theorem constantFamilyGraph_function (I x : ZFSet.{u}) :
    ZFSet.IsFunc I {x} (constantFamilyGraph I x) := by
  refine ⟨fun _ h => h, ?_⟩
  intro i hi
  exact ⟨x, (pair_mem_constantFamilyGraph I x i x).2 ⟨hi, rfl⟩,
    fun y entry => ((pair_mem_constantFamilyGraph I x i y).1 entry).2⟩

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

open SetRealization
open scoped ZFSet
universe u
variable {P : Type u} {s : Presentation P}

def grandchildrenBound (τ : Name s) : ZFSet.{u} := ⋃₀ (⋃₀ (⋃₀ (⋃₀ (⋃₀ τ.val))))

theorem isName_of_pair_mem (τ : Name s) (x : ZFSet.{u}) (p : P)
    (entry : ZFSet.pair x (s.encode p) ∈ τ.val) : IsName s x := by
  have property := τ.property
  cases property with
  | mk _ children => exact children x p entry

end PartitionPilot.Forcing.Name

end


namespace PartitionPilot.Forcing.TransitiveGround

open SetRealization SetFormula
universe u
variable (M : TransitiveGround.{u}) {P : Type u} (s : Presentation P)

theorem realize_allConditions {n : Nat} (c : Fin n) (φ : SetFormula (n + 1))
    (env : Fin n → ZFSet.{u}) (carrier : s.carrier ∈ M.sets) (code : env c = s.carrier) :
    Realize M.sets (allConditions c φ) env ↔
      ∀ p : P, Realize M.sets φ (extend (s.encode p) env) := by
  simp only [allConditions, Realize, realize_imp]
  change (∀ x ∈ M.sets, x ∈ env c → Realize M.sets φ (extend x env)) ↔ _
  rw [code]
  constructor
  · intro h p
    exact h (s.encode p) (M.transitive carrier (s.encode_mem p)) (s.encode_mem p)
  · intro h x _ hx
    obtain ⟨p, rfl⟩ := (s.mem_carrier x).1 hx
    exact h p

theorem realize_exConditions {n : Nat} (c : Fin n) (φ : SetFormula (n + 1))
    (env : Fin n → ZFSet.{u}) (carrier : s.carrier ∈ M.sets) (code : env c = s.carrier) :
    Realize M.sets (exConditions c φ) env ↔
      ∃ p : P, Realize M.sets φ (extend (s.encode p) env) := by
  simp only [exConditions, realize_ex]
  change (∃ x ∈ M.sets, x ∈ env c ∧ Realize M.sets φ (extend x env)) ↔ _
  rw [code]
  constructor
  · rintro ⟨x, _, hx, h⟩
    obtain ⟨p, rfl⟩ := (s.mem_carrier x).1 hx
    exact ⟨p, h⟩
  · rintro ⟨p, h⟩
    exact ⟨s.encode p, M.transitive carrier (s.encode_mem p), s.encode_mem p, h⟩

end PartitionPilot.Forcing.TransitiveGround

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Forcing_GroundCompleteProjectionGenericity
attribute [-instance] _root_.OAI.PartitionPilot.Forcing.GroundMainPrefix.withTopSmall
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace PartitionPilot.Forcing

namespace TransitiveGround

open SetRealization SetFormula Compression.RecursiveMaps
universe u v
variable (M : TransitiveGround.{u}) {P : Type u} (s : Presentation P)

def codedFamily : Set (Set P) := (fun x : ZFSet.{u} => {p | s.encode p ∈ x}) '' M.sets

end TransitiveGround



end PartitionPilot.Forcing

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

theorem smallFunction_le_iff (X Y N : ZFSet.{u})
    (p q : SetMembers (M.smallPartialFunctions X Y N)) :
    letI _smallOrder := M.smallFunctionOrder X Y N
    p ≤ q ↔ SetMembers.raw q ⊆ SetMembers.raw p := by
  let smallOrder := M.smallFunctionOrder X Y N
  change ZFSet.pair (SetMembers.raw p) (SetMembers.raw q) ∈
    reverseInclusionCode (M.smallPartialFunctions X Y N) ↔ _
  rw [pair_mem_reverseInclusionCode]
  exact ⟨fun h => h.2.2, fun h => ⟨SetMembers.raw_mem p, SetMembers.raw_mem q, h⟩⟩

theorem smallFunction_raw_properties (X Y N : ZFSet.{u})
    (p : SetMembers (M.smallPartialFunctions X Y N)) :
    SetMembers.raw p ∈ M.sets ∧ PartialFunctionCode X Y (SetMembers.raw p) ∧
      M.groundEmbeddable (SetMembers.raw p) N :=
  (M.mem_smallPartialFunctions X Y N _).1 (SetMembers.raw_mem p)

end PartitionPilot.Forcing.TransitiveGround


section

namespace PartitionPilot.SetRealization.Presentation

open Forcing
universe u
variable {A B : Type u} (s : Presentation A) (t : Presentation B)

theorem relation_ext {p q : ZFSet.{u}} (hp : p ⊆ ZFSet.prod s.carrier t.carrier)
    (hq : q ⊆ ZFSet.prod s.carrier t.carrier)
    (entries : ∀ a b, ZFSet.pair (s.encode a) (t.encode b) ∈ p ↔
      ZFSet.pair (s.encode a) (t.encode b) ∈ q) : p = q := by
  apply ZFSet.ext
  intro z
  constructor
  · intro hz
    obtain ⟨x, hx, y, hy, rfl⟩ := ZFSet.mem_prod.1 (hp hz)
    obtain ⟨a, rfl⟩ := (s.mem_carrier x).1 hx
    obtain ⟨b, rfl⟩ := (t.mem_carrier y).1 hy
    exact (entries a b).1 hz
  · intro hz
    obtain ⟨x, hx, y, hy, rfl⟩ := ZFSet.mem_prod.1 (hq hz)
    obtain ⟨a, rfl⟩ := (s.mem_carrier x).1 hx
    obtain ⟨b, rfl⟩ := (t.mem_carrier y).1 hy
    exact (entries a b).2 hz

theorem converse_graph (e : A ≃ B) :
    relationConverse s.carrier t.carrier (s.graph t e) = t.graph s e.symm := by
  apply t.relation_ext s (fun _ hz => (ZFSet.mem_sep.1 hz).1) (t.graph_isFunc s e.symm).1
  intro b a
  change ZFSet.pair (t.encode b) (s.encode a) ∈ relationConverse s.carrier t.carrier (s.graph t e) ↔ _
  rw [pair_mem_relationConverse, s.pair_mem_graph, t.pair_mem_graph]
  exact ⟨fun h => (congrArg e.symm h.2.2).symm.trans (e.symm_apply_apply a),
    fun eq => ⟨s.encode_mem a, t.encode_mem b, by rw [← eq, e.apply_symm_apply]⟩⟩

end PartitionPilot.SetRealization.Presentation

namespace PartitionPilot.Forcing

open SetRealization
universe u
variable {X Y : Type u} (s : Presentation X) (t : Presentation Y)

noncomputable def graphRename (e : X ≃ X) (p : ZFSet.{u}) : ZFSet.{u} :=
  (s.product t).subset (fun xy => ZFSet.pair (s.encode (e.symm xy.1)) (t.encode xy.2) ∈ p)

theorem pair_mem_graphRename (e : X ≃ X) (p : ZFSet.{u}) (x : X) (y : Y) :
    ZFSet.pair (s.encode x) (t.encode y) ∈ graphRename s t e p ↔
      ZFSet.pair (s.encode (e.symm x)) (t.encode y) ∈ p :=
  (s.product t).encode_mem_subset _ (x, y)

theorem graphRename_shape (e : X ≃ X) (p : ZFSet.{u}) :
    graphRename s t e p ⊆ ZFSet.prod s.carrier t.carrier := (s.product t).subset_carrier _

theorem graphRename_partial (e : X ≃ X) {p : ZFSet.{u}} (h : PartialFunctionCode s.carrier t.carrier p) :
    PartialFunctionCode s.carrier t.carrier (graphRename s t e p) := by
  refine ⟨graphRename_shape s t e p, ?_⟩
  intro x y z hy hz
  have xy := ZFSet.pair_mem_prod.1 (graphRename_shape s t e p hy)
  have xz := ZFSet.pair_mem_prod.1 (graphRename_shape s t e p hz)
  obtain ⟨a, rfl⟩ := (s.mem_carrier x).1 xy.1
  obtain ⟨b, rfl⟩ := (t.mem_carrier y).1 xy.2
  obtain ⟨c, rfl⟩ := (t.mem_carrier z).1 xz.2
  exact h.unique _ _ _ ((pair_mem_graphRename s t e p a b).1 hy)
    ((pair_mem_graphRename s t e p a c).1 hz)

theorem graphRename_refl {p : ZFSet.{u}} (shape : p ⊆ ZFSet.prod s.carrier t.carrier) :
    graphRename s t (Equiv.refl X) p = p := by
  apply s.relation_ext t (graphRename_shape s t _ p) shape
  intro x y
  exact pair_mem_graphRename s t _ p x y

theorem graphRename_comp (e f : X ≃ X) (p : ZFSet.{u}) :
    graphRename s t f (graphRename s t e p) = graphRename s t (e.trans f) p := by
  apply s.relation_ext t (graphRename_shape s t _ _) (graphRename_shape s t _ _)
  intro x y
  rw [pair_mem_graphRename, pair_mem_graphRename, pair_mem_graphRename]
  rfl

theorem graphRename_inverse (e : X ≃ X) {p : ZFSet.{u}}
    (shape : p ⊆ ZFSet.prod s.carrier t.carrier) :
    graphRename s t e.symm (graphRename s t e p) = p := by
  apply s.relation_ext t (graphRename_shape s t _ _) shape
  intro x y
  rw [pair_mem_graphRename, pair_mem_graphRename]
  change ZFSet.pair (s.encode (e.symm (e x))) (t.encode y) ∈ p ↔ _
  rw [e.symm_apply_apply]

theorem graphRename_mono (e : X ≃ X) {p q : ZFSet.{u}} (subset : p ⊆ q) :
    graphRename s t e p ⊆ graphRename s t e q := by
  intro z hz
  obtain ⟨⟨x, y⟩, rel, rfl⟩ := ((s.product t).mem_subset _ z).1 hz
  exact (pair_mem_graphRename s t e q x y).2 (subset rel)

end PartitionPilot.Forcing



end


end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Forcing_GroundFixedPoints
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

theorem realize_postfixedFormula {k : Nat} (φ : SetFormula (k + 2))
    (params : Fin k → ZFSet.{u}) {B S : ZFSet.{u}}
    (hS : S ∈ M.sets) (bound : S ⊆ B) :
    Realize M.sets (postfixedFormula φ) (extend S params) ↔
      S ⊆ definableOperator M.sets φ params B S := by
  simp only [postfixedFormula, Realize, realize_imp]
  constructor
  · intro h x hx
    exact ZFSet.mem_sep.2 ⟨bound hx, h x (M.transitive hS hx) hx⟩
  · intro h x _ hx
    exact (ZFSet.mem_sep.1 (h hx)).2

theorem definableOperator_mem (separation : SeparationSchema M.sets)
    {k : Nat} (φ : SetFormula (k + 2)) (params : Fin k → ZFSet.{u})
    (members : ∀ i, params i ∈ M.sets) {B S : ZFSet.{u}}
    (hB : B ∈ M.sets) (hS : S ∈ M.sets) : definableOperator M.sets φ params B S ∈ M.sets :=
  M.separation_mem separation φ (extend S params) (fun i => Fin.cases hS members i) hB

theorem exists_greatest_definable_fixedPoint
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    {k : Nat} (φ : SetFormula (k + 2)) (params : Fin k → ZFSet.{u})
    (members : ∀ i, params i ∈ M.sets) {B : ZFSet.{u}} (hB : B ∈ M.sets)
    (mono : ∀ S ∈ M.sets, ∀ T ∈ M.sets, S ⊆ B → T ⊆ B → S ⊆ T →
      definableOperator M.sets φ params B S ⊆ definableOperator M.sets φ params B T) :
    ∃ R ∈ M.sets, R ⊆ B ∧ definableOperator M.sets φ params B R = R ∧
      ∀ S ∈ M.sets, S ⊆ B → S ⊆ definableOperator M.sets φ params B S → S ⊆ R := by
  let F := definableOperator M.sets φ params B
  obtain ⟨W, hW, subsets⟩ := M.power_witness powers hB
  let C := ZFSet.sep (fun S => Realize M.sets (postfixedFormula φ) (extend S params)) W
  have hC : C ∈ M.sets := M.separation_mem separation (postfixedFormula φ) params members hW
  let R := ZFSet.sUnion C
  have hR : R ∈ M.sets := M.union_mem unions hC
  have memC : ∀ S, S ∈ C ↔ S ∈ M.sets ∧ S ⊆ B ∧ S ⊆ F S := by
    intro S
    constructor
    · intro h
      obtain ⟨hSW, post⟩ := ZFSet.mem_sep.1 h
      have hSM := M.transitive hW hSW
      have hSB := (subsets S hSM).1 hSW
      exact ⟨hSM, hSB, (M.realize_postfixedFormula φ params hSM hSB).1 post⟩
    · rintro ⟨hSM, hSB, post⟩
      exact ZFSet.mem_sep.2 ⟨(subsets S hSM).2 hSB,
        (M.realize_postfixedFormula φ params hSM hSB).2 post⟩
  have hRB : R ⊆ B := by
    intro x hx
    obtain ⟨S, hS, hxS⟩ := ZFSet.mem_sUnion.1 hx
    exact ((memC S).1 hS).2.1 hxS
  have greatest : ∀ S ∈ M.sets, S ⊆ B → S ⊆ F S → S ⊆ R := by
    intro S hS hSB post x hx
    exact ZFSet.mem_sUnion.2 ⟨S, (memC S).2 ⟨hS, hSB, post⟩, hx⟩
  have postR : R ⊆ F R := by
    intro x hx
    obtain ⟨S, hSC, hxS⟩ := ZFSet.mem_sUnion.1 hx
    obtain ⟨hS, hSB, post⟩ := (memC S).1 hSC
    exact mono S hS R hR hSB hRB (greatest S hS hSB post) (post hxS)
  have hFR : F R ∈ M.sets := M.definableOperator_mem separation φ params members hB hR
  have hFRB : F R ⊆ B := definableOperator_subset M.sets φ params B R
  have postFR : F R ⊆ F (F R) := mono R hR (F R) hFR hRB hFRB postR
  have fixed : F R = R := ZFSet.ext fun _ =>
    ⟨fun hx => greatest (F R) hFR hFRB postFR hx, fun hx => postR hx⟩
  exact ⟨R, hR, hRB, fixed, greatest⟩

end PartitionPilot.Forcing.TransitiveGround

end

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Geometry_AtomicEqualitySteps
attribute [-instance] _root_.OAI.PartitionPilot.Forcing.GroundMainPrefix.withTopSmall _root_.OAI.PartitionPilot.Forcing.Name.boundedNames_small _root_.OAI.PartitionPilot.Forcing.Name.unionIndices_small _root_.OAI.PartitionPilot.Forcing.PosetAction.mixIndices_small
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PartitionPilot.Forcing.Name

open SetRealization
universe u
variable {P : Type u} [Preorder P] {s : Presentation P}

def EqualityStep (R : P → Name s → Name s → Prop) (p : P) (σ τ : Name s) : Prop :=
  (∀ ρ r, Entry ρ σ r → ∀ q, q ≤ p → q ≤ r →
    ∃ t, t ≤ q ∧ ∃ ν k, Entry ν τ k ∧ t ≤ k ∧ R t ρ ν) ∧
  (∀ ν k, Entry ν τ k → ∀ q, q ≤ p → q ≤ k →
    ∃ t, t ≤ q ∧ ∃ ρ r, Entry ρ σ r ∧ t ≤ r ∧ R t ρ ν)

def RelationMembership (R : P → Name s → Name s → Prop) (p : P) (σ τ : Name s) : Prop :=
  ∀ q, q ≤ p → ∃ t, t ≤ q ∧ ∃ ν r, Entry ν τ r ∧ t ≤ r ∧ R t σ ν

theorem forcesEq_step (p : P) (σ τ : Name s) : ForcesEq p σ τ ↔ EqualityStep ForcesEq p σ τ := by
  rw [ForcesEq]
  simp only [EqualityStep, exists_prop]

theorem equalityStep_dense (R : P → Name s → Name s → Prop) (p : P) (σ τ : Name s) :
    EqualityStep R p σ τ ↔
      (∀ ρ r, Entry ρ σ r → ∀ q, q ≤ p → q ≤ r → RelationMembership R q ρ τ) ∧
      (∀ ν k, Entry ν τ k → ∀ q, q ≤ p → q ≤ k →
        RelationMembership (fun t ρ ν => R t ν ρ) q ν σ) := by
  constructor
  · intro h
    exact ⟨fun ρ r hr q qp qr t tq => h.1 ρ r hr t (tq.trans qp) (tq.trans qr),
      fun ν k hk q qp qk t tq => h.2 ν k hk t (tq.trans qp) (tq.trans qk)⟩
  · rintro ⟨left, right⟩
    exact ⟨fun ρ r hr q qp qr => left ρ r hr q qp qr q le_rfl,
      fun ν k hk q qp qk => right ν k hk q qp qk q le_rfl⟩

theorem postfixed_equality_sound (D : NameDomain s) (R : P → Name s → Name s → Prop)
    (post : ∀ σ ∈ D.names, ∀ τ ∈ D.names, ∀ p, R p σ τ → EqualityStep R p σ τ) :
    ∀ σ ∈ D.names, ∀ τ ∈ D.names, ∀ p, R p σ τ → ForcesEq p σ τ := by
  intro σ
  induction σ using inductionOn with
  | step σ ih =>
    intro hσ τ hτ p rel
    have h := post σ hσ τ hτ p rel
    rw [forcesEq_step]
    constructor
    · intro ρ r hr q qp qr
      obtain ⟨t, tq, ν, k, hk, tk, hrel⟩ := h.1 ρ r hr q qp qr
      exact ⟨t, tq, ν, k, hk, tk, ih ρ r hr (D.children hσ hr) ν (D.children hτ hk) t hrel⟩
    · intro ν k hk q qp qk
      obtain ⟨t, tq, ρ, r, hr, tr, hrel⟩ := h.2 ν k hk q qp qk
      exact ⟨t, tq, ρ, r, hr, tr, ih ρ r hr (D.children hσ hr) ν (D.children hτ hk) t hrel⟩

theorem prefixed_equality_complete (D : NameDomain s) (R : P → Name s → Name s → Prop)
    (pre : ∀ σ ∈ D.names, ∀ τ ∈ D.names, ∀ p, EqualityStep R p σ τ → R p σ τ) :
    ∀ σ ∈ D.names, ∀ τ ∈ D.names, ∀ p, ForcesEq p σ τ → R p σ τ := by
  intro σ
  induction σ using inductionOn with
  | step σ ih =>
    intro hσ τ hτ p forced
    have h := (forcesEq_step p σ τ).1 forced
    apply pre σ hσ τ hτ p
    constructor
    · intro ρ r hr q qp qr
      obtain ⟨t, tq, ν, k, hk, tk, hrel⟩ := h.1 ρ r hr q qp qr
      exact ⟨t, tq, ν, k, hk, tk, ih ρ r hr (D.children hσ hr) ν (D.children hτ hk) t hrel⟩
    · intro ν k hk q qp qk
      obtain ⟨t, tq, ρ, r, hr, tr, hrel⟩ := h.2 ν k hk q qp qk
      exact ⟨t, tq, ρ, r, hr, tr, ih ρ r hr (D.children hσ hr) ν (D.children hτ hk) t hrel⟩

theorem fixed_equality_iff (D : NameDomain s) (R : P → Name s → Name s → Prop)
    (fixed : ∀ σ ∈ D.names, ∀ τ ∈ D.names, ∀ p, R p σ τ ↔ EqualityStep R p σ τ)
    {σ τ : Name s} (hσ : σ ∈ D.names) (hτ : τ ∈ D.names) (p : P) :
    R p σ τ ↔ ForcesEq p σ τ :=
  ⟨postfixed_equality_sound D R (fun σ hσ τ hτ p => (fixed σ hσ τ hτ p).1) σ hσ τ hτ p,
    prefixed_equality_complete D R (fun σ hσ τ hτ p => (fixed σ hσ τ hτ p).2) σ hσ τ hτ p⟩

end PartitionPilot.Forcing.Name

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

def RelationMeaning (D : Name.NameDomain s) (R : P → Name s → Name s → Prop) {k : Nat} (E : SetFormula (k + 3))
    (constants : Fin k → ZFSet.{u}) : Prop :=
  ∀ (p : P) (σ τ : D.names),
    Realize M.sets E (extend (s.encode p) (extend σ.val.val (extend τ.val.val constants))) ↔
      R p σ.val τ.val

end PartitionPilot.Forcing.TransitiveGround



end

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Definability_CodedEqualityRelations
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
variable {P : Type u} (s : Presentation P)

def codedEqualityRelation (S : ZFSet.{u}) (p : P) (σ τ : Name s) : Prop :=
  ZFSet.pair (s.encode p) (ZFSet.pair σ.val τ.val) ∈ S

end PartitionPilot.Forcing.Name

namespace PartitionPilot.Forcing.TransitiveGround

open SetRealization SetFormula
universe u
variable (M : TransitiveGround.{u})

theorem realize_tripleMembershipFormula
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    {n : Nat} (p x y r : Fin n) (env : Fin n → ZFSet.{u})
    (hp : env p ∈ M.sets) (hx : env x ∈ M.sets)
    (hy : env y ∈ M.sets) (hr : env r ∈ M.sets) :
    Realize M.sets (tripleMembershipFormula p x y r) env ↔
      ZFSet.pair (env p) (ZFSet.pair (env x) (env y)) ∈ env r := by
  rw [tripleMembershipFormula, realize_ex]
  constructor
  · rintro ⟨z, hz, shape, member⟩
    have eq := (M.realize_orderedPairFormula pairing 0 x.succ y.succ
      (extend z env) hz hx hy).1 shape
    have raw := (M.realize_pairMembershipFormula pairing p.succ 0 r.succ
      (extend z env) hp hz hr).1 member
    change z = ZFSet.pair (env x) (env y) at eq
    change ZFSet.pair (env p) z ∈ env r at raw
    exact eq ▸ raw
  · intro member
    have hz := M.orderedPair_mem pairing hx hy
    refine ⟨ZFSet.pair (env x) (env y), hz, ?_, ?_⟩
    · exact (M.realize_orderedPairFormula pairing 0 x.succ y.succ
        (extend (ZFSet.pair (env x) (env y)) env) hz hx hy).2 rfl
    · exact (M.realize_pairMembershipFormula pairing p.succ 0 r.succ
        (extend (ZFSet.pair (env x) (env y)) env) hp hz hr).2 member

variable {P : Type u} (s : Presentation P)

theorem relationMeaning_coded (D : Name.NameDomain s)
    (ground : ∀ τ ∈ D.names, τ.val ∈ M.sets)
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (carrier : s.carrier ∈ M.sets)
    {k : Nat} (r : Fin k) (constants : Fin k → ZFSet.{u})
    (hr : constants r ∈ M.sets) :
    M.RelationMeaning s D (Name.codedEqualityRelation s (constants r))
      (tripleMembershipFormula 0 1 2 r.succ.succ.succ) constants := by
  intro p σ τ
  exact M.realize_tripleMembershipFormula pairing 0 1 2 r.succ.succ.succ _
    (M.transitive carrier (s.encode_mem p)) (ground σ.val σ.property)
    (ground τ.val τ.property) hr

end PartitionPilot.Forcing.TransitiveGround

end

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Geometry_RawEqualitySteps
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

def RawRelationMeaning {k : Nat} (R : P → ZFSet.{u} → ZFSet.{u} → Prop)
    (E : SetFormula (k + 3)) (constants : Fin k → ZFSet.{u}) : Prop :=
  ∀ p x, x ∈ M.sets → ∀ y, y ∈ M.sets →
    (Realize M.sets E (extend (s.encode p) (extend x (extend y constants))) ↔ R p x y)

def RawMembership (R : P → ZFSet.{u} → ZFSet.{u} → Prop) (p : P) (x y : ZFSet.{u}) : Prop :=
  ∀ q, q ≤ p → ∃ t, t ≤ q ∧ ∃ v ∈ M.sets, ∃ r,
    ZFSet.pair v (s.encode r) ∈ y ∧ t ≤ r ∧ R t x v

def RawMatching (R : P → ZFSet.{u} → ZFSet.{u} → Prop) (p : P) (x y : ZFSet.{u}) : Prop :=
  ∀ v ∈ M.sets, ∀ r, ZFSet.pair v (s.encode r) ∈ x →
    ∀ q, q ≤ p → q ≤ r → M.RawMembership s R q v y

def RawEqualityStep (R : P → ZFSet.{u} → ZFSet.{u} → Prop)
    (p : P) (x y : ZFSet.{u}) : Prop :=
  M.RawMatching s R p x y ∧ M.RawMatching s (fun t v w => R t w v) p y x

theorem rawEqualityStep_mono {R S : P → ZFSet.{u} → ZFSet.{u} → Prop}
    (mono : ∀ p x y, R p x y → S p x y) {p : P} {x y : ZFSet.{u}}
    (h : M.RawEqualityStep s R p x y) : M.RawEqualityStep s S p x y := by
  constructor
  · intro v hv r entry q qp qr t tq
    obtain ⟨a, hat, w, hw, b, eb, ab, rel⟩ := h.1 v hv r entry q qp qr t tq
    exact ⟨a, hat, w, hw, b, eb, ab, mono a v w rel⟩
  · intro v hv r entry q qp qr t tq
    obtain ⟨a, hat, w, hw, b, eb, ab, rel⟩ := h.2 v hv r entry q qp qr t tq
    exact ⟨a, hat, w, hw, b, eb, ab, mono a w v rel⟩

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

theorem realize_orderedTripleFormula
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    {n : Nat} (z p x y : Fin n) (env : Fin n → ZFSet.{u})
    (hz : env z ∈ M.sets) (hp : env p ∈ M.sets)
    (hx : env x ∈ M.sets) (hy : env y ∈ M.sets) :
    Realize M.sets (orderedTripleFormula z p x y) env ↔
      env z = ZFSet.pair (env p) (ZFSet.pair (env x) (env y)) := by
  rw [orderedTripleFormula, realize_ex]
  constructor
  · rintro ⟨w, hw, inner, outer⟩
    have wi := (M.realize_orderedPairFormula pairing 0 x.succ y.succ
      (extend w env) hw hx hy).1 inner
    have zo := (M.realize_orderedPairFormula pairing z.succ p.succ 0
      (extend w env) hz hp hw).1 outer
    change w = ZFSet.pair (env x) (env y) at wi
    change env z = ZFSet.pair (env p) w at zo
    exact wi ▸ zo
  · intro eq
    have hw := M.orderedPair_mem pairing hx hy
    exact ⟨ZFSet.pair (env x) (env y), hw,
      (M.realize_orderedPairFormula pairing 0 x.succ y.succ
        (extend (ZFSet.pair (env x) (env y)) env) hw hx hy).2 rfl,
      (M.realize_orderedPairFormula pairing z.succ p.succ 0
        (extend (ZFSet.pair (env x) (env y)) env) hz hp hw).2 eq⟩

variable {P : Type u} [Preorder P] (s : Presentation P)

def RawCodedRelation (S : ZFSet.{u}) (p : P) (x y : ZFSet.{u}) : Prop :=
  ZFSet.pair (s.encode p) (ZFSet.pair x y) ∈ S

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

open SetFormula
universe u
variable (M : TransitiveGround.{u})

theorem realize_transitiveSetFormula {n : Nat} (t : Fin n) (env : Fin n → ZFSet.{u})
    (ht : env t ∈ M.sets) :
    Realize M.sets (transitiveSetFormula t) env ↔
      ∀ x ∈ env t, ∀ y ∈ x, y ∈ env t := by
  simp only [transitiveSetFormula, realize_imp, Realize]
  constructor
  · intro h x hx y hy
    exact h x (M.transitive ht hx) hx y (M.transitive (M.transitive ht hx) hy) hy
  · intro h x _ hx y _ hy
    exact h x hx y hy

theorem realize_transitiveCoverFormula (x T : ZFSet.{u}) (hT : T ∈ M.sets) :
    Realize M.sets transitiveCoverFormula (extend x (extend T Fin.elim0)) ↔
      x ∈ T ∧ ∀ z ∈ T, ∀ y ∈ z, y ∈ T := by
  change (x ∈ T ∧ Realize M.sets (transitiveSetFormula 1) _) ↔ _
  rw [M.realize_transitiveSetFormula 1 _ hT]
  rfl

theorem exists_transitiveCover
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (separation : SeparationSchema M.sets) (collection : CollectionSchema M.sets) :
    ∀ x ∈ M.sets, ∃ T ∈ M.sets, x ∈ T ∧ ∀ z ∈ T, ∀ y ∈ z, y ∈ T := by
  intro x
  induction x using ZFSet.inductionOn with
  | h x ih =>
    intro hx
    have witnesses : ∀ y ∈ x, ∃ T ∈ M.sets,
        Realize M.sets transitiveCoverFormula (extend y (extend T Fin.elim0)) := by
      intro y hy
      obtain ⟨T, hT, member, trans⟩ := ih y hy (M.transitive hx hy)
      exact ⟨T, hT, (M.realize_transitiveCoverFormula y T hT).2 ⟨member, trans⟩⟩
    obtain ⟨W, hW, covers⟩ := M.collection_witness collection transitiveCoverFormula Fin.elim0
      (fun i => Fin.elim0 i) hx witnesses
    let C := ZFSet.sep (fun T => Realize M.sets (transitiveSetFormula 0) (extend T Fin.elim0)) W
    have hC : C ∈ M.sets := M.separation_mem separation (transitiveSetFormula 0) Fin.elim0
      (fun i => Fin.elim0 i) hW
    have transC : ∀ T ∈ C, ∀ z ∈ T, ∀ y ∈ z, y ∈ T := by
      intro T hTC
      obtain ⟨hTW, spec⟩ := ZFSet.mem_sep.1 hTC
      exact (M.realize_transitiveSetFormula 0 (extend T Fin.elim0) (M.transitive hW hTW)).1 spec
    have included : x ⊆ ZFSet.sUnion C := by
      intro y hy
      obtain ⟨T, hTW, spec⟩ := covers y hy
      have hT := M.transitive hW hTW
      obtain ⟨member, trans⟩ := (M.realize_transitiveCoverFormula y T hT).1 spec
      exact ZFSet.mem_sUnion.2 ⟨T, ZFSet.mem_sep.2 ⟨hTW,
        (M.realize_transitiveSetFormula 0 (extend T Fin.elim0) hT).2 trans⟩, member⟩
    have transU : ∀ z ∈ ZFSet.sUnion C, ∀ y ∈ z, y ∈ ZFSet.sUnion C := by
      intro z hz y hy
      obtain ⟨T, hTC, hzT⟩ := ZFSet.mem_sUnion.1 hz
      exact ZFSet.mem_sUnion.2 ⟨T, hTC, transC T hTC z hzT y hy⟩
    let T := ({x, x} : ZFSet.{u}) ∪ ZFSet.sUnion C
    have hT : T ∈ M.sets := M.binary_union_mem pairing unions
      (M.unorderedPair_mem pairing hx hx) (M.union_mem unions hC)
    refine ⟨T, hT, ZFSet.mem_union.2 (Or.inl (ZFSet.mem_pair.2 (Or.inl rfl))), ?_⟩
    intro z hz y hy
    apply ZFSet.mem_union.2
    apply Or.inr
    rcases ZFSet.mem_union.1 hz with hz | hz
    · rcases ZFSet.mem_pair.1 hz with rfl | rfl
      · exact included hy
      · exact included hy
    · exact transU z hz y hy

theorem exists_pair_transitiveCover
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (separation : SeparationSchema M.sets) (collection : CollectionSchema M.sets)
    {x y : ZFSet.{u}} (hx : x ∈ M.sets) (hy : y ∈ M.sets) :
    ∃ T ∈ M.sets, x ∈ T ∧ y ∈ T ∧ ∀ z ∈ T, ∀ w ∈ z, w ∈ T := by
  obtain ⟨T, hT, pair, trans⟩ := M.exists_transitiveCover pairing unions separation collection
    ({x, y} : ZFSet.{u}) (M.unorderedPair_mem pairing hx hy)
  exact ⟨T, hT, trans _ pair x (ZFSet.mem_pair.2 (Or.inl rfl)),
    trans _ pair y (ZFSet.mem_pair.2 (Or.inr rfl)), trans⟩

end PartitionPilot.Forcing.TransitiveGround

end


namespace PartitionPilot.Forcing.TransitiveGround

open SetRealization SetFormula
universe u
variable (M : TransitiveGround.{u}) {P : Type u} [Preorder P] (s : Presentation P)

def EqualityMeaning (D : Name.NameDomain s) {k : Nat} (E : SetFormula (k + 3))
    (constants : Fin k → ZFSet.{u}) : Prop :=
  ∀ (p : P) (σ τ : D.names),
    Realize M.sets E (extend (s.encode p) (extend σ.val.val (extend τ.val.val constants))) ↔
      Name.ForcesEq p σ.val τ.val

end PartitionPilot.Forcing.TransitiveGround



namespace PartitionPilot.Forcing.TransitiveGround

open SetRealization SetFormula
universe u
variable {P : Type u} (s : Presentation P)

def namesInTransitiveSet (T : ZFSet.{u})
    (trans : ∀ {x y : ZFSet.{u}}, x ∈ T → y ∈ x → y ∈ T) : Name.NameDomain s :=
  nameDomain ⟨{x | x ∈ T}, trans⟩ s

end PartitionPilot.Forcing.TransitiveGround


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


namespace PartitionPilot.Forcing

open SetRealization
universe u
variable {P : Type u} (s : Presentation P)

def NameCodeStep (S x : ZFSet.{u}) : Prop :=
  ∀ z ∈ x, ∃ y ∈ S, ∃ p, z = ZFSet.pair y (s.encode p)

theorem nameCodeStep_mono {S T x : ZFSet.{u}} (sub : S ⊆ T) (h : NameCodeStep s S x) :
    NameCodeStep s T x := by
  intro z hz
  obtain ⟨y, hy, p, shape⟩ := h z hz
  exact ⟨y, sub hy, p, shape⟩

theorem nameCodePostfixed_sound (S : ZFSet.{u}) (post : ∀ x ∈ S, NameCodeStep s S x) :
    ∀ x ∈ S, IsName s x := by
  intro x
  apply (InvImage.wf (fun z : ZFSet.{u} => ZFSet.rank z) wellFounded_lt).induction x
  intro x ih hx
  apply IsName.mk
  · intro z hz
    obtain ⟨y, _, p, shape⟩ := post x hx z hz
    exact ⟨y, p, shape⟩
  · intro y p entry
    obtain ⟨v, hv, q, shape⟩ := post x hx _ entry
    have eq := (ZFSet.pair_inj.1 shape).1
    have hy : y ∈ S := eq ▸ hv
    have lt : ZFSet.rank y < ZFSet.rank x :=
      (ZFSet.rank_lt_of_mem (ZFSet.mem_singleton.2 rfl : y ∈ ({y} : ZFSet.{u}))).trans
        ((ZFSet.rank_lt_of_mem (ZFSet.mem_pair.2 (Or.inl rfl) :
          ({y} : ZFSet.{u}) ∈ ZFSet.pair y (s.encode p))).trans (ZFSet.rank_lt_of_mem entry))
    exact ih y lt hy

theorem nameCodePrefixed_complete (D : Name.NameDomain s) (S : ZFSet.{u})
    (pre : ∀ τ ∈ D.names, NameCodeStep s S τ.val → τ.val ∈ S) :
    ∀ τ ∈ D.names, τ.val ∈ S := by
  intro τ
  induction τ using Name.inductionOn with
  | step τ ih =>
    intro hτ
    apply pre τ hτ
    intro z hz
    obtain ⟨ν, p, rfl⟩ := Name.entries_cover τ hz
    exact ⟨ν.val, ih ν p hz (D.children hτ hz), p, rfl⟩

namespace TransitiveGround

open SetFormula
variable (M : TransitiveGround.{u})

theorem realize_nameCodeStepFormula
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0) (carrier : s.carrier ∈ M.sets)
    (x S : ZFSet.{u}) (hx : x ∈ M.sets) (hS : S ∈ M.sets) :
    Realize M.sets nameCodeStepFormula (extend x (extend S (extend s.carrier Fin.elim0))) ↔
      NameCodeStep s S x := by
  let env := extend x (extend S (extend s.carrier Fin.elim0))
  change (∀ z ∈ M.sets, Realize M.sets _ (extend z env)) ↔ _
  constructor
  · intro h z hz
    obtain ⟨y, hy, member, rest⟩ := (realize_ex M.sets _ _).1
      ((realize_imp M.sets _ _ _).1 (h z (M.transitive hx hz)) hz)
    obtain ⟨p, shape⟩ := (M.realize_exConditions s 4 _ (extend y (extend z env)) carrier rfl).1 rest
    exact ⟨y, member, p,
      (M.realize_orderedPairFormula pairing 2 1 0 (extend (s.encode p) (extend y (extend z env)))
        (M.transitive hx hz) hy (M.transitive carrier (s.encode_mem p))).1 shape⟩
  · intro h z hzM
    apply (realize_imp M.sets _ _ _).2
    intro hz
    obtain ⟨y, hy, p, shape⟩ := h z hz
    rw [realize_ex]
    refine ⟨y, M.transitive hS hy, hy, ?_⟩
    apply (M.realize_exConditions s 4 _ (extend y (extend z env)) carrier rfl).2
    exact ⟨p, (M.realize_orderedPairFormula pairing 2 1 0
      (extend (s.encode p) (extend y (extend z env))) hzM (M.transitive hS hy)
      (M.transitive carrier (s.encode_mem p))).2 shape⟩

theorem nameCertificate_sound
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0) (carrier : s.carrier ∈ M.sets)
    {S : ZFSet.{u}} (hS : S ∈ M.sets)
    (certificate : Realize M.sets nameCertificateFormula (extend S (extend s.carrier Fin.elim0))) :
    ∀ x ∈ S, IsName s x := by
  apply nameCodePostfixed_sound s S
  intro x hx
  exact (M.realize_nameCodeStepFormula s pairing carrier x S (M.transitive hS hx) hS).1
    ((realize_imp M.sets _ _ _).1 (certificate x (M.transitive hS hx)) hx)

end TransitiveGround
end PartitionPilot.Forcing



namespace PartitionPilot.Forcing.TransitiveGround

open SetRealization SetFormula
universe u
variable (M : TransitiveGround.{u}) {P : Type u} [Preorder P] (s : Presentation P)

def DomainMeaning (D : Name.NameDomain s) {k : Nat} (N : SetFormula (k + 1))
    (constants : Fin k → ZFSet.{u}) : Prop :=
  ∀ x ∈ M.sets, Realize M.sets N (extend x constants) ↔ ∃ τ : D.names, τ.val.val = x

end PartitionPilot.Forcing.TransitiveGround



namespace PartitionPilot.Forcing.TransitiveGround

open SetRealization SetFormula
universe u
variable (M : TransitiveGround.{u}) {P : Type u} (s : Presentation P)

theorem exists_groundName_certificate
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0)
    (separation : SeparationSchema M.sets) (collection : CollectionSchema M.sets)
    (carrier : s.carrier ∈ M.sets) (τ : Name s) (hτ : τ.val ∈ M.sets) :
    ∃ S ∈ M.sets, Realize M.sets nameCertificateFormula (extend S (extend s.carrier Fin.elim0)) ∧
      τ.val ∈ S := by
  obtain ⟨T, hT, τT, trans⟩ := M.exists_transitiveCover pairing unions separation collection τ.val hτ
  let D := namesInTransitiveSet s T (fun hx hy => trans _ hx _ hy)
  let params := extend s.carrier Fin.elim0
  have members : ∀ i, params i ∈ M.sets := Fin.cases carrier (fun i => Fin.elim0 i)
  have mono : ∀ S ∈ M.sets, ∀ U ∈ M.sets, S ⊆ T → U ⊆ T → S ⊆ U →
      definableOperator M.sets nameCodeStepFormula params T S ⊆
        definableOperator M.sets nameCodeStepFormula params T U := by
    intro S hS U hU _ _ sub x hx
    obtain ⟨hxT, step⟩ := ZFSet.mem_sep.1 hx
    have hxM := M.transitive hT hxT
    exact ZFSet.mem_sep.2 ⟨hxT, (M.realize_nameCodeStepFormula s pairing carrier x U hxM hU).2
      (nameCodeStep_mono s sub ((M.realize_nameCodeStepFormula s pairing carrier x S hxM hS).1 step))⟩
  obtain ⟨S, hS, bound, fixed, _⟩ := M.exists_greatest_definable_fixedPoint unions powers separation
    nameCodeStepFormula params members hT mono
  have certificate : Realize M.sets nameCertificateFormula (extend S params) := by
    apply (M.realize_postfixedFormula nameCodeStepFormula params hS bound).2
    rw [fixed]
  have pre : ∀ ν ∈ D.names, NameCodeStep s S ν.val → ν.val ∈ S := by
    intro ν hν step
    have member : ν.val ∈ definableOperator M.sets nameCodeStepFormula params T S :=
      ZFSet.mem_sep.2 ⟨hν, (M.realize_nameCodeStepFormula s pairing carrier ν.val S
        (M.transitive hT hν) hS).2 step⟩
    rwa [fixed] at member
  exact ⟨S, hS, certificate, nameCodePrefixed_complete s D S pre τ τT⟩

theorem isName_iff_exists_certificate
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0)
    (separation : SeparationSchema M.sets) (collection : CollectionSchema M.sets)
    (carrier : s.carrier ∈ M.sets) (x : ZFSet.{u}) (hx : x ∈ M.sets) :
    IsName s x ↔
      ∃ S ∈ M.sets, Realize M.sets nameCertificateFormula (extend S (extend s.carrier Fin.elim0)) ∧
        x ∈ S := by
  constructor
  · intro name
    exact M.exists_groundName_certificate s pairing unions powers separation collection carrier ⟨x, name⟩ hx
  · rintro ⟨S, hS, certificate, member⟩
    exact M.nameCertificate_sound s pairing carrier hS certificate x member

end PartitionPilot.Forcing.TransitiveGround


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


namespace PartitionPilot.Forcing.Name

open SetRealization
universe u
variable {P : Type u} {s : Presentation P}

def RenameStep (f : P → P) (R : Name s → Name s → Prop) (σ τ : Name s) : Prop :=
  (∀ ν p, Entry ν σ p → ∃ ρ, Entry ρ τ (f p) ∧ R ν ρ) ∧
  (∀ ρ q, Entry ρ τ q → ∃ ν p, Entry ν σ p ∧ f p = q ∧ R ν ρ)

theorem rename_eq_step (f : P → P) (σ τ : Name s) :
    rename s f σ = τ ↔ RenameStep f (fun ν ρ => rename s f ν = ρ) σ τ := by
  constructor
  · intro eq
    constructor
    · intro ν p entry
      refine ⟨rename s f ν, ?_, rfl⟩
      rw [← eq, entry_rename]
      exact ⟨ν, p, entry, rfl, rfl⟩
    · intro ρ q entry
      rw [← eq, entry_rename] at entry
      obtain ⟨ν, p, old, image, condition⟩ := entry
      exact ⟨ν, p, old, condition, image⟩
  · rintro ⟨left, right⟩
    apply ext
    intro ρ q
    rw [entry_rename]
    constructor
    · rintro ⟨ν, p, entry, image, condition⟩
      obtain ⟨χ, matched, hχ⟩ := left ν p entry
      have eq : χ = ρ := hχ.symm.trans image
      simpa only [eq, condition] using matched
    · intro entry
      obtain ⟨ν, p, old, condition, image⟩ := right ρ q entry
      exact ⟨ν, p, old, image, condition⟩

theorem rename_postfixed_sound (D : NameDomain s) (f : P → P) (R : Name s → Name s → Prop)
    (post : ∀ σ ∈ D.names, ∀ τ ∈ D.names, R σ τ → RenameStep f R σ τ) :
    ∀ σ ∈ D.names, ∀ τ ∈ D.names, R σ τ → rename s f σ = τ := by
  intro σ
  induction σ using inductionOn with
  | step σ ih =>
    intro hσ τ hτ rel
    obtain ⟨left, right⟩ := post σ hσ τ hτ rel
    apply (rename_eq_step f σ τ).2
    constructor
    · intro ν p entry
      obtain ⟨ρ, matched, child⟩ := left ν p entry
      exact ⟨ρ, matched, ih ν p entry (D.children hσ entry) ρ (D.children hτ matched) child⟩
    · intro ρ q entry
      obtain ⟨ν, p, old, condition, child⟩ := right ρ q entry
      exact ⟨ν, p, old, condition, ih ν p old (D.children hσ old) ρ (D.children hτ entry) child⟩

theorem rename_prefixed_complete (D : NameDomain s) (f : P → P) (R : Name s → Name s → Prop)
    (pre : ∀ σ ∈ D.names, ∀ τ ∈ D.names, RenameStep f R σ τ → R σ τ) :
    ∀ σ ∈ D.names, ∀ τ ∈ D.names, rename s f σ = τ → R σ τ := by
  intro σ
  induction σ using inductionOn with
  | step σ ih =>
    intro hσ τ hτ eq
    obtain ⟨left, right⟩ := (rename_eq_step f σ τ).1 eq
    apply pre σ hσ τ hτ
    constructor
    · intro ν p entry
      obtain ⟨ρ, matched, child⟩ := left ν p entry
      exact ⟨ρ, matched, ih ν p entry (D.children hσ entry) ρ (D.children hτ matched) child⟩
    · intro ρ q entry
      obtain ⟨ν, p, old, condition, child⟩ := right ρ q entry
      exact ⟨ν, p, old, condition, ih ν p old (D.children hσ old) ρ (D.children hτ entry) child⟩

end PartitionPilot.Forcing.Name



end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Definability_RawRenameFormulas
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

theorem realize_orientedPairFormula
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    {n : Nat} (reverse : Bool) (x y r : Fin n) (env : Fin n → ZFSet.{u})
    (hx : env x ∈ M.sets) (hy : env y ∈ M.sets) (hr : env r ∈ M.sets) :
    Realize M.sets (orientedPairFormula reverse x y r) env ↔
      if reverse then ZFSet.pair (env y) (env x) ∈ env r else ZFSet.pair (env x) (env y) ∈ env r := by
  cases reverse
  · exact M.realize_pairMembershipFormula pairing x y r env hx hy hr
  · exact M.realize_pairMembershipFormula pairing y x r env hy hx hr

end PartitionPilot.Forcing.TransitiveGround



namespace PartitionPilot.Forcing.TransitiveGround

open SetRealization SetFormula
universe u
variable (M : TransitiveGround.{u}) {P : Type u} (s : Presentation P)

def RawRenameMatch (reverse : Bool) (f : P → P) (R x y : ZFSet.{u}) : Prop :=
  ∀ v ∈ M.sets, ∀ p, ZFSet.pair v (s.encode p) ∈ x →
    ∃ w ∈ M.sets, ∃ q, ZFSet.pair w (s.encode q) ∈ y ∧
      (if reverse then f q = p else f p = q) ∧
      (if reverse then ZFSet.pair w v ∈ R else ZFSet.pair v w ∈ R)

def RawRenameStep (f : P → P) (R x y : ZFSet.{u}) : Prop :=
  M.RawRenameMatch s false f R x y ∧ M.RawRenameMatch s true f R y x

theorem rawRenameStep_mono (f : P → P) {R S x y : ZFSet.{u}} (sub : R ⊆ S)
    (h : M.RawRenameStep s f R x y) : M.RawRenameStep s f S x y := by
  constructor
  · intro v hv p entry
    obtain ⟨w, hw, q, matched, cond, rel⟩ := h.1 v hv p entry
    exact ⟨w, hw, q, matched, cond, sub rel⟩
  · intro w hw q entry
    obtain ⟨v, hv, p, matched, cond, rel⟩ := h.2 w hw q entry
    exact ⟨v, hv, p, matched, cond, sub rel⟩

theorem realize_orientedMapFormula
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (carrier : s.carrier ∈ M.sets) (f : P → P) (graph : s.graph s f ∈ M.sets)
    {n : Nat} (reverse : Bool) (i j k : Fin n) (env : Fin n → ZFSet.{u}) (p q : P)
    (hi : env i = s.encode p) (hj : env j = s.encode q) (hk : env k = s.graph s f) :
    Realize M.sets (orientedPairFormula reverse i j k) env ↔
      if reverse then f q = p else f p = q := by
  rw [M.realize_orientedPairFormula pairing reverse i j k env
    (hi ▸ M.transitive carrier (s.encode_mem p)) (hj ▸ M.transitive carrier (s.encode_mem q))
    (hk ▸ graph), hi, hj, hk]
  cases reverse
  · exact s.pair_mem_graph s f p q
  · exact s.pair_mem_graph s f q p

theorem realize_renameMatchFormula
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (carrier : s.carrier ∈ M.sets) (f : P → P) (graph : s.graph s f ∈ M.sets)
    {n : Nat} (reverse : Bool) (c g r x y : Fin n) (env : Fin n → ZFSet.{u})
    (hc : env c = s.carrier) (hg : env g = s.graph s f)
    (hr : env r ∈ M.sets) (hx : env x ∈ M.sets) (hy : env y ∈ M.sets) :
    Realize M.sets (renameMatchFormula reverse c g r x y) env ↔
      M.RawRenameMatch s reverse f (env r) (env x) (env y) := by
  change (∀ v ∈ M.sets, Realize M.sets _ (extend v env)) ↔ _
  apply forall_congr'
  intro v
  apply forall_congr'
  intro hv
  rw [M.realize_allConditions s c.succ _ (extend v env) carrier hc]
  apply forall_congr'
  intro p
  rw [realize_imp, M.realize_pairMembershipFormula pairing 1 0 x.succ.succ
    (extend (s.encode p) (extend v env)) hv (M.transitive carrier (s.encode_mem p)) hx]
  apply forall_congr'
  intro _
  rw [realize_ex]
  apply exists_congr
  intro w
  apply and_congr_right
  intro hw
  rw [M.realize_exConditions s c.succ.succ.succ _ (extend w (extend (s.encode p) (extend v env)))
    carrier hc]
  apply exists_congr
  intro q
  let e := extend (s.encode q) (extend w (extend (s.encode p) (extend v env)))
  change (Realize M.sets _ e ∧ Realize M.sets _ e ∧ Realize M.sets _ e) ↔ _
  rw [M.realize_pairMembershipFormula pairing 1 0 y.succ.succ.succ.succ e hw
    (M.transitive carrier (s.encode_mem q)) hy,
    M.realize_orientedMapFormula s pairing carrier f graph reverse 2 0 g.succ.succ.succ.succ e p q rfl rfl hg,
    M.realize_orientedPairFormula pairing reverse 3 1 r.succ.succ.succ.succ e hv hw hr]
  rfl

theorem realize_renameStepFormula
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (carrier : s.carrier ∈ M.sets) (f : P → P) (graph : s.graph s f ∈ M.sets)
    {n : Nat} (c g r x y : Fin n) (env : Fin n → ZFSet.{u})
    (hc : env c = s.carrier) (hg : env g = s.graph s f)
    (hr : env r ∈ M.sets) (hx : env x ∈ M.sets) (hy : env y ∈ M.sets) :
    Realize M.sets (renameStepFormula c g r x y) env ↔
      M.RawRenameStep s f (env r) (env x) (env y) := by
  change (Realize M.sets _ env ∧ Realize M.sets _ env) ↔ _
  rw [M.realize_renameMatchFormula s pairing carrier f graph false c g r x y env hc hg hr hx hy,
    M.realize_renameMatchFormula s pairing carrier f graph true c g r y x env hc hg hr hy hx]
  rfl

end PartitionPilot.Forcing.TransitiveGround

end

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Geometry_DecodedGroundGroups
attribute [-instance] _root_.OAI.PartitionPilot.Forcing.GroundMainPrefix.withTopSmall
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PartitionPilot.Forcing.GroupCode

open SetRealization
universe u
variable {G m i e : ZFSet.{u}} (h : GroupCode G m i e)

theorem multiplication_graph_eq :
    letI := h.toGroup
    ((SetMembers.presentation G).product (SetMembers.presentation G)).graph
      (SetMembers.presentation G) (fun x => x.1 * x.2) = m := by
  let := h.toGroup
  exact ((SetMembers.presentation G).product (SetMembers.presentation G)).graph_decodeFunction
    (SetMembers.presentation G) m h.mul_function

theorem identity_code_eq :
    letI := h.toGroup
    (SetMembers.presentation G).encode 1 = e := h.raw_one

end PartitionPilot.Forcing.GroupCode

end

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

namespace PartitionPilot.Forcing.TransitiveGround

open SetRealization SetFormula
universe u
variable (M : TransitiveGround.{u}) {P : Type u} (s : Presentation P)

noncomputable def renameParameters (f : P → P) : Fin 2 → ZFSet.{u} :=
  extend s.carrier (extend (s.graph s f) Fin.elim0)

theorem realize_renameState
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (carrier : s.carrier ∈ M.sets) (f : P → P) (graph : s.graph s f ∈ M.sets)
    (z R : ZFSet.{u}) (hz : z ∈ M.sets) (hr : R ∈ M.sets) :
    Realize M.sets renameStateFormula (extend z (extend R (renameParameters s f))) ↔
      ∃ x ∈ M.sets, ∃ y ∈ M.sets, z = ZFSet.pair x y ∧ M.RawRenameStep s f R x y := by
  rw [renameStateFormula, realize_ex]
  apply exists_congr
  intro x
  apply and_congr_right
  intro hx
  rw [realize_ex]
  apply exists_congr
  intro y
  apply and_congr_right
  intro hy
  let e := extend y (extend x (extend z (extend R (renameParameters s f))))
  change (Realize M.sets _ e ∧ Realize M.sets _ e) ↔ _
  rw [M.realize_orderedPairFormula pairing 2 1 0 e hz hx hy,
    M.realize_renameStepFormula s pairing carrier f graph 4 5 3 1 0 e rfl rfl hr hx hy]
  rfl

theorem rawRenameStep_names (D : Name.NameDomain s)
    (ground : ∀ τ ∈ D.names, τ.val ∈ M.sets)
    (f : P → P) (R : ZFSet.{u}) (σ τ : D.names) :
    M.RawRenameStep s f R σ.val.val τ.val.val ↔
      Name.RenameStep f (fun ν ρ => ZFSet.pair ν.val ρ.val ∈ R) σ.val τ.val := by
  constructor
  · rintro ⟨left, right⟩
    constructor
    · intro ν p entry
      obtain ⟨w, _, q, matched, cond, rel⟩ := left ν.val (ground ν (D.children σ.property entry)) p entry
      change f p = q at cond
      subst q
      let ρ : Name s := ⟨w, Name.isName_of_pair_mem τ.val w (f p) matched⟩
      exact ⟨ρ, matched, rel⟩
    · intro ρ q entry
      obtain ⟨v, _, p, matched, cond, rel⟩ := right ρ.val (ground ρ (D.children τ.property entry)) q entry
      let ν : Name s := ⟨v, Name.isName_of_pair_mem σ.val v p matched⟩
      exact ⟨ν, p, matched, cond, rel⟩
  · rintro ⟨left, right⟩
    constructor
    · intro v _ p entry
      let ν : Name s := ⟨v, Name.isName_of_pair_mem σ.val v p entry⟩
      obtain ⟨ρ, matched, rel⟩ := left ν p entry
      exact ⟨ρ.val, ground ρ (D.children τ.property matched), f p, matched, rfl, rel⟩
    · intro w _ q entry
      let ρ : Name s := ⟨w, Name.isName_of_pair_mem τ.val w q entry⟩
      obtain ⟨ν, p, matched, cond, rel⟩ := right ρ q entry
      exact ⟨ν.val, ground ν (D.children σ.property matched), p, matched, cond, rel⟩

theorem realize_renameState_names (D : Name.NameDomain s)
    (ground : ∀ τ ∈ D.names, τ.val ∈ M.sets)
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (carrier : s.carrier ∈ M.sets) (f : P → P) (graph : s.graph s f ∈ M.sets)
    (R : ZFSet.{u}) (hr : R ∈ M.sets) (σ τ : D.names) :
    Realize M.sets renameStateFormula
      (extend (ZFSet.pair σ.val.val τ.val.val) (extend R (renameParameters s f))) ↔
      Name.RenameStep f (fun ν ρ => ZFSet.pair ν.val ρ.val ∈ R) σ.val τ.val := by
  have hz := M.orderedPair_mem pairing (ground σ.val σ.property) (ground τ.val τ.property)
  rw [M.realize_renameState s pairing carrier f graph _ R hz hr]
  constructor
  · rintro ⟨x, _, y, _, shape, step⟩
    obtain ⟨sx, ty⟩ := ZFSet.pair_inj.1 shape
    subst x
    subst y
    exact (M.rawRenameStep_names s D ground f R σ τ).1 step
  · intro step
    exact ⟨σ.val.val, ground σ.val σ.property, τ.val.val, ground τ.val τ.property, rfl,
      (M.rawRenameStep_names s D ground f R σ τ).2 step⟩

theorem renameCertificate_sound (D : Name.NameDomain s)
    (ground : ∀ τ ∈ D.names, τ.val ∈ M.sets)
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (carrier : s.carrier ∈ M.sets) (f : P → P) (graph : s.graph s f ∈ M.sets)
    {R : ZFSet.{u}} (hr : R ∈ M.sets)
    (certificate : Realize M.sets renameCertificateFormula (extend R (renameParameters s f)))
    (σ τ : D.names) : ZFSet.pair σ.val.val τ.val.val ∈ R → Name.rename s f σ.val = τ.val := by
  apply Name.rename_postfixed_sound D f (fun ν ρ => ZFSet.pair ν.val ρ.val ∈ R) _
    σ.val σ.property τ.val τ.property
  intro ν hν ρ hρ rel
  exact (M.realize_renameState_names s D ground pairing carrier f graph R hr ⟨ν, hν⟩ ⟨ρ, hρ⟩).1
    ((realize_imp M.sets _ _ _).1 (certificate _ (M.transitive hr rel)) rel)

end PartitionPilot.Forcing.TransitiveGround

end


namespace PartitionPilot.Forcing.TransitiveGround

open SetRealization SetFormula
universe u
variable (M : TransitiveGround.{u}) {P : Type u} (s : Presentation P)

theorem exists_renameState_fixedPoint
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (carrier : s.carrier ∈ M.sets) (f : P → P) (graph : s.graph s f ∈ M.sets)
    (B : ZFSet.{u}) (hB : B ∈ M.sets) :
    ∃ R ∈ M.sets, R ⊆ B ∧ definableOperator M.sets renameStateFormula (renameParameters s f) B R = R := by
  have members : ∀ i, renameParameters s f i ∈ M.sets :=
    Fin.cases carrier (Fin.cases graph (fun i => Fin.elim0 i))
  have mono : ∀ R ∈ M.sets, ∀ S ∈ M.sets, R ⊆ B → S ⊆ B → R ⊆ S →
      definableOperator M.sets renameStateFormula (renameParameters s f) B R ⊆
        definableOperator M.sets renameStateFormula (renameParameters s f) B S := by
    intro R hr S hs _ _ sub z hz
    obtain ⟨hzB, step⟩ := ZFSet.mem_sep.1 hz
    have hzM := M.transitive hB hzB
    obtain ⟨x, hx, y, hy, shape, raw⟩ := (M.realize_renameState s pairing carrier f graph z R hzM hr).1 step
    exact ZFSet.mem_sep.2 ⟨hzB, (M.realize_renameState s pairing carrier f graph z S hzM hs).2
      ⟨x, hx, y, hy, shape, M.rawRenameStep_mono s f sub raw⟩⟩
  obtain ⟨R, hr, bound, fixed, _⟩ := M.exists_greatest_definable_fixedPoint unions powers separation
    renameStateFormula (renameParameters s f) members hB mono
  exact ⟨R, hr, bound, fixed⟩

theorem exists_groundRename_certificate
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0)
    (separation : SeparationSchema M.sets) (collection : CollectionSchema M.sets)
    (carrier : s.carrier ∈ M.sets) (f : P → P) (graph : s.graph s f ∈ M.sets)
    (σ τ : Name s) (hσ : σ.val ∈ M.sets) (hτ : τ.val ∈ M.sets) (eq : Name.rename s f σ = τ) :
    ∃ R ∈ M.sets, Realize M.sets renameCertificateFormula (extend R (renameParameters s f)) ∧
      ZFSet.pair σ.val τ.val ∈ R := by
  obtain ⟨T, hT, σT, τT, trans⟩ := M.exists_pair_transitiveCover pairing unions separation collection hσ hτ
  let D := namesInTransitiveSet s T (fun hx hy => trans _ hx _ hy)
  have ground : ∀ ν ∈ D.names, ν.val ∈ M.sets := fun _ h => M.transitive hT h
  obtain ⟨B, hB, pairBound⟩ := M.exists_pair_bound pairing unions powers hT hT
  obtain ⟨R, hr, bound, fixed⟩ := M.exists_renameState_fixedPoint s pairing unions powers separation
    carrier f graph B hB
  have certificate : Realize M.sets renameCertificateFormula (extend R (renameParameters s f)) := by
    apply (M.realize_postfixedFormula renameStateFormula (renameParameters s f) hr bound).2
    rw [fixed]
  have pre : ∀ ν ∈ D.names, ∀ ρ ∈ D.names,
      Name.RenameStep f (fun χ ψ => ZFSet.pair χ.val ψ.val ∈ R) ν ρ → ZFSet.pair ν.val ρ.val ∈ R := by
    intro ν hν ρ hρ step
    have member : ZFSet.pair ν.val ρ.val ∈
        definableOperator M.sets renameStateFormula (renameParameters s f) B R :=
      ZFSet.mem_sep.2 ⟨pairBound ν.val hν ρ.val hρ,
        (M.realize_renameState_names s D ground pairing carrier f graph R hr ⟨ν, hν⟩ ⟨ρ, hρ⟩).2 step⟩
    rwa [fixed] at member
  exact ⟨R, hr, certificate, Name.rename_prefixed_complete D f
    (fun ν ρ => ZFSet.pair ν.val ρ.val ∈ R) pre σ σT τ τT eq⟩

theorem rename_eq_iff_exists_certificate
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0)
    (separation : SeparationSchema M.sets) (collection : CollectionSchema M.sets)
    (carrier : s.carrier ∈ M.sets) (f : P → P) (graph : s.graph s f ∈ M.sets)
    (σ τ : Name s) (hσ : σ.val ∈ M.sets) (hτ : τ.val ∈ M.sets) :
    Name.rename s f σ = τ ↔
      ∃ R ∈ M.sets, Realize M.sets renameCertificateFormula (extend R (renameParameters s f)) ∧
        ZFSet.pair σ.val τ.val ∈ R := by
  constructor
  · exact M.exists_groundRename_certificate s pairing unions powers separation collection carrier f graph σ τ hσ hτ
  · rintro ⟨R, hr, certificate, member⟩
    exact M.renameCertificate_sound s (M.nameDomain s) (fun _ h => h) pairing carrier f graph hr
      certificate ⟨σ, hσ⟩ ⟨τ, hτ⟩ member

end PartitionPilot.Forcing.TransitiveGround


section



namespace PartitionPilot.Forcing.PosetAction

open SetRealization
universe u
variable {G P : Type u} [Group G] [PartialOrder P]
variable (a : PosetAction G P) (s : Presentation P) (t : Presentation G)

noncomputable def conditionMapFamily : ZFSet.{u} :=
  ZFSet.range (fun g : G => ZFSet.pair (t.encode g) (s.graph s (a.iso g)))

theorem pair_mem_conditionMapFamily (g : G) (F : ZFSet.{u}) :
    ZFSet.pair (t.encode g) F ∈ a.conditionMapFamily s t ↔ F = s.graph s (a.iso g) := by
  rw [conditionMapFamily, ZFSet.mem_range]
  constructor
  · rintro ⟨h, eq⟩
    obtain ⟨hg, value⟩ := ZFSet.pair_inj.1 eq
    have hgeq := t.injective hg
    subst h
    exact value.symm
  · intro eq
    exact ⟨g, congrArg (ZFSet.pair (t.encode g)) eq.symm⟩

end PartitionPilot.Forcing.PosetAction

namespace PartitionPilot.Forcing.TransitiveGround

open SetRealization SetFormula
universe u
variable (M : TransitiveGround.{u}) {G P : Type u} [Group G] [PartialOrder P]

theorem conditionMap_graph_mem (a : PosetAction G P) (s : Presentation P) (t : Presentation G)
    (maps : a.conditionMapFamily s t ∈ M.sets) (g : G) : s.graph s (a.iso g) ∈ M.sets :=
  M.pair_right (M.transitive maps ((a.pair_mem_conditionMapFamily s t g _).2 rfl))

end PartitionPilot.Forcing.TransitiveGround



end


namespace PartitionPilot.Forcing
open SetRealization SetFormula
universe u

def identityPosetAction (G P : Type u) [Group G] [PartialOrder P] : PosetAction G P where
  iso _ := OrderIso.refl P
  one _ := rfl
  mul _ _ _ := rfl

def trivialGroupPresentation : Presentation (Equiv.Perm (ULift.{u} Unit)) where
  carrier := {∅}
  encode _ := ∅
  injective := fun _ _ _ => Subsingleton.elim _ _
  mem_carrier x := by
    rw [ZFSet.mem_singleton]
    exact ⟨fun h => ⟨1, h.symm⟩, fun ⟨_, h⟩ => h.symm⟩

end PartitionPilot.Forcing


section



namespace PartitionPilot.SetRealization.Presentation

universe u
variable {I : Type u} [Bot I]

noncomputable def nonbottom (s : Presentation I) : Presentation {x : I // x ≠ ⊥} where
  carrier := ZFSet.sep (fun z => z ≠ s.encode ⊥) s.carrier
  encode x := s.encode x.val
  injective := fun _ _ eq => Subtype.ext (s.injective eq)
  mem_carrier z := by
    rw [ZFSet.mem_sep]
    constructor
    · rintro ⟨hz, ne⟩
      obtain ⟨x, rfl⟩ := (s.mem_carrier z).1 hz
      exact ⟨⟨x, fun eq => ne (congrArg s.encode eq)⟩, rfl⟩
    · rintro ⟨x, rfl⟩
      exact ⟨s.encode_mem x.val, fun eq => x.property (s.injective eq)⟩

end PartitionPilot.SetRealization.Presentation

namespace PartitionPilot.Forcing.PosetAction

universe u v
variable {G : Type v} [Group G] {I : Type u} [PartialOrder I] [OrderBot I]

def nonbottomIso (a : PosetAction G I) (g : G) :
    {x : I // x ≠ ⊥} ≃o {x : I // x ≠ ⊥} where
  toFun x := ⟨a.iso g x.val, fun eq =>
    x.property ((a.iso g).injective (eq.trans (a.iso g).map_bot.symm))⟩
  invFun x := ⟨(a.iso g).symm x.val, fun eq =>
    x.property ((a.iso g).symm.injective (eq.trans (a.iso g).symm.map_bot.symm))⟩
  left_inv x := Subtype.ext ((a.iso g).symm_apply_apply x.val)
  right_inv x := Subtype.ext ((a.iso g).apply_symm_apply x.val)
  map_rel_iff' := (a.iso g).map_rel_iff

def nonbottom (a : PosetAction G I) : PosetAction G {x : I // x ≠ ⊥} where
  iso := a.nonbottomIso
  one x := Subtype.ext (a.one x.val)
  mul g h x := Subtype.ext (a.mul g h x.val)

end PartitionPilot.Forcing.PosetAction

namespace PartitionPilot.Forcing.TransitiveGround

open SetRealization SetFormula
universe u
variable (M : TransitiveGround.{u})

theorem nonbottom_carrier_mem {I : Type u} [Bot I] (s : Presentation I)
    (separation : SeparationSchema M.sets) (carrier : s.carrier ∈ M.sets) :
    s.nonbottom.carrier ∈ M.sets := by
  have bottom := M.transitive carrier (s.encode_mem ⊥)
  exact M.bounded_separation_mem separation (.neg (.equal 0 1))
    (extend (s.encode ⊥) Fin.elim0) (Fin.cases bottom (fun j => Fin.elim0 j)) carrier

end PartitionPilot.Forcing.TransitiveGround

end


end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Forcing_NamePresentationEquivalences
attribute [-instance] _root_.OAI.PartitionPilot.Forcing.GroundMainPrefix.withTopSmall _root_.OAI.PartitionPilot.Forcing.Name.boundedNames_small _root_.OAI.PartitionPilot.Forcing.Name.unionIndices_small _root_.OAI.PartitionPilot.Forcing.PosetAction.mixIndices_small
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PartitionPilot.SetRealization.Presentation
universe u
variable {P : Type u} (s : Presentation P)

noncomputable def intoSet (B : ZFSet.{u}) (sub : s.carrier ⊆ B) : P → SetMembers B :=
  fun p => SetMembers.ofMem (s.encode p) (sub (s.encode_mem p))

end PartitionPilot.SetRealization.Presentation

namespace PartitionPilot.Forcing.Name
open SetRealization
universe u
variable {P Q : Type u} {s : Presentation P}

theorem rename_val_of_encode (t : Presentation Q) (f : P → Q)
    (codes : ∀ p, t.encode (f p) = s.encode p) (τ : Name s) :
    (rename t f τ).val = τ.val := by
  induction τ using inductionOn with
  | step τ ih =>
    apply ZFSet.ext
    intro z
    constructor
    · intro hz
      obtain ⟨ρ, q, rfl⟩ := entries_cover (rename t f τ) hz
      obtain ⟨σ, p, entry, rfl, rfl⟩ := (entry_rename t f τ ρ q).1 hz
      rw [ih σ p entry, codes p]
      exact entry
    · intro hz
      obtain ⟨σ, p, rfl⟩ := entries_cover τ hz
      have entry := (entry_rename t f τ (rename t f σ) (f p)).2 ⟨σ, p, hz, rfl, rfl⟩
      change ZFSet.pair (rename t f σ).val (t.encode (f p)) ∈ (rename t f τ).val at entry
      simpa only [ih σ p hz, codes p] using entry

end PartitionPilot.Forcing.Name



namespace PartitionPilot.Forcing.Name
open SetRealization
universe u
variable {P : Type u} (s t : Presentation P)

noncomputable def presentationEquiv : Name s ≃ Name t where
  toFun := rename t id
  invFun := rename s id
  left_inv τ := by rw [rename_comp]; exact rename_id τ
  right_inv τ := by rw [rename_comp]; exact rename_id τ

end PartitionPilot.Forcing.Name

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


namespace PartitionPilot.Forcing.Name
open SetRealization
universe u v
variable {P : Type u} {s : Presentation P}

theorem isName_of_subset {T z : ZFSet.{u}}
    (valid : ∀ x ∈ T, IsName s x) (subset : z ⊆ ZFSet.prod T s.carrier) :
    IsName s z := by
  refine IsName.mk ?_ ?_
  · intro w hw
    obtain ⟨x, _, y, hy, equal⟩ := ZFSet.mem_prod.1 (subset hw)
    obtain ⟨p, rfl⟩ := (s.mem_carrier y).1 hy
    exact ⟨x, p, equal⟩
  · intro x p entry
    exact valid x (ZFSet.pair_mem_prod.1 (subset entry)).1

def ofSubset {T z : ZFSet.{u}} (valid : ∀ x ∈ T, IsName s x)
    (subset : z ⊆ ZFSet.prod T s.carrier) : Name s :=
  ⟨z, isName_of_subset valid subset⟩

theorem entry_term_of_subset {T : ZFSet.{u}} {σ τ : Name s} {p : P}
    (subset : τ.val ⊆ ZFSet.prod T s.carrier) (entry : Entry σ τ p) : σ.val ∈ T :=
  (ZFSet.pair_mem_prod.1 (subset entry)).1

theorem act_subset_of_closed {G : Type v} [Group G] [PartialOrder P]
    (a : PosetAction G P) {T : ZFSet.{u}}
    (closed : ∀ g (σ : Name s), σ.val ∈ T → (a.act s g σ).val ∈ T)
    {τ : Name s} (subset : τ.val ⊆ ZFSet.prod T s.carrier) (g : G) :
    (a.act s g τ).val ⊆ ZFSet.prod T s.carrier := by
  intro z hz
  obtain ⟨ν, p, rfl⟩ := entries_cover (a.act s g τ) hz
  change Entry ν (rename s (a.iso g) τ) p at hz
  obtain ⟨σ, q, entry, rfl, rfl⟩ := (entry_rename s (a.iso g) τ ν p).1 hz
  exact ZFSet.pair_mem_prod.2
    ⟨closed g σ (entry_term_of_subset subset entry), s.encode_mem _⟩

end PartitionPilot.Forcing.Name



namespace PartitionPilot.Forcing.Name
open SetRealization
universe u
variable {Upper Lower : Type u} [PartialOrder Upper]
variable (s : Presentation Upper) (t : Presentation Lower)
variable (inclusion : Lower → Upper) (J : ZFSet.{u}) (tau : Name s)

noncomputable def crossStageMembershipCode : ZFSet.{u} :=
  ZFSet.sep (fun z => ∃ sigma : Name t, ∃ p : Lower,
    z = ZFSet.pair sigma.val (t.encode p) ∧
      ForcesMem (inclusion p) (rename s inclusion sigma) tau)
    (ZFSet.prod J t.carrier)

theorem crossStageMembershipCode_subset :
    crossStageMembershipCode s t inclusion J tau ⊆ ZFSet.prod J t.carrier :=
  fun _ member => (ZFSet.mem_sep.1 member).1

theorem crossStageMembershipCode_isName (valid : ∀ z ∈ J, IsName t z) :
    IsName t (crossStageMembershipCode s t inclusion J tau) :=
  isName_of_subset valid (crossStageMembershipCode_subset s t inclusion J tau)

noncomputable def crossStageMembershipName (valid : ∀ z ∈ J, IsName t z)
    (tau : Name s) : Name t :=
  ⟨crossStageMembershipCode s t inclusion J tau,
    crossStageMembershipCode_isName s t inclusion J tau valid⟩

end PartitionPilot.Forcing.Name



namespace PartitionPilot.Forcing.PosetAction

open Compression.RecursiveMaps Compression.RecursiveMaps.CosetGeometry.OrderAction
universe u
variable {G I : Type u} [Group G] [PartialOrder I] (a : PosetAction G I)

theorem point_inv_left (g : G) (x : I) : a.iso g⁻¹ (a.iso g x) = x := by
  rw [← a.mul, inv_mul_cancel, a.one]

end PartitionPilot.Forcing.PosetAction



namespace PartitionPilot.Forcing
open SetRealization Compression.RecursiveMaps Compression.RecursiveMaps.CosetGeometry.OrderAction
universe u v
variable {P : Type u} [PartialOrder P] {G : Type v} [Group G]

def NiceNameCode (a : PosetAction G P) (s : Presentation P)
    (T : ZFSet.{u}) (K : Subgroup G) (z : ZFSet.{u}) : Prop :=
  ∃ τ : Name s, τ.val = z ∧ τ.val ⊆ ZFSet.prod T s.carrier ∧ K ≤ a.stabilizer s τ

variable (a : PosetAction G P) (s : Presentation P)

theorem niceNameCode_iff {T : ZFSet.{u}} {K : Subgroup G} (τ : Name s) :
    NiceNameCode a s T K τ.val ↔
      τ.val ⊆ ZFSet.prod T s.carrier ∧ K ≤ a.stabilizer s τ := by
  constructor
  · rintro ⟨ν, equal, subset, fixed⟩
    have same : ν = τ := Subtype.ext equal
    exact same ▸ ⟨subset, fixed⟩
  · rintro ⟨subset, fixed⟩
    exact ⟨τ, rfl, subset, fixed⟩

theorem niceNameCode_isName {T z : ZFSet.{u}} {K : Subgroup G}
    (code : NiceNameCode a s T K z) : IsName s z := by
  obtain ⟨τ, equal, _, _⟩ := code
  exact equal ▸ τ.property

theorem niceNameCode_hs (F : NormalSubgroupFamily G) {T : ZFSet.{u}} {K : Subgroup G}
    (member : F.mem K)
    (children : ∀ σ : Name s, σ.val ∈ T → HereditarilySymmetric a s F σ)
    {τ : Name s} (code : NiceNameCode a s T K τ.val) : HereditarilySymmetric a s F τ := by
  obtain ⟨subset, fixed⟩ := (niceNameCode_iff a s τ).1 code
  exact HereditarilySymmetric.mk (F.upward member fixed)
    (fun σ p entry => children σ (Name.entry_term_of_subset subset entry))

theorem niceNameCode_conjugate {T : ZFSet.{u}} {K : Subgroup G}
    (closed : ∀ g (σ : Name s), σ.val ∈ T → (a.act s g σ).val ∈ T)
    {τ : Name s} (code : NiceNameCode a s T K τ.val) (g : G) :
    NiceNameCode a s T (K.map (conjugateHom g)) (a.act s g τ).val := by
  obtain ⟨subset, fixed⟩ := (niceNameCode_iff a s τ).1 code
  apply (niceNameCode_iff a s _).2
  refine ⟨Name.act_subset_of_closed a closed subset g, ?_⟩
  intro h member
  obtain ⟨k, hk, rfl⟩ := Subgroup.mem_map.1 member
  change a.act s (g * k * g⁻¹) (a.act s g τ) = a.act s g τ
  rw [a.act_mul, a.act_mul, a.act_inv_left, fixed hk]

theorem niceNameCode_act_iff {T : ZFSet.{u}} {K : Subgroup G}
    (closed : ∀ g (σ : Name s), σ.val ∈ T → (a.act s g σ).val ∈ T)
    (g : G) (τ : Name s) :
    NiceNameCode a s T (K.map (conjugateHom g)) (a.act s g τ).val ↔
      NiceNameCode a s T K τ.val := by
  constructor
  · intro code
    obtain ⟨subset, fixed⟩ := (niceNameCode_iff a s _).1 code
    apply (niceNameCode_iff a s τ).2
    refine ⟨?_, ?_⟩
    · have back := Name.act_subset_of_closed a closed subset g⁻¹
      simpa only [a.act_inv_left] using back
    · intro k hk
      have image : conjugateHom g k ∈ K.map (conjugateHom g) :=
        Subgroup.mem_map.2 ⟨k, hk, rfl⟩
      have equal := fixed image
      change a.act s (g * k * g⁻¹) (a.act s g τ) = a.act s g τ at equal
      rw [a.act_mul, a.act_mul, a.act_inv_left] at equal
      exact (a.nameEquiv s g).injective equal
  · intro code
    exact niceNameCode_conjugate a s closed code g

end PartitionPilot.Forcing



namespace PartitionPilot.Forcing.TransitiveGround
open SetRealization SetFormula
universe u
variable (M : TransitiveGround.{u}) {G P : Type u} [Group G] [PartialOrder P]
variable (a : PosetAction G P) (s : Presentation P)

noncomputable def niceNameCandidates (T : ZFSet.{u}) (K : Subgroup G) : ZFSet.{u} :=
  ZFSet.sep (NiceNameCode a s T K) (M.groundRelations T s.carrier)

theorem mem_niceNameCandidates (T : ZFSet.{u}) (K : Subgroup G) (z : ZFSet.{u}) :
    z ∈ M.niceNameCandidates a s T K ↔ z ∈ M.sets ∧ NiceNameCode a s T K z := by
  rw [niceNameCandidates, ZFSet.mem_sep, M.mem_groundRelations]
  constructor
  · exact fun h => ⟨h.1.1, h.2⟩
  · rintro ⟨ground, τ, equal, subset, fixed⟩
    exact ⟨⟨ground, equal ▸ subset⟩, τ, equal, subset, fixed⟩

theorem name_mem_niceNameCandidates (T : ZFSet.{u}) (K : Subgroup G) (τ : Name s) :
    τ.val ∈ M.niceNameCandidates a s T K ↔
      τ.val ∈ M.sets ∧ τ.val ⊆ ZFSet.prod T s.carrier ∧ K ≤ a.stabilizer s τ := by
  rw [M.mem_niceNameCandidates]
  constructor
  · rintro ⟨ground, σ, equal, subset, fixed⟩
    have same : σ = τ := Subtype.ext equal
    subst σ
    exact ⟨ground, subset, fixed⟩
  · rintro ⟨ground, subset, fixed⟩
    exact ⟨ground, τ, rfl, subset, fixed⟩

theorem niceNameCandidates_subset (T : ZFSet.{u}) (K : Subgroup G) :
    M.niceNameCandidates a s T K ⊆ M.groundRelations T s.carrier := by
  intro z hz
  exact (ZFSet.mem_sep.1 hz).1

end PartitionPilot.Forcing.TransitiveGround

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Forcing_GroundGraphValueDescendantWitnesses
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
variable {P : Type u} {s : Presentation P}

theorem child_mem_doubleUnion {σ τ : Name s} {p : P} (entry : Entry σ τ p) :
    σ.val ∈ ZFSet.sUnion (ZFSet.sUnion τ.val) := by
  have single : ({σ.val} : ZFSet.{u}) ∈ ZFSet.sUnion τ.val :=
    ZFSet.mem_sUnion.2 ⟨ZFSet.pair σ.val (s.encode p), entry, ZFSet.mem_pair.2 (Or.inl rfl)⟩
  exact ZFSet.mem_sUnion.2 ⟨{σ.val}, single, ZFSet.mem_singleton.2 rfl⟩

end PartitionPilot.Forcing.Name



namespace PartitionPilot.Forcing.Name
open SetRealization
universe u
variable {P : Type u} {s : Presentation P}

noncomputable def immediateChildCodes (τ : Name s) : ZFSet.{u} :=
  relationImage s.carrier (ZFSet.sUnion (ZFSet.sUnion τ.val))
    (relationConverse (ZFSet.sUnion (ZFSet.sUnion τ.val)) s.carrier τ.val)

end PartitionPilot.Forcing.Name

end


section

namespace PartitionPilot.Forcing.Name
open SetRealization Compression.RecursiveMaps
universe u v
variable {P : Type u} (s : Presentation P)

noncomputable def childFamilyCodes (W : ZFSet.{u}) : ZFSet.{u} :=
  relationImage s.carrier (ZFSet.sUnion (ZFSet.sUnion (ZFSet.sUnion W)))
    (relationConverse (ZFSet.sUnion (ZFSet.sUnion (ZFSet.sUnion W))) s.carrier
      (ZFSet.sUnion W))

end PartitionPilot.Forcing.Name



namespace PartitionPilot.Forcing.Name
open SetRealization Compression.RecursiveMaps
universe u v
variable {P : Type u} (s : Presentation P)

noncomputable def descendantFamilyCodes (tau : Name s) : Nat → ZFSet.{u}
  | 0 => {tau.val}
  | n + 1 => childFamilyCodes s (descendantFamilyCodes tau n)

end PartitionPilot.Forcing.Name

end


end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Definability_RawCheckFormulas
attribute [-instance] _root_.OAI.PartitionPilot.Forcing.GroundMainPrefix.withTopSmall
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace PartitionPilot.Forcing.Name

open SetRealization
universe u
variable {P : Type u} (s : Presentation P)

theorem mem_check_code (one : P) (x z : ZFSet.{u}) :
    z ∈ (check s one x).val ↔ ∃ y ∈ x, z = ZFSet.pair (check s one y).val (s.encode one) := by
  rw [check]
  change z ∈ ZFSet.range _ ↔ _
  rw [ZFSet.mem_range]
  constructor
  · rintro ⟨y, eq⟩
    exact ⟨y.val, y.property, eq.symm⟩
  · rintro ⟨y, hy, eq⟩
    exact ⟨⟨y, hy⟩, eq.symm⟩

end PartitionPilot.Forcing.Name

namespace PartitionPilot.Forcing.TransitiveGround

open SetRealization SetFormula
universe u
variable (M : TransitiveGround.{u})

def RawCheckStep (top R x y : ZFSet.{u}) : Prop :=
  (∀ v ∈ x, ∃ w ∈ M.sets, ZFSet.pair v w ∈ R ∧ ZFSet.pair w top ∈ y) ∧
  (∀ z ∈ y, ∃ v ∈ x, ∃ w ∈ M.sets, ZFSet.pair v w ∈ R ∧ z = ZFSet.pair w top)

theorem rawCheckStep_mono {top R S x y : ZFSet.{u}} (sub : R ⊆ S)
    (h : M.RawCheckStep top R x y) : M.RawCheckStep top S x y := by
  constructor
  · intro v hv
    obtain ⟨w, hw, rel, entry⟩ := h.1 v hv
    exact ⟨w, hw, sub rel, entry⟩
  · intro z hz
    obtain ⟨v, hv, w, hw, rel, eq⟩ := h.2 z hz
    exact ⟨v, hv, w, hw, sub rel, eq⟩

theorem realize_checkStepFormula
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    {n : Nat} (top r x y : Fin n) (env : Fin n → ZFSet.{u})
    (htop : env top ∈ M.sets) (hr : env r ∈ M.sets)
    (hx : env x ∈ M.sets) (hy : env y ∈ M.sets) :
    Realize M.sets (checkStepFormula top r x y) env ↔
      M.RawCheckStep (env top) (env r) (env x) (env y) := by
  change (Realize M.sets _ env ∧ Realize M.sets _ env) ↔ _
  constructor
  · rintro ⟨forward, backward⟩
    constructor
    · intro v hv
      have step := (realize_imp M.sets _ _ _).1 (forward v (M.transitive hx hv)) hv
      obtain ⟨w, hw, rel, entry⟩ := (realize_ex M.sets _ _).1 step
      let e := extend w (extend v env)
      exact ⟨w, hw,
        (M.realize_pairMembershipFormula pairing 1 0 r.succ.succ e (M.transitive hx hv) hw hr).1 rel,
        (M.realize_pairMembershipFormula pairing 0 top.succ.succ y.succ.succ e hw htop hy).1 entry⟩
    · intro z hz
      have step := (realize_imp M.sets _ _ _).1 (backward z (M.transitive hy hz)) hz
      obtain ⟨v, hv, step⟩ := (realize_ex M.sets _ _).1 step
      obtain ⟨w, hw, member, rel, shape⟩ := (realize_ex M.sets _ _).1 step
      let e := extend w (extend v (extend z env))
      exact ⟨v, member, w, hw,
        (M.realize_pairMembershipFormula pairing 1 0 r.succ.succ.succ e hv hw hr).1 rel,
        (M.realize_orderedPairFormula pairing 2 0 top.succ.succ.succ e (M.transitive hy hz) hw htop).1 shape⟩
  · rintro ⟨forward, backward⟩
    constructor
    · intro v hv
      rw [realize_imp]
      intro member
      obtain ⟨w, hw, rel, entry⟩ := forward v member
      rw [realize_ex]
      let e := extend w (extend v env)
      exact ⟨w, hw,
        (M.realize_pairMembershipFormula pairing 1 0 r.succ.succ e hv hw hr).2 rel,
        (M.realize_pairMembershipFormula pairing 0 top.succ.succ y.succ.succ e hw htop hy).2 entry⟩
    · intro z hz
      rw [realize_imp]
      intro member
      obtain ⟨v, hv, w, hw, rel, shape⟩ := backward z member
      rw [realize_ex]
      refine ⟨v, M.transitive hx hv, ?_⟩
      rw [realize_ex]
      let e := extend w (extend v (extend z env))
      exact ⟨w, hw, hv,
        (M.realize_pairMembershipFormula pairing 1 0 r.succ.succ.succ e (M.transitive hx hv) hw hr).2 rel,
        (M.realize_orderedPairFormula pairing 2 0 top.succ.succ.succ e hz hw htop).2 shape⟩

theorem rawCheckStep_eq {P : Type u} (s : Presentation P) (one : P) {R x y : ZFSet.{u}}
    (step : M.RawCheckStep (s.encode one) R x y)
    (children : ∀ v ∈ x, ∀ w ∈ M.sets, ZFSet.pair v w ∈ R → w = (Name.check s one v).val) :
    y = (Name.check s one x).val := by
  apply ZFSet.ext
  intro z
  rw [Name.mem_check_code]
  constructor
  · intro hz
    obtain ⟨v, hv, w, hw, rel, eq⟩ := step.2 z hz
    exact ⟨v, hv, eq.trans (congrArg (fun q => ZFSet.pair q (s.encode one)) (children v hv w hw rel))⟩
  · rintro ⟨v, hv, rfl⟩
    obtain ⟨w, hw, rel, entry⟩ := step.1 v hv
    rwa [children v hv w hw rel] at entry

end PartitionPilot.Forcing.TransitiveGround

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Geometry_CheckCertificates
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

theorem realize_checkState
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (top z R : ZFSet.{u}) (htop : top ∈ M.sets) (hz : z ∈ M.sets) (hr : R ∈ M.sets) :
    Realize M.sets checkStateFormula (extend z (extend R (extend top Fin.elim0))) ↔
      ∃ x ∈ M.sets, ∃ y ∈ M.sets, z = ZFSet.pair x y ∧ M.RawCheckStep top R x y := by
  rw [checkStateFormula, realize_ex]
  apply exists_congr
  intro x
  apply and_congr_right
  intro hx
  rw [realize_ex]
  apply exists_congr
  intro y
  apply and_congr_right
  intro hy
  let e := extend y (extend x (extend z (extend R (extend top Fin.elim0))))
  change (Realize M.sets _ e ∧ Realize M.sets _ e) ↔ _
  rw [M.realize_orderedPairFormula pairing 2 1 0 e hz hx hy,
    M.realize_checkStepFormula pairing 4 3 1 0 e htop hr hx hy]
  rfl

theorem checkCertificate_sound {P : Type u} (s : Presentation P) (one : P)
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0) (hone : s.encode one ∈ M.sets)
    {R : ZFSet.{u}} (hr : R ∈ M.sets)
    (certificate : Realize M.sets checkCertificateFormula (extend R (extend (s.encode one) Fin.elim0))) :
    ∀ x ∈ M.sets, ∀ y ∈ M.sets, ZFSet.pair x y ∈ R → y = (Name.check s one x).val := by
  have post : ∀ x ∈ M.sets, ∀ y ∈ M.sets, ZFSet.pair x y ∈ R →
      M.RawCheckStep (s.encode one) R x y := by
    intro x _ y _ rel
    have step := (realize_imp M.sets _ _ _).1 (certificate _ (M.transitive hr rel)) rel
    obtain ⟨v, _, w, _, eq, raw⟩ := (M.realize_checkState pairing (s.encode one) _ R
      hone (M.transitive hr rel) hr).1 step
    obtain ⟨rfl, rfl⟩ := ZFSet.pair_inj.1 eq
    exact raw
  intro x
  induction x using ZFSet.inductionOn with
  | h x ih =>
    intro hx y hy rel
    exact M.rawCheckStep_eq s one (post x hx y hy rel)
      (fun v hv w hw relation => ih v hv (M.transitive hx hv) w hw relation)

end PartitionPilot.Forcing.TransitiveGround

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


namespace PartitionPilot.Forcing.TransitiveGround

open SetRealization SetFormula
universe u
variable (M : TransitiveGround.{u})

theorem exists_checkState_fixedPoint
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (top : ZFSet.{u}) (htop : top ∈ M.sets) (B : ZFSet.{u}) (hB : B ∈ M.sets) :
    ∃ R ∈ M.sets, R ⊆ B ∧
      definableOperator M.sets checkStateFormula (extend top Fin.elim0) B R = R := by
  have mono : ∀ R ∈ M.sets, ∀ S ∈ M.sets, R ⊆ B → S ⊆ B → R ⊆ S →
      definableOperator M.sets checkStateFormula (extend top Fin.elim0) B R ⊆
        definableOperator M.sets checkStateFormula (extend top Fin.elim0) B S := by
    intro R hr S hs _ _ sub z hz
    obtain ⟨hzB, step⟩ := ZFSet.mem_sep.1 hz
    have hzM := M.transitive hB hzB
    obtain ⟨x, hx, y, hy, shape, raw⟩ := (M.realize_checkState pairing top z R htop hzM hr).1 step
    exact ZFSet.mem_sep.2 ⟨hzB, (M.realize_checkState pairing top z S htop hzM hs).2
      ⟨x, hx, y, hy, shape, M.rawCheckStep_mono sub raw⟩⟩
  obtain ⟨R, hr, bound, fixed, _⟩ := M.exists_greatest_definable_fixedPoint unions powers separation
    checkStateFormula (extend top Fin.elim0) (Fin.cases htop (fun i => Fin.elim0 i)) hB mono
  exact ⟨R, hr, bound, fixed⟩

theorem exists_groundCheck_certificate {P : Type u} (s : Presentation P) (one : P)
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0)
    (separation : SeparationSchema M.sets) (collection : CollectionSchema M.sets)
    (hone : s.encode one ∈ M.sets) (x : ZFSet.{u}) (hx : x ∈ M.sets)
    (hcheck : (Name.check s one x).val ∈ M.sets) :
    ∃ R ∈ M.sets, Realize M.sets checkCertificateFormula (extend R (extend (s.encode one) Fin.elim0)) ∧
      ZFSet.pair x (Name.check s one x).val ∈ R := by
  obtain ⟨T, hT, xT, checkT, trans⟩ := M.exists_pair_transitiveCover pairing unions separation collection hx hcheck
  let N : TransitiveGround.{u} := ⟨{z | z ∈ T}, fun hz hy => trans _ hz _ hy⟩
  obtain ⟨B, hB, pairBound⟩ := M.exists_pair_bound pairing unions powers hT hT
  obtain ⟨R, hr, bound, fixed⟩ := M.exists_checkState_fixedPoint pairing unions powers separation
    (s.encode one) hone B hB
  have certificate : Realize M.sets checkCertificateFormula (extend R (extend (s.encode one) Fin.elim0)) := by
    apply (M.realize_postfixedFormula checkStateFormula (extend (s.encode one) Fin.elim0) hr bound).2
    rw [fixed]
  have complete : ∀ v, v ∈ T → (Name.check s one v).val ∈ T →
      ZFSet.pair v (Name.check s one v).val ∈ R := by
    intro v
    induction v using ZFSet.inductionOn with
    | h v ih =>
      intro hv hc
      have childT : ∀ w ∈ v, (Name.check s one w).val ∈ T := by
        intro w hw
        exact (N.nameDomain s).children hc ((Name.entry_check one v (Name.check s one w) one).2
          ⟨w, hw, rfl, rfl⟩)
      have raw : M.RawCheckStep (s.encode one) R v (Name.check s one v).val := by
        constructor
        · intro w hw
          exact ⟨(Name.check s one w).val, M.transitive hT (childT w hw),
            ih w hw (trans _ hv _ hw) (childT w hw),
            (Name.mem_check_code s one v _).2 ⟨w, hw, rfl⟩⟩
        · intro z hz
          obtain ⟨w, hw, eq⟩ := (Name.mem_check_code s one v z).1 hz
          exact ⟨w, hw, (Name.check s one w).val, M.transitive hT (childT w hw),
            ih w hw (trans _ hv _ hw) (childT w hw), eq⟩
      have member : ZFSet.pair v (Name.check s one v).val ∈
          definableOperator M.sets checkStateFormula (extend (s.encode one) Fin.elim0) B R :=
        ZFSet.mem_sep.2 ⟨pairBound v hv (Name.check s one v).val hc,
          (M.realize_checkState pairing (s.encode one) _ R hone
            (M.orderedPair_mem pairing (M.transitive hT hv) (M.transitive hT hc)) hr).2
            ⟨v, M.transitive hT hv, (Name.check s one v).val, M.transitive hT hc, rfl, raw⟩⟩
      rwa [fixed] at member
  exact ⟨R, hr, certificate, complete x xT checkT⟩

end PartitionPilot.Forcing.TransitiveGround


namespace PartitionPilot.Forcing
open SetRealization SetFormula
universe u

namespace Name
variable {P : Type u} {s : Presentation P}

theorem orderedPair_code (one : P) (σ τ : Name s) :
    (orderedPair one σ τ).val = orderedPairNameCode (s.encode one) σ.val τ.val := by
  have single : singleton one σ = unorderedPair one σ σ := by
    apply Name.ext
    intro ν p
    simp only [singleton, unorderedPair, entry_assemble]
    constructor
    · rintro ⟨_, rfl, rfl⟩
      exact ⟨true, rfl, rfl⟩
    · rintro ⟨b, equal, rfl⟩
      have same : (if b then σ else σ) = σ := by split <;> rfl
      exact ⟨(), same.symm.trans equal, rfl⟩
  rw [orderedPair, single]
  rw [TransitiveGround.pairName_code, TransitiveGround.pairName_code,
    TransitiveGround.pairName_code]
  rfl

end Name

namespace TransitiveGround
variable (M : TransitiveGround.{u})

theorem pairNameCode_mem (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    {one x y : ZFSet.{u}} (hone : one ∈ M.sets) (hx : x ∈ M.sets) (hy : y ∈ M.sets) :
    pairNameCode one x y ∈ M.sets :=
  M.unorderedPair_mem pairing (M.orderedPair_mem pairing hx hone) (M.orderedPair_mem pairing hy hone)

theorem orderedPairNameCode_mem (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    {one x y : ZFSet.{u}} (hone : one ∈ M.sets) (hx : x ∈ M.sets) (hy : y ∈ M.sets) :
    orderedPairNameCode one x y ∈ M.sets :=
  M.pairNameCode_mem pairing hone (M.pairNameCode_mem pairing hone hx hx)
    (M.pairNameCode_mem pairing hone hx hy)

theorem realize_pairNameCodeFormula
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    {n} (z x y one : Fin n) (env : Fin n → ZFSet.{u})
    (members : ∀ j, env j ∈ M.sets) :
    Realize M.sets (pairNameCodeFormula z x y one) env ↔
      env z = pairNameCode (env one) (env x) (env y) := by
  rw [pairNameCodeFormula, realize_ex]
  constructor
  · rintro ⟨a, ha, rest⟩
    obtain ⟨b, hb, left, right, shape⟩ := (realize_ex M.sets _ _).1 rest
    have ea := (M.realize_orderedPairFormula pairing 1 x.succ.succ one.succ.succ
      _ ha (members x) (members one)).1 left
    have eb := (M.realize_orderedPairFormula pairing 0 y.succ.succ one.succ.succ
      _ hb (members y) (members one)).1 right
    have ez := (M.realize_unorderedPairFormula z.succ.succ 1 0 _ (members z) ha hb).1 shape
    exact ez.trans (congrArg₂ (fun p q : ZFSet.{u} => ({p, q} : ZFSet.{u})) ea eb)
  · intro equal
    have ha := M.orderedPair_mem pairing (members x) (members one)
    have hb := M.orderedPair_mem pairing (members y) (members one)
    refine ⟨ZFSet.pair (env x) (env one), ha, ?_⟩
    rw [realize_ex]
    refine ⟨ZFSet.pair (env y) (env one), hb, ?_, ?_, ?_⟩
    · exact (M.realize_orderedPairFormula pairing 1 x.succ.succ one.succ.succ
        _ ha (members x) (members one)).2 rfl
    · exact (M.realize_orderedPairFormula pairing 0 y.succ.succ one.succ.succ
        _ hb (members y) (members one)).2 rfl
    · exact (M.realize_unorderedPairFormula z.succ.succ 1 0 _ (members z) ha hb).2 equal

theorem realize_orderedPairNameCodeFormula
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    {n} (z x y one : Fin n) (env : Fin n → ZFSet.{u})
    (members : ∀ j, env j ∈ M.sets) :
    Realize M.sets (orderedPairNameCodeFormula z x y one) env ↔
      env z = orderedPairNameCode (env one) (env x) (env y) := by
  rw [orderedPairNameCodeFormula, realize_ex]
  constructor
  · rintro ⟨a, ha, rest⟩
    obtain ⟨b, hb, left, right, shape⟩ := (realize_ex M.sets _ _).1 rest
    have all : ∀ j, (extend b (extend a env)) j ∈ M.sets := Fin.cases hb (Fin.cases ha members)
    have ea := (M.realize_pairNameCodeFormula pairing 1 x.succ.succ x.succ.succ one.succ.succ _ all).1 left
    have eb := (M.realize_pairNameCodeFormula pairing 0 x.succ.succ y.succ.succ one.succ.succ _ all).1 right
    have ez := (M.realize_pairNameCodeFormula pairing z.succ.succ 1 0 one.succ.succ _ all).1 shape
    exact ez.trans (congrArg₂ (pairNameCode (env one)) ea eb)
  · intro equal
    have ha := M.pairNameCode_mem pairing (members one) (members x) (members x)
    have hb := M.pairNameCode_mem pairing (members one) (members x) (members y)
    refine ⟨pairNameCode (env one) (env x) (env x), ha, ?_⟩
    rw [realize_ex]
    have all : ∀ j, (extend (pairNameCode (env one) (env x) (env y))
      (extend (pairNameCode (env one) (env x) (env x)) env)) j ∈ M.sets :=
      Fin.cases hb (Fin.cases ha members)
    exact ⟨pairNameCode (env one) (env x) (env y), hb,
      (M.realize_pairNameCodeFormula pairing 1 x.succ.succ x.succ.succ one.succ.succ _ all).2 rfl,
      (M.realize_pairNameCodeFormula pairing 0 x.succ.succ y.succ.succ one.succ.succ _ all).2 rfl,
      (M.realize_pairNameCodeFormula pairing z.succ.succ 1 0 one.succ.succ _ all).2 equal⟩

end TransitiveGround





def checkCodePresentation (one : ZFSet.{u}) : Presentation (ULift.{u} Unit) where
  carrier := {one}
  encode _ := one
  injective := fun _ _ _ => Subsingleton.elim _ _
  mem_carrier x := by
    rw [ZFSet.mem_singleton]
    exact ⟨fun h => ⟨⟨()⟩, h.symm⟩, fun ⟨_, h⟩ => h.symm⟩

noncomputable def checkNameCode (one x : ZFSet.{u}) : ZFSet.{u} :=
  (Name.check (checkCodePresentation one) ⟨()⟩ x).val





namespace Name
variable {P : Type u} {s : Presentation P} {I f : ZFSet.{u}}

noncomputable def indexedGraphName (one : P) (function : FunctionGraphOn I f)
    (names : ∀ i, IsName s (function.value i)) : Name s :=
  assemble (fun i : I => orderedPair one (check s one i.val)
    ⟨function.value i, names i⟩) (fun _ => one)

theorem mem_indexedGraphName_code (one : P) (function : FunctionGraphOn I f)
    (names : ∀ i, IsName s (function.value i)) (z : ZFSet.{u}) :
    z ∈ (indexedGraphName one function names).val ↔
      ∃ i : I, z = ZFSet.pair
        (orderedPairNameCode (s.encode one) (check s one i.val).val (function.value i))
        (s.encode one) := by
  change z ∈ ZFSet.range _ ↔ _
  rw [ZFSet.mem_range]
  apply exists_congr
  intro index
  let named : Name s := ⟨function.value index, names index⟩
  change ZFSet.pair (orderedPair one (check s one index.val) named).val (s.encode one) = z ↔ _
  rw [orderedPair_code]
  exact eq_comm

end Name

end PartitionPilot.Forcing



namespace PartitionPilot.Forcing
open SetRealization SetFormula
universe u
variable {P : Type u}

noncomputable def namePool (s : Presentation P) (B : ZFSet.{u}) : ZFSet.{u} :=
  ZFSet.sep (IsName s) B

end PartitionPilot.Forcing



namespace PartitionPilot.Forcing.Name
open SetRealization Compression.RecursiveMaps
universe u v
variable {P Q : Type u} {s : Presentation P}

noncomputable def indexedTuple (one : P) (I : ZFSet.{u})
    (names : I.toSet → Name s) : Name s :=
  assemble (fun i : I => orderedPair one (check s one i.val) (names i)) (fun _ => one)

end PartitionPilot.Forcing.Name

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Definability_OrbitImageFormulas
attribute [-instance] _root_.OAI.PartitionPilot.Forcing.GroundMainPrefix.withTopSmall
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace PartitionPilot.Forcing.TransitiveGround

open SetRealization SetFormula
universe u
variable (M : TransitiveGround.{u}) {G P : Type u} [Group G] [PartialOrder P]
variable (a : PosetAction G P) (s : Presentation P) (t : Presentation G)

noncomputable def orbitParameters (W : ZFSet.{u}) : Fin 4 → ZFSet.{u} :=
  extend W (extend s.carrier (extend t.carrier (extend (a.conditionMapFamily s t) Fin.elim0)))

end PartitionPilot.Forcing.TransitiveGround

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Geometry_GroundMixtureTermBounds
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

noncomputable def mixtureTermCodes (τ : Name s) : ZFSet.{u} :=
  a.orbitCodes s (M.nameDomain s) (Name.immediateChildCodes τ)

end PartitionPilot.Forcing.TransitiveGround

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Forcing_GroundMixtureNames
attribute [-instance] _root_.OAI.PartitionPilot.Forcing.GroundMainPrefix.withTopSmall
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open scoped ZFSet


section

namespace PartitionPilot.Forcing.Name

open SetRealization
universe u
variable {P : Type u} [Preorder P] {s : Presentation P}

noncomputable def restrictBelow (p : P) (τ : Name s) : Name s := selectName (fun _ q => q ≤ p) τ

end PartitionPilot.Forcing.Name

end


namespace PartitionPilot.Forcing.PosetAction

open SetRealization
universe u
variable {G P : Type u} [Group G] [PartialOrder P]
variable (a : PosetAction G P) (s : Presentation P)

noncomputable def subgroupOrbitCodes (K : Subgroup G) (τ : Name s) : ZFSet.{u} :=
  ZFSet.range (fun g : K => (a.act s g.val τ).val)

end PartitionPilot.Forcing.PosetAction



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


section

namespace PartitionPilot.Forcing

open SetRealization Compression.RecursiveMaps.RationalHeights
universe u

noncomputable def fractionCarrier : ZFSet.{u} :=
  ZFSet.prod ZFSet.omega (ZFSet.sep (fun d => d ≠ natSetCode 0) ZFSet.omega)

def fractionEncode (a : Fraction) : ZFSet.{u} :=
  ZFSet.pair (natSetCode (Fraction.intCode a.num)) (natSetCode a.den)

theorem fractionEncode_mem (a : Fraction) : fractionEncode a ∈ fractionCarrier.{u} := by
  exact ZFSet.pair_mem_prod.2 ⟨natSetCode_mem_omega _,
    ZFSet.mem_sep.2 ⟨natSetCode_mem_omega _, fun h => by
      have := natSetCode_injective h
      have := a.positive
      omega⟩⟩

theorem fractionEncode_injective : Function.Injective (fractionEncode : Fraction → ZFSet.{u}) := by
  intro a b equal
  have parts := ZFSet.pair_inj.1 equal
  have hn := Fraction.intCode_injective a.num b.num (natSetCode_injective parts.1)
  have hd := natSetCode_injective parts.2
  cases a
  cases b
  cases hn
  cases hd
  rfl

theorem mem_fractionCarrier (z : ZFSet.{u}) :
    z ∈ fractionCarrier ↔ ∃ a : Fraction, fractionEncode a = z := by
  constructor
  · intro hz
    obtain ⟨n, hn, d, hd, rfl⟩ := ZFSet.mem_prod.1 hz
    obtain ⟨k, rfl⟩ := (mem_omega_iff_natSetCode n).1 hn
    obtain ⟨hd, nonzero⟩ := ZFSet.mem_sep.1 hd
    obtain ⟨m, rfl⟩ := (mem_omega_iff_natSetCode d).1 hd
    obtain ⟨a, ha⟩ := Fraction.intCode_surjective k
    have positive : 0 < m := by
      have : m ≠ 0 := fun h => nonzero (congrArg natSetCode h)
      omega
    exact ⟨⟨a, m, positive⟩, by dsimp only [fractionEncode]; rw [ha]⟩
  · rintro ⟨a, rfl⟩
    exact fractionEncode_mem a

noncomputable def fractionEquivGraph : ZFSet.{u} :=
  ZFSet.sep (fun z => ∃ a b : Fraction,
    z = ZFSet.pair (fractionEncode a) (fractionEncode b) ∧ Fraction.Equiv a b)
    (ZFSet.prod fractionCarrier fractionCarrier)

noncomputable def fractionLtGraph : ZFSet.{u} :=
  ZFSet.sep (fun z => ∃ a b : Fraction,
    z = ZFSet.pair (fractionEncode a) (fractionEncode b) ∧ Fraction.Lt a b)
    (ZFSet.prod fractionCarrier fractionCarrier)

theorem fractionEquivGraph_subset : fractionEquivGraph.{u} ⊆ ZFSet.prod fractionCarrier fractionCarrier :=
  fun _ hz => (ZFSet.mem_sep.1 hz).1

theorem pair_mem_fractionEquivGraph (a b : Fraction) :
    ZFSet.pair (fractionEncode a) (fractionEncode b) ∈ fractionEquivGraph.{u} ↔ Fraction.Equiv a b := by
  constructor
  · intro h
    obtain ⟨c, d, equal, rel⟩ := (ZFSet.mem_sep.1 h).2
    have parts := ZFSet.pair_inj.1 equal
    obtain rfl := fractionEncode_injective parts.1
    obtain rfl := fractionEncode_injective parts.2
    exact rel
  · intro rel
    exact ZFSet.mem_sep.2 ⟨ZFSet.pair_mem_prod.2 ⟨fractionEncode_mem a, fractionEncode_mem b⟩,
      a, b, rfl, rel⟩

end PartitionPilot.Forcing

end


namespace PartitionPilot.Forcing
open SetRealization SetFormula
universe u

def taggedSumEncode {A B : Type u} (s : Presentation A) (t : Presentation B) : A ⊕ B → ZFSet.{u}
  | .inl a => ZFSet.pair (natSetCode 0) (s.encode a)
  | .inr b => ZFSet.pair (natSetCode 1) (t.encode b)

theorem taggedSumEncode_injective {A B : Type u} (s : Presentation A) (t : Presentation B) :
    Function.Injective (taggedSumEncode s t) := by
  intro x y equal
  cases x <;> cases y
  · exact congrArg Sum.inl (s.injective (ZFSet.pair_inj.1 equal).2)
  · exact False.elim (Nat.zero_ne_one (natSetCode_injective (ZFSet.pair_inj.1 equal).1))
  · exact False.elim (Nat.zero_ne_one (natSetCode_injective (ZFSet.pair_inj.1 equal).1.symm))
  · exact congrArg Sum.inr (t.injective (ZFSet.pair_inj.1 equal).2)

end PartitionPilot.Forcing

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Models_GroundCountableQuotients
attribute [-instance] _root_.OAI.PartitionPilot.Forcing.GroundMainPrefix.withTopSmall
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PartitionPilot.Forcing

universe u

theorem canonical_exists {S E c x : ZFSet.{u}}
    (equivalence : EquivalenceRelationCode S E) (injection : InjectionCode S ZFSet.omega c)
    (hx : x ∈ S) : ∃ y ∈ canonicalRepresentatives S E c, ZFSet.pair x y ∈ E := by
  classical
  let valid : Nat → Prop := fun n => ∃ y ∈ S, ZFSet.pair x y ∈ E ∧ ZFSet.pair y (natSetCode n) ∈ c
  have existsValid : ∃ n, valid n := by
    obtain ⟨a, entry, _⟩ := injection.function.2 x hx
    have aNat := (ZFSet.pair_mem_prod.1 (injection.function.1 entry)).2
    obtain ⟨n, rfl⟩ := (mem_omega_iff_natSetCode a).1 aNat
    exact ⟨n, x, hx, equivalence.refl x hx, entry⟩
  obtain ⟨y, hy, related, entry⟩ := Nat.find_spec existsValid
  refine ⟨y, (mem_canonicalRepresentatives S E c y).2
    ⟨hy, natSetCode (Nat.find existsValid), natSetCode_mem_omega _, entry, ?_⟩, related⟩
  intro z hz yz m hm smaller
  obtain ⟨k, lower, equal⟩ := (mem_natSetCode m (Nat.find existsValid)).1 hm
  have validK : valid k := ⟨z, hz, equivalence.trans x y z related yz, equal ▸ smaller⟩
  exact Nat.not_lt_of_ge (Nat.find_min' existsValid validK) lower

theorem canonical_equiv_eq {S E c x y : ZFSet.{u}}
    (equivalence : EquivalenceRelationCode S E) (injection : InjectionCode S ZFSet.omega c)
    (hx : x ∈ canonicalRepresentatives S E c) (hy : y ∈ canonicalRepresentatives S E c)
    (related : ZFSet.pair x y ∈ E) : x = y := by
  obtain ⟨xS, n, hn, xn, leastX⟩ := (mem_canonicalRepresentatives S E c x).1 hx
  obtain ⟨yS, m, hm, ym, leastY⟩ := (mem_canonicalRepresentatives S E c y).1 hy
  obtain ⟨k, rfl⟩ := (mem_omega_iff_natSetCode n).1 hn
  obtain ⟨l, rfl⟩ := (mem_omega_iff_natSetCode m).1 hm
  rcases lt_trichotomy k l with smaller | equal | larger
  · exact False.elim (leastY x xS (equivalence.symm x y related) (natSetCode k)
      ((natSetCode_mem_iff k l).2 smaller) xn)
  · subst l
    exact injection.injective x y (natSetCode k) xn ym
  · exact False.elim (leastX y yS related (natSetCode l)
      ((natSetCode_mem_iff l k).2 larger) ym)

theorem canonical_exists_unique {S E c x : ZFSet.{u}}
    (equivalence : EquivalenceRelationCode S E) (injection : InjectionCode S ZFSet.omega c)
    (hx : x ∈ S) : ∃! y, y ∈ canonicalRepresentatives S E c ∧ ZFSet.pair x y ∈ E := by
  obtain ⟨y, hy, related⟩ := canonical_exists equivalence injection hx
  refine ⟨y, ⟨hy, related⟩, ?_⟩
  intro z hz
  exact canonical_equiv_eq equivalence injection hz.1 hy
    (equivalence.trans z x y (equivalence.symm x z hz.2) related)

end PartitionPilot.Forcing

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Definability_RationalCodeLaws
attribute [-instance] _root_.OAI.PartitionPilot.Forcing.GroundMainPrefix.withTopSmall
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace PartitionPilot.Forcing

open SetRealization Compression.RecursiveMaps.RationalHeights
universe u

theorem fractionEquivalence_code : EquivalenceRelationCode fractionCarrier.{u} fractionEquivGraph := by
  refine ⟨fractionEquivGraph_subset, ?_, ?_, ?_⟩
  · intro x hx
    obtain ⟨a, rfl⟩ := (mem_fractionCarrier x).1 hx
    exact (pair_mem_fractionEquivGraph a a).2 rfl
  · intro x y hxy
    have shape := ZFSet.pair_mem_prod.1 (fractionEquivGraph_subset hxy)
    obtain ⟨a, rfl⟩ := (mem_fractionCarrier x).1 shape.1
    obtain ⟨b, rfl⟩ := (mem_fractionCarrier y).1 shape.2
    exact (pair_mem_fractionEquivGraph b a).2 ((pair_mem_fractionEquivGraph a b).1 hxy).symm
  · intro x y z hxy hyz
    have shape := ZFSet.pair_mem_prod.1 (fractionEquivGraph_subset hxy)
    have zmem := (ZFSet.pair_mem_prod.1 (fractionEquivGraph_subset hyz)).2
    obtain ⟨a, rfl⟩ := (mem_fractionCarrier x).1 shape.1
    obtain ⟨b, rfl⟩ := (mem_fractionCarrier y).1 shape.2
    obtain ⟨d, rfl⟩ := (mem_fractionCarrier z).1 zmem
    exact (pair_mem_fractionEquivGraph a d).2 (Fraction.equiv_trans
      ((pair_mem_fractionEquivGraph a b).1 hxy) ((pair_mem_fractionEquivGraph b d).1 hyz))

noncomputable def rationalCarrier (c : ZFSet.{u}) : ZFSet.{u} :=
  canonicalRepresentatives fractionCarrier fractionEquivGraph c

theorem rationalCarrier_subset (c : ZFSet.{u}) : rationalCarrier c ⊆ fractionCarrier :=
  canonicalRepresentatives_subset _ _ _

noncomputable def rationalEncode {c : ZFSet.{u}}
    (hc : InjectionCode fractionCarrier ZFSet.omega c) (r : Rational) : ZFSet.{u} :=
  Classical.choose (canonical_exists_unique fractionEquivalence_code hc
    (fractionEncode_mem (Rational.representative r)))

theorem rationalEncode_spec {c : ZFSet.{u}}
    (hc : InjectionCode fractionCarrier ZFSet.omega c) (r : Rational) :
    rationalEncode hc r ∈ rationalCarrier c ∧
      ZFSet.pair (fractionEncode (Rational.representative r)) (rationalEncode hc r) ∈ fractionEquivGraph :=
  (Classical.choose_spec (canonical_exists_unique fractionEquivalence_code hc
    (fractionEncode_mem (Rational.representative r)))).1

theorem rationalEncode_class {c : ZFSet.{u}}
    (hc : InjectionCode fractionCarrier ZFSet.omega c) (r : Rational) :
    ∃ a : Fraction, fractionEncode a = rationalEncode hc r ∧ Rational.mk a = r := by
  have spec := rationalEncode_spec hc r
  obtain ⟨a, ha⟩ := (mem_fractionCarrier _).1 (rationalCarrier_subset c spec.1)
  refine ⟨a, ha, ?_⟩
  rw [← ha] at spec
  have eq := (Rational.mk_eq_iff _ _).2 ((pair_mem_fractionEquivGraph _ _).1 spec.2)
  exact eq.symm.trans (Rational.representative_eq r)

theorem rationalEncode_injective {c : ZFSet.{u}}
    (hc : InjectionCode fractionCarrier ZFSet.omega c) : Function.Injective (rationalEncode hc) := by
  intro r s eq
  obtain ⟨a, ha, ar⟩ := rationalEncode_class hc r
  obtain ⟨b, hb, bs⟩ := rationalEncode_class hc s
  have ab := fractionEncode_injective (ha.trans (eq.trans hb.symm))
  exact ar.symm.trans ((congrArg Rational.mk ab).trans bs)

theorem rationalEncode_of_canonical {c : ZFSet.{u}}
    (hc : InjectionCode fractionCarrier ZFSet.omega c) (a : Fraction)
    (ha : fractionEncode a ∈ rationalCarrier c) :
    rationalEncode hc (Rational.mk a) = fractionEncode a := by
  have unique := (Classical.choose_spec (canonical_exists_unique fractionEquivalence_code hc
    (fractionEncode_mem (Rational.representative (Rational.mk a))))).2
  exact (unique (fractionEncode a) ⟨ha,
    (pair_mem_fractionEquivGraph _ _).2 (Rational.representative_equiv a)⟩).symm

noncomputable def rationalPresentation {c : ZFSet.{u}}
    (hc : InjectionCode fractionCarrier ZFSet.omega c) : Presentation (ULift.{u} Rational) where
  carrier := rationalCarrier c
  encode r := rationalEncode hc r.down
  injective := fun _ _ eq => ULift.ext _ _ (rationalEncode_injective hc eq)
  mem_carrier x := by
    constructor
    · intro hx
      obtain ⟨a, rfl⟩ := (mem_fractionCarrier _).1 (rationalCarrier_subset c hx)
      exact ⟨⟨Rational.mk a⟩, rationalEncode_of_canonical hc a hx⟩
    · rintro ⟨r, rfl⟩
      exact (rationalEncode_spec hc r.down).1

noncomputable def rationalLtGraph (c : ZFSet.{u}) : ZFSet.{u} :=
  ZFSet.sep (fun z => z ∈ ZFSet.prod (rationalCarrier c) (rationalCarrier c)) fractionLtGraph

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

noncomputable def pairNameFamilyBound (one X Y : ZFSet.{u}) : ZFSet.{u} :=
  M.groundPower (ZFSet.prod (M.groundPower (ZFSet.prod (X ∪ Y) {one})) {one})

theorem orderedPairNameFamily_subset_bound
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    {one X Y : ZFSet.{u}} (hone : one ∈ M.sets) (hX : X ∈ M.sets) (hY : Y ∈ M.sets) :
    orderedPairNameFamily one X Y ⊆ M.pairNameFamilyBound one X Y := by
  intro z hz
  obtain ⟨x, hx, y, hy, rfl⟩ := (mem_orderedPairNameFamily one X Y z).1 hz
  have hxM := M.transitive hX hx
  have hyM := M.transitive hY hy
  have hxB : x ∈ X ∪ Y := ZFSet.mem_union.2 (Or.inl hx)
  have hyB : y ∈ X ∪ Y := ZFSet.mem_union.2 (Or.inr hy)
  have first : pairNameCode one x x ∈ M.groundPower (ZFSet.prod (X ∪ Y) {one}) :=
    (M.mem_groundPower _ _).2 ⟨M.pairNameCode_mem pairing hone hxM hxM,
      pairNameCode_subset hxB hxB⟩
  have second : pairNameCode one x y ∈ M.groundPower (ZFSet.prod (X ∪ Y) {one}) :=
    (M.mem_groundPower _ _).2 ⟨M.pairNameCode_mem pairing hone hxM hyM,
      pairNameCode_subset hxB hyB⟩
  exact (M.mem_groundPower _ _).2
    ⟨M.orderedPairNameCode_mem pairing hone hxM hyM, pairNameCode_subset first second⟩

theorem realize_orderedPairNameFamilyMemberFormula
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    {n} (z one X Y : Fin n) (env : Fin n → ZFSet.{u}) (members : ∀ j, env j ∈ M.sets) :
    Realize M.sets (orderedPairNameFamilyMemberFormula z one X Y) env ↔
      env z ∈ orderedPairNameFamily (env one) (env X) (env Y) := by
  rw [orderedPairNameFamilyMemberFormula, realize_ex, mem_orderedPairNameFamily]
  constructor
  · rintro ⟨x, hxM, hx, rest⟩
    obtain ⟨y, hyM, hy, named⟩ := (realize_ex M.sets _ _).1 rest
    exact ⟨x, hx, y, hy, (M.realize_orderedPairNameCodeFormula pairing
      z.succ.succ 1 0 one.succ.succ _ (Fin.cases hyM (Fin.cases hxM members))).1 named⟩
  · rintro ⟨x, hx, y, hy, equal⟩
    have hxM := M.transitive (members X) hx
    have hyM := M.transitive (members Y) hy
    refine ⟨x, hxM, hx, ?_⟩
    rw [realize_ex]
    exact ⟨y, hyM, hy, (M.realize_orderedPairNameCodeFormula pairing
      z.succ.succ 1 0 one.succ.succ _ (Fin.cases hyM (Fin.cases hxM members))).2 equal⟩

end TransitiveGround
end PartitionPilot.Forcing

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Forcing_GroundNiceNameNormalization
attribute [-instance] _root_.OAI.PartitionPilot.Forcing.GroundMainPrefix.withTopSmall
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace PartitionPilot.Forcing
open SetRealization Compression.RecursiveMaps SetFormula
universe u v
namespace Name
variable {P : Type u} {s : Presentation P}

noncomputable def familySet (one : P) (T : ZFSet.{u})
    (valid : ∀ z ∈ T, IsName s z) : Name s :=
  assemble (fun z : T => ⟨z.val, valid z.val z.property⟩) (fun _ => one)

theorem entry_familySet (one : P) (T : ZFSet.{u}) (valid : ∀ z ∈ T, IsName s z)
    (σ : Name s) (p : P) : Entry σ (familySet one T valid) p ↔ σ.val ∈ T ∧ p = one := by
  refine (entry_assemble (fun member : T => ⟨member.val, valid member.val member.property⟩)
    (fun _ => one) σ p).trans ?_
  constructor
  · rintro ⟨z, eq, hp⟩
    exact ⟨congrArg Subtype.val eq ▸ z.property, hp.symm⟩
  · rintro ⟨hσ, rfl⟩
    exact ⟨⟨σ.val, hσ⟩, Subtype.ext rfl, rfl⟩

theorem familySet_code (one : P) (T : ZFSet.{u}) (valid : ∀ z ∈ T, IsName s z) :
    (familySet one T valid).val = ZFSet.prod T {s.encode one} := by
  apply ZFSet.ext
  intro z
  change z ∈ ZFSet.range _ ↔ _
  rw [ZFSet.mem_range, ZFSet.mem_prod]
  constructor
  · rintro ⟨x, rfl⟩
    exact ⟨x.val, x.property, s.encode one, ZFSet.mem_singleton.2 rfl, rfl⟩
  · rintro ⟨x, hx, y, hy, eq⟩
    have same := ZFSet.mem_singleton.1 hy
    subst y
    exact ⟨⟨x, hx⟩, eq.symm⟩

theorem mem_eval_familySet (H : Set P) (one : P) (hone : one ∈ H)
    (T : ZFSet.{u}) (valid : ∀ z ∈ T, IsName s z) (x : ZFSet.{u}) :
    x ∈ eval H (familySet one T valid) ↔ ∃ τ : Name s, τ.val ∈ T ∧ eval H τ = x := by
  rw [mem_eval]
  simp only [entry_familySet]
  constructor
  · rintro ⟨τ, p, ⟨hτ, rfl⟩, _, eq⟩
    exact ⟨τ, hτ, eq⟩
  · rintro ⟨τ, hτ, eq⟩
    exact ⟨τ, one, ⟨hτ, rfl⟩, hone, eq⟩

theorem act_familySet {G : Type v} [Group G] [PartialOrder P] [OrderTop P]
    (a : PosetAction G P) (T : ZFSet.{u}) (valid : ∀ z ∈ T, IsName s z)
    (closed : ∀ g (τ : Name s), τ.val ∈ T → (a.act s g τ).val ∈ T) (g : G) :
    a.act s g (familySet ⊤ T valid) = familySet ⊤ T valid := by
  apply Name.ext
  intro σ p
  change Entry σ (rename s (a.iso g) (familySet ⊤ T valid)) p ↔ _
  rw [entry_rename, entry_familySet]
  constructor
  · rintro ⟨τ, q, entry, eq, hp⟩
    obtain ⟨hτ, rfl⟩ := (entry_familySet ⊤ T valid τ q).1 entry
    have target := closed g τ hτ
    change a.act s g τ = σ at eq
    exact ⟨eq ▸ target, hp.symm.trans (a.iso g).map_top⟩
  · rintro ⟨hσ, rfl⟩
    exact ⟨a.act s g⁻¹ σ, ⊤,
      (entry_familySet ⊤ T valid _ ⊤).2 ⟨closed g⁻¹ σ hσ, rfl⟩,
      a.act_inv_right s g σ, (a.iso g).map_top⟩

end Name

namespace TransitiveGround
variable (M : TransitiveGround.{u})
theorem familySet_mem {P : Type u} (s : Presentation P) (one : P)
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    {T : ZFSet.{u}} (hT : T ∈ M.sets) (hone : s.encode one ∈ M.sets)
    (valid : ∀ z ∈ T, IsName s z) : (Name.familySet one T valid).val ∈ M.sets := by
  rw [Name.familySet_code]
  apply M.prod_mem pairing unions powers separation hT
  simpa only [ZFSet.pair_eq_singleton] using M.unorderedPair_mem pairing hone hone

end TransitiveGround
end PartitionPilot.Forcing



namespace PartitionPilot.Forcing.Name
open SetRealization SetFormula
universe u v
variable {P : Type u} [PartialOrder P] [OrderTop P] {s : Presentation P}

noncomputable def niceNormalize (D : NameDomain s) (T : ZFSet.{u})
    (valid : ∀ z ∈ T, IsName s z) (τ : D.names) : Name s :=
  separationName D (.mem 0 1) (extend τ Fin.elim0) (familySet ⊤ T valid)

theorem entry_niceNormalize (D : NameDomain s) (T : ZFSet.{u})
    (valid : ∀ z ∈ T, IsName s z) (τ : D.names) (σ : Name s) (p : P) :
    Entry σ (niceNormalize D T valid τ) p ↔
      σ.val ∈ T ∧ ∃ h : σ ∈ D.names,
        Forces D (.mem 0 1) (extend ⟨σ, h⟩ (extend τ Fin.elim0)) p := by
  rw [niceNormalize, entry_separationName]
  constructor
  · rintro ⟨r, entry, _, forced⟩
    exact ⟨((entry_familySet ⊤ T valid σ r).1 entry).1, forced⟩
  · rintro ⟨member, forced⟩
    exact ⟨⊤, (entry_familySet ⊤ T valid σ ⊤).2 ⟨member, rfl⟩, le_top, forced⟩

theorem niceNormalize_subset (D : NameDomain s) (T : ZFSet.{u})
    (valid : ∀ z ∈ T, IsName s z) (τ : D.names) :
    (niceNormalize D T valid τ).val ⊆ ZFSet.prod T s.carrier := by
  intro z member
  obtain ⟨σ, p, rfl⟩ := entries_cover (niceNormalize D T valid τ) member
  exact ZFSet.pair_mem_prod.2
    ⟨((entry_niceNormalize D T valid τ σ p).1 member).1, s.encode_mem p⟩

theorem eval_niceNormalize (D : NameDomain s) (T : ZFSet.{u})
    (valid : ∀ z ∈ T, IsName s z) (τ : D.names)
    (family : familySet ⊤ T valid ∈ D.names) (H : ConditionFilter P)
    (generic : H.GenericFor (formulaFamily D)) :
    eval {p | H.mem p} (niceNormalize D T valid τ) =
      eval {p | H.mem p} τ.val ∩ eval {p | H.mem p} (familySet ⊤ T valid) := by
  rw [niceNormalize, eval_separationName D H generic (.mem 0 1) (extend τ Fin.elim0) family]
  apply ZFSet.ext
  intro x
  simp only [ZFSet.mem_sep, ZFSet.mem_inter]
  change (_ ∧ x ∈ eval {p | H.mem p} τ.val) ↔ _
  exact and_comm

theorem eval_niceNormalize_of_subset (D : NameDomain s) (T : ZFSet.{u})
    (valid : ∀ z ∈ T, IsName s z) (τ : D.names)
    (family : familySet ⊤ T valid ∈ D.names) (H : ConditionFilter P)
    (generic : H.GenericFor (formulaFamily D))
    (subset : eval {p | H.mem p} τ.val ⊆
      eval {p | H.mem p} (familySet ⊤ T valid)) :
    eval {p | H.mem p} (niceNormalize D T valid τ) = eval {p | H.mem p} τ.val := by
  rw [eval_niceNormalize D T valid τ family H generic]
  apply ZFSet.ext
  intro x
  exact ⟨fun h => (ZFSet.mem_inter.1 h).1,
    fun h => ZFSet.mem_inter.2 ⟨h, subset h⟩⟩

variable {G : Type v} [Group G] (a : PosetAction G P)

theorem niceNormalize_niceNameCode (D : NameDomain s)
    (closed : ∀ g σ, σ ∈ D.names → a.act s g σ ∈ D.names)
    (T : ZFSet.{u}) (valid : ∀ z ∈ T, IsName s z)
    (terms : ∀ g (σ : Name s), σ.val ∈ T → (a.act s g σ).val ∈ T)
    (τ : D.names) (K : Subgroup G) (fixed : K ≤ a.stabilizer s τ.val) :
    NiceNameCode a s T K (niceNormalize D T valid τ).val := by
  apply (niceNameCode_iff a s _).2
  refine ⟨niceNormalize_subset D T valid τ, ?_⟩
  intro g hg
  change a.act s g (niceNormalize D T valid τ) = niceNormalize D T valid τ
  unfold niceNormalize
  rw [a.act_separationName s D closed, act_familySet a T valid terms]
  have env : a.actAssignment s D closed g (extend τ Fin.elim0) = extend τ Fin.elim0 := by
    funext i
    refine Fin.cases ?_ (fun j => Fin.elim0 j) i
    apply Subtype.ext
    exact fixed hg
  rw [env]

end PartitionPilot.Forcing.Name



end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Geometry_RowPositionBounds
attribute [-instance] _root_.OAI.PartitionPilot.Forcing.GroundMainPrefix.withTopSmall
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace PartitionPilot.Forcing
open SetFormula SetRealization
universe u

namespace TransitiveGround
variable (M : TransitiveGround.{u})

noncomputable def rowPositionSequences (L r I mu : ZFSet.{u}) : ZFSet.{u} :=
  ZFSet.sep (RowPositionSequenceCode L r I mu) (M.groundRelations mu I)

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

section
universe u

theorem stageOneAssignment_eq_iff (t u w t' u' w' : ZFSet.{u}) :
    stageOneAssignment t u w = stageOneAssignment t' u' w' ↔
      t = t' ∧ u = u' ∧ w = w' := by
  simp only [stageOneAssignment, ZFSet.pair_inj]

end

namespace TransitiveGround

open SetFormula
universe u
variable (M : TransitiveGround.{u})

noncomputable def groundSmallSubsets (B N : ZFSet.{u}) : ZFSet.{u} :=
  ZFSet.sep (fun D => M.groundEmbeddable D N) (M.groundPower B)

theorem mem_groundSmallSubsets (B N D : ZFSet.{u}) :
    D ∈ M.groundSmallSubsets B N ↔ D ∈ M.sets ∧ D ⊆ B ∧ M.groundEmbeddable D N := by
  rw [groundSmallSubsets, ZFSet.mem_sep, M.mem_groundPower]
  exact and_assoc

theorem stageOneAssignments_mem
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    {I T : ZFSet.{u}} (hI : I ∈ M.sets) (hT : T ∈ M.sets) :
    stageOneAssignments I T ∈ M.sets :=
  M.prod_mem pairing unions powers separation hI (M.prod_mem pairing unions powers separation hT hT)

noncomputable def stageOneCandidateBound (rawRowCarrier I T : ZFSet.{u}) : ZFSet.{u} :=
  ZFSet.prod rawRowCarrier (M.groundSmallSubsets (stageOneAssignments I T) ZFSet.omega)

theorem pair_mem_stageOneCandidateBound (rawRowCarrier I T p A : ZFSet.{u}) :
    ZFSet.pair p A ∈ M.stageOneCandidateBound rawRowCarrier I T ↔
      p ∈ rawRowCarrier ∧ A ∈ M.sets ∧ A ⊆ stageOneAssignments I T ∧
        M.groundEmbeddable A ZFSet.omega := by
  rw [stageOneCandidateBound, ZFSet.pair_mem_prod, M.mem_groundSmallSubsets]

theorem mem_stageOneCandidateBound (rawRowCarrier I T z : ZFSet.{u}) :
    z ∈ M.stageOneCandidateBound rawRowCarrier I T ↔
      ∃ p ∈ rawRowCarrier, ∃ A ∈ M.sets, A ⊆ stageOneAssignments I T ∧
        M.groundEmbeddable A ZFSet.omega ∧ z = ZFSet.pair p A := by
  constructor
  · intro member
    obtain ⟨p, hp, A, hA, equal⟩ := ZFSet.mem_prod.1 member
    obtain ⟨ground, subset, small⟩ := (M.mem_groundSmallSubsets (stageOneAssignments I T) ZFSet.omega A).1 hA
    exact ⟨p, hp, A, ground, subset, small, equal⟩
  · rintro ⟨p, hp, A, ground, subset, small, rfl⟩
    exact (M.pair_mem_stageOneCandidateBound rawRowCarrier I T p A).2 ⟨hp, ground, subset, small⟩

theorem stageOneCandidateBound_empty {rawRowCarrier I T p : ZFSet.{u}}
    (hRow : rawRowCarrier ∈ M.sets) (hp : p ∈ rawRowCarrier) :
    ZFSet.pair p ∅ ∈ M.stageOneCandidateBound rawRowCarrier I T :=
  (M.pair_mem_stageOneCandidateBound rawRowCarrier I T p ∅).2
    ⟨hp, M.empty_mem ⟨rawRowCarrier, hRow⟩,
      fun z hz => False.elim (ZFSet.notMem_empty z hz),
      M.empty_groundEmbeddable ZFSet.omega ⟨rawRowCarrier, hRow⟩⟩

end TransitiveGround

section
open SetRealization SetFormula
universe u

noncomputable def stageOneDataBounds (A I T S L mu X r anchors tuples : ZFSet.{u}) : ZFSet.{u} :=
  ZFSet.sep (fun z => ∃ v ∈ A, ∃ D ∈ L, ∃ i ∈ I, ∃ u ∈ T, ∃ w ∈ T, ∃ E ∈ L,
    ∃ fu ∈ S, ∃ fw ∈ S, z = ZFSet.pair v D ∧ v = stageOneAssignment i u w ∧
      ZFSet.pair i E ∈ anchors ∧ ZFSet.pair E D ∈ r ∧
      ZFSet.pair fu u ∈ tuples ∧ ZFSet.pair fw w ∈ tuples ∧
      RowPositionBound mu X r fu D ∧ RowPositionBound mu X r fw D)
    (ZFSet.prod A L)

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


namespace PartitionPilot.Forcing.Name
open SetRealization Compression.RecursiveMaps
universe u v
variable {P : Type u} [PartialOrder P] [OrderTop P] {s : Presentation P}

noncomputable def refinementClass (T : ZFSet.{u})
    (valid : ∀ z ∈ T, IsName s z) (R w : Name s) : Name s :=
  selectName (fun z p => ForcesMem p (orderedPair ⊤ z w) R) (familySet ⊤ T valid)

theorem entry_refinementClass (T : ZFSet.{u}) (valid : ∀ z ∈ T, IsName s z)
    (R w z : Name s) (p : P) :
    Entry z (refinementClass T valid R w) p ↔
      z.val ∈ T ∧ ForcesMem p (orderedPair ⊤ z w) R := by
  rw [refinementClass, entry_selectName]
  constructor
  · rintro ⟨r, entry, _, forced⟩
    exact ⟨((entry_familySet ⊤ T valid z r).1 entry).1, forced⟩
  · rintro ⟨member, forced⟩
    exact ⟨⊤, (entry_familySet ⊤ T valid z ⊤).2 ⟨member, rfl⟩, le_top, forced⟩

theorem refinementClass_subset (T : ZFSet.{u}) (valid : ∀ z ∈ T, IsName s z)
    (R w : Name s) : (refinementClass T valid R w).val ⊆ ZFSet.prod T s.carrier := by
  intro x member
  obtain ⟨z, p, rfl⟩ := entries_cover (refinementClass T valid R w) member
  exact ZFSet.pair_mem_prod.2
    ⟨((entry_refinementClass T valid R w z p).1 member).1, s.encode_mem p⟩

variable {G : Type v} [Group G] (a : PosetAction G P)

theorem act_refinementClass (T : ZFSet.{u}) (valid : ∀ z ∈ T, IsName s z)
    (closed : ∀ g (z : Name s), z.val ∈ T → (a.act s g z).val ∈ T)
    (g : G) (R w : Name s) :
    a.act s g (refinementClass T valid R w) =
      refinementClass T valid (a.act s g R) (a.act s g w) := by
  unfold refinementClass
  rw [a.act_selectName s g _ (fun z p => ForcesMem p (orderedPair ⊤ z (a.act s g w)) (a.act s g R))]
  · rw [act_familySet a T valid closed]
  · intro z p
    have paired : a.act s g (orderedPair ⊤ z w) =
        orderedPair ⊤ (a.act s g z) (a.act s g w) := by
      change rename s (a.iso g) _ = _
      rw [rename_orderedPair, (a.iso g).map_top]
      rfl
    rw [← paired]
    exact a.forcesMem_act_iff s g p (orderedPair ⊤ z w) R

end PartitionPilot.Forcing.Name



namespace PartitionPilot.Forcing.Name
open SetRealization
universe u
variable {P Q : Type u} [PartialOrder P] [OrderTop P]
variable {s : Presentation P} (upper : Presentation Q) (incl : P → Q) (one : Q)

noncomputable def refinementAssignmentLabel (T : ZFSet.{u})
    (valid : ∀ z ∈ T, IsName s z) (idx : ZFSet.{u}) (Rf Rc : Name s) : Name upper :=
  assemble
    (fun a : {a : (T × T) × Q //
        ∃ row A, upper.encode a.2 = ZFSet.pair row A ∧
          stageOneAssignment idx a.1.1.val a.1.2.val ∈ A} =>
      orderedPair one
        (rename upper incl (refinementClass T valid Rc
          ⟨a.val.1.1.val, valid _ a.val.1.1.property⟩))
        (rename upper incl (refinementClass T valid Rf
          ⟨a.val.1.2.val, valid _ a.val.1.2.property⟩)))
    (fun a => a.val.2)

end PartitionPilot.Forcing.Name

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Geometry_GroundLiteralTaskFieldRecognition
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

theorem constantFamilyGraph_mem
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    {I x : ZFSet.{u}} (hI : I ∈ M.sets) (hx : x ∈ M.sets) : constantFamilyGraph I x ∈ M.sets := by
  have single : ({x} : ZFSet.{u}) ∈ M.sets := by
    simpa only [ZFSet.pair_eq_singleton] using M.unorderedPair_mem pairing hx hx
  exact M.prod_mem pairing unions powers separation hI single

end PartitionPilot.Forcing.TransitiveGround



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

theorem familyCodeGraph_function {I : Type v} [Small.{u} I]
    (key value : I → ZFSet.{u}) (injective : Function.Injective key) :
    FunctionGraphOn (ZFSet.range key) (familyCodeGraph key value) :=
  ⟨ZFSet.range value, familyCodeGraph_isFunc key value injective⟩

theorem familyCodeGraph_finite_ground {M : TransitiveGround.{u}} {I : Type v}
    [Small.{u} I] [Finite I]
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0) (nonempty : M.sets.Nonempty)
    (key value : I → ZFSet.{u})
    (keys : ∀ i, key i ∈ M.sets) (values : ∀ i, value i ∈ M.sets) :
    familyCodeGraph key value ∈ M.sets :=
  M.finite_range_mem pairing unions nonempty _
    (fun i => M.orderedPair_mem pairing (keys i) (values i))

end



section
open SetFormula SetRealization
universe u
namespace GroundDefinableFunction
variable {M : TransitiveGround.{u}} {n : Nat}
variable {f : (Fin (n + 1) → ZFSet.{u}) → ZFSet.{u}}

noncomputable def graph (_defined : GroundDefinableFunction M f)
    (params : Fin n → ZFSet.{u}) (A : ZFSet.{u}) : ZFSet.{u} :=
  familyCodeGraph (fun x : A => x.val) (fun x => f (extend x.val params))

theorem mem_graph (defined : GroundDefinableFunction M f)
    (params : Fin n → ZFSet.{u}) (A z : ZFSet.{u}) :
    z ∈ defined.graph params A ↔ ∃ x ∈ A, z = ZFSet.pair x (f (extend x params)) := by
  rw [graph, mem_familyCodeGraph]
  constructor
  · rintro ⟨x, equal⟩
    exact ⟨x.val, x.property, equal.symm⟩
  · rintro ⟨x, hx, equal⟩
    exact ⟨⟨x, hx⟩, equal.symm⟩

end GroundDefinableFunction
end




section
open SetRealization SetFormula
universe u

namespace TransitiveGround
variable (M : TransitiveGround.{u}) {G P : Type u} [Group G] [PartialOrder P]
variable (a : PosetAction G P) (s : Presentation P) (t : Presentation G)
variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
variable (unions : Realize M.sets SetFormula.union Fin.elim0)
variable (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
variable (collection : CollectionSchema M.sets)
variable (carrier : s.carrier ∈ M.sets) (group : t.carrier ∈ M.sets)
variable (maps : a.conditionMapFamily s t ∈ M.sets)
include pairing unions powers separation collection carrier group maps

omit pairing unions powers separation collection carrier group maps in
noncomputable def orbitCodeFamily (F : ZFSet.{u}) : ZFSet.{u} :=
  familyCodeGraph (fun W : F => W.val) (fun W => a.orbitCodes s (M.nameDomain s) W.val)

end TransitiveGround
end



open SetRealization SetFormula
universe u
namespace Name
variable {P : Type u} [PartialOrder P] [OrderTop P] {s : Presentation P}

noncomputable def refinementClassGraph (T : ZFSet.{u})
    (valid : ∀ z ∈ T, IsName s z) (R : Name s)
    (W : ZFSet.{u}) (validW : ∀ z ∈ W, IsName s z) : ZFSet.{u} :=
  familyCodeGraph (fun w : W => w.val)
    (fun w => (refinementClass T valid R ⟨w.val, validW w.val w.property⟩).val)

theorem mem_refinementClassGraph (T : ZFSet.{u})
    (valid : ∀ z ∈ T, IsName s z) (R : Name s)
    (W : ZFSet.{u}) (validW : ∀ z ∈ W, IsName s z) (x : ZFSet.{u}) :
    x ∈ refinementClassGraph T valid R W validW ↔
      ∃ w : Name s, w.val ∈ W ∧ x = ZFSet.pair w.val (refinementClass T valid R w).val := by
  rw [refinementClassGraph, mem_familyCodeGraph]
  constructor
  · rintro ⟨w, equal⟩
    exact ⟨⟨w.val, validW w.val w.property⟩, w.property, equal.symm⟩
  · rintro ⟨w, member, equal⟩
    exact ⟨⟨w.val, member⟩, equal.symm⟩

theorem pair_mem_refinementClassGraph (T : ZFSet.{u})
    (valid : ∀ z ∈ T, IsName s z) (R : Name s)
    (W : ZFSet.{u}) (validW : ∀ z ∈ W, IsName s z) (w : Name s) (y : ZFSet.{u}) :
    ZFSet.pair w.val y ∈ refinementClassGraph T valid R W validW ↔
      w.val ∈ W ∧ y = (refinementClass T valid R w).val := by
  rw [mem_refinementClassGraph]
  constructor
  · rintro ⟨z, member, equal⟩
    obtain ⟨same, value⟩ := ZFSet.pair_inj.1 equal
    have named : w = z := Subtype.ext same
    cases named
    exact ⟨member, value⟩
  · rintro ⟨member, equal⟩
    exact ⟨w, member, congrArg (ZFSet.pair w.val) equal⟩

end Name


end PartitionPilot.Forcing

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Geometry_FiniteIterationTraces
attribute [-instance] _root_.OAI.PartitionPilot.Forcing.GroundMainPrefix.withTopSmall
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace PartitionPilot.Forcing

open SetRealization
universe u

noncomputable def finiteIterationTrace {B : Type u} (s : Presentation B) (f : B → B)
    (b : B) (n : Nat) : ZFSet.{u} :=
  (natInitialPresentation (n + 1)).graph s (fun i => natIterate f b i.down.val)

theorem pair_mem_finiteIterationTrace {B : Type u} (s : Presentation B) (f : B → B)
    (b : B) (n k : Nat) (y : ZFSet.{u}) :
    ZFSet.pair (natSetCode k) y ∈ finiteIterationTrace s f b n ↔
      k ≤ n ∧ y = s.encode (natIterate f b k) := by
  rw [finiteIterationTrace, Presentation.mem_graph]
  constructor
  · rintro ⟨i, eq⟩
    obtain ⟨first, second⟩ := ZFSet.pair_inj.1 eq
    have same : i.down.val = k := natSetCode_injective first
    exact ⟨by have := i.down.isLt; omega, by simpa only [same] using second.symm⟩
  · rintro ⟨hk, rfl⟩
    exact ⟨⟨⟨k, by omega⟩⟩, rfl⟩

theorem finiteIterationTrace_code {B : Type u} (s : Presentation B) (f : B → B)
    (b : B) (n : Nat) :
    IterationTraceCode (natSetCode n) (natSetCode (n + 1)) s.carrier
      (s.graph s f) (s.encode b) (finiteIterationTrace s f b n) := by
  refine ⟨(natInitialPresentation (n + 1)).graph_isFunc s _, ?_, ?_⟩
  · exact (pair_mem_finiteIterationTrace s f b n 0 _).2 ⟨Nat.zero_le _, rfl⟩
  · intro i hi j _ x _ y _ successor prev next
    obtain ⟨k, hk, rfl⟩ := (mem_natSetCode i n).1 hi
    have previous := ((pair_mem_finiteIterationTrace s f b n k x).1 prev).2
    have jcode : j = natSetCode (k + 1) := successor
    have following := ((pair_mem_finiteIterationTrace s f b n (k + 1) y).1 (jcode ▸ next)).2
    rw [previous, following]
    exact (s.pair_mem_graph s f _ _).2 rfl

theorem IterationTraceCode.value {B : Type u} (s : Presentation B) (f : B → B) (b : B)
    {n : Nat} {t : ZFSet.{u}}
    (trace : IterationTraceCode (natSetCode n) (natSetCode (n + 1)) s.carrier
      (s.graph s f) (s.encode b) t) :
    ∀ k ≤ n, ZFSet.pair (natSetCode k) (s.encode (natIterate f b k)) ∈ t := by
  intro k
  induction k with
  | zero => exact fun _ => trace.seed
  | succ k ih =>
    intro hk
    have domain := (natSetCode_mem_iff (k + 1) (n + 1)).2 (by omega)
    obtain ⟨y, rel, _⟩ := trace.function.2 (natSetCode (k + 1)) domain
    have hy := (ZFSet.pair_mem_prod.1 (trace.function.1 rel)).2
    obtain ⟨c, eq⟩ := (s.mem_carrier y).1 hy
    have step := trace.next (natSetCode k) ((natSetCode_mem_iff k n).2 (by omega))
      (natSetCode (k + 1)) domain _ (s.encode_mem _) y hy rfl (ih (by omega)) rel
    rw [← eq] at step
    have output := (s.pair_mem_graph s f _ c).1 step
    have same : y = s.encode (natIterate f b (k + 1)) := eq.symm.trans (congrArg s.encode output.symm)
    exact same ▸ rel

theorem IterationTraceCode.output {B : Type u} (s : Presentation B) (f : B → B) (b : B)
    {n : Nat} {t y : ZFSet.{u}}
    (trace : IterationTraceCode (natSetCode n) (natSetCode (n + 1)) s.carrier
      (s.graph s f) (s.encode b) t) (rel : ZFSet.pair (natSetCode n) y ∈ t) :
    y = s.encode (natIterate f b n) := by
  obtain ⟨z, _, unique⟩ := trace.function.2 (natSetCode n)
    ((natSetCode_mem_iff n (n + 1)).2 (by omega))
  exact (unique y rel).trans (unique _ (trace.value s f b n (Nat.le_refl n))).symm

namespace TransitiveGround

open SetFormula

theorem finiteIterationTrace_mem (M : TransitiveGround.{u})
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (separation : SeparationSchema M.sets)
    (infinite : Realize M.sets SetFormula.infinity Fin.elim0)
    {B : Type u} (s : Presentation B) (f : B → B) (b : B) (n : Nat)
    (hB : s.carrier ∈ M.sets) : finiteIterationTrace s f b n ∈ M.sets :=
  M.finite_function_graph_mem pairing unions (natInitialPresentation (n + 1)) s _
    (M.natSetCode_mem separation infinite (n + 1)) hB

end TransitiveGround

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

noncomputable def natSuccessorGraph : ZFSet.{u} :=
  natPresentation.graph natPresentation (fun n => ⟨n.down + 1⟩)

theorem pair_mem_natSuccessorGraph (a b : Nat) :
    ZFSet.pair (natSetCode a) (natSetCode b) ∈ natSuccessorGraph.{u} ↔ b = a + 1 := by
  change ZFSet.pair (natPresentation.encode ⟨a⟩) (natPresentation.encode ⟨b⟩) ∈
    natPresentation.graph natPresentation (fun n => ⟨n.down + 1⟩) ↔ _
  rw [Presentation.pair_mem_graph]
  exact ⟨fun h => (congrArg ULift.down h).symm, fun h => ULift.ext _ _ h.symm⟩

theorem natSuccessorGraph_isFunc : ZFSet.IsFunc ZFSet.omega ZFSet.omega natSuccessorGraph.{u} :=
  natPresentation.graph_isFunc natPresentation _

noncomputable def natAddSection (a : Nat) : ZFSet.{u} :=
  natPresentation.graph natPresentation (fun n => ⟨a + n.down⟩)

end PartitionPilot.Forcing

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Definability_FiniteWordMapCodes
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
variable {B : Type u} (s : Presentation B)

theorem finiteWordGraph_nil : finiteWordGraph s [] = ∅ := by
  apply ZFSet.ext
  intro z
  rw [mem_finiteWordGraph]
  exact ⟨fun ⟨i, _⟩ => False.elim (Nat.not_lt_zero i.val i.isLt),
    fun h => False.elim (ZFSet.notMem_empty z h)⟩

end

open SetRealization SetFormula
universe u

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

theorem finiteWordGraph_append_entry {B : Type u} (s : Presentation B)
    (xs ys : List B) (k : Nat) (a : ZFSet.{u}) :
    ZFSet.pair (natSetCode k) a ∈ finiteWordGraph s (xs ++ ys) ↔
      ZFSet.pair (natSetCode k) a ∈ finiteWordGraph s xs ∨
        ∃ j, k = xs.length + j ∧ ZFSet.pair (natSetCode j) a ∈ finiteWordGraph s ys := by
  constructor
  · intro entry
    obtain ⟨hk, value⟩ := (pair_mem_finiteWordGraph s (xs ++ ys) k a).1 entry
    by_cases left : k < xs.length
    · apply Or.inl
      apply (pair_mem_finiteWordGraph s xs k a).2
      refine ⟨left, ?_⟩
      simpa only [List.get_eq_getElem, List.getElem_append_left left] using value
    · have right : xs.length ≤ k := Nat.le_of_not_gt left
      have hj : k - xs.length < ys.length := by simp only [List.length_append] at hk; omega
      refine Or.inr ⟨k - xs.length, by omega, (pair_mem_finiteWordGraph s ys _ a).2 ⟨hj, ?_⟩⟩
      simpa only [List.get_eq_getElem, List.getElem_append_right right] using value
  · rintro (entry | ⟨j, equal, entry⟩)
    · obtain ⟨hk, value⟩ := (pair_mem_finiteWordGraph s xs k a).1 entry
      apply (pair_mem_finiteWordGraph s (xs ++ ys) k a).2
      have bound : k < (xs ++ ys).length := by simp only [List.length_append]; omega
      refine ⟨bound, ?_⟩
      simpa only [List.get_eq_getElem, List.getElem_append_left hk] using value
    · subst k
      obtain ⟨hj, value⟩ := (pair_mem_finiteWordGraph s ys j a).1 entry
      apply (pair_mem_finiteWordGraph s (xs ++ ys) (xs.length + j) a).2
      have bound : xs.length + j < (xs ++ ys).length := by simp only [List.length_append]; omega
      refine ⟨bound, ?_⟩
      simpa only [List.get_eq_getElem,
        List.getElem_append_right (Nat.le_add_right xs.length j), Nat.add_sub_cancel_left] using value

end PartitionPilot.Forcing

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Geometry_GroundFiniteWordLength
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

namespace TransitiveGround

variable (M : TransitiveGround.{u})

noncomputable def finiteWordLengthGraph (A : ZFSet.{u}) : ZFSet.{u} :=
  ZFSet.sep (fun z => ∃ f ∈ M.finiteWords A, ∃ N ∈ ZFSet.omega,
    z = ZFSet.pair f N ∧ ZFSet.IsFunc N A f)
      (ZFSet.prod (M.finiteWords A) ZFSet.omega)

end TransitiveGround

end PartitionPilot.Forcing

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

theorem naturalFiniteTrace_mem_relations
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0) (separation : SeparationSchema M.sets)
    (infinite : Realize M.sets SetFormula.infinity Fin.elim0)
    (f : ULift.{u} Nat → ULift.{u} Nat) (a n : Nat) :
    finiteIterationTrace natPresentation f ⟨a⟩ n ∈ M.groundRelations ZFSet.omega ZFSet.omega := by
  refine (M.mem_groundRelations _ _ _).2
    ⟨M.finiteIterationTrace_mem pairing unions separation infinite natPresentation f ⟨a⟩ n
      (M.omega_mem separation infinite), ?_⟩
  intro z hz
  obtain ⟨x, hx, y, hy, rfl⟩ := ZFSet.mem_prod.1
    ((finiteIterationTrace_code natPresentation f ⟨a⟩ n).function.1 hz)
  obtain ⟨k, _, rfl⟩ := (mem_natSetCode x (n + 1)).1 hx
  exact ZFSet.pair_mem_prod.2 ⟨natSetCode_mem_omega k, hy⟩

end PartitionPilot.Forcing.TransitiveGround

end


namespace PartitionPilot.Forcing
open SetRealization SetFormula
universe u

namespace TransitiveGround
variable (M : TransitiveGround.{u})

noncomputable def finiteWordMapGraph (A B e : ZFSet.{u}) : ZFSet.{u} :=
  ZFSet.sep (fun z => ∃ f ∈ M.finiteWords A, ∃ g ∈ M.finiteWords B,
    z = ZFSet.pair f g ∧ FiniteWordMapCode ZFSet.omega A B e f g)
    (ZFSet.prod (M.finiteWords A) (M.finiteWords B))

end TransitiveGround





end PartitionPilot.Forcing



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

theorem indexedSizeRelation_partial {U R W N g F : ZFSet.{u}}
    (enumeration : ZFSet.IsFunc N R g) (family : ZFSet.IsFunc R W F)
    (codes : ∀ p f, ZFSet.pair p f ∈ F → InjectionCode p N f) :
    PartialFunctionCode (ZFSet.prod N N) U (indexedSizeRelation U R W N g F) := by
  refine ⟨fun _ hz => (ZFSet.mem_sep.1 hz).1, ?_⟩
  intro v x y vx vy
  obtain ⟨_, n, hn, k, _, vn, p, hp, f, _, np, pf, xk⟩ :=
    (pair_mem_indexedSizeRelation U R W N g F v x).1 vx
  obtain ⟨_, m, _, l, _, vm, q, _, h, _, mq, qh, yl⟩ :=
    (pair_mem_indexedSizeRelation U R W N g F v y).1 vy
  obtain ⟨nm, kl⟩ := ZFSet.pair_inj.1 (vn.symm.trans vm)
  subst m
  subst l
  obtain ⟨a, _, uniqueP⟩ := enumeration.2 n hn
  have pq := (uniqueP p np).trans (uniqueP q mq).symm
  subst q
  obtain ⟨b, _, uniqueF⟩ := family.2 p hp
  have fh := (uniqueF f pf).trans (uniqueF h qh).symm
  subst h
  exact (codes p f pf).injective x y k xk yl

end PartitionPilot.Forcing



namespace PartitionPilot.Forcing

open SetRealization
universe u

noncomputable def groundSequenceGraph {Q : ZFSet.{u}} (seq : Nat → SetMembers Q) : ZFSet.{u} :=
  natPresentation.graph (SetMembers.presentation Q) (fun n => seq n.down)

noncomputable def groundSequenceUnion {Q : ZFSet.{u}} (seq : Nat → SetMembers Q) : ZFSet.{u} :=
  ⋃₀ relationImage ZFSet.omega Q (groundSequenceGraph seq)

theorem mem_groundSequenceUnion {Q : ZFSet.{u}} (seq : Nat → SetMembers Q) (z : ZFSet.{u}) :
    z ∈ groundSequenceUnion seq ↔ ∃ n, z ∈ SetMembers.raw (seq n) := by
  rw [groundSequenceUnion, ZFSet.mem_sUnion]
  constructor
  · rintro ⟨p, hp, zp⟩
    obtain ⟨_, n, _, np⟩ := (mem_relationImage ZFSet.omega Q (groundSequenceGraph seq) p).1 hp
    obtain ⟨k, eq⟩ := (natPresentation.mem_graph (SetMembers.presentation Q) (fun n => seq n.down) _).1 np
    have second := (ZFSet.pair_inj.1 eq).2
    change SetMembers.raw (seq k.down) = p at second
    exact ⟨k.down, second.symm ▸ zp⟩
  · rintro ⟨n, hn⟩
    exact ⟨SetMembers.raw (seq n), (mem_relationImage ZFSet.omega Q (groundSequenceGraph seq) _).2
      ⟨SetMembers.raw_mem _, natSetCode n, natSetCode_mem_omega _,
        (natPresentation.pair_mem_graph (SetMembers.presentation Q) (fun k => seq k.down) ⟨n⟩ (seq n)).2 rfl⟩, hn⟩

def InternallyCountablyClosed (M : TransitiveGround.{u}) {P : Type u} [Preorder P]
    (s : Presentation P) : Prop :=
  ∀ seq : Nat → P, natPresentation.graph s (fun n => seq n.down) ∈ M.sets →
    Antitone seq → ∃ p, ∀ n, p ≤ seq n

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

noncomputable def binaryUnionEnumeration (A B : ZFSet.{u}) : ZFSet.{u} :=
  insert (ZFSet.pair (natSetCode 0) A)
    (ZFSet.prod (ZFSet.sep (fun n => n ≠ natSetCode 0) ZFSet.omega) {B})

theorem pair_mem_binaryUnionEnumeration (A B n p : ZFSet.{u}) :
    ZFSet.pair n p ∈ binaryUnionEnumeration A B ↔
      (n = natSetCode 0 ∧ p = A) ∨
      (n ∈ ZFSet.omega ∧ n ≠ natSetCode 0 ∧ p = B) := by
  simp only [binaryUnionEnumeration, ZFSet.mem_insert_iff, ZFSet.pair_inj,
    ZFSet.pair_mem_prod, ZFSet.mem_sep, ZFSet.mem_singleton, and_assoc]

theorem binaryUnionEnumeration_isFunc (A B : ZFSet.{u}) :
    ZFSet.IsFunc ZFSet.omega {A, B} (binaryUnionEnumeration A B) := by
  classical
  refine ⟨?_, ?_⟩
  · intro z hz
    rcases ZFSet.mem_insert_iff.1 hz with rfl | hz
    · exact ZFSet.pair_mem_prod.2 ⟨natSetCode_mem_omega 0, ZFSet.mem_pair.2 (Or.inl rfl)⟩
    · obtain ⟨n, hn, p, hp, rfl⟩ := ZFSet.mem_prod.1 hz
      exact ZFSet.pair_mem_prod.2
        ⟨(ZFSet.mem_sep.1 hn).1, ZFSet.mem_pair.2 (Or.inr (ZFSet.mem_singleton.1 hp))⟩
  · intro n hn
    by_cases zero : n = natSetCode 0
    · refine ⟨A, (pair_mem_binaryUnionEnumeration A B n A).2 (Or.inl ⟨zero, rfl⟩), ?_⟩
      intro p hp
      rcases (pair_mem_binaryUnionEnumeration A B n p).1 hp with h | h
      · exact h.2
      · exact False.elim (h.2.1 zero)
    · refine ⟨B, (pair_mem_binaryUnionEnumeration A B n B).2 (Or.inr ⟨hn, zero, rfl⟩), ?_⟩
      intro p hp
      rcases (pair_mem_binaryUnionEnumeration A B n p).1 hp with h | h
      · exact False.elim (zero h.1)
      · exact h.2.2

theorem binaryUnionEnumeration_onto (A B : ZFSet.{u}) :
    ∀ p ∈ ({A, B} : ZFSet.{u}),
      ∃ n ∈ ZFSet.omega, ZFSet.pair n p ∈ binaryUnionEnumeration A B := by
  intro p hp
  rcases ZFSet.mem_pair.1 hp with hp | hp
  · subst p
    exact ⟨natSetCode 0, natSetCode_mem_omega 0,
      (pair_mem_binaryUnionEnumeration A B _ _).2 (Or.inl ⟨rfl, rfl⟩)⟩
  · subst p
    exact ⟨natSetCode 1, natSetCode_mem_omega 1,
      (pair_mem_binaryUnionEnumeration A B _ _).2
        (Or.inr ⟨natSetCode_mem_omega 1, fun eq => Nat.one_ne_zero (natSetCode_injective eq), rfl⟩)⟩

namespace TransitiveGround

open SetFormula
variable (M : TransitiveGround.{u})

theorem binaryUnionEnumeration_mem
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (infinite : Realize M.sets SetFormula.infinity Fin.elim0)
    {A B : ZFSet.{u}} (hA : A ∈ M.sets) (hB : B ∈ M.sets) :
    binaryUnionEnumeration A B ∈ M.sets := by
  have hzero := M.natSetCode_mem separation infinite 0
  have nonzero : ZFSet.sep (fun n => n ≠ natSetCode 0) ZFSet.omega ∈ M.sets :=
    M.bounded_separation_mem separation (.neg (.equal 0 1))
      (extend (natSetCode 0) Fin.elim0) (Fin.cases hzero (fun j => Fin.elim0 j))
      (M.omega_mem separation infinite)
  have singleton : ({B} : ZFSet.{u}) ∈ M.sets := by
    simpa only [ZFSet.pair_eq_singleton] using M.unorderedPair_mem pairing hB hB
  exact M.insert_mem pairing unions (M.orderedPair_mem pairing hzero hA)
    (M.prod_mem pairing unions powers separation nonzero singleton)

end TransitiveGround

end PartitionPilot.Forcing



end

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Transfinite_GroundCoinitialOperations
attribute [-instance] _root_.OAI.PartitionPilot.Forcing.GroundMainPrefix.withTopSmall
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace PartitionPilot.Forcing

section

universe u

namespace TransitiveGround

def InternalCountableBelow (M : TransitiveGround.{u}) (order F target : ZFSet.{u}) : Prop :=
  ∃ B ∈ M.sets, M.groundEmbeddable B ZFSet.omega ∧ CoinitialBelowCode order F target B

end TransitiveGround






noncomputable def copyPullback (A L e F : ZFSet.{u}) : ZFSet.{u} :=
  relationImage F A (relationConverse A L e)

end



end PartitionPilot.Forcing

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Transfinite_GroundChronologicalBasis
attribute [-instance] _root_.OAI.PartitionPilot.Forcing.GroundMainPrefix.withTopSmall
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PartitionPilot.Forcing

universe u

noncomputable def essentialBirthIndices (F T r birth : ZFSet.{u}) : ZFSet.{u} :=
  relationImage (birthEssentialSet F T r birth) T birth

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

noncomputable def heightColumnFiber (S C Q h c : ZFSet.{u}) : ZFSet.{u} :=
  relationImage (ZFSet.prod {c} Q) S (relationConverse S (ZFSet.prod C Q) h)

end



open SetFormula
universe u

noncomputable def naturalFamilyShift (family : ZFSet.{u}) : ZFSet.{u} :=
  relationCompose ZFSet.omega ZFSet.omega family.sUnion.sUnion natSuccessorGraph family


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

universe u v

noncomputable def essentialBirthFiber (F T r birth t : ZFSet.{u}) : ZFSet.{u} :=
  relationFiber (birthEssentialSet F T r birth)
    (relationConverse (birthEssentialSet F T r birth) (essentialBirthIndices F T r birth) birth) t

end



section
universe u

namespace GroundMainStage
variable {M : TransitiveGround.{u}} {C D rD : ZFSet.{u}}
variable (stage : GroundMainStage M C D rD)

theorem bottom_ground : stage.bottom ∈ M.sets := M.transitive stage.carrier_ground stage.bottom_mem
theorem top_ground : stage.top ∈ M.sets := M.transitive stage.carrier_ground stage.top_mem
theorem identity_ground : stage.identity ∈ M.sets := M.transitive stage.actors_ground stage.group_code.identity_mem

end GroundMainStage





noncomputable def mainStageCode (P r μ G m inv one A bottom top height : ZFSet.{u}) : ZFSet.{u} :=
  nonemptyTupleCode 10 (Fin.cases P (Fin.cases r (Fin.cases μ (Fin.cases G (Fin.cases m (Fin.cases inv (Fin.cases one (Fin.cases A (Fin.cases bottom (Fin.cases top (Fin.cases height (Fin.elim0))))))))))))

namespace GroundMainStage
open SetFormula
variable {M : TransitiveGround.{u}} {C D rD : ZFSet.{u}}

def field (stage : GroundMainStage M C D rD) : Fin 11 → ZFSet.{u} :=
  Fin.cases stage.carrier (Fin.cases stage.order (Fin.cases stage.meetGraph (Fin.cases stage.actors (Fin.cases stage.multiplication (Fin.cases stage.inverse (Fin.cases stage.identity (Fin.cases stage.action (Fin.cases stage.bottom (Fin.cases stage.top (Fin.cases stage.height (Fin.elim0)))))))))))

noncomputable def code (stage : GroundMainStage M C D rD) : ZFSet.{u} :=
  nonemptyTupleCode 10 stage.field

theorem field_injective : Function.Injective (field (M := M) (C := C) (D := D) (rD := rD)) := by
  intro first second equal
  exact ext (congrFun equal (0 : Fin 11)) (congrFun equal (1 : Fin 11)) (congrFun equal (2 : Fin 11)) (congrFun equal (3 : Fin 11)) (congrFun equal (4 : Fin 11)) (congrFun equal (5 : Fin 11)) (congrFun equal (6 : Fin 11)) (congrFun equal (7 : Fin 11)) (congrFun equal (8 : Fin 11)) (congrFun equal (9 : Fin 11)) (congrFun equal (10 : Fin 11))

theorem code_injective : Function.Injective (code (M := M) (C := C) (D := D) (rD := rD)) := by
  intro first second equal
  exact field_injective (nonemptyTupleCode_injective 10 equal)

theorem field_ground (stage : GroundMainStage M C D rD) : ∀ j, stage.field j ∈ M.sets :=
  Fin.cases stage.carrier_ground (Fin.cases stage.order_ground (Fin.cases stage.meet_ground (Fin.cases stage.actors_ground (Fin.cases stage.multiplication_ground (Fin.cases stage.inverse_ground (Fin.cases stage.identity_ground (Fin.cases stage.action_ground (Fin.cases stage.bottom_ground (Fin.cases stage.top_ground (Fin.cases stage.height_ground ((fun i => Fin.elim0 i))))))))))))

theorem code_mem (stage : GroundMainStage M C D rD)
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0) : stage.code ∈ M.sets :=
  M.nonemptyTupleCode_mem pairing 10 stage.field stage.field_ground

end GroundMainStage

end



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

def groundRecursionStep (M : TransitiveGround.{u}) {k : Nat}
    (φ : SetFormula (k + 3)) (params : Fin k → ZFSet.{u}) (a p y : ZFSet.{u}) : Prop :=
  p ∈ M.sets ∧ y ∈ M.sets ∧ Realize M.sets φ (extend a (extend p (extend y params)))


end PartitionPilot.Forcing

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Transfinite_GroundIntervalRecursion
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

def GroundOrdinalStepClosure (M : TransitiveGround.{u}) (T : ZFSet.{u})
    {k : Nat} (φ : SetFormula (k + 3)) (params : Fin k → ZFSet.{u}) : Prop :=
  ∀ α ∈ T, ∀ p ∈ M.sets, OrdinalRecursionTrace (groundRecursionStep M φ params) α p →
    ∃ y ∈ M.sets, Realize M.sets φ (extend α (extend p (extend y params))) ∧
      ∀ z ∈ M.sets, Realize M.sets φ (extend α (extend p (extend z params))) → z = y

end PartitionPilot.Forcing



end

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

structure IntervalEmbeddingFamilyInputs (I As rs los his D rD : ZFSet.{u}) : Prop where
  sources : FunctionGraphOn I As
  orders : FunctionGraphOn I rs
  lows : FunctionGraphOn I los
  highs : FunctionGraphOn I his
  source_order : ∀ i, StrictLinearOrderCode (sources.value i) (orders.value i)
  lower_mem : ∀ i, lows.value i ∈ D
  upper_mem : ∀ i, highs.value i ∈ D
  gap : ∀ i, ZFSet.pair (lows.value i) (highs.value i) ∈ rD

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

theorem mem_fixedTopCarrier (P x : ZFSet.{u}) : x ∈ fixedTopCarrier P ↔ x = P ∨ x ∈ P :=
  ZFSet.mem_insert_iff

theorem fixedTopCarrier_top (P : ZFSet.{u}) : P ∈ fixedTopCarrier P :=
  (mem_fixedTopCarrier P P).2 (Or.inl rfl)

theorem fixedTopCarrier_old {P x : ZFSet.{u}} (hx : x ∈ P) : x ∈ fixedTopCarrier P :=
  (mem_fixedTopCarrier P x).2 (Or.inr hx)

theorem fixedTopCarrier_subset (P : ZFSet.{u}) : P ⊆ fixedTopCarrier P :=
  fun _ hx => fixedTopCarrier_old hx

theorem fixedTopOrder_subset (P r : ZFSet.{u}) : r ⊆ fixedTopOrder P r :=
  fun _ hx => ZFSet.mem_union.2 (Or.inl hx)

theorem fixedTopOrder_greatest {P r x : ZFSet.{u}} (hx : x ∈ fixedTopCarrier P) :
    ZFSet.pair x P ∈ fixedTopOrder P r :=
  (pair_mem_fixedTopOrder P r x P).2 (Or.inr ⟨hx, rfl⟩)

theorem fixedTopOrder_strict_top {P r x : ZFSet.{u}}
    (old : PartialOrderCode P r) (hx : x ∈ P) :
    ZFSet.pair x P ∈ fixedTopOrder P r ∧ ZFSet.pair P x ∉ fixedTopOrder P r := by
  refine ⟨fixedTopOrder_greatest (fixedTopCarrier_old hx), ?_⟩
  intro entry
  exact ZFSet.mem_irrefl P (fixedTopOrder_no_new_below old hx entry)

theorem fixedTopOrder_top_iff {P r x : ZFSet.{u}} (old : PartialOrderCode P r) :
    ZFSet.pair P x ∈ fixedTopOrder P r ↔ x = P := by
  rw [pair_mem_fixedTopOrder]
  constructor
  · rintro (entry | ⟨_, equal⟩)
    · exact False.elim (ZFSet.mem_irrefl P (ZFSet.pair_mem_prod.1 (old.relation entry)).1)
    · exact equal
  · intro equal
    exact Or.inr ⟨fixedTopCarrier_top P, equal⟩

theorem fixedTopOrder_code {P r : ZFSet.{u}} (old : PartialOrderCode P r) :
    PartialOrderCode (fixedTopCarrier P) (fixedTopOrder P r) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro z hz
    rcases ZFSet.mem_union.1 hz with entry | entry
    · obtain ⟨x, hx, y, hy, rfl⟩ := ZFSet.mem_prod.1 (old.relation entry)
      exact ZFSet.pair_mem_prod.2 ⟨fixedTopCarrier_old hx, fixedTopCarrier_old hy⟩
    · obtain ⟨x, hx, y, hy, rfl⟩ := ZFSet.mem_prod.1 entry
      have equal := ZFSet.mem_singleton.1 hy
      exact ZFSet.pair_mem_prod.2 ⟨hx, equal.symm ▸ fixedTopCarrier_top P⟩
  · intro x hx
    rcases (mem_fixedTopCarrier P x).1 hx with rfl | oldx
    · exact fixedTopOrder_greatest hx
    · exact (pair_mem_fixedTopOrder P r x x).2 (Or.inl (old.refl x oldx))
  · intro x hx y hy xy yx
    rcases (mem_fixedTopCarrier P x).1 hx with rfl | oldx
    · exact ((fixedTopOrder_top_iff old).1 xy).symm
    · have oldy := fixedTopOrder_no_new_below old oldx yx
      exact old.antisymm x oldx y oldy ((fixedTopOrder_old_iff oldy).1 xy)
        ((fixedTopOrder_old_iff oldx).1 yx)
  · intro x hx y _ z hz xy yz
    rcases (mem_fixedTopCarrier P z).1 hz with rfl | oldz
    · exact fixedTopOrder_greatest hx
    · have oldy := fixedTopOrder_no_new_below old oldz yz
      have oldx := fixedTopOrder_no_new_below old oldy xy
      exact (fixedTopOrder_old_iff oldz).2 (old.trans x oldx y oldy z oldz
        ((fixedTopOrder_old_iff oldy).1 xy) ((fixedTopOrder_old_iff oldz).1 yz))

end PartitionPilot.Forcing

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

structure TemplateHeightFamilyInputs
    {P rP μP I Qs rs μs As Es Fs Ss : ZFSet.{u}}
    (d : AttachmentBatchInputs P rP μP I Qs rs μs As Es Fs Ss)
    (Vs vrs Hs : ZFSet.{u}) : Prop where
  ranges : FunctionGraphOn I Vs
  orders : FunctionGraphOn I vrs
  heights : FunctionGraphOn I Hs
  linear : ∀ i, StrictLinearOrderCode (ranges.value i) (orders.value i)
  function : ∀ i, ZFSet.IsFunc (d.space i) (ranges.value i) (heights.value i)
  strict : ∀ i x y a b, ZFSet.pair x y ∈ d.rel i → x ≠ y →
    ZFSet.pair x a ∈ heights.value i → ZFSet.pair y b ∈ heights.value i →
      ZFSet.pair a b ∈ orders.value i

noncomputable def componentHeightGraph (I Qs B Hs Cs E C D : ZFSet.{u}) : ZFSet.{u} :=
  ZFSet.sep (fun w => ∃ i ∈ I, ∃ Q ∈ ⋃₀ ⋃₀ Qs, ∃ g ∈ ⋃₀ ⋃₀ Hs, ∃ f ∈ ⋃₀ ⋃₀ E,
    ∃ q ∈ Q, ∃ a ∈ B, ∃ c ∈ C, ∃ z ∈ D,
      w = ZFSet.pair (ZFSet.pair i q) (ZFSet.pair c z) ∧
      ZFSet.pair i Q ∈ Qs ∧ ZFSet.pair i g ∈ Hs ∧ ZFSet.pair i f ∈ E ∧
      ZFSet.pair i c ∈ Cs ∧ ZFSet.pair q a ∈ g ∧ ZFSet.pair a z ∈ f)
    (ZFSet.prod (indexedAttachmentDomain I Qs) (ZFSet.prod C D))

theorem componentHeightGraph_shape (I Qs B Hs Cs E C D : ZFSet.{u}) :
    componentHeightGraph I Qs B Hs Cs E C D ⊆
      ZFSet.prod (indexedAttachmentDomain I Qs) (ZFSet.prod C D) :=
  fun _ h => (ZFSet.mem_sep.1 h).1

theorem pair_mem_componentHeightGraph (I Qs B Hs Cs E C D i q c z : ZFSet.{u}) :
    ZFSet.pair (ZFSet.pair i q) (ZFSet.pair c z) ∈ componentHeightGraph I Qs B Hs Cs E C D ↔
      i ∈ I ∧ c ∈ C ∧ z ∈ D ∧ ∃ Q g f, ZFSet.pair i Q ∈ Qs ∧
        ZFSet.pair i g ∈ Hs ∧ ZFSet.pair i f ∈ E ∧ q ∈ Q ∧ ZFSet.pair i c ∈ Cs ∧
        ∃ a ∈ B, ZFSet.pair q a ∈ g ∧ ZFSet.pair a z ∈ f := by
  constructor
  · intro member
    obtain ⟨j, hj, Q, _, g, _, f, _, u, hu, a, ha, b, hb, v, hv,
      equal, eQ, eg, ef, ec, height, image⟩ := (ZFSet.mem_sep.1 member).2
    obtain ⟨left, right⟩ := ZFSet.pair_inj.1 equal
    obtain ⟨rfl, rfl⟩ := ZFSet.pair_inj.1 left
    obtain ⟨rfl, rfl⟩ := ZFSet.pair_inj.1 right
    exact ⟨hj, hb, hv, Q, g, f, eQ, eg, ef, hu, ec, a, ha, height, image⟩
  · rintro ⟨hi, hc, hz, Q, g, f, eQ, eg, ef, hq, ec, a, ha, height, image⟩
    exact ZFSet.mem_sep.2 ⟨ZFSet.pair_mem_prod.2
      ⟨(pair_mem_indexedAttachmentDomain I Qs i q).2 ⟨hi, Q, eQ, hq⟩,
        ZFSet.pair_mem_prod.2 ⟨hc, hz⟩⟩,
      i, hi, Q, pair_second_mem_doubleUnion eQ, g, pair_second_mem_doubleUnion eg,
      f, pair_second_mem_doubleUnion ef, q, hq, a, ha, c, hc, z, hz,
      rfl, eQ, eg, ef, ec, height, image⟩

namespace TemplateHeightFamilyInputs

variable {P rP μP I Qs rs μs As Es Fs Ss Vs vrs Hs B Cs E C D : ZFSet.{u}}
    {d : AttachmentBatchInputs P rP μP I Qs rs μs As Es Fs Ss}
    (t : TemplateHeightFamilyInputs d Vs vrs Hs)

theorem componentHeightGraph_entry_iff (embeddings : FunctionGraphOn I E)
    (i : {i : ZFSet.{u} // i ∈ I}) (q c z : ZFSet.{u}) :
    ZFSet.pair (ZFSet.pair i.val q) (ZFSet.pair c z) ∈ componentHeightGraph I Qs B Hs Cs E C D ↔
      q ∈ d.space i ∧ c ∈ C ∧ z ∈ D ∧ ZFSet.pair i.val c ∈ Cs ∧
        ∃ a ∈ B, ZFSet.pair q a ∈ t.heights.value i ∧ ZFSet.pair a z ∈ embeddings.value i := by
  rw [pair_mem_componentHeightGraph]
  constructor
  · rintro ⟨_, hc, hz, Q, g, f, eQ, eg, ef, hq, ec, a, ha, height, image⟩
    have eqQ := d.spaces.unique eQ (d.space_entry i)
    have eqg := t.heights.unique eg (t.heights.value_entry i)
    have eqf := embeddings.unique ef (embeddings.value_entry i)
    exact ⟨eqQ ▸ hq, hc, hz, ec, a, ha, eqg ▸ height, eqf ▸ image⟩
  · rintro ⟨hq, hc, hz, ec, a, ha, height, image⟩
    exact ⟨i.property, hc, hz, d.space i, t.heights.value i, embeddings.value i,
      d.space_entry i, t.heights.value_entry i, embeddings.value_entry i,
      hq, ec, a, ha, height, image⟩

theorem componentHeightGraph_function
    (columns : ZFSet.IsFunc I C Cs) (embeddings : FunctionGraphOn I E)
    (maps : ∀ i, ZFSet.IsFunc (t.ranges.value i) D (embeddings.value i))
    (bounds : ∀ i, t.ranges.value i ⊆ B) :
    ZFSet.IsFunc (indexedAttachmentDomain I Qs) (ZFSet.prod C D)
      (componentHeightGraph I Qs B Hs Cs E C D) := by
  refine ⟨componentHeightGraph_shape I Qs B Hs Cs E C D, ?_⟩
  intro x hx
  obtain ⟨i, hi, q, rfl, Q, eQ, hq⟩ := (mem_indexedAttachmentDomain I Qs x).1 hx
  let j : {i : ZFSet.{u} // i ∈ I} := ⟨i, hi⟩
  have qQ : q ∈ d.space j := d.spaces.unique eQ (d.space_entry j) ▸ hq
  obtain ⟨a, height, uniqueA⟩ := (t.function j).2 q qQ
  have aV := (ZFSet.pair_mem_prod.1 ((t.function j).1 height)).2
  obtain ⟨z, image, uniqueZ⟩ := (maps j).2 a aV
  have zD := (ZFSet.pair_mem_prod.1 ((maps j).1 image)).2
  obtain ⟨c, column, uniqueC⟩ := columns.2 i hi
  have cC := (ZFSet.pair_mem_prod.1 (columns.1 column)).2
  refine ⟨ZFSet.pair c z, (t.componentHeightGraph_entry_iff embeddings j q c z).2
    ⟨qQ, cC, zD, column, a, bounds j aV, height, image⟩, ?_⟩
  intro y entry
  have shape := ZFSet.pair_mem_prod.1 (componentHeightGraph_shape I Qs B Hs Cs E C D entry)
  obtain ⟨c', _, z', _, rfl⟩ := ZFSet.mem_prod.1 shape.2
  obtain ⟨_, _, _, column', a', _, height', image'⟩ :=
    (t.componentHeightGraph_entry_iff embeddings j q c' z').1 entry
  have equalA := uniqueA a' height'
  exact congrArg₂ ZFSet.pair (uniqueC c' column') (uniqueZ z' (equalA ▸ image'))

end TemplateHeightFamilyInputs

noncomputable def taggedHeightGraph (P N H old fresh : ZFSet.{u}) : ZFSet.{u} :=
  old ∪ ZFSet.sep (fun w => ∃ x ∈ N, ∃ h ∈ H,
    w = ZFSet.pair (ZFSet.pair P x) h ∧ ZFSet.pair x h ∈ fresh)
    (ZFSet.prod (taggedExtension P N) H)

def heightImageCandidate (Qs Bs Hs i R : ZFSet.{u}) : Prop :=
  ∃ Q ∈ ⋃₀ ⋃₀ Qs, ∃ B ∈ ⋃₀ ⋃₀ Bs, ∃ h ∈ ⋃₀ ⋃₀ Hs,
    ZFSet.pair i Q ∈ Qs ∧ ZFSet.pair i B ∈ Bs ∧ ZFSet.pair i h ∈ Hs ∧
      R = relationImage Q B h

noncomputable def heightImageFamily (I W Qs Bs Hs : ZFSet.{u}) : ZFSet.{u} :=
  ZFSet.sep (fun z => ∃ i ∈ I, ∃ R ∈ W,
    z = ZFSet.pair i R ∧ heightImageCandidate Qs Bs Hs i R) (ZFSet.prod I W)

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

namespace SetFormula

def taggedExtensionSetFormula {n} (output p fresh : Fin n) : SetFormula n :=
  exactSetFormula output (BoundedFormula.disj (.mem 0 p.succ)
    (BoundedFormula.attachmentTagFormula 0 p.succ fresh.succ)).toFormula

def canonicalMeetSetFormula {n} (output carrier order : Fin n) : SetFormula n :=
  exactSetFormula output (BoundedFormula.canonicalMeetEntryFormula 0 carrier.succ order.succ).toFormula

def codedAttachmentOrderSetFormula {n} (output carrier p fresh order inside shadow upper : Fin n) :
    SetFormula n :=
  exactSetFormula output (BoundedFormula.codedAttachmentOrderEntryFormula 0 carrier.succ
    p.succ fresh.succ order.succ inside.succ shadow.succ upper.succ).toFormula

end SetFormula

namespace TransitiveGround
variable (M : TransitiveGround.{u})

theorem realize_exactBoundedSetFormula {n} (output : Fin n) (entry : BoundedFormula (n + 1))
    (env : Fin n → ZFSet.{u}) (members : ∀ i, env i ∈ M.sets)
    {target : ZFSet.{u}} (ground : target ∈ M.sets)
    (meaning : ∀ z, BoundedFormula.Truth entry (extend z env) ↔ z ∈ target) :
    Realize M.sets (exactSetFormula output entry.toFormula) env ↔ env output = target :=
  M.realize_exactSetFormula output entry.toFormula env (members output)
    (fun _ hz => M.transitive ground hz) (fun z hz =>
      (BoundedFormula.realize_toFormula M entry (extend z env) (Fin.cases hz members)).trans (meaning z))

theorem realize_sUnionSetFormula
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    {n} (output source : Fin n) (env : Fin n → ZFSet.{u}) (members : ∀ i, env i ∈ M.sets) :
    Realize M.sets (sUnionSetFormula output source) env ↔ env output = ZFSet.sUnion (env source) := by
  apply M.realize_exactBoundedSetFormula output _ env members (M.union_mem unions (members source))
  intro z
  simp only [BoundedFormula.truth_exMem, BoundedFormula.Truth, ZFSet.mem_sUnion]
  rfl

variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
variable (unions : Realize M.sets SetFormula.union Fin.elim0)
variable (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
include pairing unions powers separation

theorem realize_taggedExtensionSetFormula {n} (output p fresh : Fin n)
    (env : Fin n → ZFSet.{u}) (members : ∀ i, env i ∈ M.sets) :
    Realize M.sets (taggedExtensionSetFormula output p fresh) env ↔
      env output = taggedExtension (env p) (env fresh) := by
  apply M.realize_exactBoundedSetFormula output _ env members
    (M.taggedExtension_mem pairing unions powers separation (members p) (members fresh))
  intro z
  simp only [BoundedFormula.truth_disj, BoundedFormula.Truth,
    BoundedFormula.attachmentTagFormula, BoundedFormula.truth_exMem,
    BoundedFormula.truth_orderedPairFormula, mem_taggedExtension]
  rfl

end TransitiveGround




namespace SetFormula
def batchInsideSetFormula {n} (output i qs rs qb rb : Fin n) : SetFormula n :=
  exactSetFormula output (BoundedFormula.batchAttachmentInsideEntryFormula
    0 i.succ qs.succ rs.succ qb.succ rb.succ).toFormula

def batchUpperSetFormula {n} (output i p qs fs qb fb : Fin n) : SetFormula n :=
  exactSetFormula output (BoundedFormula.batchAttachmentUpperEntryFormula
    0 i.succ p.succ qs.succ fs.succ qb.succ fb.succ).toFormula

end SetFormula

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

theorem base_function {G m e : ZFSet.{u}} (action : PosetActionCode G P m e r A)
    (hg : g ∈ G) : ZFSet.IsFunc (attachmentIdeal P r source) P base := by
  refine ⟨?_, ?_⟩
  · intro z hz
    obtain ⟨x, hx, y, hy, rfl⟩ := ZFSet.mem_prod.1 (code.shape hz)
    exact ZFSet.pair_mem_prod.2
      ⟨(mem_attachmentIdeal P r source x).2 ⟨hx, ((code.entries x hx y hy).1 hz).1⟩, hy⟩
  · intro x hx
    have parts := (mem_attachmentIdeal P r source x).1 hx
    obtain ⟨y, entry, unique⟩ := action.function.2 (ZFSet.pair g x)
      (ZFSet.pair_mem_prod.2 ⟨hg, parts.1⟩)
    have hy := (ZFSet.pair_mem_prod.1 (action.function.1 entry)).2
    exact ⟨y, (code.entries x parts.1 y hy).2 ⟨parts.2, entry⟩,
      fun z hz => unique z (code.entry_action hz)⟩

theorem source_entry (order : PartialOrderCode P r) (hsource : source ∈ P)
    (htarget : target ∈ P) : ZFSet.pair source target ∈ base :=
  (code.entries source hsource target htarget).2
    ⟨order.refl source hsource, code.target_entry⟩

end RestrictedActionCode

end PartitionPilot.Forcing

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Definability_GroundStrongLimitFormulas
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

def relativePowerFormula {n} (a p : Fin n) : SetFormula n :=
  .all (.conj
    (imp (.mem 0 p.succ) (BoundedFormula.subsetFormula 0 a.succ).toFormula)
    (imp (BoundedFormula.subsetFormula 0 a.succ).toFormula (.mem 0 p.succ)))

end SetFormula
end PartitionPilot.Forcing

end

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Geometry_GroundCumulativeHierarchyLevels
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

namespace SetFormula

def cumulativeMemberFormula {n} (x a p : Fin n) : SetFormula n :=
  ex (.conj (.mem 0 a.succ) (ex (.conj
    (BoundedFormula.pairMembershipFormula 1 0 p.succ.succ).toFormula
    (BoundedFormula.subsetFormula x.succ.succ 0).toFormula)))

def cumulativeStepFormula : SetFormula 3 :=
  .all (.conj
    (imp (.mem 0 3) (cumulativeMemberFormula 0 1 2))
    (imp (cumulativeMemberFormula 0 1 2) (.mem 0 3)))

end SetFormula

namespace TransitiveGround
variable (M : TransitiveGround.{u})

noncomputable def cumulativeNext (a p : ZFSet.{u}) : ZFSet.{u} :=
  ZFSet.sep (fun x => ∃ b ∈ a, ∃ v, ZFSet.pair b v ∈ p ∧ x ⊆ v)
    (M.groundPower (⋃₀ ⋃₀ ⋃₀ p))

end TransitiveGround

end PartitionPilot.Forcing

namespace PartitionPilot.Forcing
open SetFormula
universe u

def GroundCumulativeHierarchyCode (M : TransitiveGround.{u}) (T H : ZFSet.{u}) : Prop :=
  OrdinalRecursionTrace (fun a p y => y = M.cumulativeNext a p) T H

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
open scoped ZFSet
universe u

noncomputable def naturalFamilyUnion (family : ZFSet.{u}) : ZFSet.{u} :=
  ⋃₀ relationImage ZFSet.omega (⋃₀ ⋃₀ family) family

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
namespace SetFormula

def compositionFamilyEntryFormula {n} (z K I J B D L Es Ss : Fin n) : SetFormula n :=
  let lift (i : Fin n) := i.succ.succ.succ.succ.succ
  let body := BoundedFormula.conj (.mem 4 (lift I)) (.conj (.mem 3 (lift J))
      (.conj (BoundedFormula.orderedTripleFormula (lift z) 4 3 0)
        (.conj (BoundedFormula.pairMembershipFormula 4 3 (lift K))
          (.conj (BoundedFormula.pairMembershipFormula 3 2 (lift Es))
            (.conj (BoundedFormula.pairMembershipFormula 4 1 (lift Ss))
              (BoundedFormula.compositionGraphFormula 0 (lift B) (lift D) (lift L) 2 1))))))
  ex (ex (ex (ex (ex body.toFormula))))

def compositionFamilyFormula {n} (family K I J B D L Es Ss : Fin n) : SetFormula n :=
  exactSetFormula family
    (compositionFamilyEntryFormula 0 K.succ I.succ J.succ B.succ D.succ L.succ Es.succ Ss.succ)

end SetFormula

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

universe u
namespace SetFormula

def pushFilterFamilyEntryFormula {n} (z K I J L r Maps Fs : Fin n) : SetFormula n :=
  let lift (i : Fin n) := i.succ.succ.succ.succ.succ
  let body := BoundedFormula.conj (.mem 4 (lift I)) (.conj (.mem 3 (lift J))
      (.conj (BoundedFormula.orderedTripleFormula (lift z) 4 3 0)
        (.conj (BoundedFormula.pairMembershipFormula 4 3 (lift K))
          (.conj (BoundedFormula.pairMembershipFormula 4 2 (lift Maps))
            (.conj (BoundedFormula.pairMembershipFormula 3 1 (lift Fs))
              (BoundedFormula.pushFilterFormula 0 (lift L) (lift r) 2 1))))))
  ex (ex (ex (ex (ex body.toFormula))))

def pushFilterFamilyFormula {n} (family K I J L r Maps Fs : Fin n) : SetFormula n :=
  exactSetFormula family
    (pushFilterFamilyEntryFormula 0 K.succ I.succ J.succ L.succ r.succ Maps.succ Fs.succ)

end SetFormula

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
open SetFormula
universe u

namespace TransitiveGround
variable (M : TransitiveGround.{u})

noncomputable def indexedClassInclusions (T U L E : ZFSet.{u}) : ZFSet.{u} :=
  M.indexedRelationSections T U (equivalenceClasses L E) (equivalenceClassifier L E)

end TransitiveGround

end PartitionPilot.Forcing

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Definability_GroundFlatCopyPresentation
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
variable {B : Type u} (s : Presentation B) (r : Setoid B) {E : ZFSet.{u}}
variable (equivalence : EquivalenceRelationCode s.carrier E)
variable (related : ∀ x y, ZFSet.pair (s.encode x) (s.encode y) ∈ E ↔ r.r x y)

noncomputable def quotientEncode : Quotient r → ZFSet.{u} :=
  Quotient.lift (fun x => equivalenceClass s.carrier E (s.encode x))
    (fun x y h => (equivalence.class_eq_iff (s.encode_mem x) (s.encode_mem y)).2
      ((related x y).2 h))

theorem quotientEncode_injective :
    Function.Injective (s.quotientEncode r equivalence related) := by
  intro q q'
  refine Quotient.inductionOn₂ q q' ?_
  intro x y equal
  exact Quotient.sound ((related x y).1
    ((equivalence.class_eq_iff (s.encode_mem x) (s.encode_mem y)).1 equal))

theorem mem_equivalenceClasses_iff_quotientEncode (C : ZFSet.{u}) :
    C ∈ equivalenceClasses s.carrier E ↔
      ∃ q, s.quotientEncode r equivalence related q = C := by
  constructor
  · intro hC
    obtain ⟨x, hx, rfl⟩ := (mem_equivalenceClasses s.carrier E C).1 hC
    obtain ⟨b, rfl⟩ := (s.mem_carrier x).1 hx
    exact ⟨Quotient.mk r b, rfl⟩
  · rintro ⟨q, rfl⟩
    refine Quotient.inductionOn q ?_
    intro x
    exact equivalenceClass_mem (s.encode_mem x)

noncomputable def quotientPresentation : Presentation (Quotient r) where
  carrier := equivalenceClasses s.carrier E
  encode := s.quotientEncode r equivalence related
  injective := s.quotientEncode_injective r equivalence related
  mem_carrier := s.mem_equivalenceClasses_iff_quotientEncode r equivalence related

theorem quotientPresentation_classifier_entry_iff (x : B) (q : Quotient r) :
    ZFSet.pair (s.encode x) ((s.quotientPresentation r equivalence related).encode q) ∈
      equivalenceClassifier s.carrier E ↔ Quotient.mk r x = q := by
  rw [pair_mem_equivalenceClassifier]
  constructor
  · rintro ⟨_, equal⟩
    apply (s.quotientPresentation r equivalence related).injective
    exact equal.symm
  · rintro rfl
    exact ⟨s.encode_mem x, rfl⟩

theorem quotientClassifier_eq_graph :
    equivalenceClassifier s.carrier E =
      s.graph (s.quotientPresentation r equivalence related) (Quotient.mk r) := by
  apply ZFSet.ext
  intro z
  rw [mem_equivalenceClassifier, mem_graph]
  constructor
  · rintro ⟨y, hy, rfl⟩
    obtain ⟨x, rfl⟩ := (s.mem_carrier y).1 hy
    exact ⟨x, rfl⟩
  · rintro ⟨x, rfl⟩
    exact ⟨s.encode x, s.encode_mem x, rfl⟩

end PartitionPilot.SetRealization.Presentation

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
open SetRealization
universe u

theorem quotientBinaryGraph_eq_graph {A B : Type u} (s : Presentation A) (t : Presentation B)
    (q : A → B) (source : A → A → A) (target : B → B → B)
    (onto : Function.Surjective q)
    (compatible : ∀ x y, q (source x y) = target (q x) (q y)) :
    quotientBinaryGraph s.carrier t.carrier (s.graph t q)
      ((s.product s).graph s (fun p => source p.1 p.2)) =
        (t.product t).graph t (fun p => target p.1 p.2) := by
  apply ZFSet.ext
  intro z
  rw [mem_quotientBinaryGraph, Presentation.mem_graph]
  constructor
  · rintro ⟨a, ha, b, hb, c, hc, rfl, x, hx, y, hy, w, hw, xa, yb, wc, op⟩
    obtain ⟨a, rfl⟩ := (t.mem_carrier a).1 ha
    obtain ⟨b, rfl⟩ := (t.mem_carrier b).1 hb
    obtain ⟨c, rfl⟩ := (t.mem_carrier c).1 hc
    obtain ⟨x, rfl⟩ := (s.mem_carrier x).1 hx
    obtain ⟨y, rfl⟩ := (s.mem_carrier y).1 hy
    obtain ⟨w, rfl⟩ := (s.mem_carrier w).1 hw
    have first := (s.pair_mem_graph t q x a).1 xa
    have second := (s.pair_mem_graph t q y b).1 yb
    have output := (s.pair_mem_graph t q w c).1 wc
    have value := ((s.product s).pair_mem_graph s (fun p => source p.1 p.2) (x, y) w).1 op
    have equal : target a b = c := by
      rw [← first, ← second, ← compatible, value]
      exact output
    exact ⟨(a, b), by change ZFSet.pair (ZFSet.pair _ _) (t.encode (target a b)) = _; rw [equal]⟩
  · rintro ⟨⟨a, b⟩, rfl⟩
    obtain ⟨x, rfl⟩ := onto a
    obtain ⟨y, rfl⟩ := onto b
    refine ⟨t.encode (q x), t.encode_mem _, t.encode (q y), t.encode_mem _,
      t.encode (target (q x) (q y)), t.encode_mem _, rfl,
      s.encode x, s.encode_mem _, s.encode y, s.encode_mem _,
      s.encode (source x y), s.encode_mem _, ?_, ?_, ?_, ?_⟩
    · exact (s.pair_mem_graph t q _ _).2 rfl
    · exact (s.pair_mem_graph t q _ _).2 rfl
    · exact (s.pair_mem_graph t q _ _).2 (compatible x y)
    · exact ((s.product s).pair_mem_graph s (fun p => source p.1 p.2) (x, y) _).2 rfl

end PartitionPilot.Forcing



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

section

namespace PartitionPilot.SetRealization.Presentation

open Forcing
universe u

theorem relationCompose_graph {A B C : Type u}
    (s : Presentation A) (t : Presentation B) (v : Presentation C) (f : A → B) (g : B → C) :
    relationCompose s.carrier t.carrier v.carrier (s.graph t f) (t.graph v g) =
      s.graph v (fun x => g (f x)) := by
  apply ZFSet.ext
  intro z
  rw [mem_relationCompose, mem_graph]
  constructor
  · rintro ⟨x, hx, y, hy, w, hw, rfl, first, second⟩
    obtain ⟨a, rfl⟩ := (s.mem_carrier x).1 hx
    obtain ⟨b, rfl⟩ := (t.mem_carrier y).1 hy
    obtain ⟨c, rfl⟩ := (v.mem_carrier w).1 hw
    have ab := (s.pair_mem_graph t f a b).1 first
    have bc := (t.pair_mem_graph v g b c).1 second
    subst b c
    exact ⟨a, rfl⟩
  · rintro ⟨a, rfl⟩
    exact ⟨s.encode a, s.encode_mem a, t.encode (f a), t.encode_mem (f a),
      v.encode (g (f a)), v.encode_mem (g (f a)), rfl,
      (s.pair_mem_graph t f a (f a)).2 rfl,
      (t.pair_mem_graph v g (f a) (g (f a))).2 rfl⟩

end PartitionPilot.SetRealization.Presentation

end

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Geometry_GroundExternalGroupEmbeddings
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

namespace GroupEmbeddingCode

theorem map_inv {G H mG mH invG invH oneG oneH e a b a' b' : ZFSet.{u}}
    (embedding : GroupEmbeddingCode G H mG mH oneG oneH e)
    (source : GroupCode G mG invG oneG) (target : GroupCode H mH invH oneH)
    (inverse : ZFSet.pair a b ∈ invG) (first : ZFSet.pair a a' ∈ e) (second : ZFSet.pair b b' ∈ e) :
    ZFSet.pair a' b' ∈ invH := by
  let := target.toGroup
  have bounds := ZFSet.pair_mem_prod.1 (source.inv_function.1 inverse)
  have product := embedding.mul b a oneG b' a' oneH
    (source.inv_mul a bounds.1 b bounds.2 inverse) second first embedding.one
  let x := SetMembers.ofMem a' (ZFSet.pair_mem_prod.1 (embedding.injection.function.1 first)).2
  let y := SetMembers.ofMem b' (ZFSet.pair_mem_prod.1 (embedding.injection.function.1 second)).2
  have product' : y * x = (1 : SetMembers H) := by
    apply (target.mul_eq_iff y x target.one).2
    simpa only [target.raw_one, x, y, SetMembers.raw_ofMem] using product
  have equal : x⁻¹ = y := inv_eq_of_mul_eq_one_left product'
  have entry := target.inv_mem x
  change ZFSet.pair (SetMembers.raw x) (SetMembers.raw (x⁻¹)) ∈ invH at entry
  rw [equal] at entry
  simpa only [x, y, SetMembers.raw_ofMem] using entry

end GroupEmbeddingCode
end PartitionPilot.Forcing

end

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Models_LiteralQuotientRankBounds
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
variable {o : Ordinal.{u}} (limit : Order.IsSuccLimit o)
include limit

theorem rank_fixedTopCarrier_lt {P : ZFSet.{u}} (carrier : ZFSet.rank P < o) :
    ZFSet.rank (fixedTopCarrier P) < o := by
  rw [fixedTopCarrier, ZFSet.rank_insert]
  exact max_lt (limit.succ_lt carrier) carrier

end PartitionPilot.Forcing

end

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Geometry_TaggedGrowthLayerRanks
attribute [-instance] _root_.OAI.PartitionPilot.Forcing.GroundMainPrefix.withTopSmall
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PartitionPilot.Forcing
universe u

theorem rank_nonemptyTupleCode_field_le (k : Nat) (fields : Fin (k + 1) → ZFSet.{u}) :
    ∀ j, ZFSet.rank (fields j) ≤ ZFSet.rank (nonemptyTupleCode k fields) := by
  induction k with
  | zero => exact Fin.cases le_rfl (fun i => Fin.elim0 i)
  | succ k ih =>
    let tail := nonemptyTupleCode k (fun j => fields j.succ)
    have both : ZFSet.rank ({fields 0, tail} : ZFSet.{u}) <
        ZFSet.rank (ZFSet.pair (fields 0) tail) :=
      ZFSet.rank_lt_of_mem (ZFSet.mem_pair.2 (Or.inr rfl))
    have head : ZFSet.rank (fields 0) < ZFSet.rank (ZFSet.pair (fields 0) tail) :=
      (ZFSet.rank_lt_of_mem (show fields 0 ∈ ({fields 0, tail} : ZFSet.{u}) from
        ZFSet.mem_pair.2 (Or.inl rfl))).trans both
    have rest : ZFSet.rank tail < ZFSet.rank (ZFSet.pair (fields 0) tail) :=
      (ZFSet.rank_lt_of_mem (show tail ∈ ({fields 0, tail} : ZFSet.{u}) from
        ZFSet.mem_pair.2 (Or.inr rfl))).trans both
    exact Fin.cases head.le (fun j => (ih _ j).trans rest.le)

end PartitionPilot.Forcing

end

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
universe u v

def finiteMainIndexKey {n : Nat} (i : Fin n) : ZFSet.{u} := natSetCode i.val

theorem finiteMainIndexKey_injective (n : Nat) :
    Function.Injective (@finiteMainIndexKey.{u} n) :=
  fun _ _ equal => Fin.ext (natSetCode_injective equal)

theorem finiteMainIndexKey_order {n : Nat} (i j : Fin n) :
    i ≤ j ↔ finiteMainIndexKey i = finiteMainIndexKey j ∨ finiteMainIndexKey i ∈ finiteMainIndexKey j := by
  change i.val ≤ j.val ↔ natSetCode i.val = natSetCode j.val ∨ natSetCode i.val ∈ natSetCode j.val
  rw [natSetCode_injective.eq_iff, natSetCode_mem_iff]
  omega

theorem finiteMainIndexKey_range (n : Nat) :
    ZFSet.range (@finiteMainIndexKey.{u} n) = natSetCode n := by
  apply ZFSet.ext
  intro z
  rw [ZFSet.mem_range, mem_natSetCode]
  exact ⟨fun ⟨i, hi⟩ => ⟨i.val, i.isLt, hi.symm⟩,
    fun ⟨i, hi, equal⟩ => ⟨⟨i, hi⟩, equal.symm⟩⟩

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

theorem familyCodeGraph_eq_of_entries {I : Type v} [Small.{u} I]
    {A f : ZFSet.{u}} (function : FunctionGraphOn A f)
    (key value : I → ZFSet.{u}) (domain : ZFSet.range key = A)
    (entries : ∀ i, ZFSet.pair (key i) (value i) ∈ f) :
    familyCodeGraph key value = f := by
  apply ZFSet.ext
  intro z
  constructor
  · intro hz
    obtain ⟨i, rfl⟩ := (mem_familyCodeGraph key value z).1 hz
    exact entries i
  · intro hz
    obtain ⟨x, hx, y, rfl⟩ := function.shape _ hz
    rw [← domain] at hx
    obtain ⟨i, rfl⟩ := ZFSet.mem_range.1 hx
    have equal := function.unique (entries i) hz
    exact (mem_familyCodeGraph key value _).2 ⟨i, congrArg (ZFSet.pair (key i)) equal⟩

theorem familyCodeGraph_ground_of_entries {M : TransitiveGround.{u}}
    {I : Type v} [Small.{u} I] {A f : ZFSet.{u}} (ground : f ∈ M.sets)
    (function : FunctionGraphOn A f) (key value : I → ZFSet.{u})
    (domain : ZFSet.range key = A) (entries : ∀ i, ZFSet.pair (key i) (value i) ∈ f) :
    familyCodeGraph key value ∈ M.sets :=
  (familyCodeGraph_eq_of_entries function key value domain entries).symm ▸ ground

end PartitionPilot.Forcing

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

namespace SetFormula

def recursiveSeparatorEntryFormula {n} (z K I J D L Maps Ss : Fin n) : SetFormula n :=
  let lift (i : Fin n) := i.succ.succ.succ.succ.succ
  let body := BoundedFormula.conj (.mem 4 (lift I)) (.conj (.mem 3 (lift J))
    (.conj (.mem 1 (lift D)) (.conj (.mem 0 (lift L))
      (.conj (BoundedFormula.orderedTripleFormula (lift z) 4 3 0)
        (.conj (BoundedFormula.pairMembershipFormula 4 3 (lift K))
          (.conj (BoundedFormula.pairMembershipFormula 4 2 (lift Maps))
            (.conj (BoundedFormula.pairMembershipFormula 3 1 (lift Ss))
              (BoundedFormula.pairMembershipFormula 1 0 2))))))))
  ex (ex (ex (ex (ex body.toFormula))))

def recursiveSeparatorFamilyFormula {n} (family K I J D L Maps Ss : Fin n) : SetFormula n :=
  exactSetFormula family
    (recursiveSeparatorEntryFormula 0 K.succ I.succ J.succ D.succ L.succ Maps.succ Ss.succ)

end SetFormula

end PartitionPilot.Forcing

end

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Geometry_GroundCantorDiagonal
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

noncomputable def injectionDiagonal (A f : ZFSet.{u}) : ZFSet.{u} :=
  ZFSet.sep (fun x => ∃ X ∈ M.groundPower A, ZFSet.pair X x ∈ f ∧ x ∉ X) A

end TransitiveGround
end PartitionPilot.Forcing

end

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



namespace PartitionPilot.Forcing.TransitiveGround

open SetRealization SetFormula
universe u
variable (M : TransitiveGround.{u})

def rowDistinguishing (I C Y i j : ZFSet.{u}) :
    Set (SetMembers (M.smallPartialFunctions (ZFSet.prod I C) Y ZFSet.omega)) :=
  {p | ∃ c ∈ C, ∃ a ∈ Y, ∃ b ∈ Y, a ≠ b ∧
    ZFSet.pair (ZFSet.pair i c) a ∈ SetMembers.raw p ∧
    ZFSet.pair (ZFSet.pair j c) b ∈ SetMembers.raw p}

end PartitionPilot.Forcing.TransitiveGround

end

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



namespace PartitionPilot.Forcing.TransitiveGround

open SetRealization SetFormula
universe u
variable (M : TransitiveGround.{u})

noncomputable def countableGenericGraph (X Y : ZFSet.{u}) :
    letI := M.smallFunctionOrder X Y ZFSet.omega
    ConditionFilter (SetMembers (M.smallPartialFunctions X Y ZFSet.omega)) → ZFSet.{u} := by
  letI := M.smallFunctionOrder X Y ZFSet.omega
  exact fun H => ZFSet.sep (fun z => ∃ p, H.mem p ∧ z ∈ SetMembers.raw p) (ZFSet.prod X Y)

end PartitionPilot.Forcing.TransitiveGround



end

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Geometry_GroundBinaryRows
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

noncomputable def binaryGenericRow (I C : ZFSet.{u}) :
    letI := M.smallFunctionOrder (ZFSet.prod I C) (natSetCode 2) ZFSet.omega
    ConditionFilter (SetMembers (M.smallPartialFunctions (ZFSet.prod I C) (natSetCode 2) ZFSet.omega)) →
      ZFSet.{u} → ZFSet.{u} := by
  letI := M.smallFunctionOrder (ZFSet.prod I C) (natSetCode 2) ZFSet.omega
  exact fun H i => ZFSet.sep (fun c => ZFSet.pair (ZFSet.pair i c) (natSetCode 1) ∈
    M.countableGenericGraph (ZFSet.prod I C) (natSetCode 2) H) C

end TransitiveGround

end PartitionPilot.Forcing

end

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Forcing_GroundBinaryRowNames
attribute [-instance] _root_.OAI.PartitionPilot.Forcing.GroundMainPrefix.withTopSmall
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PartitionPilot.Forcing.TransitiveGround

open SetRealization
universe u
variable (M : TransitiveGround.{u})

noncomputable def binaryRowName (I C : ZFSet.{u})
    (one : SetMembers (M.smallPartialFunctions (ZFSet.prod I C) (natSetCode 2) ZFSet.omega))
    (i : ZFSet.{u}) :
    Name (SetMembers.presentation (M.smallPartialFunctions (ZFSet.prod I C) (natSetCode 2) ZFSet.omega)) :=
  Name.assemble
    (fun z : {z : SetMembers C × SetMembers
        (M.smallPartialFunctions (ZFSet.prod I C) (natSetCode 2) ZFSet.omega) //
        ZFSet.pair (ZFSet.pair i (SetMembers.raw z.1)) (natSetCode 1) ∈ SetMembers.raw z.2} =>
      Name.check (SetMembers.presentation
        (M.smallPartialFunctions (ZFSet.prod I C) (natSetCode 2) ZFSet.omega)) one (SetMembers.raw z.val.1))
    (fun z => z.val.2)

end PartitionPilot.Forcing.TransitiveGround

end

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Definability_GroundBinaryRowSets
attribute [-instance] _root_.OAI.PartitionPilot.Forcing.GroundMainPrefix.withTopSmall
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PartitionPilot.Forcing.TransitiveGround

open SetRealization
universe u
variable (M : TransitiveGround.{u})

noncomputable def binaryRowSetName (I C : ZFSet.{u})
    (one : SetMembers (M.smallPartialFunctions (ZFSet.prod I C) (natSetCode 2) ZFSet.omega)) :
    Name (SetMembers.presentation (M.smallPartialFunctions (ZFSet.prod I C) (natSetCode 2) ZFSet.omega)) :=
  Name.assemble (fun i : SetMembers I => M.binaryRowName I C one (SetMembers.raw i)) (fun _ => one)

end PartitionPilot.Forcing.TransitiveGround

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

noncomputable def rowAssignmentActionGraph (G Q C B J rowMaps assignmentMaps : ZFSet.{u}) : ZFSet.{u} :=
  ZFSet.sep (fun z => ∃ g ∈ G, ∃ x ∈ Q, ∃ y ∈ Q, ∃ p ∈ C, ∃ A ∈ B, ∃ q ∈ C, ∃ D ∈ B,
    ∃ rf ∈ ⋃₀ ⋃₀ rowMaps, ∃ af ∈ ⋃₀ ⋃₀ assignmentMaps,
      z = ZFSet.pair (ZFSet.pair g x) y ∧ x = ZFSet.pair p A ∧ y = ZFSet.pair q D ∧
      ZFSet.pair g rf ∈ rowMaps ∧ ZFSet.pair p q ∈ rf ∧
      ZFSet.pair g af ∈ assignmentMaps ∧ D = relationImage A J af)
    (ZFSet.prod (ZFSet.prod G Q) Q)

theorem mem_rowAssignmentActionGraph (G Q C B J rowMaps assignmentMaps z : ZFSet.{u}) :
    z ∈ rowAssignmentActionGraph G Q C B J rowMaps assignmentMaps ↔
      ∃ g ∈ G, ∃ x ∈ Q, ∃ y ∈ Q, ∃ p ∈ C, ∃ A ∈ B, ∃ q ∈ C, ∃ D ∈ B,
        ∃ rf ∈ ⋃₀ ⋃₀ rowMaps, ∃ af ∈ ⋃₀ ⋃₀ assignmentMaps,
          z = ZFSet.pair (ZFSet.pair g x) y ∧ x = ZFSet.pair p A ∧ y = ZFSet.pair q D ∧
          ZFSet.pair g rf ∈ rowMaps ∧ ZFSet.pair p q ∈ rf ∧
          ZFSet.pair g af ∈ assignmentMaps ∧ D = relationImage A J af := by
  rw [rowAssignmentActionGraph, ZFSet.mem_sep]
  constructor
  · exact And.right
  · intro h
    obtain ⟨g,hg,x,hx,y,hy,p,hp,A,hA,q,hq,D,hD,rf,hrf,af,haf,equal,rest⟩ := h
    exact ⟨equal.symm ▸ ZFSet.pair_mem_prod.2 ⟨ZFSet.pair_mem_prod.2 ⟨hg,hx⟩,hy⟩,
      g,hg,x,hx,y,hy,p,hp,A,hA,q,hq,D,hD,rf,hrf,af,haf,equal,rest⟩

theorem pair_mem_rowAssignmentActionGraph (G Q C B J rowMaps assignmentMaps g p A q D : ZFSet.{u}) :
    ZFSet.pair (ZFSet.pair g (ZFSet.pair p A)) (ZFSet.pair q D) ∈
      rowAssignmentActionGraph G Q C B J rowMaps assignmentMaps ↔
      g ∈ G ∧ ZFSet.pair p A ∈ Q ∧ ZFSet.pair q D ∈ Q ∧ p ∈ C ∧ A ∈ B ∧ q ∈ C ∧ D ∈ B ∧
      ∃ rf af, ZFSet.pair g rf ∈ rowMaps ∧ ZFSet.pair p q ∈ rf ∧
        ZFSet.pair g af ∈ assignmentMaps ∧ D = relationImage A J af := by
  rw [mem_rowAssignmentActionGraph]
  constructor
  · rintro ⟨g',hg,x,hx,y,hy,p',hp,A',hA,q',hq,D',hD,rf,_,af,_,equal,xEq,yEq,rest⟩
    obtain ⟨outerSource,target⟩ := ZFSet.pair_injective equal
    obtain ⟨rfl,innerSource⟩ := ZFSet.pair_injective outerSource
    obtain ⟨rfl,rfl⟩ := ZFSet.pair_injective (innerSource.trans xEq)
    obtain ⟨rfl,rfl⟩ := ZFSet.pair_injective (target.trans yEq)
    exact ⟨hg,innerSource.symm ▸ hx,target.symm ▸ hy,hp,hA,hq,hD,rf,af,rest⟩
  · rintro ⟨hg,hx,hy,hp,hA,hq,hD,rf,af,indexed,row,indexedA,image⟩
    exact ⟨g,hg,_,hx,_,hy,p,hp,A,hA,q,hq,D,hD,rf,pair_second_mem_doubleUnion indexed,
      af,pair_second_mem_doubleUnion indexedA,rfl,rfl,rfl,indexed,row,indexedA,image⟩

end PartitionPilot.Forcing

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
variable (M : TransitiveGround.{u}) {G P : Type u} [Group G] [PartialOrder P]
variable (a : PosetAction G P) (s : Presentation P) (t : Presentation G)

theorem realize_actionSectionEntry (g : G) (z : ZFSet.{u})
    (hg : t.encode g ∈ M.sets) (hz : z ∈ M.sets)
    (graph : a.actionGraph s t ∈ M.sets) (carrier : s.carrier ∈ M.sets) :
    Realize M.sets (BoundedFormula.actionSectionEntryFormula 0 1 2 3).toFormula
      (extend z (extend (t.encode g) (extend (a.actionGraph s t) (extend s.carrier Fin.elim0)))) ↔
        z ∈ s.graph s (a.iso g) :=
  (BoundedFormula.realize_toFormula M _ _
    (Fin.cases hz (Fin.cases hg (Fin.cases graph (Fin.cases carrier (fun j => Fin.elim0 j)))))).trans
      (BoundedFormula.actionSectionEntry_correct a s t g z)

theorem actionGraph_section_mem
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (carrier : s.carrier ∈ M.sets) (graph : a.actionGraph s t ∈ M.sets)
    (g : G) (hg : t.encode g ∈ M.sets) : s.graph s (a.iso g) ∈ M.sets := by
  obtain ⟨B, hB, bounds⟩ := M.exists_pair_bound pairing unions powers carrier carrier
  let params := extend (t.encode g) (extend (a.actionGraph s t) (extend s.carrier Fin.elim0))
  have selected := M.separation_mem separation (BoundedFormula.actionSectionEntryFormula 0 1 2 3).toFormula
    params (Fin.cases hg (Fin.cases graph (Fin.cases carrier (fun j => Fin.elim0 j)))) hB
  have eq : ZFSet.sep (fun z => Realize M.sets
      (BoundedFormula.actionSectionEntryFormula 0 1 2 3).toFormula (extend z params)) B =
        s.graph s (a.iso g) := by
    apply ZFSet.ext
    intro z
    rw [ZFSet.mem_sep]
    constructor
    · rintro ⟨hz, rel⟩
      exact (M.realize_actionSectionEntry a s t g z hg (M.transitive hB hz) graph carrier).1 rel
    · intro hz
      have hzB : z ∈ B := by
        obtain ⟨p, eq⟩ := (s.mem_graph s (a.iso g) z).1 hz
        exact eq ▸ bounds _ (s.encode_mem p) _ (s.encode_mem (a.iso g p))
      exact ⟨hzB, (M.realize_actionSectionEntry a s t g z hg (M.transitive hB hzB) graph carrier).2 hz⟩
  exact eq ▸ selected

end PartitionPilot.Forcing.TransitiveGround

section

namespace PartitionPilot.Forcing.SetFormula

def actionMapPairFormula : SetFormula 4 :=
  ex (.conj (BoundedFormula.orderedPairFormula 2 1 0).toFormula
    (BoundedFormula.actionSectionFormula 0 1 3 4).toFormula)

end PartitionPilot.Forcing.SetFormula

namespace PartitionPilot.Forcing.TransitiveGround

open SetRealization SetFormula
universe u
variable (M : TransitiveGround.{u}) {G P : Type u} [Group G] [PartialOrder P]
variable (a : PosetAction G P) (s : Presentation P) (t : Presentation G)

theorem realize_actionMapPairFormula (g : G) (z : ZFSet.{u})
    (hg : t.encode g ∈ M.sets) (hz : z ∈ M.sets)
    (graph : a.actionGraph s t ∈ M.sets) (carrier : s.carrier ∈ M.sets)
    (section_mem : s.graph s (a.iso g) ∈ M.sets) :
    Realize M.sets actionMapPairFormula
      (extend (t.encode g) (extend z (extend (a.actionGraph s t) (extend s.carrier Fin.elim0)))) ↔
        z = ZFSet.pair (t.encode g) (s.graph s (a.iso g)) := by
  rw [actionMapPairFormula, realize_ex]
  constructor
  · rintro ⟨F, hF, pair, rel⟩
    have members : ∀ j, (extend F (extend (t.encode g) (extend z
        (extend (a.actionGraph s t) (extend s.carrier Fin.elim0))))) j ∈ M.sets :=
      Fin.cases hF (Fin.cases hg (Fin.cases hz (Fin.cases graph
        (Fin.cases carrier (fun j => Fin.elim0 j)))))
    have shape := (BoundedFormula.truth_orderedPairFormula 2 1 0 _).1
      ((BoundedFormula.realize_toFormula M _ _ members).1 pair)
    have raw := (BoundedFormula.realize_toFormula M _ _ members).1 rel
    change BoundedFormula.Truth (BoundedFormula.actionSectionFormula 0 1 2 3)
      (extend F (extend (t.encode g) (extend (a.actionGraph s t) (extend s.carrier Fin.elim0)))) at raw
    have eq := (BoundedFormula.actionSection_correct a s t g F).1 raw
    change z = ZFSet.pair (t.encode g) F at shape
    exact eq ▸ shape
  · intro eq
    refine ⟨s.graph s (a.iso g), section_mem, ?_, ?_⟩
    · apply (BoundedFormula.realize_toFormula M _ _ (Fin.cases section_mem (Fin.cases hg
        (Fin.cases hz (Fin.cases graph (Fin.cases carrier (fun j => Fin.elim0 j))))))).2
      exact (BoundedFormula.truth_orderedPairFormula 2 1 0 _).2 eq
    · apply (BoundedFormula.realize_toFormula M _ _ (Fin.cases section_mem (Fin.cases hg
        (Fin.cases hz (Fin.cases graph (Fin.cases carrier (fun j => Fin.elim0 j))))))).2
      change BoundedFormula.Truth (BoundedFormula.actionSectionFormula 0 1 2 3)
        (extend (s.graph s (a.iso g)) (extend (t.encode g)
          (extend (a.actionGraph s t) (extend s.carrier Fin.elim0))))
      exact (BoundedFormula.actionSection_correct a s t g _).2 rfl

end PartitionPilot.Forcing.TransitiveGround

end

namespace PartitionPilot.Forcing
open SetRealization
universe u
variable {G P L : Type u} [Group G] [PartialOrder P] [OrderTop P] [PartialOrder L]

structure StageOneActionParameters (M : TransitiveGround.{u}) (a : PosetAction G P)
    (s : Presentation P) (t : Presentation G) (b : Presentation L) (d : PosetAction G L)
    (T T2 : ZFSet.{u}) (valid : ∀ z ∈ T, IsName s z) : Prop where
  condition_maps : a.conditionMapFamily s t ∈ M.sets
  node_maps : d.conditionMapFamily b t ∈ M.sets
  terms_closed : ∀ g (tau : Name s), tau.val ∈ T → (a.act s g tau).val ∈ T
  pairs_closed : ∀ g (tau : Name s), tau.val ∈ T2 → (a.act s g tau).val ∈ T2
  family_ground : (Name.familySet ⊤ T valid).val ∈ M.sets

end PartitionPilot.Forcing

namespace PartitionPilot.Forcing
open SetRealization SetFormula
universe u
variable {L G : Type u} [PartialOrder L] [OrderBot L] [Group G]

noncomputable def rowPositionSequenceAction (a : PosetAction G L) (s : Presentation L)
    (g : G) (mu f : ZFSet.{u}) : ZFSet.{u} :=
  relationCompose mu s.nonbottom.carrier s.nonbottom.carrier f
    (s.nonbottom.graph s.nonbottom (a.nonbottom.iso g))

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

theorem renameActionRelation_iff {X Y G : Type u} [Group G] [PartialOrder X]
    (a : PosetAction G X) (s : Presentation X) (t : Presentation Y) (b : Presentation G)
    (g : G) {p q : ZFSet.{u}} (shapeQ : q ⊆ ZFSet.prod s.carrier t.carrier) :
    RenameActionRelation s.carrier t.carrier (a.actionGraph s b) (b.encode g) p q ↔
      graphRename s t (a.iso g).toEquiv p = q := by
  constructor
  · intro h
    apply s.relation_ext t (graphRename_shape s t _ _) shapeQ
    intro x y
    rw [pair_mem_graphRename]
    exact h _ (s.encode_mem ((a.iso g).symm x)) _ (s.encode_mem x) _ (t.encode_mem y)
      ((a.triple_mem_actionGraph s b g ((a.iso g).symm x) x).2 ((a.iso g).apply_symm_apply x))
  · intro eq i hi j hj v hv rel
    obtain ⟨x, rfl⟩ := (s.mem_carrier i).1 hi
    obtain ⟨x', rfl⟩ := (s.mem_carrier j).1 hj
    obtain ⟨y, rfl⟩ := (t.mem_carrier v).1 hv
    have same := (a.triple_mem_actionGraph s b g x x').1 rel
    rw [← eq, pair_mem_graphRename]
    rw [← same]
    change ZFSet.pair (s.encode x) (t.encode y) ∈ p ↔
      ZFSet.pair (s.encode ((a.iso g).toEquiv.symm ((a.iso g).toEquiv x))) (t.encode y) ∈ p
    rw [(a.iso g).toEquiv.symm_apply_apply]

end PartitionPilot.Forcing

end

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Geometry_RowCopyRefinements
attribute [-instance] _root_.OAI.PartitionPilot.Forcing.GroundMainPrefix.withTopSmall _root_.OAI.PartitionPilot.Forcing.Name.boundedNames_small
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section



namespace PartitionPilot.Forcing.PosetAction

open SetRealization Compression.RecursiveMaps
universe u v
variable {G : Type v} [Group G] {P : Type u} [PartialOrder P]
variable (a : PosetAction G P) (s : Presentation P)

def RectangleWitness (p : P) (x y : Name s) (g₁ g₂ : G) : Set P :=
  {q | ∃ h₁ h₂, q ≤ a.iso h₁ p ∧ q ≤ a.iso h₂ p ∧
    a.act s h₁ x = a.act s g₁ x ∧ a.act s h₂ x = a.act s g₂ x ∧
    a.act s h₁ y = a.act s h₂ y}

def SeparationWitness (K : Subgroup G) (Sep : G → G → Prop) (p : P) (g₁ g₂ : G) : Set P :=
  {q | ∃ h ∈ K, q ≤ a.iso h p ∧ Sep h g₁ ∧ Sep h g₂}

def copyWitnessFamily (K : Subgroup G) (Sep : G → G → Prop) (p : P) (x y : Name s) :
    Set (Set P) :=
  {D | (∃ r g₁ g₂, D = Localized r (a.RectangleWitness s p x y g₁ g₂)) ∨
    ∃ r g₁ g₂, D = Localized r (a.SeparationWitness K Sep p g₁ g₂)}

end PartitionPilot.Forcing.PosetAction



end

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Models_GroundOrdinalPartitionInjectionAssembly
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

noncomputable def definableRelation {n} (φ : SetFormula (n + 2))
    (params : Fin n → ZFSet.{u}) (A B : ZFSet.{u}) : ZFSet.{u} :=
  ZFSet.sep (fun z => ∃ x ∈ A, ∃ y ∈ B, z = ZFSet.pair x y ∧
    Realize M.sets φ (extend x (extend y params))) (ZFSet.prod A B)

end TransitiveGround
end PartitionPilot.Forcing




namespace PartitionPilot.Forcing
open SetRealization SetFormula
universe u
namespace BoundedFormula
def coveringPositionFormula : BoundedFormula 5 :=
  disj (.conj (emptyFormula 1) (.allMem 2 (.neg (pairMembershipFormula 0 1 4))))
    (.conj (functionFormula 4 2 1)
      (.conj (.allMem 4 (.allMem 3
        (imp (pairMembershipFormula 1 0 3) (pairMembershipFormula 0 2 5))))
        (.allMem 2 (imp (pairMembershipFormula 0 1 4)
          (exMem 5 (pairMembershipFormula 0 1 3))))))

end BoundedFormula
end PartitionPilot.Forcing



end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Forcing_GroundNiceNameGraphs
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
variable (M : TransitiveGround.{u}) {I G P : Type u} [Group G] [PartialOrder P]
variable (a : PosetAction G P) (s : Presentation P) (t : Presentation G) (b : Presentation I)

noncomputable def niceNameCandidateGraph (T : ZFSet.{u}) (K : I → Subgroup G) : ZFSet.{u} :=
  familyCodeGraph b.encode (fun i => M.niceNameCandidates a s T (K i))

theorem mem_niceNameCandidateGraph (T : ZFSet.{u}) (K : I → Subgroup G) (z : ZFSet.{u}) :
    z ∈ M.niceNameCandidateGraph a s b T K ↔
      ∃ i, z = ZFSet.pair (b.encode i) (M.niceNameCandidates a s T (K i)) := by
  rw [niceNameCandidateGraph, mem_familyCodeGraph]
  exact exists_congr (fun _ => eq_comm)

theorem pair_mem_niceNameCandidateGraph (T : ZFSet.{u}) (K : I → Subgroup G) (i : I) (z : ZFSet.{u}) :
    ZFSet.pair (b.encode i) z ∈ M.niceNameCandidateGraph a s b T K ↔
      z = M.niceNameCandidates a s T (K i) :=
  pair_mem_familyCodeGraph _ _ b.injective i z

theorem niceNameCandidateGraph_function (T : ZFSet.{u}) (K : I → Subgroup G) :
    FunctionGraphOn b.carrier (M.niceNameCandidateGraph a s b T K) := by
  have equal : ZFSet.range b.encode = b.carrier := by
    apply ZFSet.ext
    intro z
    rw [ZFSet.mem_range]
    exact (b.mem_carrier z).symm
  simpa only [niceNameCandidateGraph, equal] using familyCodeGraph_function b.encode
    (fun i => M.niceNameCandidates a s T (K i)) b.injective

end PartitionPilot.Forcing.TransitiveGround

end

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

theorem familyCodeGraph_valueRange_eq (key value : I → ZFSet.{u}) :
    ZFSet.range value = relationImage (ZFSet.range key)
      (ZFSet.sUnion (ZFSet.sUnion (familyCodeGraph key value))) (familyCodeGraph key value) := by
  apply ZFSet.ext
  intro y
  rw [ZFSet.mem_range, mem_relationImage]
  constructor
  · rintro ⟨i, rfl⟩
    have entry := (mem_familyCodeGraph key value _).2 ⟨i, rfl⟩
    exact ⟨pair_second_mem_doubleUnion entry, key i, ZFSet.mem_range.2 ⟨i, rfl⟩, entry⟩
  · rintro ⟨_, x, _, entry⟩
    obtain ⟨i, equal⟩ := (mem_familyCodeGraph key value _).1 entry
    exact ⟨i, (ZFSet.pair_inj.1 equal).2⟩

theorem familyCodeGraph_valueRange_rank_le (key value : I → ZFSet.{u}) :
    ZFSet.rank (ZFSet.range value) ≤ ZFSet.rank (familyCodeGraph key value) := by
  have subset : ZFSet.range value ⊆ ZFSet.sUnion (ZFSet.sUnion (familyCodeGraph key value)) := by
    intro y hy
    obtain ⟨i, rfl⟩ := ZFSet.mem_range.1 hy
    exact pair_second_mem_doubleUnion ((mem_familyCodeGraph key value _).2 ⟨i, rfl⟩)
  exact (ZFSet.rank_mono subset).trans ((ZFSet.rank_sUnion_le _).trans (ZFSet.rank_sUnion_le _))

theorem familyCodeGraph_valueUnion_rank_le (key value : I → ZFSet.{u}) :
    ZFSet.rank (ZFSet.sUnion (ZFSet.range value)) ≤ ZFSet.rank (familyCodeGraph key value) :=
  (ZFSet.rank_sUnion_le _).trans (familyCodeGraph_valueRange_rank_le key value)

end PartitionPilot.Forcing

end

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Definability_GroundPrincipalNiceSupportCodes
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
variable (M : TransitiveGround.{u}) {I G P : Type u}
variable [Group G] [PartialOrder P]
variable (a : PosetAction G P) (s : Presentation P) (b : Presentation I)
variable (T : ZFSet.{u}) (K : I → Subgroup G)

noncomputable def niceSupportNameCodes : ZFSet.{u} :=
  ZFSet.sUnion (ZFSet.range (fun i => M.niceNameCandidates a s T (K i)))

theorem mem_niceSupportNameCodes (z : ZFSet.{u}) :
    z ∈ M.niceSupportNameCodes a s T K ↔
      z ∈ M.sets ∧ ∃ i, NiceNameCode a s T (K i) z := by
  rw [niceSupportNameCodes, familyCodeGraph_valueUnion_mem_iff]
  constructor
  · rintro ⟨i, hi⟩
    have code := (M.mem_niceNameCandidates a s T (K i) z).1 hi
    exact ⟨code.1, i, code.2⟩
  · rintro ⟨ground, i, code⟩
    exact ⟨i, (M.mem_niceNameCandidates a s T (K i) z).2 ⟨ground, code⟩⟩

theorem niceSupportNameCodes_valid :
    ∀ z ∈ M.niceSupportNameCodes a s T K, IsName s z := by
  intro z member
  obtain ⟨_, i, code⟩ := (M.mem_niceSupportNameCodes a s T K z).1 member
  exact niceNameCode_isName a s code

noncomputable def niceSupportRelation : ZFSet.{u} :=
  ZFSet.sep (fun z => ∃ i tau, z = ZFSet.pair (b.encode i) tau ∧
    tau ∈ M.niceNameCandidates a s T (K i))
    (ZFSet.prod b.carrier (M.niceSupportNameCodes a s T K))

end PartitionPilot.Forcing.TransitiveGround



end

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Forcing_AllSupportFamilies
attribute [-instance] _root_.OAI.PartitionPilot.Forcing.GroundMainPrefix.withTopSmall
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PartitionPilot.Forcing
open SetRealization Compression.RecursiveMaps
universe u v

def allSupportFamily (G : Type u) [Group G] : NormalSubgroupFamily G where
  mem := fun _ => True
  top := True.intro
  upward := fun _ _ => True.intro
  inf := fun _ _ => True.intro
  conjugate := fun _ {_} _ => True.intro

end PartitionPilot.Forcing

end

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Forcing_GroundNameSequenceForcingWitness
attribute [-instance] _root_.OAI.PartitionPilot.Forcing.GroundMainPrefix.withTopSmall
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PartitionPilot.Forcing

section
open SetFormula SetRealization
universe u

namespace Name
variable {P : Type u} [Preorder P] (s : Presentation P)

noncomputable def sequenceDecision (one : P) (τ : Name s)
    (p : P) (n a : ZFSet.{u}) : Prop :=
  ForcesMem p (check s one (ZFSet.pair n a)) τ

end Name

namespace Name
variable {P : Type u} [Preorder P] (s : Presentation P)

noncomputable def sequenceDecisionRelation (one : P) (τ : Name s) (N U : ZFSet.{u}) : ZFSet.{u} :=
  ZFSet.sep (fun z => ∃ p : P, ∃ n ∈ N, ∃ a ∈ U,
    z = ZFSet.pair (ZFSet.pair (s.encode p) n) a ∧ sequenceDecision s one τ p n a)
      (ZFSet.prod (ZFSet.prod s.carrier N) U)

end Name

end

end PartitionPilot.Forcing

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Forcing_GroundNameSequenceValues
attribute [-instance] _root_.OAI.PartitionPilot.Forcing.GroundMainPrefix.withTopSmall
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI



namespace PartitionPilot.Forcing
open SetFormula SetRealization
universe u

def enumeratedFamilyDecisionFormula : BoundedFormula 7 :=
  .exMem 1 (.exMem 3 (.exMem 5 (.exMem 7
    (.conj (BoundedFormula.orderedTripleFormula 4 3 2 1)
      (.conj (BoundedFormula.pairMembershipFormula 2 1 9)
        (.conj (BoundedFormula.pairMembershipFormula 1 0 10) (.mem 3 0)))))))

end PartitionPilot.Forcing



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


namespace PartitionPilot.Forcing.Name
open SetRealization
universe u
variable {P : Type u} [Preorder P] {s : Presentation P}

noncomputable def activeImage (T : ZFSet.{u}) (valid : ∀ z ∈ T, IsName s z)
    (U : Name s) (image : Name s → Name s) : Name s :=
  assemble
    (fun a : {a : T × P // ForcesMem a.2 ⟨a.1.val, valid a.1.val a.1.property⟩ U} =>
      image ⟨a.val.1.val, valid a.val.1.val a.val.1.property⟩)
    (fun a => a.val.2)

theorem entry_activeImage (T : ZFSet.{u}) (valid : ∀ z ∈ T, IsName s z)
    (U : Name s) (image : Name s → Name s) (σ : Name s) (p : P) :
    Entry σ (activeImage T valid U image) p ↔
      ∃ w : Name s, w.val ∈ T ∧ ForcesMem p w U ∧ image w = σ := by
  rw [activeImage, entry_assemble]
  constructor
  · rintro ⟨a, equal, condition⟩
    refine ⟨⟨a.val.1.val, valid a.val.1.val a.val.1.property⟩, a.val.1.property, ?_, equal⟩
    exact condition ▸ a.property
  · rintro ⟨w, hw, forced, equal⟩
    exact ⟨⟨(⟨w.val, hw⟩, p), forced⟩, equal, rfl⟩

theorem activeImage_subset (T : ZFSet.{u}) (valid : ∀ z ∈ T, IsName s z)
    (U : Name s) (image : Name s → Name s) (F : ZFSet.{u})
    (images : ∀ w : Name s, w.val ∈ T → (image w).val ∈ F) :
    (activeImage T valid U image).val ⊆ ZFSet.prod F s.carrier := by
  intro z hz
  obtain ⟨σ, p, rfl⟩ := entries_cover (activeImage T valid U image) hz
  obtain ⟨w, hw, _, rfl⟩ := (entry_activeImage T valid U image σ p).1 hz
  exact ZFSet.pair_mem_prod.2 ⟨images w hw, s.encode_mem p⟩

end PartitionPilot.Forcing.Name



namespace PartitionPilot.Forcing.Name
open SetRealization Compression.RecursiveMaps
universe u v
variable {P : Type u} [PartialOrder P] {s : Presentation P}
variable {G : Type v} [Group G] (a : PosetAction G P)

theorem act_activeImage (T : ZFSet.{u}) (valid : ∀ z ∈ T, IsName s z)
    (closed : ∀ g (w : Name s), w.val ∈ T → (a.act s g w).val ∈ T)
    (g : G) (U : Name s) (image other : Name s → Name s)
    (equivariant : ∀ w : Name s, w.val ∈ T →
      a.act s g (image w) = other (a.act s g w)) :
    a.act s g (activeImage T valid U image) =
      activeImage T valid (a.act s g U) other := by
  apply Name.ext
  intro σ p
  change Entry σ (rename s (a.iso g) (activeImage T valid U image)) p ↔ _
  rw [entry_rename, entry_activeImage]
  constructor
  · rintro ⟨ν, q, entry, equal, rfl⟩
    obtain ⟨w, hw, forced, rfl⟩ := (entry_activeImage T valid U image ν q).1 entry
    exact ⟨a.act s g w, closed g w hw, a.forcesMem_act s g forced,
      (equivariant w hw).symm.trans equal⟩
  · rintro ⟨w, hw, forced, equal⟩
    have oldMember := closed g⁻¹ w hw
    have oldForced : ForcesMem ((a.iso g).symm p) (a.act s g⁻¹ w) U := by
      apply (a.forcesMem_act_iff s g ((a.iso g).symm p) (a.act s g⁻¹ w) U).1
      simpa only [OrderIso.apply_symm_apply, a.act_inv_right] using forced
    refine ⟨image (a.act s g⁻¹ w), (a.iso g).symm p,
      (entry_activeImage T valid U image _ _).2 ⟨a.act s g⁻¹ w, oldMember, oldForced, rfl⟩,
      ?_, (a.iso g).apply_symm_apply p⟩
    change a.act s g (image (a.act s g⁻¹ w)) = σ
    rw [equivariant _ oldMember, a.act_inv_right]
    exact equal

end PartitionPilot.Forcing.Name



end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Models_GroundRefinementQuotientNames
attribute [-instance] _root_.OAI.PartitionPilot.Forcing.GroundMainPrefix.withTopSmall
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI



namespace PartitionPilot.Forcing
open SetRealization
universe u

namespace Name
variable {P : Type u} [PartialOrder P] [OrderTop P] {s : Presentation P}

noncomputable def refinementQuotient (T : ZFSet.{u}) (valid : ∀ z ∈ T, IsName s z)
    (U R : Name s) : Name s :=
  activeImage T valid U (refinementClass T valid R)

noncomputable def refinementNaturalMap (T : ZFSet.{u}) (valid : ∀ z ∈ T, IsName s z)
    (U Rf Rc : Name s) : Name s :=
  activeImage T valid U (fun w =>
    orderedPair ⊤ (refinementClass T valid Rf w) (refinementClass T valid Rc w))

theorem entry_refinementQuotient (T : ZFSet.{u}) (valid : ∀ z ∈ T, IsName s z)
    (U R σ : Name s) (p : P) :
    Entry σ (refinementQuotient T valid U R) p ↔
      ∃ w : Name s, w.val ∈ T ∧ ForcesMem p w U ∧ refinementClass T valid R w = σ :=
  entry_activeImage T valid U _ σ p

theorem entry_refinementNaturalMap (T : ZFSet.{u}) (valid : ∀ z ∈ T, IsName s z)
    (U Rf Rc σ : Name s) (p : P) :
    Entry σ (refinementNaturalMap T valid U Rf Rc) p ↔
      ∃ w : Name s, w.val ∈ T ∧ ForcesMem p w U ∧
        orderedPair ⊤ (refinementClass T valid Rf w) (refinementClass T valid Rc w) = σ :=
  entry_activeImage T valid U _ σ p

end Name

end PartitionPilot.Forcing



namespace PartitionPilot.Forcing.Name
open SetRealization Compression.RecursiveMaps
universe u v
variable {P : Type u} [PartialOrder P] [OrderTop P] {s : Presentation P}
variable {G : Type v} [Group G] (a : PosetAction G P)
variable (T : ZFSet.{u}) (valid : ∀ z ∈ T, IsName s z)
variable (closed : ∀ g (w : Name s), w.val ∈ T → (a.act s g w).val ∈ T)
include closed

theorem act_refinementNaturalMap (g : G) (U Rf Rc : Name s) :
    a.act s g (refinementNaturalMap T valid U Rf Rc) =
      refinementNaturalMap T valid (a.act s g U) (a.act s g Rf) (a.act s g Rc) := by
  apply act_activeImage a T valid closed g U
  intro w _
  change rename s (a.iso g) (orderedPair ⊤ _ _) = _
  rw [rename_orderedPair, (a.iso g).map_top]
  change orderedPair ⊤ (a.act s g (refinementClass T valid Rf w))
    (a.act s g (refinementClass T valid Rc w)) = _
  rw [act_refinementClass a T valid closed, act_refinementClass a T valid closed]

end PartitionPilot.Forcing.Name



end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Geometry_GroundNormalizedRefinementOutputs
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

structure RefinementObjectValues {P : Type u} [PartialOrder P] [OrderTop P]
    {s : Presentation P} (H : Set P) (T : ZFSet.{u}) (valid : ∀ z ∈ T, IsName s z)
    (U Rf Rc : Name s) : Prop where
  validity : RefinementValidityCode (Name.eval H (Name.familySet ⊤ T valid))
    (Name.eval H U) (Name.eval H Rf) (Name.eval H Rc)
  fine_class : ∀ w : Name s, w.val ∈ T →
    Name.eval H (Name.refinementClass T valid Rf w) =
      equivalenceClass (Name.eval H U) (Name.eval H Rf) (Name.eval H w)
  coarse_class : ∀ w : Name s, w.val ∈ T →
    Name.eval H (Name.refinementClass T valid Rc w) =
      equivalenceClass (Name.eval H U) (Name.eval H Rc) (Name.eval H w)
  fine_quotient : Name.eval H (Name.refinementQuotient T valid U Rf) =
    equivalenceClasses (Name.eval H U) (Name.eval H Rf)
  coarse_quotient : Name.eval H (Name.refinementQuotient T valid U Rc) =
    equivalenceClasses (Name.eval H U) (Name.eval H Rc)
  natural_map : Name.eval H (Name.refinementNaturalMap T valid U Rf Rc) =
    refinementQuotientMap (Name.eval H U) (Name.eval H Rf) (Name.eval H Rc)
  function : ZFSet.IsFunc (Name.eval H (Name.refinementQuotient T valid U Rf))
    (Name.eval H (Name.refinementQuotient T valid U Rc))
    (Name.eval H (Name.refinementNaturalMap T valid U Rf Rc))
  onto : ∀ C ∈ Name.eval H (Name.refinementQuotient T valid U Rc),
    ∃ D ∈ Name.eval H (Name.refinementQuotient T valid U Rf),
      ZFSet.pair D C ∈ Name.eval H (Name.refinementNaturalMap T valid U Rf Rc)
  inactive : ∀ w : Name s, w.val ∈ T → Name.eval H w ∉ Name.eval H U →
    Name.eval H (Name.refinementClass T valid Rf w) = ∅ ∧
    Name.eval H (Name.refinementClass T valid Rc w) = ∅

namespace TransitiveGround
variable (M : TransitiveGround.{u}) {P : Type u} [PartialOrder P] [OrderTop P] (s : Presentation P)

noncomputable def refinementNameEnv (T : ZFSet.{u}) (valid : ∀ z ∈ T, IsName s z)
    (hFamily : (Name.familySet ⊤ T valid).val ∈ M.sets)
    (U Rf Rc : (M.nameDomain s).names) : Assignment (M.nameDomain s) 4 :=
  extend U (extend Rf (extend Rc (extend ⟨Name.familySet ⊤ T valid, hFamily⟩ Fin.elim0)))

end TransitiveGround

end PartitionPilot.Forcing



end

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Forcing_GroundIndexedGraphNameFamilies
attribute [-instance] _root_.OAI.PartitionPilot.Forcing.GroundMainPrefix.withTopSmall
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open scoped ZFSet

section

namespace PartitionPilot.Forcing
open SetRealization SetFormula
universe u

noncomputable def indexedGraphNameCode (one I f : ZFSet.{u}) : ZFSet.{u} :=
  ZFSet.range (fun a : {a : ↥I × ↥(⋃₀ ⋃₀ f) // ZFSet.pair a.1.val a.2.val ∈ f} =>
    ZFSet.pair (orderedPairNameCode one (checkNameCode one a.val.1.val) a.val.2.val) one)

theorem mem_indexedGraphNameCode (one I f z : ZFSet.{u}) :
    z ∈ indexedGraphNameCode one I f ↔ ∃ i ∈ I, ∃ v,
      ZFSet.pair i v ∈ f ∧ z = ZFSet.pair (orderedPairNameCode one (checkNameCode one i) v) one := by
  rw [indexedGraphNameCode, ZFSet.mem_range]
  constructor
  · rintro ⟨a, equal⟩
    exact ⟨a.val.1.val, a.val.1.property, a.val.2.val, a.property, equal.symm⟩
  · rintro ⟨i, hi, v, entry, equal⟩
    exact ⟨⟨(⟨i, hi⟩, ⟨v, pair_second_mem_doubleUnion entry⟩), entry⟩, equal.symm⟩

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



namespace PartitionPilot.Forcing
open SetRealization SetFormula
universe u

noncomputable def rowTupleCode (one mu I W rows f : ZFSet.{u}) : ZFSet.{u} :=
  indexedGraphNameCode one mu (relationCompose mu I W f rows)

noncomputable def rowTupleFamily (one mu I W rows S : ZFSet.{u}) : ZFSet.{u} :=
  familyCodeGraph (fun f : S => f.val) (fun f => rowTupleCode one mu I W rows f.val)

end PartitionPilot.Forcing



end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Forcing_PairFamilyEvaluation
attribute [-instance] _root_.OAI.PartitionPilot.Forcing.GroundMainPrefix.withTopSmall
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PartitionPilot.Forcing
open SetRealization Compression.RecursiveMaps
universe u v
variable {P : Type u} {s : Presentation P}

theorem orderedPairNameFamily_valid (one : P) {X Y : ZFSet.{u}}
    (validX : ∀ z ∈ X, IsName s z) (validY : ∀ z ∈ Y, IsName s z) :
    ∀ z ∈ orderedPairNameFamily (s.encode one) X Y, IsName s z := by
  intro z hz
  obtain ⟨x, hx, y, hy, rfl⟩ := (mem_orderedPairNameFamily _ X Y z).1 hz
  have code := Name.orderedPair_code one (⟨x, validX x hx⟩ : Name s)
    (⟨y, validY y hy⟩ : Name s)
  exact code ▸ (Name.orderedPair one ⟨x, validX x hx⟩ ⟨y, validY y hy⟩).property

theorem iteratedPairNameFamily_valid (one : P) {T : ZFSet.{u}}
    (valid : ∀ z ∈ T, IsName s z) (n : Nat) :
    ∀ z ∈ iteratedPairNameFamily (s.encode one) T n, IsName s z := by
  induction n with
  | zero => exact valid
  | succ n ih => exact orderedPairNameFamily_valid one ih valid

end PartitionPilot.Forcing



end

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

noncomputable def renameFamilyGraph (t : Presentation Q) (f : P → Q)
    (T : ZFSet.{u}) (valid : ∀ x ∈ T, IsName s x) : ZFSet.{u} :=
  familyCodeGraph (fun x : T => x.val)
    (fun x => (rename t f ⟨x.val, valid x.val x.property⟩).val)

theorem mem_renameFamilyGraph (t : Presentation Q) (f : P → Q)
    (T : ZFSet.{u}) (valid : ∀ x ∈ T, IsName s x) (z : ZFSet.{u}) :
    z ∈ renameFamilyGraph t f T valid ↔
      ∃ σ : Name s, σ.val ∈ T ∧ z = ZFSet.pair σ.val (rename t f σ).val := by
  rw [renameFamilyGraph, mem_familyCodeGraph]
  constructor
  · rintro ⟨x, rfl⟩
    exact ⟨⟨x.val, valid x.val x.property⟩, x.property, rfl⟩
  · rintro ⟨σ, hσ, rfl⟩
    exact ⟨⟨σ.val, hσ⟩, rfl⟩

theorem pair_mem_renameFamilyGraph (t : Presentation Q) (f : P → Q)
    (T : ZFSet.{u}) (valid : ∀ x ∈ T, IsName s x) (σ : Name s) (y : ZFSet.{u}) :
    ZFSet.pair σ.val y ∈ renameFamilyGraph t f T valid ↔
      σ.val ∈ T ∧ y = (rename t f σ).val := by
  rw [mem_renameFamilyGraph]
  constructor
  · rintro ⟨τ, hτ, eq⟩
    obtain ⟨keys, values⟩ := ZFSet.pair_inj.1 eq
    have same : σ = τ := Subtype.ext keys
    exact ⟨same.symm ▸ hτ, by simpa only [same] using values⟩
  · rintro ⟨hσ, rfl⟩
    exact ⟨σ, hσ, rfl⟩

end PartitionPilot.Forcing.Name

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

namespace PartitionPilot.SetRealization.Presentation
open Forcing
universe u
variable {P : Type u} (s : Presentation P)

noncomputable def pairEmpty : Presentation P where
  carrier := ZFSet.prod s.carrier {∅}
  encode p := ZFSet.pair (s.encode p) ∅
  injective := fun _ _ eq => s.injective (ZFSet.pair_inj.1 eq).1
  mem_carrier z := by
    rw [ZFSet.mem_prod]
    constructor
    · rintro ⟨x, hx, y, hy, eq⟩
      have empty : y = ∅ := ZFSet.mem_singleton.1 hy
      obtain ⟨p, rfl⟩ := (s.mem_carrier x).1 hx
      exact ⟨p, by rw [empty] at eq; exact eq.symm⟩
    · rintro ⟨p, rfl⟩
      exact ⟨s.encode p, s.encode_mem p, ∅, ZFSet.mem_singleton.2 rfl, rfl⟩

end PartitionPilot.SetRealization.Presentation

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Forcing_NameFamilySetTransport
attribute [-instance] _root_.OAI.PartitionPilot.Forcing.GroundMainPrefix.withTopSmall
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PartitionPilot.Forcing.Name
open SetRealization Compression.RecursiveMaps
universe u v
variable {P : Type u} [PartialOrder P] [OrderTop P] {s : Presentation P}
variable {G : Type v} [Group G] (a : PosetAction G P)

theorem act_familySet_transport (T U : ZFSet.{u})
    (validT : ∀ z ∈ T, IsName s z) (validU : ∀ z ∈ U, IsName s z)
    (g : G) (transport : ∀ τ : Name s, (a.act s g τ).val ∈ U ↔ τ.val ∈ T) :
    a.act s g (familySet ⊤ T validT) = familySet ⊤ U validU := by
  apply Name.ext
  intro σ p
  change Entry σ (rename s (a.iso g) (familySet ⊤ T validT)) p ↔ _
  rw [entry_rename, entry_familySet]
  constructor
  · rintro ⟨τ, q, entry, equal, hp⟩
    obtain ⟨hτ, rfl⟩ := (entry_familySet ⊤ T validT τ q).1 entry
    have target := (transport τ).2 hτ
    change a.act s g τ = σ at equal
    exact ⟨equal ▸ target, hp.symm.trans (a.iso g).map_top⟩
  · rintro ⟨hσ, rfl⟩
    have back : (a.act s g⁻¹ σ).val ∈ T := (transport _).1 (by
      simpa only [a.act_inv_right] using hσ)
    exact ⟨a.act s g⁻¹ σ, ⊤,
      (entry_familySet ⊤ T validT _ ⊤).2 ⟨back, rfl⟩,
      a.act_inv_right s g σ, (a.iso g).map_top⟩

theorem familySet_support (T : ZFSet.{u}) (valid : ∀ z ∈ T, IsName s z)
    (K : Subgroup G) (supported : ∀ τ : Name s, τ.val ∈ T → K ≤ a.stabilizer s τ) :
    K ≤ a.stabilizer s (familySet ⊤ T valid) := by
  intro g hg
  apply Name.ext
  intro σ p
  change Entry σ (rename s (a.iso g) (familySet ⊤ T valid)) p ↔ _
  rw [entry_rename, entry_familySet]
  constructor
  · rintro ⟨τ, q, entry, equal, hp⟩
    obtain ⟨hτ, rfl⟩ := (entry_familySet ⊤ T valid τ q).1 entry
    have fixed := supported τ hτ hg
    change a.act s g τ = σ at equal
    rw [fixed] at equal
    exact ⟨equal ▸ hτ, hp.symm.trans (a.iso g).map_top⟩
  · rintro ⟨hσ, rfl⟩
    exact ⟨σ, ⊤, (entry_familySet ⊤ T valid σ ⊤).2 ⟨hσ, rfl⟩,
      supported σ hσ hg, (a.iso g).map_top⟩

end PartitionPilot.Forcing.Name

end

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

theorem niceNameCandidates_valid (T : ZFSet.{u}) (K : Subgroup G) :
    ∀ z ∈ M.niceNameCandidates a s T K, IsName s z := by
  intro z hz
  exact niceNameCode_isName a s ((M.mem_niceNameCandidates a s T K z).1 hz).2

variable [OrderTop P]

noncomputable def niceVisibilityName (T : ZFSet.{u}) (K : Subgroup G) : Name s :=
  Name.familySet ⊤ (M.niceNameCandidates a s T K) (M.niceNameCandidates_valid a s T K)

theorem niceVisibilityName_code (T : ZFSet.{u}) (K : Subgroup G) :
    (M.niceVisibilityName a s T K).val =
      ZFSet.prod (M.niceNameCandidates a s T K) {s.encode ⊤} :=
  Name.familySet_code ⊤ _ _

theorem entry_niceVisibilityName (T : ZFSet.{u}) (K : Subgroup G)
    (τ : Name s) (p : P) :
    Name.Entry τ (M.niceVisibilityName a s T K) p ↔
      τ.val ∈ M.niceNameCandidates a s T K ∧ p = ⊤ :=
  Name.entry_familySet ⊤ _ _ τ p

theorem mem_eval_niceVisibilityName (T : ZFSet.{u}) (K : Subgroup G)
    (H : Set P) (top : ⊤ ∈ H) (x : ZFSet.{u}) :
    x ∈ Name.eval H (M.niceVisibilityName a s T K) ↔
      ∃ τ : Name s, τ.val ∈ M.niceNameCandidates a s T K ∧ Name.eval H τ = x :=
  Name.mem_eval_familySet H ⊤ top _ _ x

theorem niceVisibilityName_support (T : ZFSet.{u}) (K : Subgroup G) :
    K ≤ a.stabilizer s (M.niceVisibilityName a s T K) := by
  apply Name.familySet_support a _ _ K
  intro τ hτ
  exact ((M.name_mem_niceNameCandidates a s T K τ).1 hτ).2.2

theorem niceVisibilityName_hs (F : NormalSubgroupFamily G)
    (T : ZFSet.{u}) (K : Subgroup G) (member : F.mem K)
    (children : ∀ τ : Name s, τ.val ∈ T → HereditarilySymmetric a s F τ) :
    HereditarilySymmetric a s F (M.niceVisibilityName a s T K) := by
  refine HereditarilySymmetric.mk (F.upward member (M.niceVisibilityName_support a s T K)) ?_
  intro τ p entry
  have candidate := ((M.mem_niceNameCandidates a s T K τ.val).1
    ((M.entry_niceVisibilityName a s T K τ p).1 entry).1).2
  exact niceNameCode_hs a s F member children candidate

end PartitionPilot.Forcing.TransitiveGround

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Definability_GroundNiceVisibilityGraphs
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
variable (M : TransitiveGround.{u}) {I G P : Type u} [Group G] [PartialOrder P] [OrderTop P]
variable (a : PosetAction G P) (s : Presentation P) (t : Presentation G) (b : Presentation I)

noncomputable def niceVisibilityGraph (T : ZFSet.{u}) (K : I → Subgroup G) : ZFSet.{u} :=
  familyCodeGraph b.encode (fun i => (M.niceVisibilityName a s T (K i)).val)

theorem mem_niceVisibilityGraph (T : ZFSet.{u}) (K : I → Subgroup G) (z : ZFSet.{u}) :
    z ∈ M.niceVisibilityGraph a s b T K ↔
      ∃ i, z = ZFSet.pair (b.encode i) (M.niceVisibilityName a s T (K i)).val := by
  rw [niceVisibilityGraph, mem_familyCodeGraph]
  exact exists_congr (fun _ => eq_comm)

theorem pair_mem_niceVisibilityGraph (T : ZFSet.{u}) (K : I → Subgroup G) (i : I) (z : ZFSet.{u}) :
    ZFSet.pair (b.encode i) z ∈ M.niceVisibilityGraph a s b T K ↔
      z = (M.niceVisibilityName a s T (K i)).val :=
  pair_mem_familyCodeGraph _ _ b.injective i z

theorem niceVisibilityGraph_function (T : ZFSet.{u}) (K : I → Subgroup G) :
    FunctionGraphOn b.carrier (M.niceVisibilityGraph a s b T K) := by
  have equal : ZFSet.range b.encode = b.carrier := by
    apply ZFSet.ext
    intro z
    rw [ZFSet.mem_range]
    exact (b.mem_carrier z).symm
  simpa only [niceVisibilityGraph, equal] using familyCodeGraph_function b.encode
    (fun i => (M.niceVisibilityName a s T (K i)).val) b.injective

end PartitionPilot.Forcing.TransitiveGround

end

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Forcing_RefinementCoarseImageNames
attribute [-instance] _root_.OAI.PartitionPilot.Forcing.GroundMainPrefix.withTopSmall
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PartitionPilot.Forcing
open SetRealization SetFormula
universe u v

namespace Name
variable {P : Type u} [PartialOrder P] [OrderTop P] {s : Presentation P}

noncomputable def refinementCoarseImage (D : NameDomain s) (T : ZFSet.{u})
    (valid : ∀ z ∈ T, IsName s z) (U sigma Rc : D.names) : Name s :=
  separationName D BoundedFormula.coarseClassImageFormula.toFormula
    (extend U (extend sigma (extend Rc Fin.elim0))) (familySet ⊤ T valid)

end Name

end PartitionPilot.Forcing

end

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
universe u

def RefinementIndexLevelCode (I level : ZFSet.{u}) : Prop :=
  ∀ z ∈ I, ∃ fields : Fin 6 → ZFSet.{u},
    z = nonemptyTupleCode 5 fields ∧ fields 0 = level

end PartitionPilot.Forcing



namespace PartitionPilot.Forcing
open SetRealization SetFormula
universe u
variable {G P L : Type u} [Group G] [PartialOrder P] [OrderTop P] [PartialOrder L]

namespace TransitiveGround
noncomputable def niceRefinementIndexBounds (M : TransitiveGround.{u})
    (s : Presentation P) (b : Presentation L) (level T1 T2 : ZFSet.{u}) : Fin 6 → ZFSet.{u} :=
  ![{level}, b.carrier, b.carrier, M.groundRelations T1 s.carrier,
    M.groundRelations T2 s.carrier, M.groundRelations T2 s.carrier]

end TransitiveGround

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

theorem assignmentCut_mem (separation : SeparationSchema M.sets)
    {levels alpha A : ZFSet.{u}}
    (hLevels : levels ∈ M.sets) (hAlpha : alpha ∈ M.sets) (hA : A ∈ M.sets) :
    assignmentCut levels alpha A ∈ M.sets := by
  let formula : BoundedFormula 3 := BoundedFormula.exMem 1
    (BoundedFormula.pairMembershipFormula 1 0 3)
  let params := extend alpha (extend levels Fin.elim0)
  have ground := M.bounded_separation_mem separation formula params
    (Fin.cases hAlpha (Fin.cases hLevels (fun i => Fin.elim0 i))) hA
  have equal : ZFSet.sep (fun z => BoundedFormula.Truth formula (extend z params)) A =
      assignmentCut levels alpha A := by
    apply ZFSet.ext
    intro z
    simp only [ZFSet.mem_sep, assignmentCut, formula,
      BoundedFormula.truth_exMem, BoundedFormula.truth_pairMembershipFormula]
    rfl
  exact equal ▸ ground

theorem assignmentUpper_mem (separation : SeparationSchema M.sets)
    {levels alpha A : ZFSet.{u}}
    (hLevels : levels ∈ M.sets) (hAlpha : alpha ∈ M.sets) (hA : A ∈ M.sets) :
    assignmentUpper levels alpha A ∈ M.sets := by
  exact M.bounded_separation_mem separation (.neg (.mem 0 1))
    (extend (assignmentCut levels alpha A) Fin.elim0)
    (Fin.cases (M.assignmentCut_mem separation hLevels hAlpha hA) (fun i => Fin.elim0 i)) hA

theorem assignmentSplice_mem
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0) (separation : SeparationSchema M.sets)
    {levels alpha Aq Ap : ZFSet.{u}}
    (hLevels : levels ∈ M.sets) (hAlpha : alpha ∈ M.sets)
    (hAq : Aq ∈ M.sets) (hAp : Ap ∈ M.sets) :
    assignmentSplice levels alpha Aq Ap ∈ M.sets :=
  M.binary_union_mem pairing unions
    (M.assignmentCut_mem separation hLevels hAlpha hAq)
    (M.assignmentUpper_mem separation hLevels hAlpha hAp)

end PartitionPilot.Forcing.TransitiveGround



end

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Geometry_GroundRowAssignmentCuts
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
def rowAssignmentCutBody {n : Nat} (z levels alpha : Fin n) : BoundedFormula (n + 5) :=
  let old := suffixIndex n 5
  let v := prefixIndex n 5
  .conj (BoundedFormula.orderedPairFormula (old z) (v 3) (v 4))
    (.conj (BoundedFormula.orderedPairFormula (v 3) (v 0) (v 1))
      (.conj (BoundedFormula.orderedPairFormula (v 4) (v 0) (v 2))
        (BoundedFormula.assignmentCutFormula (v 2) (old levels) (old alpha) (v 1))))

def rowAssignmentCutFormula {n : Nat} (z levels alpha : Fin n) : SetFormula n :=
  exBlock 5 (rowAssignmentCutBody z levels alpha).toFormula

end SetFormula

end PartitionPilot.Forcing

end

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

namespace TransitiveGround
variable (M : TransitiveGround.{u})

theorem realize_stageOnePairLookup {n : Nat} (x y R : Fin n) (env : Fin n → ZFSet.{u})
    (members : ∀ j, env j ∈ M.sets) :
    Realize M.sets (BoundedFormula.pairMembershipFormula x y R).toFormula env ↔
      ZFSet.pair (env x) (env y) ∈ env R :=
  (BoundedFormula.realize_toFormula M _ env members).trans (BoundedFormula.truth_pairMembershipFormula x y R env)

end TransitiveGround

end

open SetFormula
universe u

end PartitionPilot.Forcing

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Forcing_GroundPreparationForcing
attribute [-instance] _root_.OAI.PartitionPilot.Forcing.GroundMainPrefix.withTopSmall
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace PartitionPilot.Forcing.TransitiveGround
open SetRealization SetFormula
universe u
variable (M : TransitiveGround.{u}) {I G P : Type u}
variable [Group G] [PartialOrder P] [OrderTop P]
variable (a : PosetAction G P) (s : Presentation P) (b : Presentation I)

theorem visibilityValues_isName (T : ZFSet.{u}) (K : I → Subgroup G)
    (i : b.carrier.toSet) :
    IsName s ((M.niceVisibilityGraph_function a s b T K).value i) := by
  obtain ⟨v, equal⟩ := (b.mem_carrier i.val).1 i.property
  have entry : ZFSet.pair i.val (M.niceVisibilityName a s T (K v)).val ∈
      M.niceVisibilityGraph a s b T K := by
    rw [← equal]
    exact (M.pair_mem_niceVisibilityGraph a s b T K v _).2 rfl
  rw [(M.niceVisibilityGraph_function a s b T K).value_eq_of_entry i entry]
  exact (M.niceVisibilityName a s T (K v)).property

noncomputable def niceVisibilityEvaluationName (T : ZFSet.{u}) (K : I → Subgroup G) : Name s :=
  Name.indexedGraphName ⊤ (M.niceVisibilityGraph_function a s b T K)
    (visibilityValues_isName M a s b T K)

end PartitionPilot.Forcing.TransitiveGround



namespace PartitionPilot.Forcing.TransitiveGround
open SetRealization SetFormula
universe u
variable (M : TransitiveGround.{u}) {I G P : Type u}
variable [Group G] [PartialOrder P] [OrderTop P]
variable (a : PosetAction G P) (s : Presentation P) (t : Presentation G) (b : Presentation I)
variable (K : I → Subgroup G)

def DecidesVisibilityProfile (T F : ZFSet.{u}) (z : Name s) (p : P) : Prop :=
  ∀ v : I,
    (b.encode v ∈ F → Name.ForcesMem p z (M.niceVisibilityName a s T (K v))) ∧
    (b.encode v ∉ F → ∀ q : P, q ≤ p → ¬ Name.ForcesMem q z (M.niceVisibilityName a s T (K v)))

end PartitionPilot.Forcing.TransitiveGround




end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Geometry_GroundOrdinarySubmodelReflection
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
variable (M : TransitiveGround.{u}) {P : Type u} [Preorder P]
variable (s : Presentation P)

def ordinaryExtension (H : ConditionFilter P) : TransitiveGround.{u} :=
  ⟨(M.nameDomain s).values {q | H.mem q}, (M.nameDomain s).values_transitive {q | H.mem q}⟩

end TransitiveGround

section
open SetFormula
universe u

def GroundSequenceReflection (M N : TransitiveGround.{u}) (P : ZFSet.{u}) : Prop :=
  ∀ f ∈ N.sets, ZFSet.IsFunc ZFSet.omega P f → f ∈ M.sets

end

end PartitionPilot.Forcing

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Forcing_GroundProjectedRowChooserWitnesses
attribute [-instance] _root_.OAI.PartitionPilot.Forcing.GroundMainPrefix.withTopSmall
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace PartitionPilot.Forcing.TransitiveGround
open SetFormula SetRealization Compression.RecursiveMaps
universe u v
variable (M : TransitiveGround.{u}) {P : Type u} [PartialOrder P]
variable (s : Presentation P) {G : Type v} [Group G]
variable (a : PosetAction G P) (F : NormalSubgroupFamily G)

def symmetricExtension (H : ConditionFilter P) : TransitiveGround.{u} :=
  ⟨(a.symmetricDomain s (M.nameDomain s) F).values {q | H.mem q},
    (a.symmetricDomain s (M.nameDomain s) F).values_transitive {q | H.mem q}⟩

end PartitionPilot.Forcing.TransitiveGround


section

namespace PartitionPilot.Forcing.Name
open SetRealization Compression.RecursiveMaps
universe u
variable {G P : Type u} [Group G] [PartialOrder P]
variable (a : PosetAction G P) (s : Presentation P)

noncomputable def supportedFamilyCodes (K : Subgroup G) (W : ZFSet.{u}) : ZFSet.{u} :=
  ZFSet.sep (fun z => ∃ tau : Name s, tau.val = z ∧ K ≤ a.stabilizer s tau) W

end PartitionPilot.Forcing.Name

end


end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Forcing_GeneratedMeetFilters
attribute [-instance] _root_.OAI.PartitionPilot.Compression.RecursiveMaps.TileRequests.Family.child_countable _root_.OAI.PartitionPilot.Compression.RecursiveMaps.TileRequests.Request.child_countable _root_.OAI.PartitionPilot.Forcing.GroundMainPrefix.withTopSmall
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PartitionPilot
universe u
variable {α : Type u} (P : MeetOrder α) (A : α → Prop)

theorem MeetOrder.meet_assoc (a b c : α) :
    P.meet (P.meet a b) c = P.meet a (P.meet b c) := by
  apply P.antisymm
  · exact P.le_meet
      (P.trans (P.meet_le_left _ _) (P.meet_le_left _ _))
      (P.le_meet (P.trans (P.meet_le_left _ _) (P.meet_le_right _ _)) (P.meet_le_right _ _))
  · exact P.le_meet
      (P.le_meet (P.meet_le_left _ _) (P.trans (P.meet_le_right _ _) (P.meet_le_left _ _)))
      (P.trans (P.meet_le_right _ _) (P.meet_le_right _ _))

def meetGeneratorStep (x y : α) : Prop := ∃ a, A a ∧ y = P.meet x a

def generatedMeetPredicate (x : α) : Prop :=
  ∃ a, A a ∧ ∃ b, Relation.ReflTransGen (meetGeneratorStep P A) a b ∧ P.le b x

theorem meetGeneratorPath_left {x y : α}
    (path : Relation.ReflTransGen (meetGeneratorStep P A) x y) (z : α) :
    Relation.ReflTransGen (meetGeneratorStep P A) (P.meet z x) (P.meet z y) := by
  apply path.lift (P.meet z)
  intro x y step
  obtain ⟨a, ha, rfl⟩ := step
  exact ⟨a, ha, (P.meet_assoc z x a).symm⟩

theorem generatedMeetPredicate_contains {x : α} (hx : A x) : generatedMeetPredicate P A x :=
  ⟨x, hx, x, .refl, P.refl x⟩

def generatedMeetFilter (nonempty : ∃ a, A a) : Compression.MeetFilter P where
  mem := generatedMeetPredicate P A
  nonempty := by
    obtain ⟨a, ha⟩ := nonempty
    exact ⟨a, generatedMeetPredicate_contains P A ha⟩
  upward := by
    rintro x y ⟨a, ha, b, path, lower⟩ xy
    exact ⟨a, ha, b, path, P.trans lower xy⟩
  closed_meet := by
    rintro x y ⟨a, ha, b, first, bx⟩ ⟨c, hc, d, second, dy⟩
    refine ⟨a, ha, P.meet b d, ?_, ?_⟩
    · exact (first.tail ⟨c, hc, rfl⟩).trans (meetGeneratorPath_left P A second b)
    · exact P.le_meet (P.trans (P.meet_le_left b d) bx) (P.trans (P.meet_le_right b d) dy)

end PartitionPilot

end

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

open SetFormula
universe u
variable (M : TransitiveGround.{u})

noncomputable def groundMeetFilters (P r μ : ZFSet.{u}) : ZFSet.{u} :=
  ZFSet.sep (MeetFilterCode P r μ) (M.groundPower P)

end TransitiveGround

universe u

noncomputable def testedMeetFilter (F r e : ZFSet.{u}) : ZFSet.{u} :=
  relationImage {e} F r

end PartitionPilot.Forcing

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Forcing_PresentedMeetActionCodes
attribute [-instance] _root_.OAI.PartitionPilot.Forcing.GroundMainPrefix.withTopSmall
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PartitionPilot.SetRealization.Presentation
open Forcing Compression.RecursiveMaps.CosetGeometry
universe u
variable {A : Type u} (s : Presentation A) (P : MeetOrder A) {r : ZFSet.{u}}
variable (shape : r ⊆ ZFSet.prod s.carrier s.carrier)
variable (related : ∀ x y, ZFSet.pair (s.encode x) (s.encode y) ∈ r ↔ P.le x y)

include shape related in
theorem partialOrderCode : PartialOrderCode s.carrier r := by
  refine ⟨shape, ?_, ?_, ?_⟩
  · intro x hx
    obtain ⟨x, rfl⟩ := (s.mem_carrier x).1 hx
    exact (related x x).2 (P.refl x)
  · intro x hx y hy xy yx
    obtain ⟨x, rfl⟩ := (s.mem_carrier x).1 hx
    obtain ⟨y, rfl⟩ := (s.mem_carrier y).1 hy
    exact congrArg s.encode (P.antisymm ((related x y).1 xy) ((related y x).1 yx))
  · intro x hx y hy z hz xy yz
    obtain ⟨x, rfl⟩ := (s.mem_carrier x).1 hx
    obtain ⟨y, rfl⟩ := (s.mem_carrier y).1 hy
    obtain ⟨z, rfl⟩ := (s.mem_carrier z).1 hz
    exact (related x z).2 (P.trans ((related x y).1 xy) ((related y z).1 yz))

include shape related in
theorem canonicalMeetOrderCode : MeetOrderCode s.carrier r (canonicalMeetGraph s.carrier r) := by
  apply canonicalMeetGraph_code (s.partialOrderCode P shape related)
  intro x hx y hy
  obtain ⟨x, rfl⟩ := (s.mem_carrier x).1 hx
  obtain ⟨y, rfl⟩ := (s.mem_carrier y).1 hy
  refine ⟨s.encode (P.meet x y), s.encode_mem _, (related _ _).2 (P.meet_le_left x y),
    (related _ _).2 (P.meet_le_right x y), ?_⟩
  intro w hw wx wy
  obtain ⟨w, rfl⟩ := (s.mem_carrier w).1 hw
  exact (related _ _).2 (P.le_meet ((related _ _).1 wx) ((related _ _).1 wy))

include related in
theorem canonicalMeetGraph_iff (x y z : A) :
    ZFSet.pair (ZFSet.pair (s.encode x) (s.encode y)) (s.encode z) ∈
      canonicalMeetGraph s.carrier r ↔ P.meet x y = z := by
  rw [pair_mem_canonicalMeetGraph]
  constructor
  · rintro ⟨_, _, _, left, right, greatest⟩
    apply P.antisymm
    · exact (related _ _).1 (greatest (s.encode (P.meet x y)) (s.encode_mem _)
        ((related _ _).2 (P.meet_le_left x y)) ((related _ _).2 (P.meet_le_right x y)))
    · exact P.le_meet ((related _ _).1 left) ((related _ _).1 right)
  · rintro rfl
    refine ⟨s.encode_mem _, s.encode_mem _, s.encode_mem _,
      (related _ _).2 (P.meet_le_left x y), (related _ _).2 (P.meet_le_right x y), ?_⟩
    intro w hw wx wy
    obtain ⟨w, rfl⟩ := (s.mem_carrier w).1 hw
    exact (related _ _).2 (P.le_meet ((related _ _).1 wx) ((related _ _).1 wy))

variable {G : Type u} [Group G] (t : Presentation G) (a : OrderAction G P)
include related in
theorem posetActionCode : PosetActionCode t.carrier s.carrier
    ((t.product t).graph t (fun gh => gh.1 * gh.2)) (t.encode 1) r
    ((t.product s).graph s (fun gx => (a.iso gx.1).toFun gx.2)) := by
  refine ⟨(t.product s).graph_isFunc s _, ?_, ?_, ?_⟩
  · intro x hx
    obtain ⟨x, rfl⟩ := (s.mem_carrier x).1 hx
    exact ((t.product s).pair_mem_graph s _ (1, x) x).2 (a.one x)
  · intro g hg h hh k hk x hx y hy z hz gh xy yz
    obtain ⟨g, rfl⟩ := (t.mem_carrier g).1 hg
    obtain ⟨h, rfl⟩ := (t.mem_carrier h).1 hh
    obtain ⟨k, rfl⟩ := (t.mem_carrier k).1 hk
    obtain ⟨x, rfl⟩ := (s.mem_carrier x).1 hx
    obtain ⟨y, rfl⟩ := (s.mem_carrier y).1 hy
    obtain ⟨z, rfl⟩ := (s.mem_carrier z).1 hz
    have product := ((t.product t).pair_mem_graph t _ (g, h) k).1 gh
    have first := ((t.product s).pair_mem_graph s _ (h, x) y).1 xy
    have second := ((t.product s).pair_mem_graph s _ (g, y) z).1 yz
    apply ((t.product s).pair_mem_graph s _ (k, x) z).2
    rw [← product, a.mul, first, second]
  · intro g hg x hx y hy z hz w hw xz yw xy
    obtain ⟨g, rfl⟩ := (t.mem_carrier g).1 hg
    obtain ⟨x, rfl⟩ := (s.mem_carrier x).1 hx
    obtain ⟨y, rfl⟩ := (s.mem_carrier y).1 hy
    obtain ⟨z, rfl⟩ := (s.mem_carrier z).1 hz
    obtain ⟨w, rfl⟩ := (s.mem_carrier w).1 hw
    have first := ((t.product s).pair_mem_graph s _ (g, x) z).1 xz
    have second := ((t.product s).pair_mem_graph s _ (g, y) w).1 yw
    apply (related z w).2
    rw [← first, ← second]
    exact ((a.iso g).le_iff x y).2 ((related x y).1 xy)

end PartitionPilot.SetRealization.Presentation

end

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Definability_FlatCopyGraphRealization
attribute [-instance] _root_.OAI.PartitionPilot.Forcing.GroundMainPrefix.withTopSmall
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PartitionPilot.Forcing
open SetRealization Compression.RecursiveMaps Attachment CosetGeometry
universe u
variable {A J R : Type u} [Group J] {P : MeetOrder A}
variable (f : TileRequests.Family P R) (a : OrderAction J P)
variable (s : Presentation (External J f.Letters)) (t : Presentation A) (q : Presentation (f.Node a))
variable {classifier r : ZFSet.{u}}
variable (classed : ∀ w x z, ZFSet.pair (ZFSet.pair (s.encode w) (t.encode x)) (q.encode z) ∈ classifier ↔
  (f.copy a w).toFun x = z)
variable (related : ∀ x y, ZFSet.pair (t.encode x) (t.encode y) ∈ r ↔ P.le x y)

include classed related in
theorem flatCopy_order_iff (x y : f.Node a) :
    ZFSet.pair (q.encode x) (q.encode y) ∈
      flatCopyOrderGraph s.carrier t.carrier q.carrier classifier r ↔ (f.gluedOrder a).le x y := by
  rw [pair_mem_flatCopyOrderGraph]
  constructor
  · rintro ⟨_, _, w, hw, b, hb, c, hc, bc, bx, cy⟩
    obtain ⟨w, rfl⟩ := (s.mem_carrier w).1 hw
    obtain ⟨b, rfl⟩ := (t.mem_carrier b).1 hb
    obtain ⟨c, rfl⟩ := (t.mem_carrier c).1 hc
    rw [← (classed w b x).1 bx, ← (classed w c y).1 cy]
    exact ((f.copy a w).le_iff b c).2 ((related b c).1 bc)
  · intro xy
    obtain ⟨w, b, c, bx, cy, bc⟩ := f.comparison_in_copy a x y xy
    exact ⟨q.encode_mem x, q.encode_mem y, s.encode w, s.encode_mem w,
      t.encode b, t.encode_mem b, t.encode c, t.encode_mem c,
      (related b c).2 bc, (classed w b x).2 bx, (classed w c y).2 cy⟩

include classed in
theorem flatCopy_action_iff (g : External J f.Letters) (x y : f.Node a) :
    ZFSet.pair (ZFSet.pair (s.encode g) (q.encode x)) (q.encode y) ∈
      flatCopyActionGraph s.carrier t.carrier q.carrier classifier
        ((s.product s).graph s (fun gh => gh.1 * gh.2)) ↔ f.translate a g x = y := by
  rw [pair_mem_flatCopyActionGraph]
  constructor
  · rintro ⟨_, _, _, w, hw, v, hv, b, hb, gw, wx, vy⟩
    obtain ⟨w, rfl⟩ := (s.mem_carrier w).1 hw
    obtain ⟨v, rfl⟩ := (s.mem_carrier v).1 hv
    obtain ⟨b, rfl⟩ := (t.mem_carrier b).1 hb
    have product := ((s.product s).pair_mem_graph s _ (g, w) v).1 gw
    rw [← (classed w b x).1 wx, f.translate_copy, product]
    exact (classed v b y).1 vy
  · intro xy
    obtain ⟨w, b, rfl⟩ := f.copy_cover a x
    refine ⟨s.encode_mem g, q.encode_mem _, q.encode_mem y, s.encode w, s.encode_mem w,
      s.encode (g * w), s.encode_mem _, t.encode b, t.encode_mem b,
      ((s.product s).pair_mem_graph s _ (g, w) (g * w)).2 rfl, (classed w b _).2 rfl, ?_⟩
    exact (classed (g * w) b y).2 ((f.translate_copy a g w b).symm.trans xy)

include classed in
theorem flatCopy_action_eq_graph :
    flatCopyActionGraph s.carrier t.carrier q.carrier classifier
      ((s.product s).graph s (fun gh => gh.1 * gh.2)) =
      (s.product q).graph q (fun gx => f.translate a gx.1 gx.2) := by
  apply ZFSet.ext
  intro z
  constructor
  · intro hz
    obtain ⟨g, hg, x, hx, y, hy, rfl, _⟩ := (mem_flatCopyActionGraph _ _ _ _ _ z).1 hz
    obtain ⟨g, rfl⟩ := (s.mem_carrier g).1 hg
    obtain ⟨x, rfl⟩ := (q.mem_carrier x).1 hx
    obtain ⟨y, rfl⟩ := (q.mem_carrier y).1 hy
    exact ((s.product q).pair_mem_graph q _ (g, x) y).2
      ((flatCopy_action_iff f a s t q classed g x y).1 hz)
  · intro hz
    obtain ⟨⟨g, x⟩, rfl⟩ := ((s.product q).mem_graph q _ z).1 hz
    exact (flatCopy_action_iff f a s t q classed g x _).2 rfl

include classed related in
theorem flatCopy_meetOrder :
    MeetOrderCode q.carrier (flatCopyOrderGraph s.carrier t.carrier q.carrier classifier r)
      (canonicalMeetGraph q.carrier (flatCopyOrderGraph s.carrier t.carrier q.carrier classifier r)) :=
  q.canonicalMeetOrderCode (f.gluedOrder a) (fun _ hz => (ZFSet.mem_sep.1 hz).1)
    (flatCopy_order_iff f a s t q classed related)

include classed related in
theorem flatCopy_actionCode :
    PosetActionCode s.carrier q.carrier ((s.product s).graph s (fun gh => gh.1 * gh.2)) (s.encode 1)
      (flatCopyOrderGraph s.carrier t.carrier q.carrier classifier r)
      (flatCopyActionGraph s.carrier t.carrier q.carrier classifier
        ((s.product s).graph s (fun gh => gh.1 * gh.2))) := by
  rw [flatCopy_action_eq_graph f a s t q classed]
  exact q.posetActionCode (f.gluedOrder a) (flatCopy_order_iff f a s t q classed related) s (f.externalAction a)

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

section

namespace PartitionPilot.Forcing
universe u

structure IdealEmbeddingCode (P Q rP rQ μP μQ e : ZFSet.{u}) : Prop
    extends MeetEmbeddingCode P Q rP rQ μP μQ e where
  reflect : ∀ x y x' y', ZFSet.pair x x' ∈ e → ZFSet.pair y y' ∈ e →
    ZFSet.pair x' y' ∈ rQ → ZFSet.pair x y ∈ rP
  ideal : ∀ v v' z, ZFSet.pair v v' ∈ e → z ∈ Q → ZFSet.pair z v' ∈ rQ →
    ∃ x ∈ P, ZFSet.pair x v ∈ rP ∧ ZFSet.pair x z ∈ e

namespace IdealEmbeddingCode
variable {P Q rP rQ μP μQ e : ZFSet.{u}}
variable (code : IdealEmbeddingCode P Q rP rQ μP μQ e)
include code

theorem order_iff {x y x' y' : ZFSet.{u}}
    (first : ZFSet.pair x x' ∈ e) (second : ZFSet.pair y y' ∈ e) :
    ZFSet.pair x' y' ∈ rQ ↔ ZFSet.pair x y ∈ rP :=
  ⟨code.reflect x y x' y' first second,
    fun lower => code.monotone x y x' y' lower first second⟩

end IdealEmbeddingCode
end PartitionPilot.Forcing

end

namespace PartitionPilot.Forcing
open SetFormula SetRealization
open Compression.RecursiveMaps Attachment CosetGeometry
universe u

variable {A J R : Type u} [Group J] {P : MeetOrder A}
variable (f : TileRequests.Family P R) (a : OrderAction J P)
variable (s : Presentation (External J f.Letters)) (t : Presentation A) (q : Presentation (f.Node a))
variable {classifier r μ : ZFSet.{u}}
variable (classed : ∀ w x z, ZFSet.pair (ZFSet.pair (s.encode w) (t.encode x)) (q.encode z) ∈ classifier ↔
  (f.copy a w).toFun x = z)

include classed in
theorem flatCopyEmbeddingGraph_eq_graph (w : External J f.Letters) :
    flatCopyEmbeddingGraph t.carrier q.carrier classifier (s.encode w) = t.graph q (f.copy a w).toFun := by
  apply ZFSet.ext
  intro z
  constructor
  · intro entry
    obtain ⟨x, hx, y, hy, rfl⟩ := ZFSet.mem_prod.1 (ZFSet.mem_sep.1 entry).1
    obtain ⟨x, rfl⟩ := (t.mem_carrier x).1 hx
    obtain ⟨y, rfl⟩ := (q.mem_carrier y).1 hy
    exact (t.pair_mem_graph q _ x y).2 ((classed w x y).1
      ((pair_mem_flatCopyEmbeddingGraph _ _ _ _ _ _).1 entry).2.2)
  · intro entry
    obtain ⟨x, equal⟩ := (t.mem_graph q (f.copy a w).toFun z).1 entry
    rw [← equal]
    exact (pair_mem_flatCopyEmbeddingGraph _ _ _ _ _ _).2
      ⟨t.encode_mem _, q.encode_mem _, (classed w x _).2 rfl⟩

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



namespace PartitionPilot.Forcing.IdealEmbeddingCode
universe u
variable {P Q rP rQ μP μQ e G H mG mH oneG oneH A B : ZFSet.{u}}
variable (code : IdealEmbeddingCode P Q rP rQ μP μQ e)
variable (source : PosetActionCode G P mG oneG rP A)
variable (target : PosetActionCode H Q mH oneH rQ B)
include code source target

theorem actionAgreementBelow {g h g' h' v v' : ZFSet.{u}}
    (hg : g ∈ G) (hg' : g' ∈ H) (hh' : h' ∈ H)
    (image : ZFSet.pair v v' ∈ e)
    (agree : ActionAgreementBelow P rP A g h v)
    (firstEquivariant : ∀ x ∈ P, ∀ y ∈ P, ∀ x' y',
      ZFSet.pair x x' ∈ e → ZFSet.pair y y' ∈ e →
      ZFSet.pair (ZFSet.pair g x) y ∈ A → ZFSet.pair (ZFSet.pair g' x') y' ∈ B)
    (secondEquivariant : ∀ x ∈ P, ∀ y ∈ P, ∀ x' y',
      ZFSet.pair x x' ∈ e → ZFSet.pair y y' ∈ e →
      ZFSet.pair (ZFSet.pair h x) y ∈ A → ZFSet.pair (ZFSet.pair h' x') y' ∈ B) :
    ActionAgreementBelow Q rQ B g' h' v' := by
  intro x' hx' z _ lower
  obtain ⟨x, hx, oldLower, xx'⟩ := code.ideal v v' x' image hx' lower
  obtain ⟨y, gy, _⟩ := source.function.2 (ZFSet.pair g x) (ZFSet.pair_mem_prod.2 ⟨hg, hx⟩)
  have hy := (ZFSet.pair_mem_prod.1 (source.function.1 gy)).2
  have hyAct := (agree x hx y hy oldLower).1 gy
  obtain ⟨y', yy', _⟩ := code.injection.function.2 y hy
  have first := firstEquivariant x hx y hy x' y' xx' yy' gy
  have second := secondEquivariant x hx y hy x' y' xx' yy' hyAct
  obtain ⟨a, _, uniqueFirst⟩ := target.function.2 (ZFSet.pair g' x') (ZFSet.pair_mem_prod.2 ⟨hg', hx'⟩)
  obtain ⟨b, _, uniqueSecond⟩ := target.function.2 (ZFSet.pair h' x') (ZFSet.pair_mem_prod.2 ⟨hh', hx'⟩)
  constructor
  · intro entry
    have equal : z = y' := (uniqueFirst z entry).trans (uniqueFirst y' first).symm
    exact equal.symm ▸ second
  · intro entry
    have equal : z = y' := (uniqueSecond z entry).trans (uniqueSecond y' second).symm
    exact equal.symm ▸ first

end PartitionPilot.Forcing.IdealEmbeddingCode



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

namespace SetFormula

def indexedFreshSetFormula {n} (output i qs rs anchors qb rb ab : Fin n) : SetFormula n :=
  exactSetFormula output (BoundedFormula.indexedAttachmentFreshEntryFormula 0 i.succ qs.succ
    rs.succ anchors.succ qb.succ rb.succ ab.succ).toFormula

end SetFormula

namespace TransitiveGround
variable (M : TransitiveGround.{u})
variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
variable (unions : Realize M.sets SetFormula.union Fin.elim0)
variable (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
include pairing unions powers separation

theorem realize_indexedFreshSetFormula {n} (output i qs rs anchors qb rb ab : Fin n)
    (env : Fin n → ZFSet.{u}) (members : ∀ x, env x ∈ M.sets)
    (qBound : env qb = ZFSet.sUnion (ZFSet.sUnion (env qs)))
    (rBound : env rb = ZFSet.sUnion (ZFSet.sUnion (env rs)))
    (aBound : env ab = ZFSet.sUnion (ZFSet.sUnion (env anchors))) :
    Realize M.sets (indexedFreshSetFormula output i qs rs anchors qb rb ab) env ↔
      env output = indexedAttachmentFresh (env i) (env qs) (env rs) (env anchors) := by
  apply M.realize_exactBoundedSetFormula output _ env members
    (M.indexedAttachmentFresh_mem pairing unions powers separation (members i) (members qs)
      (members rs) (members anchors))
  intro z
  rw [BoundedFormula.truth_indexedAttachmentFreshEntryFormula]
  change (∃ j ∈ env i, ∃ Q ∈ env qb, ∃ r ∈ env rb, ∃ a ∈ env ab, ∃ q ∈ Q,
    ZFSet.pair j Q ∈ env qs ∧ ZFSet.pair j r ∈ env rs ∧ ZFSet.pair j a ∈ env anchors ∧
      z = ZFSet.pair j q ∧ ZFSet.pair q a ∉ r) ↔ _
  rw [qBound, rBound, aBound, indexedAttachmentFresh, ZFSet.mem_sep]
  constructor
  · intro witness
    refine ⟨?_, witness⟩
    obtain ⟨j, hj, Q, _, _, _, _, _, q, hq, entry, _, _, equal, _⟩ := witness
    rw [equal]
    exact (pair_mem_indexedAttachmentDomain (env i) (env qs) j q).2 ⟨hj, Q, entry, hq⟩
  · exact And.right

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

noncomputable def definable_sUnion (unions : Realize M.sets SetFormula.union Fin.elim0) :
    GroundDefinableFunction M (fun env : Fin 1 → ZFSet.{u} => ZFSet.sUnion (env 0)) where
  formula := sUnionSetFormula 0 1
  closed := fun _env members => M.union_mem unions (members 0)
  correct := fun env members z hz =>
    M.realize_sUnionSetFormula unions 0 1 (extend z env) (Fin.cases hz members)

variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
variable (unions : Realize M.sets SetFormula.union Fin.elim0)
variable (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
include pairing unions powers separation

noncomputable def definable_taggedExtension : GroundDefinableFunction M
    (fun env : Fin 2 → ZFSet.{u} => taggedExtension (env 0) (env 1)) where
  formula := taggedExtensionSetFormula 0 1 2
  closed := fun _env members => M.taggedExtension_mem pairing unions powers separation (members 0) (members 1)
  correct := fun env members z hz => M.realize_taggedExtensionSetFormula pairing unions powers separation
    0 1 2 (extend z env) (Fin.cases hz members)

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

namespace PartitionPilot.Forcing

universe u

namespace RecursiveStateData

noncomputable def code (state : RecursiveStateData.{u}) : ZFSet.{u} :=
  nonemptyTupleCode 12 state.field

end RecursiveStateData

noncomputable def recursiveStateCode (D rD μD J Qs rs μs As Es Fs Ss Maps A : ZFSet.{u}) : ZFSet.{u} :=
  (RecursiveStateData.mk D rD μD J Qs rs μs As Es Fs Ss Maps A).code

end PartitionPilot.Forcing

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

namespace GroundDefinableFunction

def congr {M : TransitiveGround.{u}} {n : Nat}
    {f g : (Fin n → ZFSet.{u}) → ZFSet.{u}} (definition : GroundDefinableFunction M f)
    (equal : ∀ env, f env = g env) : GroundDefinableFunction M g where
  formula := definition.formula
  closed := fun env members => equal env ▸ definition.closed env members
  correct := by
    intro env members z hz
    rw [definition.correct env members z hz, equal env]

end GroundDefinableFunction

structure GroundSetTerm (M : TransitiveGround.{u}) (n : Nat) where
  eval : (Fin n → ZFSet.{u}) → ZFSet.{u}
  definition : GroundDefinableFunction M eval

namespace GroundSetTerm

def var (M : TransitiveGround.{u}) {n : Nat} (j : Fin n) : GroundSetTerm M n :=
  ⟨fun env => env j, GroundDefinableFunction.projection M j⟩

theorem ground {M : TransitiveGround.{u}} {n : Nat} (term : GroundSetTerm M n)
    (env : Fin n → ZFSet.{u}) (members : ∀ i, env i ∈ M.sets) : term.eval env ∈ M.sets :=
  term.definition.closed env members

theorem correct {M : TransitiveGround.{u}} {n : Nat} (term : GroundSetTerm M n)
    (env : Fin n → ZFSet.{u}) (members : ∀ i, env i ∈ M.sets) (z : ZFSet.{u}) (hz : z ∈ M.sets) :
    Realize M.sets term.definition.formula (extend z env) ↔ z = term.eval env :=
  term.definition.correct env members z hz

end GroundSetTerm

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

def groundMeetFiltersFormula {n} (output P r μ : Fin n) : SetFormula n :=
  exactSetFormula output (BoundedFormula.meetFilterFormula P.succ r.succ μ.succ 0).toFormula

end SetFormula

namespace SetFormula

def groundLiteralTaskFieldFormula {n} (j : Fin 6) (output I P r μ Labels : Fin n) : SetFormula n :=
  ex (ex (.conj (groundRelationsFormula 1 P.succ.succ P.succ.succ)
    (.conj (groundMeetFiltersFormula 0 P.succ.succ r.succ.succ μ.succ.succ)
      (literalTaskFieldSetFormula j output.succ.succ I.succ.succ P.succ.succ 1 0 Labels.succ.succ))))

end SetFormula

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
universe u

structure RecursiveTemplateConstancy (P r μ : ZFSet.{u}) (state : RecursiveStateData.{u}) : Prop where
  spaces : state.Qs = constantFamilyGraph state.J P
  relations : state.rs = constantFamilyGraph state.J r
  meets : state.μs = constantFamilyGraph state.J μ

namespace RecursiveTemplateConstancy
variable {P r μ : ZFSet.{u}} {state : RecursiveStateData.{u}}
variable (constant : RecursiveTemplateConstancy P r μ state)
include constant

theorem space_entry_iff (i Q : ZFSet.{u}) :
    ZFSet.pair i Q ∈ state.Qs ↔ i ∈ state.J ∧ Q = P := by
  rw [constant.spaces, pair_mem_constantFamilyGraph]

theorem relation_entry_iff (i relation : ZFSet.{u}) :
    ZFSet.pair i relation ∈ state.rs ↔ i ∈ state.J ∧ relation = r := by
  rw [constant.relations, pair_mem_constantFamilyGraph]

theorem meet_entry_iff (i operation : ZFSet.{u}) :
    ZFSet.pair i operation ∈ state.μs ↔ i ∈ state.J ∧ operation = μ := by
  rw [constant.meets, pair_mem_constantFamilyGraph]

end RecursiveTemplateConstancy

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

namespace PartitionPilot.Forcing.TransitiveGround
open SetFormula
universe u
variable (M : TransitiveGround.{u})

theorem ownerFresh_mem (separation : SeparationSchema M.sets)
    {P B : ZFSet.{u}} (hP : P ∈ M.sets) (hB : B ∈ M.sets) :
    ownerFresh P B ∈ M.sets := by
  let params := extend P Fin.elim0
  let formula : BoundedFormula 2 := .neg (.mem 0 1)
  exact M.bounded_separation_mem separation formula params
    (Fin.cases hP (fun j => Fin.elim0 j)) hB

end PartitionPilot.Forcing.TransitiveGround

namespace PartitionPilot.Forcing
universe u

theorem ownerBirthGraph_fresh_nat_iff {P B T T0 old levels stamps x t : ZFSet.{u}}
    (oldFunction : ZFSet.IsFunc P T0 old) (hx : x ∉ P) :
    ZFSet.pair x t ∈ ownerBirthGraph P B T old levels stamps ↔
      x ∈ B ∧ t ∈ T ∧ ∃ n : Nat,
        ZFSet.pair x (natSetCode n) ∈ levels ∧ ZFSet.pair (natSetCode n) t ∈ stamps := by
  rw [ownerBirthGraph_fresh_iff oldFunction hx]
  apply and_congr_right
  intro _
  apply and_congr_right
  intro _
  constructor
  · rintro ⟨i, hi, level, stamp⟩
    obtain ⟨n, rfl⟩ := (mem_omega_iff_natSetCode i).1 hi
    exact ⟨n, level, stamp⟩
  · rintro ⟨n, level, stamp⟩
    exact ⟨natSetCode n, (mem_omega_iff_natSetCode _).2 ⟨n, rfl⟩, level, stamp⟩

end PartitionPilot.Forcing

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Definability_GroundMainTransitionCodes
attribute [-instance] _root_.OAI.PartitionPilot.Forcing.GroundMainPrefix.withTopSmall
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PartitionPilot.Forcing
universe u

structure GroundMainTransition {M : TransitiveGround.{u}} {C D rD : ZFSet.{u}}
    (source target : GroundMainStage M C D rD) where
  points : ZFSet.{u}
  actors : ZFSet.{u}
  points_ground : points ∈ M.sets
  actors_ground : actors ∈ M.sets
  point_embedding : MeetEmbeddingCode source.carrier target.carrier source.order target.order
    source.meetGraph target.meetGraph points
  order_iff : ∀ x y x' y', ZFSet.pair x x' ∈ points → ZFSet.pair y y' ∈ points →
    (ZFSet.pair x' y' ∈ target.order ↔ ZFSet.pair x y ∈ source.order)
  group_embedding : GroupEmbeddingCode source.actors target.actors source.multiplication target.multiplication
    source.identity target.identity actors
  equivariant : ∀ g g' x y x' y', ZFSet.pair g g' ∈ actors →
    ZFSet.pair x x' ∈ points → ZFSet.pair y y' ∈ points →
    ZFSet.pair (ZFSet.pair g x) y ∈ source.action → ZFSet.pair (ZFSet.pair g' x') y' ∈ target.action
  bottom : ZFSet.pair source.bottom target.bottom ∈ points
  height : ∀ x y z, ZFSet.pair x y ∈ points →
    (ZFSet.pair y z ∈ target.height ↔ ZFSet.pair x z ∈ source.height)
  agreement : ∀ g h g' h' v v', ZFSet.pair g g' ∈ actors → ZFSet.pair h h' ∈ actors →
    ZFSet.pair v v' ∈ points → ActionAgreementBelow source.carrier source.order source.action g h v →
      ActionAgreementBelow target.carrier target.order target.action g' h' v'

end PartitionPilot.Forcing

end

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

def RectangleIdealCode (Q H R B e a c b g h k l : ZFSet.{u}) : Prop :=
  (∀ c' ∈ Q, ∀ g' ∈ H, ∀ h' ∈ H,
    ZFSet.pair c c' ∈ e → ZFSet.pair g g' ∈ a → ZFSet.pair h h' ∈ a →
      ActionAgreementBelow Q R B k g' c' ∧ ActionAgreementBelow Q R B l h' c') ∧
  ∀ b' ∈ Q, ZFSet.pair b b' ∈ e → ActionAgreementBelow Q R B k l b'

def RectangleActorPairCode (P μ A Q H R ν B e a c b d g h k l : ZFSet.{u}) : Prop :=
  RectangleIdealCode Q H R B e a c b g h k l ∧
  RectangleRootMeetCode P μ A Q ν B e c d g k ∧
  RectangleRootMeetCode P μ A Q ν B e c d h l ∧
  RectangleCrossMeetCode Q ν B e b d k l

end PartitionPilot.Forcing



namespace PartitionPilot.Forcing
universe u

structure RectangleAtBoundCode (P r μ A c b d g h X k l : ZFSet.{u}) : Prop where
  first_agreement : ActionAgreementBelow P r A k g c
  second_agreement : ActionAgreementBelow P r A l h c
  common_agreement : ActionAgreementBelow P r A k l b
  values : ∃ v ∈ P, ∃ w ∈ P, ∃ y ∈ P, ∃ z ∈ P, ∃ t ∈ P,
    ZFSet.pair (ZFSet.pair g c) v ∈ A ∧ ZFSet.pair (ZFSet.pair h c) w ∈ A ∧
    ZFSet.pair (ZFSet.pair k d) y ∈ A ∧ ZFSet.pair (ZFSet.pair l d) z ∈ A ∧
    ZFSet.pair (ZFSet.pair k b) t ∈ A ∧ ZFSet.pair (ZFSet.pair l b) t ∈ A ∧
    ZFSet.pair (ZFSet.pair y X) v ∈ μ ∧ ZFSet.pair (ZFSet.pair z X) w ∈ μ ∧
    ZFSet.pair (ZFSet.pair y z) t ∈ μ

end PartitionPilot.Forcing



end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Definability_HistoryFieldFormulas
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

def stateFieldFormula {n} (code value : Fin n) (j : Fin 13) : SetFormula n :=
  exBlock 13 (.conj
    (BoundedFormula.nonemptyTupleFormula 12 (suffixIndex n 13 code) (prefixIndex n 13)).toFormula
    (.equal (suffixIndex n 13 value) (prefixIndex n 13 j)))

def historyFieldValueFormula {n} (index value history : Fin n) (j : Fin 13) : SetFormula n :=
  ex (.conj (BoundedFormula.pairMembershipFormula index.succ 0 history.succ).toFormula
    (stateFieldFormula 0 value.succ j))

def historyFieldPairFormula {n} (index output history : Fin n) (j : Fin 13) : SetFormula n :=
  ex (.conj (historyFieldValueFormula index.succ 0 history.succ j)
    (BoundedFormula.orderedPairFormula output.succ index.succ 0).toFormula)

end SetFormula

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

theorem fixedTopBirth_function {P T birth s : ZFSet.{u}}
    (born : ZFSet.IsFunc P T birth) (hs : s ∈ T) :
    ZFSet.IsFunc (fixedTopCarrier P) T (fixedTopBirth P birth s) := by
  refine ⟨?_, ?_⟩
  · intro z hz
    rcases ZFSet.mem_insert_iff.1 hz with rfl | old
    · exact ZFSet.pair_mem_prod.2 ⟨fixedTopCarrier_top P, hs⟩
    · obtain ⟨x, hx, t, ht, rfl⟩ := ZFSet.mem_prod.1 (born.1 old)
      exact ZFSet.pair_mem_prod.2 ⟨fixedTopCarrier_old hx, ht⟩
  · intro x hx
    rcases (mem_fixedTopCarrier P x).1 hx with rfl | old
    · exact ⟨s, (fixedTopBirth_top_iff born).2 rfl, fun t entry => (fixedTopBirth_top_iff born).1 entry⟩
    · obtain ⟨t, entry, unique⟩ := born.2 x old
      exact ⟨t, (fixedTopBirth_old_iff old).2 entry,
        fun t' entry' => unique t' ((fixedTopBirth_old_iff old).1 entry')⟩

end

namespace TransitiveGround

open SetFormula
universe u
variable (M : TransitiveGround.{u})

theorem fixedTopBirth_mem
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    {P birth s : ZFSet.{u}} (hP : P ∈ M.sets) (hBirth : birth ∈ M.sets) (hs : s ∈ M.sets) :
    fixedTopBirth P birth s ∈ M.sets :=
  M.insert_mem pairing unions (M.orderedPair_mem pairing hP hs) hBirth

theorem fixedTopBirth_singleton_small
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    {P : ZFSet.{u}} (hP : P ∈ M.sets) :
    ({P} : ZFSet.{u}) ∈ M.sets ∧ M.groundEmbeddable {P} ZFSet.omega := by
  have hSingle : ({P} : ZFSet.{u}) ∈ M.sets := by
    simpa only [ZFSet.pair_eq_singleton] using M.unorderedPair_mem pairing hP hP
  have hEntry := M.orderedPair_mem pairing hP (M.empty_mem ⟨P, hP⟩)
  have hGraph : ({ZFSet.pair P ∅} : ZFSet.{u}) ∈ M.sets := by
    simpa only [ZFSet.pair_eq_singleton] using M.unorderedPair_mem pairing hEntry hEntry
  exact ⟨hSingle, {ZFSet.pair P ∅}, hGraph, fixedTopBirth_singleton_injection P⟩

end TransitiveGround

open SetRealization SetFormula
universe u

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

open SetFormula
universe u

namespace TransitiveGround
variable (M : TransitiveGround.{u})
variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
variable (unions : Realize M.sets SetFormula.union Fin.elim0)
variable (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)

include pairing unions in
theorem dartIncidenceGraph_mem {source target : ZFSet.{u}}
    (hs : source ∈ M.sets) (ht : target ∈ M.sets) : dartIncidenceGraph source target ∈ M.sets :=
  M.binary_union_mem pairing unions hs ht

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

namespace StrictLexHeightCode

noncomputable def value {L C D r h rD : ZFSet.{u}}
    (code : StrictLexHeightCode L C D r h rD) (x : {a : ZFSet.{u} // a ∈ L}) :
    {y : ZFSet.{u} // y ∈ ZFSet.prod C D} :=
  let function : FunctionGraphOn L h := ⟨ZFSet.prod C D, code.function⟩
  ⟨function.value x, (ZFSet.pair_mem_prod.1 (code.function.1 (function.value_entry x))).2⟩

theorem value_entry {L C D r h rD : ZFSet.{u}}
    (code : StrictLexHeightCode L C D r h rD) (x : {a : ZFSet.{u} // a ∈ L}) :
    ZFSet.pair x.val (code.value x).val ∈ h :=
  (show FunctionGraphOn L h from ⟨ZFSet.prod C D, code.function⟩).value_entry x

theorem value_eq_of_entry {L C D r h rD y : ZFSet.{u}}
    (code : StrictLexHeightCode L C D r h rD) (x : {a : ZFSet.{u} // a ∈ L})
    (entry : ZFSet.pair x.val y ∈ h) : (code.value x).val = y :=
  (show FunctionGraphOn L h from ⟨ZFSet.prod C D, code.function⟩).value_eq_of_entry x entry

end StrictLexHeightCode

noncomputable def batchFreshHeightGraph (I Qs rs As Vs Hs Cs E C D : ZFSet.{u}) : ZFSet.{u} :=
  ZFSet.sep (fun z => z ∈ ZFSet.prod (indexedAttachmentFresh I Qs rs As) (ZFSet.prod C D))
    (componentHeightGraph I Qs (familyPointBound Vs) Hs Cs E C D)

noncomputable def batchHeightGraph (P I Qs rs As Vs Hs Cs E C D old : ZFSet.{u}) : ZFSet.{u} :=
  taggedHeightGraph P (indexedAttachmentFresh I Qs rs As) (ZFSet.prod C D) old
    (batchFreshHeightGraph I Qs rs As Vs Hs Cs E C D)

namespace TemplateHeightFamilyInputs

variable {P rP μP I Qs rs μs As Es Fs Ss Vs vrs Hs C D rD old Cs los his E : ZFSet.{u}}
  {d : AttachmentBatchInputs P rP μP I Qs rs μs As Es Fs Ss}
  (t : TemplateHeightFamilyInputs d Vs vrs Hs)
  (e : BatchHeightEndpointCode d C D old rD Cs los his)
  (embeddings : FunctionGraphOn I E)
  (maps : ∀ i, IntervalEmbeddingCode (t.ranges.value i) D (t.orders.value i) rD
    (e.low i) (e.high i) (embeddings.value i))

include t e embeddings maps

theorem batch_component_function :
    ZFSet.IsFunc (indexedAttachmentDomain I Qs) (ZFSet.prod C D)
      (componentHeightGraph I Qs (familyPointBound Vs) Hs Cs E C D) :=
  t.componentHeightGraph_function e.columns embeddings (fun i => (maps i).injection.function)
    (fun i _ member => mem_familyPointBound_of_entry (t.ranges.value_entry i) member)

noncomputable def componentValue (i : {i : ZFSet.{u} // i ∈ I})
    (q : d.templates.Space i) : {h : ZFSet.{u} // h ∈ ZFSet.prod C D} :=
  let function : FunctionGraphOn (indexedAttachmentDomain I Qs)
      (componentHeightGraph I Qs (familyPointBound Vs) Hs Cs E C D) :=
    ⟨ZFSet.prod C D, t.batch_component_function e embeddings maps⟩
  let point : {x : ZFSet.{u} // x ∈ indexedAttachmentDomain I Qs} :=
    ⟨ZFSet.pair i.val q.val, (pair_mem_indexedAttachmentDomain I Qs i.val q.val).2
      ⟨i.property, d.space i, d.space_entry i, q.property⟩⟩
  ⟨function.value point, (ZFSet.pair_mem_prod.1
    ((t.batch_component_function e embeddings maps).1 (function.value_entry point))).2⟩

theorem componentValue_entry (i : {i : ZFSet.{u} // i ∈ I}) (q : d.templates.Space i) :
    ZFSet.pair (ZFSet.pair i.val q.val) (t.componentValue e embeddings maps i q).val ∈
      componentHeightGraph I Qs (familyPointBound Vs) Hs Cs E C D :=
  (show FunctionGraphOn (indexedAttachmentDomain I Qs)
      (componentHeightGraph I Qs (familyPointBound Vs) Hs Cs E C D) from
    ⟨ZFSet.prod C D, t.batch_component_function e embeddings maps⟩).value_entry _

theorem componentValue_spec (i : {i : ZFSet.{u} // i ∈ I}) (q : d.templates.Space i) :
    ∃ c ∈ C, ∃ z ∈ D, (t.componentValue e embeddings maps i q).val = ZFSet.pair c z ∧
      ZFSet.pair i.val c ∈ Cs ∧ ∃ a ∈ t.ranges.value i,
        ZFSet.pair q.val a ∈ t.heights.value i ∧ ZFSet.pair a z ∈ embeddings.value i := by
  obtain ⟨c, hc, z, hz, equal⟩ := ZFSet.mem_prod.1 (t.componentValue e embeddings maps i q).property
  have entry := equal ▸ t.componentValue_entry e embeddings maps i q
  obtain ⟨_, _, _, column, a, _, height, image⟩ := (t.componentHeightGraph_entry_iff embeddings i q.val c z).1 entry
  exact ⟨c, hc, z, hz, equal, column, a,
    (ZFSet.pair_mem_prod.1 ((t.function i).1 height)).2, height, image⟩

end TemplateHeightFamilyInputs

end PartitionPilot.Forcing



end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Geometry_GroundFixedTopOrders
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

theorem fixedTopCarrier_mem
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    {P : ZFSet.{u}} (hP : P ∈ M.sets) : fixedTopCarrier P ∈ M.sets :=
  M.insert_mem pairing unions hP hP

theorem fixedTopOrder_mem
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    {P r : ZFSet.{u}} (hP : P ∈ M.sets) (hr : r ∈ M.sets) : fixedTopOrder P r ∈ M.sets := by
  have singleton : ({P} : ZFSet.{u}) ∈ M.sets := by
    simpa only [ZFSet.pair_eq_singleton] using M.unorderedPair_mem pairing hP hP
  exact M.binary_union_mem pairing unions hr (M.prod_mem pairing unions powers separation
    (M.fixedTopCarrier_mem pairing unions hP) singleton)

end PartitionPilot.Forcing.TransitiveGround

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

structure GroundChronologyFields (M : TransitiveGround.{u}) (T : ZFSet.{u}) where
  time_ground : T ∈ M.sets
  bound : ZFSet.{u}
  bound_ground : bound ∈ M.sets
  graph : Fin 5 → ZFSet.{u}
  graph_ground : ∀ j, graph j ∈ M.sets
  function : ∀ j, ZFSet.IsFunc T bound (graph j)

namespace GroundChronologyFields
variable {M : TransitiveGround.{u}} {T : ZFSet.{u}}
variable (fields : GroundChronologyFields M T)

theorem graphFunction (j : Fin 5) : FunctionGraphOn T (fields.graph j) :=
  ⟨fields.bound, fields.function j⟩

noncomputable def codeFields : Fin 7 → ZFSet.{u} :=
  Fin.cases T (Fin.cases fields.bound fields.graph)

noncomputable def code : ZFSet.{u} := nonemptyTupleCode 6 fields.codeFields

theorem code_ground (pairing : Realize M.sets SetFormula.pairing Fin.elim0) :
    fields.code ∈ M.sets :=
  M.nonemptyTupleCode_mem pairing 6 fields.codeFields
    (Fin.cases fields.time_ground (Fin.cases fields.bound_ground fields.graph_ground))

end GroundChronologyFields

namespace GroundChronologyFields
variable {M : TransitiveGround.{u}} {T : ZFSet.{u}}

noncomputable def ofGraphs
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (hT : T ∈ M.sets) (graphs : Fin 5 → ZFSet.{u})
    (ground : ∀ j, graphs j ∈ M.sets) (functions : ∀ j, FunctionGraphOn T (graphs j)) :
    GroundChronologyFields M T := by
  let all := graphs 0 ∪ (graphs 1 ∪ (graphs 2 ∪ (graphs 3 ∪ graphs 4)))
  have subset (j : Fin 5) : graphs j ⊆ all := by
    refine Fin.cases (fun _ hz => ZFSet.mem_union.2 (Or.inl hz)) ?_ j
    intro j
    refine Fin.cases (fun _ hz => ZFSet.mem_union.2 (Or.inr (ZFSet.mem_union.2 (Or.inl hz)))) ?_ j
    intro j
    refine Fin.cases (fun _ hz => ZFSet.mem_union.2 (Or.inr (ZFSet.mem_union.2 (Or.inr (ZFSet.mem_union.2 (Or.inl hz)))))) ?_ j
    intro j
    refine Fin.cases (fun _ hz => ZFSet.mem_union.2 (Or.inr (ZFSet.mem_union.2 (Or.inr (ZFSet.mem_union.2 (Or.inr (ZFSet.mem_union.2 (Or.inl hz)))))))) ?_ j
    intro j
    have equal : j = 0 := Fin.eq_zero j
    subst j
    exact fun _ hz => ZFSet.mem_union.2 (Or.inr (ZFSet.mem_union.2 (Or.inr (ZFSet.mem_union.2 (Or.inr (ZFSet.mem_union.2 (Or.inr hz)))))))
  refine ⟨hT, ZFSet.sUnion (ZFSet.sUnion all), M.union_mem unions (M.union_mem unions
    (M.binary_union_mem pairing unions (ground 0) (M.binary_union_mem pairing unions (ground 1)
      (M.binary_union_mem pairing unions (ground 2) (M.binary_union_mem pairing unions (ground 3) (ground 4)))))),
    graphs,ground,?_⟩
  intro j
  exact ⟨fun z hz => by
    obtain ⟨x,hx,y,_,rfl⟩ := ZFSet.mem_prod.1 ((functions j).to_isFunc.1 hz)
    exact ZFSet.pair_mem_prod.2 ⟨hx,pair_second_mem_doubleUnion (subset j hz)⟩,
    (functions j).to_isFunc.2⟩

end GroundChronologyFields

end PartitionPilot.Forcing

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





structure GroundChronologicalHistory (M : TransitiveGround.{u}) (T C Q qlt : ZFSet.{u}) where
  space : ZFSet.{u} → ZFSet.{u}
  order : ZFSet.{u} → ZFSet.{u}
  meetGraph : ZFSet.{u} → ZFSet.{u}
  birth : ZFSet.{u} → ZFSet.{u}
  height : ZFSet.{u} → ZFSet.{u}
  space_mem : ∀ s ∈ T, space s ∈ M.sets
  order_mem : ∀ s ∈ T, order s ∈ M.sets
  meet_mem : ∀ s ∈ T, meetGraph s ∈ M.sets
  birth_mem : ∀ s ∈ T, birth s ∈ M.sets
  height_mem : ∀ s ∈ T, height s ∈ M.sets
  meet_order : ∀ s ∈ T, MeetOrderCode (space s) (order s) (meetGraph s)
  birth_function : ∀ s ∈ T, ZFSet.IsFunc (space s) T (birth s)
  birth_bound : ∀ s ∈ T, ∀ x ∈ space s, ∀ t,
    ZFSet.pair x t ∈ birth s → t = s ∨ t ∈ s
  old_meet : ∀ s ∈ T, OldMeetCode (order s) (meetGraph s) (birth s)
  strict_height : ∀ s ∈ T, StrictLexHeightCode (space s) C Q (order s) (height s) qlt
  layer : ∀ cutoff ∈ T, ∀ t ∈ T, t = cutoff ∨ t ∈ cutoff →
    CodedGrowthLayer M space order meetGraph (space cutoff) (order cutoff)
      (meetGraph cutoff) (birth cutoff) t

end PartitionPilot.Forcing



end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Transfinite_GroundChronologyFieldAppend
attribute [-instance] _root_.OAI.PartitionPilot.Forcing.GroundMainPrefix.withTopSmall
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI



namespace PartitionPilot.Forcing
open SetFormula
universe u

theorem appendHistoryValue_old {time t : ZFSet.{u}} (member : t ∈ time)
    (previous : ZFSet.{u} → ZFSet.{u}) (latest : ZFSet.{u}) :
    appendHistoryValue time previous latest t = previous t := by
  apply ite_eq_right
  intro equal
  exact ZFSet.mem_irrefl time (equal ▸ member)

end PartitionPilot.Forcing



end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Transfinite_GroundCompressionBirths
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

namespace TransitiveGround
variable (M : TransitiveGround.{u})

noncomputable def birthRestrictionFamily (U T Ps birth : ZFSet.{u}) : ZFSet.{u} :=
  ZFSet.sep (fun z => ∃ n ∈ ZFSet.omega, ∃ P ∈ ⋃₀ ⋃₀ Ps,
    ∃ b ∈ M.groundRelations U T,
      z = ZFSet.pair n b ∧ ZFSet.pair n P ∈ Ps ∧ b = graphRestriction P birth)
    (ZFSet.prod ZFSet.omega (M.groundRelations U T))

end TransitiveGround
end PartitionPilot.Forcing



end

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

noncomputable def heightCandidateStates
    (B Ps Rs C D rD original K : ZFSet.{u}) : ZFSet.{u} :=
  ZFSet.sep (fun z => ∃ n ∈ ZFSet.omega, ∃ h ∈ B,
    ∃ P ∈ Ps.sUnion.sUnion, ∃ r ∈ Rs.sUnion.sUnion,
      z = ZFSet.pair n h ∧ ZFSet.pair n P ∈ Ps ∧ ZFSet.pair n r ∈ Rs ∧
      StrictLexHeightCode P C D r h rD ∧ original ⊆ h ∧
      ∀ x c q, ZFSet.pair x (ZFSet.pair c q) ∈ h → c ∈ K)
    (ZFSet.prod ZFSet.omega B)

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
open SetRealization Compression.RecursiveMaps.CosetGeometry
universe u
variable {J S : Type u} [Group J]
variable (s : Presentation (External J S)) (g : Presentation J)
variable {inclusion multiplication : ZFSet.{u}}
variable (oldEntries : ∀ j k, ZFSet.pair (g.encode j) (s.encode k) ∈ inclusion ↔ old J S j = k)
variable (mulEntries : ∀ w k v,
  ZFSet.pair (ZFSet.pair (s.encode w) (s.encode k)) (s.encode v) ∈ multiplication ↔ w * k = v)

include oldEntries mulEntries in
theorem externalCosetRelation_iff (w v : External J S) :
    ZFSet.pair (s.encode w) (s.encode v) ∈ externalCosetRelation s.carrier g.carrier inclusion multiplication ↔
      point J S w = point J S v := by
  rw [pair_mem_externalCosetRelation, point_eq]
  constructor
  · rintro ⟨_, _, j, hj, k, hk, oldEntry, mulEntry⟩
    obtain ⟨j, rfl⟩ := (g.mem_carrier j).1 hj
    obtain ⟨k, rfl⟩ := (s.mem_carrier k).1 hk
    exact ⟨j, (oldEntries j k).1 oldEntry ▸ (mulEntries w k v).1 mulEntry⟩
  · rintro ⟨j, equal⟩
    exact ⟨s.encode_mem w, s.encode_mem v, g.encode j, g.encode_mem j,
      s.encode (old J S j), s.encode_mem _, (oldEntries j _).2 rfl,
      (mulEntries w _ v).2 equal⟩

include oldEntries mulEntries in
theorem externalCosetRelation_equivalence :
    EquivalenceRelationCode s.carrier (externalCosetRelation s.carrier g.carrier inclusion multiplication) := by
  have entries := externalCosetRelation_iff s g oldEntries mulEntries
  refine ⟨externalCosetRelation_subset _ _ _ _, ?_, ?_, ?_⟩
  · intro w hw
    obtain ⟨w, rfl⟩ := (s.mem_carrier w).1 hw
    exact (entries w w).2 rfl
  · intro w v related
    obtain ⟨hw, hv, _⟩ := (pair_mem_externalCosetRelation _ _ _ _ _ _).1 related
    obtain ⟨w, rfl⟩ := (s.mem_carrier w).1 hw
    obtain ⟨v, rfl⟩ := (s.mem_carrier v).1 hv
    exact (entries v w).2 ((entries w v).1 related).symm
  · intro w v z first second
    obtain ⟨hw, hv, _⟩ := (pair_mem_externalCosetRelation _ _ _ _ _ _).1 first
    obtain ⟨_, hz, _⟩ := (pair_mem_externalCosetRelation _ _ _ _ _ _).1 second
    obtain ⟨w, rfl⟩ := (s.mem_carrier w).1 hw
    obtain ⟨v, rfl⟩ := (s.mem_carrier v).1 hv
    obtain ⟨z, rfl⟩ := (s.mem_carrier z).1 hz
    exact (entries w z).2 (((entries w v).1 first).trans ((entries v z).1 second))

include oldEntries mulEntries in
theorem externalCosetRelation_related (w v : External J S) :
    ZFSet.pair (s.encode w) (s.encode v) ∈ externalCosetRelation s.carrier g.carrier inclusion multiplication ↔
      (cosetSetoid J S).r w v :=
  (externalCosetRelation_iff s g oldEntries mulEntries w v).trans (point_eq J S w v)

noncomputable def externalCosetPresentation : Presentation (Vertex J S) :=
  s.quotientPresentation (cosetSetoid J S)
    (externalCosetRelation_equivalence s g oldEntries mulEntries)
    (externalCosetRelation_related s g oldEntries mulEntries)

theorem externalCosetClassifier_entry_iff (w : External J S) (q : Vertex J S) :
    ZFSet.pair (s.encode w) ((externalCosetPresentation s g oldEntries mulEntries).encode q) ∈
      equivalenceClassifier s.carrier (externalCosetRelation s.carrier g.carrier inclusion multiplication) ↔
        point J S w = q :=
  s.quotientPresentation_classifier_entry_iff (cosetSetoid J S)
    (externalCosetRelation_equivalence s g oldEntries mulEntries)
    (externalCosetRelation_related s g oldEntries mulEntries) w q

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
open SetRealization Compression.RecursiveMaps Attachment CosetGeometry
universe u
variable {A J R : Type u} [Group J] {P : MeetOrder A}
variable (f : TileRequests.Family P R) (a : OrderAction J P)
variable (s : Presentation (External J f.Letters)) (t : Presentation A) (g : Presentation J)
variable (v : Presentation (Sigma fun r => Option (f.Child r) × A))
variable {oldGraph mulGraph actGraph placements overlaps : ZFSet.{u}}
variable (oldEntries : ∀ j w, ZFSet.pair (g.encode j) (s.encode w) ∈ oldGraph ↔ old J f.Letters j = w)
variable (mulEntries : ∀ w k l, ZFSet.pair (ZFSet.pair (s.encode w) (s.encode k)) (s.encode l) ∈ mulGraph ↔ w * k = l)
variable (actEntries : ∀ j x y, ZFSet.pair (ZFSet.pair (g.encode j) (t.encode x)) (t.encode y) ∈ actGraph ↔ (a.iso j).toFun x = y)
variable (placed : ∀ w u z, ZFSet.pair (ZFSet.pair (s.encode w) (v.encode u)) ((s.product t).encode z) ∈ placements ↔
  z = (f.flatWord w u.1 u.2.1, u.2.2))
variable (overlapSource : ∀ u w, ZFSet.pair (v.encode u) (v.encode w) ∈ overlaps → u.1 = w.1)
variable (overlapEntries : ∀ r i j x y,
  ZFSet.pair (v.encode ⟨r, i, x⟩) (v.encode ⟨r, j, y⟩) ∈ overlaps ↔
    (f.flatVertex r i).toFun x = (f.flatVertex r j).toFun y)

include oldEntries mulEntries actEntries in
theorem externalFlatCoordinate_to_step (x y : f.FlatLabel (J := J))
    (code : ExternalFlatCoordinateCode s.carrier t.carrier g.carrier oldGraph mulGraph actGraph
      ((s.product t).encode x) ((s.product t).encode y)) : f.FlatStep a x y := by
  obtain ⟨w, hw, k, hk, l, hl, j, hj, b, hb, c, hc, oldEntry, mulEntry, actEntry, left, right⟩ := code
  obtain ⟨w, rfl⟩ := (s.mem_carrier w).1 hw
  obtain ⟨k, rfl⟩ := (s.mem_carrier k).1 hk
  obtain ⟨l, rfl⟩ := (s.mem_carrier l).1 hl
  obtain ⟨j, rfl⟩ := (g.mem_carrier j).1 hj
  obtain ⟨b, rfl⟩ := (t.mem_carrier b).1 hb
  obtain ⟨c, rfl⟩ := (t.mem_carrier c).1 hc
  have hx : x = (l, b) := (s.product t).injective left
  have hy : y = (w, c) := (s.product t).injective right
  rw [hx, hy, ← (mulEntries w k l).1 mulEntry, ← (oldEntries j k).1 oldEntry,
    ← (actEntries j b c).1 actEntry]
  exact .coordinate w j b

include placed overlapSource overlapEntries in
theorem externalFlatTileStep_to_step (x y : f.FlatLabel (J := J))
    (code : ExternalFlatTileStepCode s.carrier v.carrier placements overlaps
      ((s.product t).encode x) ((s.product t).encode y)) : f.FlatStep a x y := by
  obtain ⟨w, hw, u, hu, z, hz, left, right, equal⟩ := code
  obtain ⟨w, rfl⟩ := (s.mem_carrier w).1 hw
  obtain ⟨⟨r, i, b⟩, rfl⟩ := (v.mem_carrier u).1 hu
  obtain ⟨⟨r', j, c⟩, rfl⟩ := (v.mem_carrier z).1 hz
  have same : r = r' := overlapSource ⟨r, i, b⟩ ⟨r', j, c⟩ equal
  cases same
  rw [(placed w ⟨r, i, b⟩ x).1 left, (placed w ⟨r, j, c⟩ y).1 right]
  exact .tile w r i j b c ((overlapEntries r i j b c).1 equal)

include oldEntries mulEntries actEntries placed overlapSource overlapEntries in
theorem pair_mem_externalFlatStepGraph_iff (x y : f.FlatLabel (J := J)) :
    ZFSet.pair ((s.product t).encode x) ((s.product t).encode y) ∈
      externalFlatStepGraph s.carrier t.carrier g.carrier v.carrier oldGraph mulGraph actGraph placements overlaps ↔
        f.FlatStep a x y := by
  rw [pair_mem_externalFlatStepGraph]
  constructor
  · rintro ⟨_, _, h⟩
    rcases h with (coordinate | tile) | (coordinate | tile)
    · exact externalFlatCoordinate_to_step f a s t g oldEntries mulEntries actEntries x y coordinate
    · exact externalFlatTileStep_to_step f a s t v placed overlapSource overlapEntries x y tile
    · exact (externalFlatCoordinate_to_step f a s t g oldEntries mulEntries actEntries y x coordinate).symm
    · exact (externalFlatTileStep_to_step f a s t v placed overlapSource overlapEntries y x tile).symm
  · intro h
    refine ⟨(s.product t).encode_mem x, (s.product t).encode_mem y, ?_⟩
    induction h with
    | coordinate w j b =>
      apply Or.inl
      apply Or.inl
      exact ⟨s.encode w, s.encode_mem w, s.encode (old J f.Letters j), s.encode_mem _,
        s.encode (w * old J f.Letters j), s.encode_mem _, g.encode j, g.encode_mem j,
        t.encode b, t.encode_mem b, t.encode ((a.iso j).toFun b), t.encode_mem _,
        (oldEntries j _).2 rfl, (mulEntries w _ _).2 rfl, (actEntries j b _).2 rfl, rfl, rfl⟩
    | tile w r i j b c equal =>
      apply Or.inl
      apply Or.inr
      exact ⟨s.encode w, s.encode_mem w, v.encode ⟨r, i, b⟩, v.encode_mem _,
        v.encode ⟨r, j, c⟩, v.encode_mem _, (placed w ⟨r, i, b⟩ _).2 rfl,
        (placed w ⟨r, j, c⟩ _).2 rfl, (overlapEntries r i j b c).2 equal⟩
    | symm h ih => exact ih.symm

end PartitionPilot.Forcing



end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Forcing_GroundIdealProjections
attribute [-instance] _root_.OAI.PartitionPilot.Forcing.GroundMainPrefix.withTopSmall
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PartitionPilot.Forcing
open SetRealization Compression Compression.RecursiveMaps SetFormula
universe u

noncomputable def idealProjectionGraph (P L ν e cap : ZFSet.{u}) : ZFSet.{u} :=
  relationCompose L L P (indexedRelationSection L L ν cap) (relationConverse P L e)

end PartitionPilot.Forcing

end

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
universe u

noncomputable def transportedTileCoordinates (V E I B D action heights : ZFSet.{u}) : ZFSet.{u} :=
  ZFSet.sep (fun z => ∃ v ∈ V, ∃ w ∈ E, ∃ i ∈ I, ∃ x ∈ B, ∃ q ∈ D,
    ∃ y ∈ B, ∃ h ∈ ZFSet.sUnion (ZFSet.sUnion heights), z = ZFSet.pair (ZFSet.pair v x) q ∧
      v = ZFSet.pair (natSetCode 1) (ZFSet.pair w i) ∧ ZFSet.pair i h ∈ heights ∧
      ZFSet.pair (ZFSet.pair w y) x ∈ action ∧ ZFSet.pair y q ∈ h)
    (ZFSet.prod (ZFSet.prod V B) D)

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

noncomputable def externalSlotCopyGraph
    (V E I U B action images j : ZFSet.{u}) : ZFSet.{u} :=
  ZFSet.sep (fun z => ∃ v ∈ V, ∃ u ∈ U, ∃ y ∈ B, ∃ w ∈ E, ∃ r ∈ I, ∃ x ∈ B,
    z = ZFSet.pair (ZFSet.pair v u) y ∧ v = ZFSet.pair (natSetCode 1) (ZFSet.pair w r) ∧
      ZFSet.pair (ZFSet.pair (ZFSet.pair r j) u) x ∈ images ∧
      ZFSet.pair (ZFSet.pair w x) y ∈ action)
    (ZFSet.prod (ZFSet.prod V U) B)

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

noncomputable def definable_singleton :
    GroundDefinableFunction M (fun env : Fin 1 → ZFSet.{u} => {env 0}) where
  formula := exactSetFormula 0 (.equal 0 2)
  closed := fun _ members => by
    simpa only [ZFSet.pair_eq_singleton] using M.unorderedPair_mem pairing (members 0) (members 0)
  correct := by
    intro env members z hz
    apply M.realize_exactSetFormula 0 _ (extend z env) hz
    · intro w hw
      exact (ZFSet.mem_singleton.1 hw).symm ▸ members 0
    · intro w _
      exact ZFSet.mem_singleton.symm

noncomputable def definable_binaryUnion :
    GroundDefinableFunction M (fun env : Fin 2 → ZFSet.{u} => env 0 ∪ env 1) where
  formula := exactSetFormula 0 (disj (.mem 0 2) (.mem 0 3))
  closed := fun _ members => M.binary_union_mem pairing unions (members 0) (members 1)
  correct := by
    intro env members z hz
    apply M.realize_exactSetFormula 0 _ (extend z env) hz
      (fun _ h => M.transitive (M.binary_union_mem pairing unions (members 0) (members 1)) h)
    intro w _
    rw [realize_disj]
    exact ZFSet.mem_union.symm

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
namespace Name
variable {P : Type u} [PartialOrder P] [OrderTop P] {s : Presentation P}

noncomputable def refinementOutput (kind : Fin 3) (T : ZFSet.{u})
    (valid : ∀ z ∈ T, IsName s z) (U Rf Rc : Name s) : Name s :=
  Fin.cases (refinementQuotient T valid U Rf)
    (Fin.cases (refinementQuotient T valid U Rc) (fun _ => refinementNaturalMap T valid U Rf Rc)) kind

end Name
namespace TransitiveGround
variable (M : TransitiveGround.{u})

noncomputable def refinementNameBound (T P top : ZFSet.{u}) : ZFSet.{u} :=
  M.groundRelations (M.groundRelations T P ∪
    orderedPairNameFamily top (M.groundRelations T P) (M.groundRelations T P)) P

end TransitiveGround



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

noncomputable def assignmentOnIndices (B T A : ZFSet.{u}) : ZFSet.{u} :=
  ZFSet.sep (fun z => z ∈ stageOneAssignments B T) A

noncomputable def assignmentQueriesWithin (Q X T : ZFSet.{u}) : ZFSet.{u} :=
  ZFSet.sep (AssignmentQueryWithin X T) Q

end PartitionPilot.Forcing



end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Definability_RowAssignmentTransitionFormulas
attribute [-instance] _root_.OAI.PartitionPilot.Forcing.GroundMainPrefix.withTopSmall
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PartitionPilot.Forcing
open SetFormula SetRealization
universe u

namespace SetFormula
def rowAssignmentCutGraphFormula {n : Nat} (output upper lower levels alpha : Fin n) : SetFormula n :=
  exactSetFormula output
    (.conj (BoundedFormula.cutGraphProductMember 0 upper.succ lower.succ).toFormula
      (rowAssignmentCutFormula 0 levels.succ alpha.succ))

end SetFormula

end PartitionPilot.Forcing

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Transfinite_FiniteFlatHistoryCoherence
attribute [-instance] _root_.OAI.PartitionPilot.Forcing.GroundMainPrefix.withTopSmall
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open scoped ZFSet

namespace PartitionPilot.Forcing
universe u

noncomputable def finiteStageHistory (values : Nat → ZFSet.{u}) : Nat → ZFSet.{u}
  | 0 => ∅
  | n + 1 => insert (ZFSet.pair (natSetCode n) (values n)) (finiteStageHistory values n)

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

namespace SetFormula

def stageOneCandidateFormula {n : Nat} (rows I T N z : Fin n) : SetFormula n :=
  let old := suffixIndex n 2
  let v := prefixIndex n 2
  exBlock 2 (.conj (BoundedFormula.orderedPairFormula (old z) (v 0) (v 1)).toFormula
    (.conj (.mem (v 0) (old rows))
      (.conj (BoundedFormula.stageOneAssignmentsSubsetFormula (v 1) (old I) (old T)).toFormula
        (hasInjectionFormula (v 1) (old N)))))

end SetFormula

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

variable {V X : Type u} (s : Presentation V) (q : Presentation X) (depth : V → Nat)
variable {depths supports : ZFSet.{u}} (supported : V → X → Prop)
variable (depthEntries : ∀ v n, ZFSet.pair (s.encode v) (natSetCode n) ∈ depths ↔ n = depth v)
variable (supportEntries : ∀ v x, ZFSet.pair (s.encode v) (q.encode x) ∈ supports ↔ supported v x)
include depthEntries supportEntries

theorem leastSupportCode_iff (x : X) (v : V) :
    LeastSupportCode s.carrier ZFSet.omega depths supports (q.encode x) (s.encode v) ↔
      supported v x ∧ ∀ w, supported w x → depth v ≤ depth w := by
  constructor
  · rintro ⟨support, n, hn, entry, least⟩
    obtain ⟨n, rfl⟩ := (mem_omega_iff_natSetCode n).1 hn
    have equal := (depthEntries v n).1 entry
    subst n
    refine ⟨(supportEntries v x).1 support, ?_⟩
    intro w hw
    have noLower := least (s.encode w) (s.encode_mem w) (natSetCode (depth w))
      (natSetCode_mem_omega _) ((supportEntries w x).2 hw) ((depthEntries w _).2 rfl)
    exact Nat.le_of_not_lt (fun lower => noLower ((natSetCode_mem_iff _ _).2 lower))
  · rintro ⟨support, minimal⟩
    refine ⟨(supportEntries v x).2 support, natSetCode (depth v), natSetCode_mem_omega _,
      (depthEntries v _).2 rfl, ?_⟩
    intro w hw m hm member entry lower
    obtain ⟨w, rfl⟩ := (s.mem_carrier w).1 hw
    obtain ⟨m, rfl⟩ := (mem_omega_iff_natSetCode m).1 hm
    have equal := (depthEntries w m).1 entry
    subst m
    exact Nat.not_lt_of_ge (minimal w ((supportEntries w x).1 member)) ((natSetCode_mem_iff _ _).1 lower)

theorem leastSupportGraph_entry (x : X) (v : V) :
    ZFSet.pair (q.encode x) (s.encode v) ∈ leastSupportGraph s.carrier q.carrier depths supports ↔
      supported v x ∧ ∀ w, supported w x → depth v ≤ depth w := by
  rw [pair_mem_leastSupportGraph, leastSupportCode_iff s q depth supported depthEntries supportEntries]
  exact ⟨fun h => h.2.2, fun h => ⟨q.encode_mem x, s.encode_mem v, h⟩⟩

theorem leastSupportGraph_function
    (unique : ∀ x, ∃! v, supported v x ∧ ∀ w, supported w x → depth v ≤ depth w) :
    ZFSet.IsFunc q.carrier s.carrier (leastSupportGraph s.carrier q.carrier depths supports) := by
  refine ⟨fun _ hz => (ZFSet.mem_sep.1 hz).1, ?_⟩
  intro x hx
  obtain ⟨x, rfl⟩ := (q.mem_carrier x).1 hx
  obtain ⟨v, good, only⟩ := unique x
  refine ⟨s.encode v, (leastSupportGraph_entry s q depth supported depthEntries supportEntries x v).2 good, ?_⟩
  intro w hw
  have member := (pair_mem_leastSupportGraph _ _ _ _ _ _).1 hw
  obtain ⟨w, rfl⟩ := (s.mem_carrier w).1 member.2.1
  exact congrArg s.encode (only w ((leastSupportGraph_entry s q depth supported depthEntries supportEntries x w).1 hw))

end PartitionPilot.Forcing



namespace PartitionPilot.Forcing
open SetFormula
universe u

theorem LeastSlotCode.le {supports v x j k : ZFSet.{u}}
    (code : LeastSlotCode supports v x j) (hj : j ∈ natSetCode 3) (hk : k ∈ natSetCode 3)
    (supported : ZFSet.pair (ZFSet.pair v k) x ∈ supports) : j = k ∨ j ∈ k := by
  obtain ⟨n, _, rfl⟩ := (mem_natSetCode j 3).1 hj
  obtain ⟨m, _, rfl⟩ := (mem_natSetCode k 3).1 hk
  rcases Nat.lt_trichotomy n m with less | same | greater
  · exact Or.inr ((natSetCode_mem_iff _ _).2 less)
  · exact Or.inl (congrArg natSetCode same)
  · exact False.elim (code.2 _ ((natSetCode_mem_iff _ _).2 greater) supported)

theorem LeastSlotCode.unique {supports v x j k : ZFSet.{u}}
    (first : LeastSlotCode supports v x j) (second : LeastSlotCode supports v x k)
    (hj : j ∈ natSetCode 3) (hk : k ∈ natSetCode 3) : j = k := by
  rcases first.le hj hk second.1 with same | less
  · exact same
  · exact False.elim (second.2 _ less first.1)

theorem exists_leastSlotCode {supports v x : ZFSet.{u}}
    (cover : ∃ j ∈ natSetCode 3, ZFSet.pair (ZFSet.pair v j) x ∈ supports) :
    ∃ j ∈ natSetCode 3, LeastSlotCode supports v x j := by
  classical
  have candidates : ∃ n : Nat, n < 3 ∧ ZFSet.pair (ZFSet.pair v (natSetCode n)) x ∈ supports := by
    obtain ⟨j, hj, supported⟩ := cover
    obtain ⟨n, hn, rfl⟩ := (mem_natSetCode j 3).1 hj
    exact ⟨n, hn, supported⟩
  refine ⟨natSetCode (Nat.find candidates), (natSetCode_mem_iff _ _).2 (Nat.find_spec candidates).1,
    (Nat.find_spec candidates).2, ?_⟩
  intro k hk supported
  obtain ⟨k, lower, rfl⟩ := (mem_natSetCode k (Nat.find candidates)).1 hk
  exact Nat.find_min candidates lower ⟨Nat.lt_trans lower (Nat.find_spec candidates).1, supported⟩

end PartitionPilot.Forcing

end

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Geometry_GroundMainTransitionLaws
attribute [-instance] _root_.OAI.PartitionPilot.Forcing.GroundMainPrefix.withTopSmall
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PartitionPilot.Forcing.GroundMainTransition
open SetFormula
universe u
variable {M : TransitiveGround.{u}} {C D rD : ZFSet.{u}}
variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
variable (unions : Realize M.sets SetFormula.union Fin.elim0)
variable (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)

@[ext] theorem ext {source target : GroundMainStage M C D rD}
    {first second : GroundMainTransition source target}
    (points : first.points = second.points) (actors : first.actors = second.actors) : first = second := by
  cases first
  cases second
  cases points
  cases actors
  rfl

end PartitionPilot.Forcing.GroundMainTransition

namespace PartitionPilot.Forcing
universe u
namespace GroundMainTransition
open SetFormula
variable {M : TransitiveGround.{u}} {C D rD : ZFSet.{u}}
variable {source target : GroundMainStage M C D rD}

noncomputable def code (transition : GroundMainTransition source target) : ZFSet.{u} :=
  ZFSet.pair transition.points transition.actors

theorem code_mem (transition : GroundMainTransition source target)
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0) : transition.code ∈ M.sets :=
  M.orderedPair_mem pairing transition.points_ground transition.actors_ground

end GroundMainTransition

end PartitionPilot.Forcing

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Definability_MainTransitionValidityCodes
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

structure MainTransitionLaws
    (P Q rP rQ μP μQ G H mG mH oneG oneH AP AQ bP bQ heightP heightQ points actors : ZFSet.{u}) : Prop where
  point_embedding : MeetEmbeddingCode P Q rP rQ μP μQ points
  order_iff : ∀ x y x' y', ZFSet.pair x x' ∈ points → ZFSet.pair y y' ∈ points →
    (ZFSet.pair x' y' ∈ rQ ↔ ZFSet.pair x y ∈ rP)
  group_embedding : GroupEmbeddingCode G H mG mH oneG oneH actors
  equivariant : ∀ g g' x y x' y', ZFSet.pair g g' ∈ actors →
    ZFSet.pair x x' ∈ points → ZFSet.pair y y' ∈ points →
    ZFSet.pair (ZFSet.pair g x) y ∈ AP → ZFSet.pair (ZFSet.pair g' x') y' ∈ AQ
  bottom : ZFSet.pair bP bQ ∈ points
  height : ∀ x y z, ZFSet.pair x y ∈ points →
    (ZFSet.pair y z ∈ heightQ ↔ ZFSet.pair x z ∈ heightP)
  agreement : ∀ g h g' h' v v', ZFSet.pair g g' ∈ actors → ZFSet.pair h h' ∈ actors →
    ZFSet.pair v v' ∈ points → ActionAgreementBelow P rP AP g h v →
      ActionAgreementBelow Q rQ AQ g' h' v'

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

theorem omegaMemberOrEqual_trans {k n m : ZFSet.{u}} (hk : k ∈ ZFSet.omega)
    (hn : n ∈ ZFSet.omega) (hm : m ∈ ZFSet.omega)
    (first : k = n ∨ k ∈ n) (second : n = m ∨ n ∈ m) : k = m ∨ k ∈ m := by
  obtain ⟨k, rfl⟩ := (mem_omega_iff_natSetCode k).1 hk
  obtain ⟨n, rfl⟩ := (mem_omega_iff_natSetCode n).1 hn
  obtain ⟨m, rfl⟩ := (mem_omega_iff_natSetCode m).1 hm
  have kn : k ≤ n := first.elim (fun h => Nat.le_of_eq (natSetCode_injective h))
    (fun h => Nat.le_of_lt ((natSetCode_mem_iff _ _).1 h))
  have nm : n ≤ m := second.elim (fun h => Nat.le_of_eq (natSetCode_injective h))
    (fun h => Nat.le_of_lt ((natSetCode_mem_iff _ _).1 h))
  rcases Nat.lt_or_eq_of_le (Nat.le_trans kn nm) with less | same
  · exact Or.inr ((natSetCode_mem_iff _ _).2 less)
  · exact Or.inl (congrArg natSetCode same)

theorem ownerLevelPrefix_lower {P B levels order n : ZFSet.{u}}
    (hn : n ∈ ZFSet.omega)
    (oldLower : ∀ x ∈ B, ∀ y ∈ P, ZFSet.pair x y ∈ order → x ∈ P)
    (function : ZFSet.IsFunc (ZFSet.sep (fun x => x ∉ P) B) ZFSet.omega levels)
    (monotone : ∀ x ∈ B, x ∉ P → ∀ y ∈ B, y ∉ P → ∀ k l,
      ZFSet.pair x k ∈ levels → ZFSet.pair y l ∈ levels → ZFSet.pair x y ∈ order → k = l ∨ k ∈ l) :
    ∀ x ∈ B, ∀ y ∈ ownerLevelPrefix P B levels n,
      ZFSet.pair x y ∈ order → x ∈ ownerLevelPrefix P B levels n := by
  classical
  intro x hx y hy lower
  by_cases old : x ∈ P
  · exact ownerLevelPrefix_old _ _ _ _ old
  rcases (mem_ownerLevelPrefix _ _ _ _ _).1 hy with hy | ⟨hy, fresh, l, hl, atY, bound⟩
  · exact False.elim (old (oldLower x hx y hy lower))
  · obtain ⟨k, atX, _⟩ := function.2 x (ZFSet.mem_sep.2 ⟨hx, old⟩)
    have hk := (ZFSet.pair_mem_prod.1 (function.1 atX)).2
    exact (mem_ownerLevelPrefix _ _ _ _ _).2 (Or.inr ⟨hx, old, k, hk, atX,
      omegaMemberOrEqual_trans hk hl hn (monotone x hx old y hy fresh k l atX atY lower) bound⟩)





namespace TransitiveGround
variable (M : TransitiveGround.{u})

noncomputable def ownerLevelPrefixFamily (P B levels : ZFSet.{u}) : ZFSet.{u} :=
  M.relationFiberFamily ZFSet.omega B (ownerLevelPrefixPoints P B levels)

end TransitiveGround





theorem PartialOrderCode.heightOrderRestriction {B Q r : ZFSet.{u}}
    (order : PartialOrderCode B r) (subset : Q ⊆ B) :
    PartialOrderCode Q (heightOrderRestriction Q r) := by
  refine ⟨fun _ hz => (ZFSet.mem_sep.1 hz).2, ?_, ?_, ?_⟩
  · intro x hx
    exact (pair_mem_heightOrderRestriction _ _ _ _).2 ⟨order.refl x (subset hx), hx, hx⟩
  · intro x hx y hy xy yx
    exact order.antisymm x (subset hx) y (subset hy) (ZFSet.mem_sep.1 xy).1 (ZFSet.mem_sep.1 yx).1
  · intro x hx y hy z hz xy yz
    exact (pair_mem_heightOrderRestriction _ _ _ _).2
      ⟨order.trans x (subset hx) y (subset hy) z (subset hz) (ZFSet.mem_sep.1 xy).1 (ZFSet.mem_sep.1 yz).1, hx, hz⟩

namespace TransitiveGround
variable (M : TransitiveGround.{u})
variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
variable (unions : Realize M.sets SetFormula.union Fin.elim0)
variable (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
include pairing unions powers separation

theorem heightOrderRestriction_mem {Q r : ZFSet.{u}} (hQ : Q ∈ M.sets) (hr : r ∈ M.sets) :
    heightOrderRestriction Q r ∈ M.sets := by
  have hProduct := M.prod_mem pairing unions powers separation hQ hQ
  exact M.bounded_separation_mem separation (.mem 0 1) (extend (ZFSet.prod Q Q) Fin.elim0)
    (Fin.cases hProduct (fun i => Fin.elim0 i)) hr

end TransitiveGround





namespace TransitiveGround
variable (M : TransitiveGround.{u})

noncomputable def chronologyRestrictionFamily (kind : Fin 3) (I Ps f : ZFSet.{u}) : ZFSet.{u} :=
  ZFSet.sep (fun z => ∃ i ∈ I, ∃ P ∈ ZFSet.sUnion (ZFSet.sUnion Ps), ∃ q ∈ M.groundPower f,
    z = ZFSet.pair i q ∧ ZFSet.pair i P ∈ Ps ∧ q = chronologyRestriction kind P f)
    (ZFSet.prod I (M.groundPower f))

end TransitiveGround

end PartitionPilot.Forcing



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

theorem fixedTopAction_at_top {G P A g q : ZFSet.{u}}
    (function : ZFSet.IsFunc (ZFSet.prod G P) P A) :
    ZFSet.pair (ZFSet.pair g P) q ∈ fixedTopAction G P A ↔ g ∈ G ∧ q = P := by
  rw [pair_mem_fixedTopAction]
  constructor
  · rintro (old | ⟨hg, _, equal⟩)
    · exact False.elim (ZFSet.mem_irrefl P
        (ZFSet.pair_mem_prod.1 (ZFSet.pair_mem_prod.1 (function.1 old)).1).2)
    · exact ⟨hg, equal⟩
  · rintro ⟨hg, equal⟩
    exact Or.inr ⟨hg, rfl, equal⟩

theorem fixedTopAction_fixes_top {G P A g : ZFSet.{u}} (hg : g ∈ G) :
    ZFSet.pair (ZFSet.pair g P) P ∈ fixedTopAction G P A :=
  (pair_mem_fixedTopAction G P A g P P).2 (Or.inr ⟨hg, rfl, rfl⟩)

theorem fixedTopAction_function {G P A : ZFSet.{u}}
    (function : ZFSet.IsFunc (ZFSet.prod G P) P A) :
    ZFSet.IsFunc (ZFSet.prod G (fixedTopCarrier P)) (fixedTopCarrier P) (fixedTopAction G P A) := by
  refine ⟨?_, ?_⟩
  · intro z member
    rcases ZFSet.mem_union.1 member with old | fresh
    · obtain ⟨x, hx, y, hy, rfl⟩ := ZFSet.mem_prod.1 (function.1 old)
      obtain ⟨g, hg, p, hp, rfl⟩ := ZFSet.mem_prod.1 hx
      exact ZFSet.pair_mem_prod.2 ⟨ZFSet.pair_mem_prod.2
        ⟨hg, (mem_fixedTopCarrier P p).2 (Or.inr hp)⟩,
          (mem_fixedTopCarrier P y).2 (Or.inr hy)⟩
    · obtain ⟨g, hg, rfl⟩ := (ZFSet.mem_sep.1 fresh).2
      have top : P ∈ fixedTopCarrier P := (mem_fixedTopCarrier P P).2 (Or.inl rfl)
      exact ZFSet.pair_mem_prod.2 ⟨ZFSet.pair_mem_prod.2 ⟨hg, top⟩, top⟩
  · intro x hx
    obtain ⟨g, hg, p, hp, rfl⟩ := ZFSet.mem_prod.1 hx
    rcases (mem_fixedTopCarrier P p).1 hp with rfl | old
    · exact ⟨_, fixedTopAction_fixes_top hg,
        fun q entry => ((fixedTopAction_at_top function).1 entry).2⟩
    · obtain ⟨q, entry, unique⟩ := function.2 (ZFSet.pair g p) (ZFSet.pair_mem_prod.2 ⟨hg, old⟩)
      exact ⟨q, (fixedTopAction_old_iff old).2 entry,
        fun y hy => unique y ((fixedTopAction_old_iff old).1 hy)⟩

theorem PosetActionCode.fixedTop {G P m e r A : ZFSet.{u}}
    (action : PosetActionCode G P m e r A) (order : PartialOrderCode P r) (one_mem : e ∈ G) :
    PosetActionCode G (fixedTopCarrier P) m e (fixedTopOrder P r) (fixedTopAction G P A) := by
  refine ⟨fixedTopAction_function action.function, ?_, ?_, ?_⟩
  · intro p hp
    rcases (mem_fixedTopCarrier P p).1 hp with rfl | old
    · exact fixedTopAction_fixes_top one_mem
    · exact (fixedTopAction_old_iff old).2 (action.one p old)
  · intro g hg h hh k hk p hp q _ s _ product first second
    rcases (mem_fixedTopCarrier P p).1 hp with rfl | old
    · have eqQ := ((fixedTopAction_at_top action.function).1 first).2
      subst q
      have eqS := ((fixedTopAction_at_top action.function).1 second).2
      subst s
      exact fixedTopAction_fixes_top hk
    · have firstOld := (fixedTopAction_old_iff old).1 first
      have qOld := (ZFSet.pair_mem_prod.1 (action.function.1 firstOld)).2
      have secondOld := (fixedTopAction_old_iff qOld).1 second
      have sOld := (ZFSet.pair_mem_prod.1 (action.function.1 secondOld)).2
      exact (fixedTopAction_old_iff old).2
        (action.mul g hg h hh k hk p old q qOld s sOld product firstOld secondOld)
  · intro g hg p _ q hq s hs v _ first second below
    rcases (mem_fixedTopCarrier P q).1 hq with rfl | qOld
    · have equal := ((fixedTopAction_at_top action.function).1 second).2
      subst v
      exact fixedTopOrder_greatest hs
    · have belowOld := (fixedTopOrder_old_iff qOld).1 below
      have pOld := (ZFSet.pair_mem_prod.1 (order.relation belowOld)).1
      have firstOld := (fixedTopAction_old_iff pOld).1 first
      have secondOld := (fixedTopAction_old_iff qOld).1 second
      have sOld := (ZFSet.pair_mem_prod.1 (action.function.1 firstOld)).2
      have vOld := (ZFSet.pair_mem_prod.1 (action.function.1 secondOld)).2
      exact ZFSet.mem_union.2 (Or.inl
        (action.monotone g hg p pOld q qOld s sOld v vOld firstOld secondOld belowOld))

end

section
universe u

namespace IdealEmbeddingCode
variable {P Q rP rQ μP μQ e : ZFSet.{u}}
variable (code : IdealEmbeddingCode P Q rP rQ μP μQ e)
include code

theorem preserves_bottom (target : MeetOrderCode Q rQ μQ) {b b' : ZFSet.{u}}
    (least : ∀ x ∈ P, ZFSet.pair b x ∈ rP) (image : ZFSet.pair b b' ∈ e) :
    ∀ y ∈ Q, ZFSet.pair b' y ∈ rQ := by
  intro y hy
  have hb' := (ZFSet.pair_mem_prod.1 (code.injection.function.1 image)).2
  obtain ⟨z, meet, _⟩ := target.operation.2 (ZFSet.pair b' y) (ZFSet.pair_mem_prod.2 ⟨hb', hy⟩)
  have hz := (ZFSet.pair_mem_prod.1 (target.operation.1 meet)).2
  obtain ⟨x, hx, _, xx'⟩ := code.ideal b b' z image hz (target.lower_left b' y z meet)
  exact target.order.trans b' hb' z hz y hy
    (code.monotone b x b' z (least x hx) image xx') (target.lower_right b' y z meet)

end IdealEmbeddingCode

end

open SetRealization
universe u

end PartitionPilot.Forcing

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Forcing_GroundRawRowAssignmentActions
attribute [-instance] _root_.OAI.PartitionPilot.Forcing.GroundMainPrefix.withTopSmall
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open scoped ZFSet

namespace PartitionPilot.Forcing
open SetFormula SetRealization
universe u

noncomputable def rawActionSection (g A P : ZFSet.{u}) : ZFSet.{u} :=
  ZFSet.sep (fun z => BoundedFormula.Truth (BoundedFormula.actionSectionEntryFormula 0 1 2 3)
    (extend z (extend g (extend A (extend P Fin.elim0))))) (ZFSet.prod P P)

theorem mem_rawActionSection (g A P z : ZFSet.{u}) :
    z ∈ rawActionSection g A P ↔
      BoundedFormula.Truth (BoundedFormula.actionSectionEntryFormula 0 1 2 3)
        (extend z (extend g (extend A (extend P Fin.elim0)))) := by
  rw [rawActionSection, ZFSet.mem_sep]
  constructor
  · exact And.right
  · intro meaning
    obtain ⟨x, hx, y, hy, equal, _⟩ :=
      (BoundedFormula.truth_actionSectionEntryFormula 0 1 2 3 _).1 meaning
    exact ⟨ZFSet.mem_prod.2 ⟨x, hx, y, hy, equal⟩, meaning⟩

noncomputable def rawActionMapFamily (G A P : ZFSet.{u}) : ZFSet.{u} :=
  letI := ZFSet.small_coe G
  familyCodeGraph (fun g : G.toSet => g.val) (fun g => rawActionSection g.val A P)

namespace TransitiveGround
variable (M : TransitiveGround.{u})
variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
variable (unions : Realize M.sets SetFormula.union Fin.elim0)
variable (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)

noncomputable def definable_rawActionSection :
    GroundDefinableFunction M (fun env : Fin 3 → ZFSet.{u} => rawActionSection (env 0) (env 1) (env 2)) where
  formula := exactSetFormula 0 (BoundedFormula.actionSectionEntryFormula 0 2 3 4).toFormula
  closed := by
    intro env members
    exact M.bounded_separation_mem separation (BoundedFormula.actionSectionEntryFormula 0 1 2 3)
      (extend (env 0) (extend (env 1) (extend (env 2) Fin.elim0)))
      (Fin.cases (members 0) (Fin.cases (members 1) (Fin.cases (members 2) (fun j => Fin.elim0 j))))
      (M.prod_mem pairing unions powers separation (members 2) (members 2))
  correct := by
    intro env members z hz
    apply M.realize_exactSetFormula 0 _ (extend z env) hz
    · intro w hw
      exact M.transitive (M.prod_mem pairing unions powers separation (members 2) (members 2))
        (ZFSet.mem_sep.1 hw).1
    · intro w hw
      rw [mem_rawActionSection,
        BoundedFormula.realize_toFormula M _ _ (Fin.cases hw (Fin.cases hz members))]
      rw [BoundedFormula.truth_actionSectionEntryFormula,
        BoundedFormula.truth_actionSectionEntryFormula]
      rfl

end TransitiveGround

variable {H Q : Type u} [Group H] [PartialOrder Q]
variable (a : PosetAction H Q) (s : Presentation Q) (t : Presentation H)

theorem rawActionSection_eq (g : H) :
    rawActionSection (t.encode g) (a.actionGraph s t) s.carrier = s.graph s (a.iso g) := by
  apply ZFSet.ext
  intro z
  rw [mem_rawActionSection]
  exact BoundedFormula.actionSectionEntry_correct a s t g z

theorem rawActionMapFamily_eq :
    rawActionMapFamily t.carrier (a.actionGraph s t) s.carrier = a.conditionMapFamily s t := by
  let := ZFSet.small_coe t.carrier
  apply ZFSet.ext
  intro z
  rw [rawActionMapFamily, mem_familyCodeGraph, PosetAction.conditionMapFamily, ZFSet.mem_range]
  constructor
  · rintro ⟨g, equal⟩
    obtain ⟨h, eq⟩ := (t.mem_carrier g.val).1 g.property
    refine ⟨h, ?_⟩
    rw [← eq, rawActionSection_eq] at equal
    exact equal
  · rintro ⟨g, equal⟩
    refine ⟨⟨t.encode g, t.encode_mem g⟩, ?_⟩
    change ZFSet.pair (t.encode g) (rawActionSection _ _ _) = z
    rw [rawActionSection_eq]
    exact equal

end PartitionPilot.Forcing

namespace PartitionPilot.Forcing
open SetFormula
universe u

theorem pair_mem_rawActionMapFamily (G action P g f : ZFSet.{u}) :
    ZFSet.pair g f ∈ rawActionMapFamily G action P ↔
      g ∈ G ∧ f = rawActionSection g action P := by
  let := ZFSet.small_coe G
  rw [rawActionMapFamily, mem_familyCodeGraph]
  constructor
  · rintro ⟨i, equal⟩
    obtain ⟨keys, values⟩ := ZFSet.pair_inj.1 equal
    exact ⟨keys ▸ i.property, by rw [← keys]; exact values.symm⟩
  · rintro ⟨member, rfl⟩
    exact ⟨⟨g, member⟩, rfl⟩

theorem pair_mem_rawActionSection (g action P x y : ZFSet.{u}) :
    ZFSet.pair x y ∈ rawActionSection g action P ↔
      x ∈ P ∧ y ∈ P ∧ ZFSet.pair (ZFSet.pair g x) y ∈ action := by
  rw [mem_rawActionSection, BoundedFormula.truth_actionSectionEntryFormula]
  constructor
  · rintro ⟨a, ha, b, hb, equal, entry⟩
    obtain ⟨rfl, rfl⟩ := ZFSet.pair_inj.1 equal
    exact ⟨ha, hb, entry⟩
  · rintro ⟨hx, hy, entry⟩
    exact ⟨x, hx, y, hy, rfl, entry⟩

noncomputable def rawRowAssignmentActionGraph
    (G Q C B J rowAction assignmentAction : ZFSet.{u}) : ZFSet.{u} :=
  rowAssignmentActionGraph G Q C B J (rawActionMapFamily G rowAction C)
    (rawActionMapFamily G assignmentAction J)

theorem pair_mem_rawRowAssignmentActionGraph
    (G Q C B J rowAction assignmentAction g p A q D : ZFSet.{u}) :
    ZFSet.pair (ZFSet.pair g (ZFSet.pair p A)) (ZFSet.pair q D) ∈
      rawRowAssignmentActionGraph G Q C B J rowAction assignmentAction ↔
      g ∈ G ∧ ZFSet.pair p A ∈ Q ∧ ZFSet.pair q D ∈ Q ∧
        p ∈ C ∧ A ∈ B ∧ q ∈ C ∧ D ∈ B ∧
          ZFSet.pair (ZFSet.pair g p) q ∈ rowAction ∧
            D = relationImage A J (rawActionSection g assignmentAction J) := by
  rw [rawRowAssignmentActionGraph, pair_mem_rowAssignmentActionGraph]
  constructor
  · rintro ⟨hg, hpA, hqD, hp, hA, hq, hD, rf, af, indexed, row, indexedA, image⟩
    have rowEq := (pair_mem_rawActionMapFamily G rowAction C g rf).1 indexed |>.2
    have assignmentEq := (pair_mem_rawActionMapFamily G assignmentAction J g af).1 indexedA |>.2
    rw [rowEq] at row
    rw [assignmentEq] at image
    exact ⟨hg, hpA, hqD, hp, hA, hq, hD,
      ((pair_mem_rawActionSection g rowAction C p q).1 row).2.2, image⟩
  · rintro ⟨hg, hpA, hqD, hp, hA, hq, hD, row, image⟩
    exact ⟨hg, hpA, hqD, hp, hA, hq, hD, rawActionSection g rowAction C,
      rawActionSection g assignmentAction J,
      (pair_mem_rawActionMapFamily G rowAction C g _).2 ⟨hg, rfl⟩,
      (pair_mem_rawActionSection g rowAction C p q).2 ⟨hp, hq, row⟩,
      (pair_mem_rawActionMapFamily G assignmentAction J g _).2 ⟨hg, rfl⟩, image⟩

end PartitionPilot.Forcing

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

def carrier : ZFSet.{u} := natSetCode 2
def actors : ZFSet.{u} := natSetCode 1
def top : ZFSet.{u} := natSetCode 1

end PartitionPilot.Forcing.InitialMainAlgebra

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

theorem twoPointHeight_strict {a b c d0 d1 C D rD : ZFSet.{u}}
    (different : a ≠ b) (hc : c ∈ C) (h0 : d0 ∈ D) (h1 : d1 ∈ D)
    (gap : ZFSet.pair d0 d1 ∈ rD) :
    StrictLexHeightCode {a, b} C D
      {ZFSet.pair a a, ZFSet.pair a b, ZFSet.pair b b} (twoPointHeight a b c d0 d1) rD := by
  refine ⟨twoPointHeight_function different hc h0 h1, ?_⟩
  intro x _ y _ c' q d' v ordered ne hx hy
  have endpoints : x = a ∧ y = b := by
    simp only [ZFSet.mem_insert_iff, ZFSet.mem_singleton, ZFSet.pair_inj] at ordered
    rcases ordered with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact False.elim (ne rfl)
    · exact ⟨rfl, rfl⟩
    · exact False.elim (ne rfl)
  obtain ⟨hxEq, hyEq⟩ := endpoints
  subst x y
  have first : ZFSet.pair c' q = ZFSet.pair c d0 := by
    rcases (twoPointHeight_entry a b c d0 d1 a _).1 hx with ⟨_, h⟩ | ⟨bad, _⟩
    · exact h
    · exact False.elim (different bad)
  have second : ZFSet.pair d' v = ZFSet.pair c d1 := by
    rcases (twoPointHeight_entry a b c d0 d1 b _).1 hy with ⟨bad, _⟩ | ⟨_, h⟩
    · exact False.elim (different bad.symm)
    · exact h
  obtain ⟨rfl, rfl⟩ := ZFSet.pair_inj.1 first
  obtain ⟨rfl, rfl⟩ := ZFSet.pair_inj.1 second
  exact Or.inr ⟨rfl, gap⟩

theorem twoPointHeight_image {a b c d0 d1 C D : ZFSet.{u}}
    (hc : c ∈ C) (h0 : d0 ∈ D) (h1 : d1 ∈ D) :
    relationImage {a, b} (ZFSet.prod C D) (twoPointHeight a b c d0 d1) =
      {ZFSet.pair c d0, ZFSet.pair c d1} := by
  apply ZFSet.ext
  intro y
  rw [mem_relationImage, ZFSet.mem_pair]
  constructor
  · rintro ⟨_, x, _, entry⟩
    exact ((twoPointHeight_entry a b c d0 d1 x y).1 entry).elim
      (fun h => Or.inl h.2) (fun h => Or.inr h.2)
  · rintro (rfl | rfl)
    · exact ⟨ZFSet.pair_mem_prod.2 ⟨hc, h0⟩, a, ZFSet.mem_pair.2 (Or.inl rfl),
        ZFSet.mem_pair.2 (Or.inl rfl)⟩
    · exact ⟨ZFSet.pair_mem_prod.2 ⟨hc, h1⟩, b, ZFSet.mem_pair.2 (Or.inr rfl),
        ZFSet.mem_pair.2 (Or.inr rfl)⟩

namespace TransitiveGround
variable (M : TransitiveGround.{u})

theorem twoPointHeight_mem
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    {a b c d0 d1 : ZFSet.{u}} (ha : a ∈ M.sets) (hb : b ∈ M.sets)
    (hc : c ∈ M.sets) (h0 : d0 ∈ M.sets) (h1 : d1 ∈ M.sets) :
    twoPointHeight a b c d0 d1 ∈ M.sets :=
  M.unorderedPair_mem pairing (M.orderedPair_mem pairing ha (M.orderedPair_mem pairing hc h0))
    (M.orderedPair_mem pairing hb (M.orderedPair_mem pairing hc h1))

end TransitiveGround

end PartitionPilot.Forcing

end

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

structure MainStageLaws (P r μ G m inv one A b t height C D rD : ZFSet.{u}) : Prop where
  meet : MeetOrderCode P r μ
  group : GroupCode G m inv one
  action : PosetActionCode G P m one r A
  bottom_mem : b ∈ P
  least : ∀ x ∈ P, ZFSet.pair b x ∈ r
  top_mem : t ∈ P
  greatest : ∀ x ∈ P, ZFSet.pair x t ∈ r
  height_code : StrictLexHeightCode P C D r height rD

def MainStageValidity (M : TransitiveGround.{u})
    (P r μ G m inv one A b t height C D rD : ZFSet.{u}) : Prop :=
  MainStageLaws P r μ G m inv one A b t height C D rD ∧
    M.groundEmbeddable (relationImage P (ZFSet.prod C D) height) ZFSet.omega

namespace GroundMainStage
variable {M : TransitiveGround.{u}}

theorem validity {C D rD : ZFSet.{u}} (stage : GroundMainStage M C D rD) :
    MainStageValidity M stage.carrier stage.order stage.meetGraph stage.actors
      stage.multiplication stage.inverse stage.identity stage.action stage.bottom stage.top
      stage.height C D rD :=
  ⟨⟨stage.meet, stage.group_code, stage.action_code, stage.bottom_mem, stage.least,
    stage.top_mem, stage.greatest, stage.height_code⟩, stage.height_range_countable⟩

end GroundMainStage

end PartitionPilot.Forcing

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Transfinite_CodedMainPrefixSystems
attribute [-instance] _root_.OAI.PartitionPilot.Forcing.GroundMainPrefix.withTopSmall
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI



namespace PartitionPilot.Forcing
open SetFormula
universe u

noncomputable def linkedMainStageCode (stage cutoff serial : ZFSet.{u}) : ZFSet.{u} :=
  nonemptyTupleCode 2 (Fin.cases stage (Fin.cases cutoff (fun _ => serial)))

theorem linkedMainStageCode_inj {a t h a' t' h' : ZFSet.{u}} :
    linkedMainStageCode a t h = linkedMainStageCode a' t' h' ↔ a = a' ∧ t = t' ∧ h = h' := by
  constructor
  · intro equal
    have fields := nonemptyTupleCode_injective 2 equal
    exact ⟨congrFun fields 0, congrFun fields 1, congrFun fields 2⟩
  · rintro ⟨rfl, rfl, rfl⟩
    rfl

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

def countableGrowthWitnessFormula {n} (z L birth t N : Fin n) : SetFormula n :=
  let old := suffixIndex n 3
  let field := prefixIndex n 3
  exBlock 3 (BoundedFormula.countableTaggedLayerFormula
    (old z) (field 0) (field 1) (field 2) (old L) (old birth) (old t) (old N)).toFormula

def copyGrowthWitnessFormula {n} (z Qs rs μs L r μ birth t N : Fin n) : SetFormula n :=
  let old := suffixIndex n 10
  let field := prefixIndex n 10
  exBlock 10 (BoundedFormula.copyTaggedLayerFormula (old z)
    (field 0) (field 1) (field 2) (field 3) (field 4) (field 5) (field 6)
    (old Qs) (old rs) (old μs) (old L) (old r) (old μ) (old birth) (old t) (old N)
    (field 7) (field 8) (field 9)).toFormula

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
def chronologyLayerFunctionFormula {n} (T W layers : Fin n) : SetFormula n :=
  ex (.conj (BoundedFormula.chronologyPairsEquationFormula 0 T.succ).toFormula
    (BoundedFormula.functionFormula 0 W.succ layers.succ).toFormula)

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
universe u

noncomputable def serializedChronologyCode (T V : ZFSet.{u}) (graphs : Fin 5 → ZFSet.{u})
    (W layers : ZFSet.{u}) : ZFSet.{u} :=
  nonemptyTupleCode 2 (Fin.cases (nonemptyTupleCode 6 (Fin.cases T (Fin.cases V graphs)))
    (Fin.cases W (fun _ => layers)))

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

def LinkedTransitionLawsCode (z points actors sourceBirth targetBirth : ZFSet.{u})
    (source target : Fin 24 → ZFSet.{u}) : Prop :=
  ZFSet.pair (source 11) sourceBirth ∈ source 17 ∧
  ZFSet.pair (target 11) targetBirth ∈ target 17 ∧
  (z = ZFSet.pair points actors ∧
    MainTransitionLaws (source 0) (target 0) (source 1) (target 1) (source 2) (target 2) (source 3) (target 3) (source 4) (target 4) (source 6) (target 6) (source 7) (target 7) (source 8) (target 8) (source 10) (target 10) points actors ∧
    ChronologicalTransitionLaws points (source 11) (target 11) sourceBirth targetBirth
      (linkedChronologyGraphs source) (linkedChronologyGraphs target)) ∧
  OldBirthFiberCoverageCode (source 0) points targetBirth (source 11)

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

noncomputable def mainPrefixCode (T S E : ZFSet.{u}) : ZFSet.{u} :=
  nonemptyTupleCode 2 (Fin.cases T (Fin.cases S (fun _ => E)))

theorem mainPrefixCode_inj {T S E T' S' E' : ZFSet.{u}} :
    mainPrefixCode T S E = mainPrefixCode T' S' E' ↔ T = T' ∧ S = S' ∧ E = E' := by
  constructor
  · intro equal
    have fields := nonemptyTupleCode_injective 2 equal
    exact ⟨congrFun fields 0, congrFun fields 1, congrFun fields 2⟩
  · rintro ⟨rfl, rfl, rfl⟩
    rfl

end

section
universe u

def MainPrefixExtends (old next : ZFSet.{u}) : Prop :=
  ∃ T S E T' S' E', old = mainPrefixCode T S E ∧ next = mainPrefixCode T' S' E' ∧
    T ⊆ T' ∧ S ⊆ S' ∧ E ⊆ E'

theorem mainPrefixExtends_iff {T S E T' S' E' : ZFSet.{u}} :
    MainPrefixExtends (mainPrefixCode T S E) (mainPrefixCode T' S' E') ↔
      T ⊆ T' ∧ S ⊆ S' ∧ E ⊆ E' := by
  constructor
  · rintro ⟨A, B, C, A', B', C', first, second, indices, stages, transitions⟩
    obtain ⟨rfl, rfl, rfl⟩ := mainPrefixCode_inj.1 first
    obtain ⟨rfl, rfl, rfl⟩ := mainPrefixCode_inj.1 second
    exact ⟨indices, stages, transitions⟩
  · rintro ⟨indices, stages, transitions⟩
    exact ⟨T, S, E, T', S', E', rfl, rfl, indices, stages, transitions⟩

end

end PartitionPilot.Forcing

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Transfinite_GroundMainPrefixLimitCoverageGraph
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open scoped ZFSet


namespace PartitionPilot.Forcing
universe u

def LinkedCoverageFieldsCode (z P G cutoff : ZFSet.{u}) : Prop :=
  ∃ r μ m inv one action bottom top height serial,
    z = linkedMainStageCode (mainStageCode P r μ G m inv one action bottom top height) cutoff serial

def MainLimitConeEntryCode (T S row i P G cutoff points actors : ZFSet.{u}) : Prop :=
  i ∈ T ∧ ∃ z, ZFSet.pair i z ∈ S ∧ LinkedCoverageFieldsCode z P G cutoff ∧
    ZFSet.pair (ZFSet.pair T i) (ZFSet.pair points actors) ∈ row

def MainLimitOldPointImageCode (T S row x : ZFSet.{u}) : Prop :=
  ∃ i P G cutoff points actors y, MainLimitConeEntryCode T S row i P G cutoff points actors ∧
    y ∈ P ∧ ZFSet.pair y x ∈ points

def MainLimitOldActorImageCode (T S row g : ZFSet.{u}) : Prop :=
  ∃ i P G cutoff points actors h, MainLimitConeEntryCode T S row i P G cutoff points actors ∧
    h ∈ G ∧ ZFSet.pair h g ∈ actors

def MainLimitOldCutoffCode (T S t : ZFSet.{u}) : Prop :=
  ∃ i ∈ T, ∃ z, ZFSet.pair i z ∈ S ∧
    ∃ P G cutoff, LinkedCoverageFieldsCode z P G cutoff ∧ (t = cutoff ∨ t ∈ cutoff)

structure MainLimitCoverageGraphCode (T S row Q H R top cutoff birth : ZFSet.{u}) : Prop where
  points : ∀ x, (x ∈ Q ∧ x ≠ top) ↔ MainLimitOldPointImageCode T S row x
  actors : ∀ g, g ∈ H ↔ MainLimitOldActorImageCode T S row g
  strict_top : ∀ i P G t points actors, MainLimitConeEntryCode T S row i P G t points actors →
    ∀ x y, ZFSet.pair x y ∈ points → ZFSet.pair y top ∈ R ∧ ZFSet.pair top y ∉ R
  cutoff_mem : ∀ t, t ∈ cutoff ↔ MainLimitOldCutoffCode T S t
  top_birth : ∀ x, ZFSet.pair x cutoff ∈ birth ↔ x = top

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

namespace PartitionPilot.Forcing
universe u

def OldProfilePreservationCode (P r μ Q R ν e Filters : ZFSet.{u}) : Prop :=
  ∀ F ∈ Filters, ∀ c ∈ P, ∀ E ∈ P, ∀ K ∈ P,
    CodedCapProfile P r μ c E K F →
    ∀ c' ∈ Q, ∀ E' ∈ Q, ∀ K' ∈ Q,
      ZFSet.pair c c' ∈ e → ZFSet.pair E E' ∈ e → ZFSet.pair K K' ∈ e →
      CodedCapProfile Q R ν c' E' K' (relationImage F Q e)

def TaskCapProfilesCode (I P Q R ν e Targets Separators Filters Families Caps : ZFSet.{u}) : Prop :=
  ∀ i ∈ I, ∀ c ∈ P, ∀ v ∈ P, ∀ F ∈ Families,
    ∀ K ∈ Q, ∀ c' ∈ Q, ∀ v' ∈ Q,
      ZFSet.pair i c ∈ Targets → ZFSet.pair i v ∈ Separators → ZFSet.pair i F ∈ Filters →
      ZFSet.pair i K ∈ Caps → ZFSet.pair c c' ∈ e → ZFSet.pair v v' ∈ e →
      CodedCapProfile Q R ν c' v' K (relationImage F Q e)

structure TaskCapFamilyCode (I P Q R ν e Targets Separators Filters Families Caps : ZFSet.{u}) : Prop where
  function : ZFSet.IsFunc I Q Caps
  profiles : TaskCapProfilesCode I P Q R ν e Targets Separators Filters Families Caps
  common_target : CommonTargetCapMeetCode I P Q ν e Targets Caps

end PartitionPilot.Forcing

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Forcing_MeetOrderPosetActions
attribute [-instance] _root_.OAI.PartitionPilot.Forcing.GroundMainPrefix.withTopSmall
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PartitionPilot.MeetOrder

universe u

@[instance_reducible]
def toPartialOrder {I : Type u} (P : MeetOrder I) : PartialOrder I where
  le := P.le
  le_refl := P.refl
  le_trans _ _ _ := P.trans
  le_antisymm _ _ := P.antisymm

end PartitionPilot.MeetOrder

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

section
open SetFormula
universe u

structure GroundMainFinalGeometry (M : TransitiveGround.{u}) (C D rD : ZFSet.{u}) where
  carrier : ZFSet.{u}
  order : ZFSet.{u}
  meetGraph : ZFSet.{u}
  actors : ZFSet.{u}
  multiplication : ZFSet.{u}
  inverse : ZFSet.{u}
  identity : ZFSet.{u}
  action : ZFSet.{u}
  bottom : ZFSet.{u}
  height : ZFSet.{u}
  birth : ZFSet.{u}
  times : ZFSet.{u}
  carrier_ground : carrier ∈ M.sets
  order_ground : order ∈ M.sets
  meet_ground : meetGraph ∈ M.sets
  actors_ground : actors ∈ M.sets
  multiplication_ground : multiplication ∈ M.sets
  inverse_ground : inverse ∈ M.sets
  action_ground : action ∈ M.sets
  height_ground : height ∈ M.sets
  birth_ground : birth ∈ M.sets
  times_ground : times ∈ M.sets
  columns_ground : C ∈ M.sets
  coordinates_ground : D ∈ M.sets
  coordinate_order_ground : rD ∈ M.sets
  meet : MeetOrderCode carrier order meetGraph
  group_code : GroupCode actors multiplication inverse identity
  action_code : PosetActionCode actors carrier multiplication identity order action
  bottom_mem : bottom ∈ carrier
  least : ∀ x ∈ carrier, ZFSet.pair bottom x ∈ order
  height_code : StrictLexHeightCode carrier C D order height rD
  birth_function : ZFSet.IsFunc carrier times birth
  times_ordinal : ordinalSetProperty times
  old_meet : OldMeetCode order meetGraph birth

namespace GroundMainFinalGeometry
variable {M : TransitiveGround.{u}} {C D rD : ZFSet.{u}}
variable (geometry : GroundMainFinalGeometry M C D rD)

noncomputable def fields : Fin 12 → ZFSet.{u} :=
  Fin.cases geometry.carrier (Fin.cases geometry.order (Fin.cases geometry.meetGraph
    (Fin.cases geometry.actors (Fin.cases geometry.multiplication (Fin.cases geometry.inverse
      (Fin.cases geometry.identity (Fin.cases geometry.action (Fin.cases geometry.bottom
        (Fin.cases geometry.height (Fin.cases geometry.birth (fun _ => geometry.times)))))))))))

noncomputable def code : ZFSet.{u} := nonemptyTupleCode 11 geometry.fields

end GroundMainFinalGeometry

end

namespace GroundMainFinalGeometry
open SetFormula SetRealization
universe u
variable {M : TransitiveGround.{u}} {C D rD : ZFSet.{u}}
variable (geometry : GroundMainFinalGeometry M C D rD)

@[instance_reducible] noncomputable def decodedBottom :
    letI := geometry.meet.order.toPartialOrder
    OrderBot (SetMembers geometry.carrier) := by
  letI := geometry.meet.order.toPartialOrder
  refine { bot := SetMembers.ofMem geometry.bottom geometry.bottom_mem, bot_le := ?_ }
  intro x
  change ZFSet.pair (SetMembers.raw (SetMembers.ofMem geometry.bottom geometry.bottom_mem))
    (SetMembers.raw x) ∈ geometry.order
  rw [SetMembers.raw_ofMem]
  exact geometry.least _ (SetMembers.raw_mem x)

end GroundMainFinalGeometry

end PartitionPilot.Forcing

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Definability_IndexedMixedOperationLiftCodes
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

theorem triple_mem_indexedMixedBinaryLift (T UG UP G P A JG JP g p q : ZFSet.{u}) :
    ZFSet.pair (ZFSet.pair g p) q ∈ indexedMixedBinaryLift T UG UP G P A JG JP ↔
      g ∈ G ∧ p ∈ P ∧ q ∈ P ∧ ∃ i ∈ T, ∃ a eG eP,
        ∃ u ∈ UG, ∃ x ∈ UP, ∃ y ∈ UP,
          ZFSet.pair i a ∈ A ∧ ZFSet.pair i eG ∈ JG ∧ ZFSet.pair i eP ∈ JP ∧
          ZFSet.pair u g ∈ eG ∧ ZFSet.pair x p ∈ eP ∧ ZFSet.pair y q ∈ eP ∧
          ZFSet.pair (ZFSet.pair u x) y ∈ a := by
  rw [indexedMixedBinaryLift, ZFSet.mem_sep]
  constructor
  · rintro ⟨_, g', hg, p', hp, q', hq, i, hi, a, _, eG, _, eP, _,
      u, hu, x, hx, y, hy, equal, action, actors, points, actor, first, second, source⟩
    obtain ⟨gp, rfl⟩ := ZFSet.pair_inj.1 equal
    obtain ⟨rfl, rfl⟩ := ZFSet.pair_inj.1 gp
    exact ⟨hg, hp, hq, i, hi, a, eG, eP, u, hu, x, hx, y, hy,
      action, actors, points, actor, first, second, source⟩
  · rintro ⟨hg, hp, hq, i, hi, a, eG, eP, u, hu, x, hx, y, hy,
      action, actors, points, actor, first, second, source⟩
    exact ⟨ZFSet.pair_mem_prod.2 ⟨ZFSet.pair_mem_prod.2 ⟨hg, hp⟩, hq⟩,
      g, hg, p, hp, q, hq, i, hi, a, pair_second_mem_doubleUnion action,
      eG, pair_second_mem_doubleUnion actors, eP, pair_second_mem_doubleUnion points,
      u, hu, x, hx, y, hy, rfl, action, actors, points, actor, first, second, source⟩

end PartitionPilot.Forcing

end

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Definability_IndexedOperationLiftCodes
attribute [-instance] _root_.OAI.PartitionPilot.Forcing.GroundMainPrefix.withTopSmall
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PartitionPilot.Forcing
open SetRealization
open scoped ZFSet
universe u

theorem pair_mem_indexedRelationLift (T U Q R J p q : ZFSet.{u}) :
    ZFSet.pair p q ∈ indexedRelationLift T U Q R J ↔
      p ∈ Q ∧ q ∈ Q ∧ ∃ i ∈ T, ∃ r e, ∃ x ∈ U, ∃ y ∈ U,
        ZFSet.pair i r ∈ R ∧ ZFSet.pair i e ∈ J ∧
          ZFSet.pair x p ∈ e ∧ ZFSet.pair y q ∈ e ∧ ZFSet.pair x y ∈ r := by
  rw [indexedRelationLift, ZFSet.mem_sep]
  constructor
  · rintro ⟨_, p', hp, q', hq, i, hi, r, _, e, _, x, hx, y, hy, equal, relation, inclusion, first, second, source⟩
    obtain ⟨rfl, rfl⟩ := ZFSet.pair_inj.1 equal
    exact ⟨hp, hq, i, hi, r, e, x, hx, y, hy, relation, inclusion, first, second, source⟩
  · rintro ⟨hp, hq, i, hi, r, e, x, hx, y, hy, relation, inclusion, first, second, source⟩
    exact ⟨ZFSet.pair_mem_prod.2 ⟨hp, hq⟩, p, hp, q, hq, i, hi,
      r, pair_second_mem_doubleUnion relation, e, pair_second_mem_doubleUnion inclusion,
      x, hx, y, hy, rfl, relation, inclusion, first, second, source⟩

theorem triple_mem_indexedBinaryLift (T U Q B J p q v : ZFSet.{u}) :
    ZFSet.pair (ZFSet.pair p q) v ∈ indexedBinaryLift T U Q B J ↔
      p ∈ Q ∧ q ∈ Q ∧ v ∈ Q ∧ ∃ i ∈ T, ∃ b e, ∃ x ∈ U, ∃ y ∈ U, ∃ z ∈ U,
        ZFSet.pair i b ∈ B ∧ ZFSet.pair i e ∈ J ∧
          ZFSet.pair x p ∈ e ∧ ZFSet.pair y q ∈ e ∧ ZFSet.pair z v ∈ e ∧
            ZFSet.pair (ZFSet.pair x y) z ∈ b := by
  rw [indexedBinaryLift, ZFSet.mem_sep]
  constructor
  · rintro ⟨_, p', hp, q', hq, v', hv, i, hi, b, _, e, _, x, hx, y, hy, z, hz,
      equal, operation, inclusion, first, second, third, source⟩
    obtain ⟨pq, rfl⟩ := ZFSet.pair_inj.1 equal
    obtain ⟨rfl, rfl⟩ := ZFSet.pair_inj.1 pq
    exact ⟨hp, hq, hv, i, hi, b, e, x, hx, y, hy, z, hz,
      operation, inclusion, first, second, third, source⟩
  · rintro ⟨hp, hq, hv, i, hi, b, e, x, hx, y, hy, z, hz,
      operation, inclusion, first, second, third, source⟩
    exact ⟨ZFSet.pair_mem_prod.2 ⟨ZFSet.pair_mem_prod.2 ⟨hp, hq⟩, hv⟩,
      p, hp, q, hq, v, hv, i, hi, b, pair_second_mem_doubleUnion operation,
      e, pair_second_mem_doubleUnion inclusion, x, hx, y, hy, z, hz,
      rfl, operation, inclusion, first, second, third, source⟩

end PartitionPilot.Forcing

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

theorem pair_mem_indexedValueLift (T U Q V F J q v : ZFSet.{u}) :
    ZFSet.pair q v ∈ indexedValueLift T U Q V F J ↔
      q ∈ Q ∧ v ∈ V ∧ ∃ i ∈ T, ∃ f e, ∃ x ∈ U,
        ZFSet.pair i f ∈ F ∧ ZFSet.pair i e ∈ J ∧
        ZFSet.pair x q ∈ e ∧ ZFSet.pair x v ∈ f := by
  rw [indexedValueLift, ZFSet.mem_sep]
  constructor
  · rintro ⟨_, i, hi, f, _, e, _, x, hx, p, hp, w, hw, equal, value, inclusion, image, entry⟩
    obtain ⟨rfl, rfl⟩ := ZFSet.pair_inj.1 equal
    exact ⟨hp, hw, i, hi, f, e, x, hx, value, inclusion, image, entry⟩
  · rintro ⟨hq, hv, i, hi, f, e, x, hx, value, inclusion, image, entry⟩
    exact ⟨ZFSet.pair_mem_prod.2 ⟨hq, hv⟩,
      i, hi, f, pair_second_mem_doubleUnion value, e, pair_second_mem_doubleUnion inclusion,
      x, hx, q, hq, v, hv, rfl, value, inclusion, image, entry⟩

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

namespace GroundChronologyFields
variable {M : TransitiveGround.{u}} {T C D rD : ZFSet.{u}}
variable (fields : GroundChronologyFields M T)

noncomputable def layerRelationParams (N : ZFSet.{u}) : Fin 6 → ZFSet.{u} :=
  Fin.cases T (Fin.cases (fields.graph 0) (Fin.cases (fields.graph 1)
    (Fin.cases (fields.graph 2) (Fin.cases (fields.graph 3) (fun _ => N)))))

end GroundChronologyFields

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
open SetRealization
universe u





def MainPrefixHistoryFieldMem (p x : ZFSet.{u}) (j : Fin 3) : Prop :=
  ∃ i T S E, ZFSet.pair i (mainPrefixCode T S E) ∈ p ∧
    x ∈ (Fin.cases T (Fin.cases S (fun _ => E)) : Fin 3 → ZFSet.{u}) j

def MainPrefixHistoryUnionCode (p q : ZFSet.{u}) : Prop :=
  ∃ T S E, q = mainPrefixCode T S E ∧
    ∀ (j : Fin 3) x, x ∈ (Fin.cases T (Fin.cases S (fun _ => E)) : Fin 3 → ZFSet.{u}) j ↔
      MainPrefixHistoryFieldMem p x j

end PartitionPilot.Forcing



namespace PartitionPilot.Forcing
universe u

def MainPrefixAtIndex (T q : ZFSet.{u}) : Prop :=
  ∃ S E, q = mainPrefixCode T S E

def MainPrefixHistoryExtends (p q : ZFSet.{u}) : Prop :=
  ∀ i old, ZFSet.pair i old ∈ p → MainPrefixExtends old q

def MainPrefixTraceStepCode (B seed g α p y : ZFSet.{u}) : Prop :=
  y ∈ B ∧ MainPrefixAtIndex (insert α α) y ∧ MainPrefixHistoryExtends p y ∧
    ((α = ∅ ∧ y = seed) ∨
      (α ≠ ∅ ∧ ∃ input, MainPrefixHistoryUnionCode p input ∧ ZFSet.pair input y ∈ g))

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

def MainPrefixRecursionIndexCode (Omega z : ZFSet.{u}) : Prop :=
  ∃ T S E, z = mainPrefixCode T S E ∧ T ∈ Omega ∧ T ≠ ∅

end

section
open SetFormula
universe u v

def MainPrefixSelectedStepCode (f old next : ZFSet.{u}) : Prop :=
  ∃ b S E S' E' a target z,
    old = mainPrefixCode (insert b b) S E ∧
    next = mainPrefixCode (insert (insert b b) (insert b b)) S' E' ∧
    MainPrefixExtends old next ∧
    ZFSet.pair b a ∈ S ∧ ZFSet.pair a (ZFSet.pair target z) ∈ f ∧
    ZFSet.pair (insert b b) target ∈ S' ∧
    ZFSet.pair (ZFSet.pair (insert b b) b) z ∈ E'

end

open SetFormula SetRealization
universe u v w

end PartitionPilot.Forcing

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Definability_TupleRelationProducts
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

theorem mem_tupleRelationBound (k : Nat) (f x : Fin (k + 1) → ZFSet.{u}) :
    nonemptyTupleCode k x ∈ tupleRelationBound k f ↔ ∀ j, x j ∈ ⋃₀ ⋃₀ f j := by
  induction k with
  | zero =>
    change x 0 ∈ ⋃₀ ⋃₀ f 0 ↔ _
    exact ⟨fun h => Fin.cases h (fun j => Fin.elim0 j), fun h => h 0⟩
  | succ k ih =>
    rw [tupleRelationBound, nonemptyTupleCode, ZFSet.pair_mem_prod, ih]
    exact ⟨fun h => Fin.cases h.1 h.2, fun h => ⟨h 0, fun j => h j.succ⟩⟩

theorem pair_mem_tupleRelationProduct (k : Nat) (f x y : Fin (k + 1) → ZFSet.{u}) :
    ZFSet.pair (nonemptyTupleCode k x) (nonemptyTupleCode k y) ∈ tupleRelationProduct k f ↔
      ∀ j, ZFSet.pair (x j) (y j) ∈ f j := by
  induction k with
  | zero =>
    change ZFSet.pair (x 0) (y 0) ∈ f 0 ↔ _
    exact ⟨fun h => Fin.cases h (fun j => Fin.elim0 j), fun h => h 0⟩
  | succ k ih =>
    rw [tupleRelationProduct, nonemptyTupleCode, nonemptyTupleCode,
      pair_mem_relationProduct, ih]
    constructor
    · rintro ⟨_, _, _, _, first, rest⟩
      exact Fin.cases first rest
    · intro entries
      exact ⟨pair_first_mem_doubleUnion (entries 0),
        (mem_tupleRelationBound k _ _).2 (fun j => pair_first_mem_doubleUnion (entries j.succ)),
        pair_second_mem_doubleUnion (entries 0),
        (mem_tupleRelationBound k _ _).2 (fun j => pair_second_mem_doubleUnion (entries j.succ)),
        entries 0, fun j => entries j.succ⟩

end PartitionPilot.Forcing

end

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
variable (T T2 : ZFSet.{u}) (valid : ∀ z ∈ T, IsName s z) (valid2 : ∀ z ∈ T2, IsName s z)

variable (closed : ∀ g (w : Name s), w.val ∈ T → (a.act s g w).val ∈ T)

omit [OrderTop P] in
include closed in
theorem stageOneTermAction_function (g : G) :
    ZFSet.IsFunc T T (Name.renameFamilyGraph s (a.iso g) T valid) := by
  refine ⟨?_, ?_⟩
  · intro z hz
    obtain ⟨w, hw, rfl⟩ := (Name.mem_renameFamilyGraph s (a.iso g) T valid z).1 hz
    exact ZFSet.pair_mem_prod.2 ⟨hw, closed g w hw⟩
  · intro x hx
    let w : Name s := ⟨x, valid x hx⟩
    refine ⟨(a.act s g w).val,
      (Name.pair_mem_renameFamilyGraph s (a.iso g) T valid w _).2 ⟨hx, rfl⟩, ?_⟩
    intro y hy
    exact ((Name.pair_mem_renameFamilyGraph s (a.iso g) T valid w y).1 hy).2

omit [OrderTop P] in
include closed in
theorem stageOneTermAction_injection (g : G) :
    InjectionCode T T (Name.renameFamilyGraph s (a.iso g) T valid) := by
  refine ⟨stageOneTermAction_function a s T valid closed g, ?_⟩
  intro x y z hx hy
  have func := stageOneTermAction_function a s T valid closed g
  let wx : Name s := ⟨x, valid x (ZFSet.pair_mem_prod.1 (func.1 hx)).1⟩
  let wy : Name s := ⟨y, valid y (ZFSet.pair_mem_prod.1 (func.1 hy)).1⟩
  have ex := ((Name.pair_mem_renameFamilyGraph s (a.iso g) T valid wx z).1 hx).2
  have ey := ((Name.pair_mem_renameFamilyGraph s (a.iso g) T valid wy z).1 hy).2
  have equal : a.act s g wx = a.act s g wy := Subtype.ext (ex.symm.trans ey)
  exact congrArg Subtype.val ((a.nameEquiv s g).injective equal)

end PartitionPilot.Forcing.TransitiveGround




end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Forcing_RelationActionFamilies
attribute [-instance] _root_.OAI.PartitionPilot.Forcing.GroundMainPrefix.withTopSmall
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PartitionPilot.Forcing
universe u

namespace RelationActionLaws
variable {G : Type u} [Group G] {X Y : ZFSet.{u}} {f h : G → ZFSet.{u}}

theorem image_one (laws : RelationActionLaws G X f) {A : ZFSet.{u}} (subset : A ⊆ X) :
    relationImage A X (f 1) = A := by
  apply ZFSet.ext
  intro y
  constructor
  · intro member
    obtain ⟨_, x, hx, entry⟩ := (mem_relationImage A X (f 1) y).1 member
    exact (laws.one x (subset hx) y).1 entry ▸ hx
  · intro member
    exact (mem_relationImage A X (f 1) y).2
      ⟨subset member, y, member, (laws.one y (subset member) y).2 rfl⟩

theorem image_mul (laws : RelationActionLaws G X f) (g k : G)
    {A : ZFSet.{u}} (subset : A ⊆ X) :
    relationImage A X (f (g * k)) = relationImage (relationImage A X (f k)) X (f g) := by
  apply ZFSet.ext
  intro z
  constructor
  · intro member
    obtain ⟨hz, x, hx, entry⟩ := (mem_relationImage A X (f (g * k)) z).1 member
    obtain ⟨y, hy, ek, eg⟩ := (laws.mul g k x (subset hx) z).1 entry
    exact (mem_relationImage _ X (f g) z).2
      ⟨hz, y, (mem_relationImage A X (f k) y).2 ⟨hy, x, hx, ek⟩, eg⟩
  · intro member
    obtain ⟨hz, y, hy, eg⟩ := (mem_relationImage _ X (f g) z).1 member
    obtain ⟨hy, x, hx, ek⟩ := (mem_relationImage A X (f k) y).1 hy
    exact (mem_relationImage A X (f (g * k)) z).2
      ⟨hz, x, hx, (laws.mul g k x (subset hx) z).2 ⟨y, hy, ek, eg⟩⟩

end RelationActionLaws
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


namespace PartitionPilot.Forcing
universe u

noncomputable def forcingStageCode (P order top action : ZFSet.{u}) : ZFSet.{u} :=
  nonemptyTupleCode 3 ![P, order, top, action]

theorem forcingStageCode_eq_iff (P order top action P' order' top' action' : ZFSet.{u}) :
    forcingStageCode P order top action = forcingStageCode P' order' top' action' ↔
      P = P' ∧ order = order' ∧ top = top' ∧ action = action' := by
  simp only [forcingStageCode, nonemptyTupleCode, ZFSet.pair_inj]
  rfl

end PartitionPilot.Forcing



end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Definability_GroundVaryingPreparationRelations
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI




namespace PartitionPilot.Forcing.TransitiveGround
open SetFormula
universe u
variable (M : TransitiveGround.{u})

def varyingShape {n} (z packed nodes T : Fin n) : BoundedFormula (n + 22) :=
  let old := suffixIndex n 22
  let v := prefixIndex n 22
  let f := fun j : Fin 15 => v j.succ.succ.succ.succ.succ.succ.succ
  .conj (BoundedFormula.orderedPairFormula (old z) (v 3) (v 2))
    (.conj (BoundedFormula.orderedPairFormula (v 3) (v 0) (v 1))
      (.conj (BoundedFormula.nonemptyTupleFormula 14 (v 4) f)
        (.conj (BoundedFormula.pairMembershipFormula (v 0) (v 4) (old packed))
          (.conj (.equal (f 6) (old T)) (.equal (f 10) (old nodes))))))

end PartitionPilot.Forcing.TransitiveGround




end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Definability_PresentedRowAssignmentGraphs
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open scoped ZFSet

section

namespace PartitionPilot.Forcing
open SetRealization
universe u
variable {G R : Type u} [Group G] [PartialOrder R]
variable (a : PosetAction G R) (c : Presentation R) (t : Presentation G)
variable (Q J B : ZFSet.{u})

theorem presentedRowAssignmentGraph_entry (g : G) (r q : R) (A D : ZFSet.{u}) :
    ZFSet.pair (ZFSet.pair (t.encode g) (ZFSet.pair (c.encode r) A)) (ZFSet.pair (c.encode q) D) ∈
      rawRowAssignmentActionGraph t.carrier Q c.carrier (⋃₀ ⋃₀ Q) J (a.actionGraph c t) B ↔
    ZFSet.pair (c.encode r) A ∈ Q ∧ ZFSet.pair (c.encode q) D ∈ Q ∧
      a.iso g r = q ∧ D = relationImage A J (rawActionSection (t.encode g) B J) := by
  rw [pair_mem_rawRowAssignmentActionGraph]
  constructor
  · rintro ⟨_, first, second, _, _, _, _, row, image⟩
    exact ⟨first, second, (a.triple_mem_actionGraph c t g r q).1 row, image⟩
  · rintro ⟨first, second, row, image⟩
    exact ⟨t.encode_mem g, first, second, c.encode_mem r, pair_second_mem_doubleUnion first,
      c.encode_mem q, pair_second_mem_doubleUnion second,
      (a.triple_mem_actionGraph c t g r q).2 row, image⟩

theorem presentedRowAssignmentGraph_bound :
    rawRowAssignmentActionGraph t.carrier Q c.carrier (⋃₀ ⋃₀ Q) J (a.actionGraph c t) B ⊆
      ZFSet.prod (ZFSet.prod t.carrier Q) Q := by
  intro z hz
  unfold rawRowAssignmentActionGraph rowAssignmentActionGraph at hz
  exact (ZFSet.mem_sep.1 hz).1

omit [PartialOrder R] in
theorem exists_presentedRowAssignmentCoordinates
    {Q V z : ZFSet.{u}} (shape : Q ⊆ ZFSet.prod c.carrier V) (member : z ∈ Q) :
    ∃ r : R, ∃ A ∈ V, z = ZFSet.pair (c.encode r) A := by
  obtain ⟨r, hr, A, hA, rfl⟩ := ZFSet.mem_prod.1 (shape member)
  obtain ⟨r, rfl⟩ := (c.mem_carrier r).1 hr
  exact ⟨r, A, hA, rfl⟩

theorem presentedRowAssignmentGraph_function {V : ZFSet.{u}}
    (shape : Q ⊆ ZFSet.prod c.carrier V)
    (preserves : ∀ g : G, ∀ r : R, ∀ A,
      ZFSet.pair (c.encode r) A ∈ Q →
      ZFSet.pair (c.encode (a.iso g r)) (relationImage A J (rawActionSection (t.encode g) B J)) ∈ Q) :
    ZFSet.IsFunc (ZFSet.prod t.carrier Q) Q
      (rawRowAssignmentActionGraph t.carrier Q c.carrier (⋃₀ ⋃₀ Q) J (a.actionGraph c t) B) := by
  refine ⟨presentedRowAssignmentGraph_bound a c t Q J B, ?_⟩
  intro z hz
  obtain ⟨g, hg, p, hp, rfl⟩ := ZFSet.mem_prod.1 hz
  obtain ⟨g, rfl⟩ := (t.mem_carrier g).1 hg
  obtain ⟨r, A, _, rfl⟩ := exists_presentedRowAssignmentCoordinates c shape hp
  refine ⟨ZFSet.pair (c.encode (a.iso g r)) (relationImage A J (rawActionSection (t.encode g) B J)),
    (presentedRowAssignmentGraph_entry a c t Q J B g r _ A _).2
      ⟨hp, preserves g r A hp, rfl, rfl⟩, ?_⟩
  intro y edge
  have hy := (ZFSet.pair_mem_prod.1 (presentedRowAssignmentGraph_bound a c t Q J B edge)).2
  obtain ⟨q, D, _, rfl⟩ := exists_presentedRowAssignmentCoordinates c shape hy
  obtain ⟨_, _, row, rfl⟩ := (presentedRowAssignmentGraph_entry a c t Q J B g r q A D).1 edge
  rw [row]

end PartitionPilot.Forcing

end

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Definability_StructuralAssignmentActionFormulas
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
variable (collection : CollectionSchema M.sets)

def witnessBounds : BoundedFormula 20 :=
  let w := prefixIndex 10 10
  let old := suffixIndex 10 10
  .conj (.mem (w 0) (old 1))
    (.conj (BoundedFormula.orderedTripleFormula (old 0) (w 0) (w 1) (w 2))
      (.conj (.mem (w 3) (old 8)) (.conj (.mem (w 9) (old 9))
        (.conj (BoundedFormula.nonemptyTupleFormula 4 (w 9) ![w 3,w 4,w 5,w 6,w 7])
          (BoundedFormula.pairMembershipFormula (w 1) (w 2) (w 8))))))

def operationSlots : Fin 14 → Fin 20 :=
  let w := prefixIndex 10 10
  let old := suffixIndex 10 10
  extend (w 8) ![w 0,w 4,w 5,w 6,w 7,old 1,old 2,old 3,old 4,old 5,old 6,old 7,w 3]

end PartitionPilot.Forcing.TransitiveGround

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Geometry_RowAssignmentOrderLaws
attribute [-instance] _root_.OAI.PartitionPilot.Forcing.GroundMainPrefix.withTopSmall
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PartitionPilot.Forcing
universe u

theorem rowAssignmentOrder_partialOrder {Q C B r : ZFSet.{u}}
    (shape : Q ⊆ ZFSet.prod C B) (rows : PartialOrderCode C r) :
    PartialOrderCode Q (rowAssignmentOrder Q C B r) := by
  refine ⟨fun z member => (mem_rowAssignmentOrder Q C B r z).1 member |>.1, ?_, ?_, ?_⟩
  · intro z hz
    obtain ⟨q, hq, A, hA, rfl⟩ := ZFSet.mem_prod.1 (shape hz)
    exact (pair_mem_rowAssignmentOrder Q C B r q A q A).2
      ⟨hz, hz, hq, hA, hq, hA, rows.refl q hq, fun _ h => h⟩
  · intro x hx y hy xy yx
    obtain ⟨q, hq, A, hA, rfl⟩ := ZFSet.mem_prod.1 (shape hx)
    obtain ⟨p, hp, D, hD, rfl⟩ := ZFSet.mem_prod.1 (shape hy)
    have first := (pair_mem_rowAssignmentOrder Q C B r q A p D).1 xy
    have second := (pair_mem_rowAssignmentOrder Q C B r p D q A).1 yx
    have rowEq := rows.antisymm q hq p hp first.2.2.2.2.2.2.1 second.2.2.2.2.2.2.1
    have dataEq : A = D := ZFSet.ext (fun z =>
      ⟨fun h => second.2.2.2.2.2.2.2 h, fun h => first.2.2.2.2.2.2.2 h⟩)
    rw [rowEq, dataEq]
  · intro x hx y hy z hz xy yz
    obtain ⟨q, hq, A, hA, rfl⟩ := ZFSet.mem_prod.1 (shape hx)
    obtain ⟨p, hp, D, hD, rfl⟩ := ZFSet.mem_prod.1 (shape hy)
    obtain ⟨s, hs, E, hE, rfl⟩ := ZFSet.mem_prod.1 (shape hz)
    have first := (pair_mem_rowAssignmentOrder Q C B r q A p D).1 xy
    have second := (pair_mem_rowAssignmentOrder Q C B r p D s E).1 yz
    exact (pair_mem_rowAssignmentOrder Q C B r q A s E).2
      ⟨hx, hz, hq, hA, hs, hE,
        rows.trans q hq p hp s hs first.2.2.2.2.2.2.1 second.2.2.2.2.2.2.1,
        fun _ h => first.2.2.2.2.2.2.2 (second.2.2.2.2.2.2.2 h)⟩

end PartitionPilot.Forcing

end

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Geometry_GroundDefinableRowAssignmentOrders
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PartitionPilot.Forcing
universe u

theorem pair_mem_rawRowAssignmentOrder (Q rowOrder q A p D : ZFSet.{u}) :
    ZFSet.pair (ZFSet.pair q A) (ZFSet.pair p D) ∈ rawRowAssignmentOrder Q rowOrder ↔
      ZFSet.pair q A ∈ Q ∧ ZFSet.pair p D ∈ Q ∧ ZFSet.pair q p ∈ rowOrder ∧ D ⊆ A := by
  rw [rawRowAssignmentOrder, pair_mem_rowAssignmentOrder]
  constructor
  · rintro ⟨hq, hp, _, _, _, _, below, data⟩
    exact ⟨hq, hp, below, data⟩
  · rintro ⟨hq, hp, below, data⟩
    exact ⟨hq, hp, pair_first_mem_doubleUnion hq, pair_second_mem_doubleUnion hq,
      pair_first_mem_doubleUnion hp, pair_second_mem_doubleUnion hp, below, data⟩

theorem rawRowAssignmentOrder_eq {Q C B rowOrder : ZFSet.{u}} (shape : Q ⊆ ZFSet.prod C B) :
    rawRowAssignmentOrder Q rowOrder = rowAssignmentOrder Q C B rowOrder := by
  apply ZFSet.ext
  intro z
  constructor
  · intro member
    obtain ⟨x, hx, y, hy, rfl⟩ := ZFSet.mem_prod.1 ((mem_rowAssignmentOrder _ _ _ _ z).1 member).1
    obtain ⟨q, hq, A, hA, rfl⟩ := ZFSet.mem_prod.1 (shape hx)
    obtain ⟨p, hp, D, hD, rfl⟩ := ZFSet.mem_prod.1 (shape hy)
    obtain ⟨_, _, below, data⟩ := (pair_mem_rawRowAssignmentOrder _ _ _ _ _ _).1 member
    exact (pair_mem_rowAssignmentOrder _ _ _ _ _ _ _ _).2 ⟨hx, hy, hq, hA, hp, hD, below, data⟩
  · intro member
    obtain ⟨x, hx, y, hy, rfl⟩ := ZFSet.mem_prod.1 ((mem_rowAssignmentOrder _ _ _ _ z).1 member).1
    obtain ⟨q, _, A, _, rfl⟩ := ZFSet.mem_prod.1 (shape hx)
    obtain ⟨p, _, D, _, rfl⟩ := ZFSet.mem_prod.1 (shape hy)
    obtain ⟨_, _, _, _, _, _, below, data⟩ := (pair_mem_rowAssignmentOrder _ _ _ _ _ _ _ _).1 member
    exact (pair_mem_rawRowAssignmentOrder _ _ _ _ _ _).2 ⟨hx, hy, below, data⟩

end PartitionPilot.Forcing



end

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Forcing_GroundStructuralForcingHistoryConstruction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open scoped ZFSet



namespace PartitionPilot.Forcing
open SetFormula
universe u

noncomputable def rawFlatForcingStage
    (Q rows rowOrder rowTop rowAction G J assignmentAction : ZFSet.{u}) : ZFSet.{u} :=
  forcingStageCode Q (rawRowAssignmentOrder Q rowOrder) (ZFSet.pair rowTop ∅)
    (rawRowAssignmentActionGraph G Q rows (⋃₀ ⋃₀ Q) J rowAction assignmentAction)

end PartitionPilot.Forcing



end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Geometry_PresentedRowAssignmentTotality
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PartitionPilot.Forcing
open SetRealization
universe u
variable {G R : Type u} [Group G] [PartialOrder R]
variable (a : PosetAction G R) (c : Presentation R) (t : Presentation G)
variable (Q J B : ZFSet.{u})

theorem presentedRowAssignmentGraph_totalValue {V : ZFSet.{u}}
    (shape : Q ⊆ ZFSet.prod c.carrier V)
    (function : ZFSet.IsFunc (ZFSet.prod t.carrier Q) Q
      (rawRowAssignmentActionGraph t.carrier Q c.carrier Q.sUnion.sUnion J (a.actionGraph c t) B))
    (g : G) (r : R) (A : ZFSet.{u}) (member : ZFSet.pair (c.encode r) A ∈ Q) :
    ZFSet.pair (c.encode (a.iso g r)) (relationImage A J (rawActionSection (t.encode g) B J)) ∈ Q ∧
    ZFSet.pair (ZFSet.pair (t.encode g) (ZFSet.pair (c.encode r) A))
      (ZFSet.pair (c.encode (a.iso g r)) (relationImage A J (rawActionSection (t.encode g) B J))) ∈
        rawRowAssignmentActionGraph t.carrier Q c.carrier Q.sUnion.sUnion J (a.actionGraph c t) B := by
  obtain ⟨y, edge, _unique⟩ := function.2 (ZFSet.pair (t.encode g) (ZFSet.pair (c.encode r) A))
    (ZFSet.pair_mem_prod.2 ⟨t.encode_mem g, member⟩)
  have hy := (ZFSet.pair_mem_prod.1 (function.1 edge)).2
  obtain ⟨q, D, _, rfl⟩ := exists_presentedRowAssignmentCoordinates c shape hy
  obtain ⟨_, _, row, data⟩ := (presentedRowAssignmentGraph_entry a c t Q J B g r q A D).1 edge
  rw [← row, data] at hy edge
  exact ⟨hy, edge⟩

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

namespace PartitionPilot.Forcing.SetFormula

def rectangleOrderFormula : BoundedFormula 15 :=
  .conj (BoundedFormula.tripleMembershipFormula 3 5 1 13)
    (.conj (BoundedFormula.tripleMembershipFormula 2 5 0 13)
      (.conj (BoundedFormula.pairMembershipFormula 4 1 11)
        (BoundedFormula.pairMembershipFormula 4 0 11)))

end PartitionPilot.Forcing.SetFormula

end


end OAI
end


