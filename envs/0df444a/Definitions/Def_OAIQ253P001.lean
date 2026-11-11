-- Prove2me | Definitions.Def_OAIQ253P001
-- name    : OAIQ253P001
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-11T05:43:13.774862+00:00
-- url     : https://prove2.me/theorems/87ba0c23-0b20-477e-9891-3c55da50e012
-- title:
--   Definitions bundle OAIQ253P001 of the split of OpenAI, The Partition Principle does not imply Choice
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.PartitionPilot.Forcing.TransitiveGround.exists_model_partitionPrinciple_without_choice`, carved from OpenAI's openai/math development (OpenAI, *The Partition Principle does not imply Choice*, OpenAI Math Release, September 24, 2026, result family 244, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 731 declarations of OpenAI's Lean: 377 definitions, 27 inductive types or structures, 9 instances and 318 theorems. The definitions and types are `OAI.PartitionPilot.Forcing.BoundedFormula.cutGraphProductMember`, `OAI.PartitionPilot.Forcing.BoundedFormula.equivalenceClassFormula`, `OAI.PartitionPilot.Forcing.BoundedFormula.equivalenceClassesFormula`, `OAI.PartitionPilot.Forcing.BoundedFormula.equivalenceClassifierEntryFormula`, `OAI.PartitionPilot.Forcing.BoundedFormula.equivalenceRelationFormula`, `OAI.PartitionPilot.Forcing.BoundedFormula.externalActorSymbolEntryFormula`, `OAI.PartitionPilot.Forcing.BoundedFormula.familyEvaluationEntryFormula`, `OAI.PartitionPilot.Forcing.BoundedFormula.familySetEntryFormula`, `OAI.PartitionPilot.Forcing.BoundedFormula.finiteWordFormula`, `OAI.PartitionPilot.Forcing.BoundedFormula.finiteWordLengthEntryFormula`, `OAI.PartitionPilot.Forcing.BoundedFormula.finiteWordMapEntryFormula`, `OAI.PartitionPilot.Forcing.BoundedFormula.finiteWordMapFormula`, `OAI.PartitionPilot.Forcing.BoundedFormula.firstRelationEntryFormula`, `OAI.PartitionPilot.Forcing.BoundedFormula.graphDiagonalFormula`, `OAI.PartitionPilot.Forcing.BoundedFormula.graphValueMemberFormula`, `OAI.PartitionPilot.Forcing.BoundedFormula.identityInsertionGraphEntryFormula`, `OAI.PartitionPilot.Forcing.BoundedFormula.iffFormula`, `OAI.PartitionPilot.Forcing.BoundedFormula.imageProfilePositiveFormula`, `OAI.PartitionPilot.Forcing.BoundedFormula.indexedCarrierLabelFormula`, `OAI.PartitionPilot.Forcing.BoundedFormula.indexedRelationLiftEntryFormula`, `OAI.PartitionPilot.Forcing.BoundedFormula.indexedSuborderEntryFormula`, `OAI.PartitionPilot.Forcing.BoundedFormula.indexedValueLiftEntryFormula`, `OAI.PartitionPilot.Forcing.BoundedFormula.injectionDiagonalFormula`, `OAI.PartitionPilot.Forcing.BoundedFormula.intervalEmbeddingCandidateFormula`, `OAI.PartitionPilot.Forcing.BoundedFormula.intervalEmbeddingFormula`, `OAI.PartitionPilot.Forcing.BoundedFormula.intervalEmbeddingRelationEntryFormula`, `OAI.PartitionPilot.Forcing.BoundedFormula.intervalHeightCandidateFormula`, `OAI.PartitionPilot.Forcing.BoundedFormula.intervalHeightFormula`, `OAI.PartitionPilot.Forcing.BoundedFormula.intervalHeightRelationEntryFormula`, `OAI.PartitionPilot.Forcing.BoundedFormula.intervalNextCandidateFormula`, `OAI.PartitionPilot.Forcing.BoundedFormula.intervalSequenceEntryFormula`, `OAI.PartitionPilot.Forcing.BoundedFormula.layerBirthFiberFormula`, `OAI.PartitionPilot.Forcing.BoundedFormula.leastIntervalNextCandidateFormula`, `OAI.PartitionPilot.Forcing.BoundedFormula.leastSupportEntryFormula`, `OAI.PartitionPilot.Forcing.BoundedFormula.leastSupportFormula`, `OAI.PartitionPilot.Forcing.BoundedFormula.liftOldEntryFormula`, `OAI.PartitionPilot.Forcing.BoundedFormula.literalTaskFieldEntryFormula`, `OAI.PartitionPilot.Forcing.BoundedFormula.literalTaskFormula`, `OAI.PartitionPilot.Forcing.BoundedFormula.localizedWitnessFormula`, `OAI.PartitionPilot.Forcing.BoundedFormula.nestedActionTripleFormula` and 364 more.
--
--   **Sources.** They come from these modules of lean/OAI/SetTheory, in whole or in part: `PartitionPrinciple_Definability_BatchGraphSetFormulas`, `PartitionPrinciple_Definability_BoundedAtomicEquality`, `PartitionPrinciple_Definability_CodedEqualityRelations`, `PartitionPrinciple_Definability_CodedFilterImages`, `PartitionPrinciple_Definability_CodedInjectiveCones`, `PartitionPrinciple_Definability_CodedRangeCompletion`, `PartitionPrinciple_Definability_CompressionExternalStepRealization`, `PartitionPrinciple_Definability_CountableSetFormulas`, `PartitionPrinciple_Definability_DepthSlotCodes`, `PartitionPrinciple_Definability_EquivalenceClassCodes`, `PartitionPrinciple_Definability_ExternalWordRewriteRelations`, `PartitionPrinciple_Definability_FiniteWordMapCodes`, `PartitionPrinciple_Definability_GraphValueMembershipFormula`, `PartitionPrinciple_Definability_GroundBelowFunctionGraphs`, `PartitionPrinciple_Definability_GroundExternalRequestSetRecognition`, `PartitionPrinciple_Definability_GroundFlatCopyGraphs`, `PartitionPrinciple_Definability_GroundFunctionRangeFamilies`, `PartitionPrinciple_Definability_GroundLiftedRowTupleProvenance`, `PartitionPrinciple_Definability_GroundPackedRefinementFormulaData`, `PartitionPrinciple_Definability_GroundPairCompositions`, `PartitionPrinciple_Definability_GroundPartialFunctionSpaces`, `PartitionPrinciple_Definability_GroundQuantifiedGraphFormulas`, `PartitionPrinciple_Definability_GroundRationalCodes`, `PartitionPrinciple_Definability_GroundRefinementPairClassGraphs`, `PartitionPrinciple_Definability_GroundRegularFormulas`, `PartitionPrinciple_Definability_GroundTaggedComponentGraphs`, `PartitionPrinciple_Definability_GroundVaryingPreparationRelations`, `PartitionPrinciple_Definability_IndexedMixedOperationLiftCodes`, `PartitionPrinciple_Definability_IndexedOperationLiftCodes`, `PartitionPrinciple_Definability_IndexedSubstructureCodes`, `PartitionPrinciple_Definability_IndexedValueLiftCodes`, `PartitionPrinciple_Definability_IntervalEmbeddingFormulas`, `PartitionPrinciple_Definability_IntervalHeightFormulas`, `PartitionPrinciple_Definability_IntervalSequenceFormulas`, `PartitionPrinciple_Definability_LeastSlotOwnerCodes`, `PartitionPrinciple_Definability_LiftedCompressionFormulas`, `PartitionPrinciple_Definability_MainLimitCoverageFormulas`, `PartitionPrinciple_Definability_MapFamilyApplicationGraphs`, `PartitionPrinciple_Definability_NatUnionCodes`, `PartitionPrinciple_Definability_NaturalStepFormulas`, `PartitionPrinciple_Definability_NonemptyTupleFields`, `PartitionPrinciple_Definability_PairPushFilterFamilies`, `PartitionPrinciple_Definability_ParentSupportCodes`, `PartitionPrinciple_Definability_PreparedCertificateCodes`, `PartitionPrinciple_Definability_PresentedGroupCodes`, `PartitionPrinciple_Definability_RawCheckFormulas`, `PartitionPrinciple_Definability_RawRenameFormulas`, `PartitionPrinciple_Definability_RecursivePrimitiveFormulas`, `PartitionPrinciple_Definability_RefinementValidityCodes`, `PartitionPrinciple_Definability_RowAssignmentCutGraphLaws`, `PartitionPrinciple_Definability_RowAssignmentTransitionFormulas`, `PartitionPrinciple_Definability_SeparationFulfillmentCodes`, `PartitionPrinciple_Definability_SerializedChronologyFormulas`, `PartitionPrinciple_Definability_SmallFunctionActionFormulas`, `PartitionPrinciple_Definability_SupportedCertificateRelations`, `PartitionPrinciple_Definability_TaggedSumPresentations`, `PartitionPrinciple_Definability_TaskCapFamilyCodes`, `PartitionPrinciple_Definability_TaskRepresentativeCodes`, `PartitionPrinciple_Definability_TupleRelationProducts`, `PartitionPrinciple_Definability_UnionEntryFormula`, `PartitionPrinciple_Definability_VisibilityProfileFormulas`, `PartitionPrinciple_Forcing_ActionPostcompositionCodes`, `PartitionPrinciple_Forcing_AllSupportFamilies`, `PartitionPrinciple_Forcing_CodedDenseOrders`, `PartitionPrinciple_Forcing_CodedRecursiveTaskActions`, `PartitionPrinciple_Forcing_ConditionQuantifiers`, `PartitionPrinciple_Forcing_GenericPartialFunctions`, `PartitionPrinciple_Forcing_GreedyAntichainTraces`, `PartitionPrinciple_Forcing_GroundFixedPoints`, `PartitionPrinciple_Forcing_GroundMainConditionalTotality`, `PartitionPrinciple_Forcing_GroundMainFinalStructuralCommonSupportInduction`, `PartitionPrinciple_Forcing_GroundMixtureNames`, `PartitionPrinciple_Forcing_GroundNameSequenceValues`, `PartitionPrinciple_Forcing_GroundPairNameFamilies`, `PartitionPrinciple_Forcing_GroundProductActions`, `PartitionPrinciple_Forcing_GroundPushFilters`, `PartitionPrinciple_Forcing_GroundRecursiveActions`, `PartitionPrinciple_Forcing_GroundRecursiveRowNameActions`, `PartitionPrinciple_Forcing_GroundStoredPreparedFamilyActions`, `PartitionPrinciple_Forcing_GroundUnionSizeWitnesses`, `PartitionPrinciple_Forcing_GroundVaryingFamilyEvaluation`, `PartitionPrinciple_Forcing_IndexedTupleNames`, `PartitionPrinciple_Forcing_OrbitPairGraphNames`, `PartitionPrinciple_Forcing_RefinementCoarseImageNames`, `PartitionPrinciple_Forcing_RelationActionFamilies`, `PartitionPrinciple_Forcing_TaskTransportCodes`, `PartitionPrinciple_Forcing_UniformGroundNames`, `PartitionPrinciple_Forcing_UniformGroundSizeWitnesses`, `PartitionPrinciple_Forcing_UniqueFiberForcing`, `PartitionPrinciple_Geometry_AssignmentNestedSplices`, `PartitionPrinciple_Geometry_CheckCertificates`, `PartitionPrinciple_Geometry_CompleteProjectionPredensity`, `PartitionPrinciple_Geometry_FiniteIterationTraces`, `PartitionPrinciple_Geometry_FiniteWordOperations`, `PartitionPrinciple_Geometry_GroundAbsentLiftRangeCollisions`, `PartitionPrinciple_Geometry_GroundCantorDiagonal`, `PartitionPrinciple_Geometry_GroundCodedBinaryHeights`, `PartitionPrinciple_Geometry_GroundCompressionHeightSteps`, `PartitionPrinciple_Geometry_GroundCompressionStampBounds`, `PartitionPrinciple_Geometry_GroundCompressionStarIncidence`, `PartitionPrinciple_Geometry_GroundDefinableRowAssignmentOrders`, `PartitionPrinciple_Geometry_GroundEligibleCaps`, `PartitionPrinciple_Geometry_GroundExternalAlphabetInversion`, `PartitionPrinciple_Geometry_GroundExternalGenerators`, `PartitionPrinciple_Geometry_GroundExternalGroupEmbeddings`, `PartitionPrinciple_Geometry_GroundExternalLocalHeightSelection`, `PartitionPrinciple_Geometry_GroundExternalTileSlotSupports`, `PartitionPrinciple_Geometry_GroundFairPreparationMonotonicity`, `PartitionPrinciple_Geometry_GroundFamilyValueUnions`, `PartitionPrinciple_Geometry_GroundFinalInsertionExceptions`, `PartitionPrinciple_Geometry_GroundFiniteWordLaws`, `PartitionPrinciple_Geometry_GroundFiniteWordLength`, `PartitionPrinciple_Geometry_GroundHeightPushforward`, `PartitionPrinciple_Geometry_GroundIdentityInsertionTasks`, `PartitionPrinciple_Geometry_GroundIndexedClassInclusions`, `PartitionPrinciple_Geometry_GroundIndexedOperationLifts`, `PartitionPrinciple_Geometry_GroundIntervalEmbeddingRelation`, `PartitionPrinciple_Geometry_GroundLiteralTaskFieldRecognition`, `PartitionPrinciple_Geometry_GroundMeetGeneratorSteps`, `PartitionPrinciple_Geometry_GroundNaturalFamilyShift`, `PartitionPrinciple_Geometry_GroundPartialCoverPartitions`, `PartitionPrinciple_Geometry_GroundPreparationFamilyImages`, `PartitionPrinciple_Geometry_GroundRawLayerPushforward`, `PartitionPrinciple_Geometry_GroundRefinementAssignmentLabelEntries`, `PartitionPrinciple_Geometry_GroundRetainedPreparationSelections`, `PartitionPrinciple_Geometry_GroundRowAssignmentCuts`, `PartitionPrinciple_Geometry_GroundTaskRepresentativeRecognition`, `PartitionPrinciple_Geometry_GroundTemplateIntervalFamilies`, `PartitionPrinciple_Geometry_GroundTileStarIncidence`, `PartitionPrinciple_Geometry_GroundTwoPointHeights`, `PartitionPrinciple_Geometry_GroundVisibilitySupportIncidence`, `PartitionPrinciple_Geometry_IntervalEmbeddingFamilyCodes`, `PartitionPrinciple_Geometry_LiftedCompressionFunctions`, `PartitionPrinciple_Geometry_RectangleFulfillmentAtBound`, `PartitionPrinciple_Geometry_RowAssignmentOrderLaws`, `PartitionPrinciple_Geometry_RowPositionBounds`, `PartitionPrinciple_Geometry_TemplateHeightRangeCodes`, `PartitionPrinciple_Geometry_TileStarIncomingCodes`, `PartitionPrinciple_Geometry_UniformAtomicEquality`, `PartitionPrinciple_Models_GroundChoiceEnumerationSteps`, `PartitionPrinciple_Models_GroundCoherentHeightChoices`, `PartitionPrinciple_Models_GroundCountableQuotients`, `PartitionPrinciple_Models_GroundExternalWordQuotient`, `PartitionPrinciple_Models_GroundInjectionRestrictions`, `PartitionPrinciple_Models_GroundQuotientBinaryOperations`, `PartitionPrinciple_Models_GroundQuotientUnaryOperations`, `PartitionPrinciple_Models_GroundRefinementQuotientNames`, `PartitionPrinciple_Models_GroundSuccessorInjections`, `PartitionPrinciple_Models_GroundSupportedEqualityChoices`, `PartitionPrinciple_Transfinite_CodedMainPrefixSystems`, `PartitionPrinciple_Transfinite_ExternalChronologyStageLaws`, `PartitionPrinciple_Transfinite_GroundBatchBirths`, `PartitionPrinciple_Transfinite_GroundChronologicalBasis`, `PartitionPrinciple_Transfinite_GroundChronologyFieldAppend`, `PartitionPrinciple_Transfinite_GroundChronologyPairs`, `PartitionPrinciple_Transfinite_GroundCoinitialOperations`, `PartitionPrinciple_Transfinite_GroundCompressionBirthData`, `PartitionPrinciple_Transfinite_GroundCompressionPrefixGraphs`, `PartitionPrinciple_Transfinite_GroundCountableFunctionClosure`, `PartitionPrinciple_Transfinite_GroundCountableLayerCodes`, `PartitionPrinciple_Transfinite_GroundCountableProducts`, `PartitionPrinciple_Transfinite_GroundIntervalRecursion`, `PartitionPrinciple_Transfinite_GroundLayerBirthFibers`, `PartitionPrinciple_Transfinite_GroundLinkedMainStageCodeLaws`, `PartitionPrinciple_Transfinite_GroundMainPrefixConePreservation`, `PartitionPrinciple_Transfinite_GroundMainPrefixLimitCoverageConstruction`, `PartitionPrinciple_Transfinite_GroundMainPrefixLimitCoverageGraph`, `PartitionPrinciple_Transfinite_GroundMainPrefixLimitGroupLaws`, `PartitionPrinciple_Transfinite_GroundMainPrefixPreservedSeeds`, `PartitionPrinciple_Transfinite_GroundMainStageFromCodes`, `PartitionPrinciple_Transfinite_GroundOmegaOneTaskBearingSuccessorFunction`, `PartitionPrinciple_Transfinite_GroundOrdinalImagePartitions`, `PartitionPrinciple_Transfinite_GroundOrdinalOrderCodes`, `PartitionPrinciple_Transfinite_GroundStageOneAssignmentUnions`, `PartitionPrinciple_Transfinite_GroundStageOneOrder`, `PartitionPrinciple_Transfinite_GroundStandardInaccessible`, `PartitionPrinciple_Transfinite_GroundTaskBearingSuccessorDecoding`, `PartitionPrinciple_Transfinite_GroundTwoStageMainDiagram`, `PartitionPrinciple_Transfinite_MainPrefixSelectedTraceLaws`, `PartitionPrinciple_Transfinite_NonzeroLimitOrdinalCodes`, `PartitionPrinciple_Transfinite_OrdinalRecursionTraces`, `PartitionPrinciple_Transfinite_OrdinalSetCodes`, `PartitionPrinciple_Transfinite_OwnerBirthLayers`, `PartitionPrinciple_Transfinite_RecursiveLiftAgreement`, `PartitionPrinciple_Transfinite_RecursiveStateFieldEnvironments`, `PartitionPrinciple_Transfinite_SetRankBounds`.
--
--   **Imports.** It imports the published bundle `Def_PartitionPrinciple`.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ253P002` and `OAIQ253P003`.
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

section
-- module Solutions.OAIQ253_PP.Compat
namespace OAI

/-! Compatibility with the newer Lean core OpenAI's code was written against: lemmas it uses by
names this environment (Lean 4.33.1, Mathlib 0df444a) does not have yet. Each is the
corresponding `if_pos` / `if_neg` / `dif_pos` / `dif_neg`. The `dite` forms are stated as
`dite p a b`, not with the `if hp : p then …` notation: its eta-expanded lambdas form is a higher-order pattern
that `rw` cannot find (DepthThree, PeriodicTiling 2026-10-25). -/
section OAICompat434
theorem ite_eq_left {α : Sort _} {c : Prop} {_ : Decidable c} {a b : α} (h : c) :
    (if c then a else b) = a := if_pos h

/-- Mathlib's newer `TensorProduct.inductionOn` (no `zero` case: it is the `tmul` case at
`0 ⊗ₜ 0`); ours has only `TensorProduct.induction_on`, which asks for one. Not named
`TensorProduct.inductionOn`: inside `namespace OAI` that would make `open TensorProduct` open
`OAI.TensorProduct` instead of Mathlib's. -/
@[elab_as_elim]
theorem tensorInductionOn {R M N : Type*} [CommSemiring R] [AddCommMonoid M] [AddCommMonoid N]
    [Module R M] [Module R N] {motive : TensorProduct R M N → Prop} (z : TensorProduct R M N)
    (tmul : ∀ x y, motive (TensorProduct.tmul R x y))
    (add : ∀ x y, motive x → motive y → motive (x + y)) : motive z :=
  TensorProduct.induction_on z (by simpa using tmul 0 0) tmul add
/-- The first projection of a probability measure on a product: found by instance search in d13f23b
(total `Measure.map`), here a measurable map. -/
instance isProbabilityMeasure_map_fst {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    {μ : MeasureTheory.Measure (α × β)} [MeasureTheory.IsProbabilityMeasure μ] :
    MeasureTheory.IsProbabilityMeasure (μ.map Prod.fst) :=
  MeasureTheory.Measure.isProbabilityMeasure_map measurable_fst.aemeasurable
instance isProbabilityMeasure_map_snd {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    {μ : MeasureTheory.Measure (α × β)} [MeasureTheory.IsProbabilityMeasure μ] :
    MeasureTheory.IsProbabilityMeasure (μ.map Prod.snd) :=
  MeasureTheory.Measure.isProbabilityMeasure_map measurable_snd.aemeasurable
instance isProbabilityMeasure_map_subtype_val {α : Type*} [MeasurableSpace α] {p : α → Prop}
    {μ : MeasureTheory.Measure {a // p a}} [MeasureTheory.IsProbabilityMeasure μ] :
    MeasureTheory.IsProbabilityMeasure (μ.map Subtype.val) :=
  MeasureTheory.Measure.isProbabilityMeasure_map measurable_subtype_coe.aemeasurable
/-- Mathlib d13f23b's `YoungDiagram.card_transpose`. -/
@[simp]
theorem _root_.YoungDiagram.card_transpose (μ : YoungDiagram) : μ.transpose.card = μ.card := by
  unfold YoungDiagram.card
  apply Finset.card_bij (fun c _ => c.swap)
  · intro c hc
    have : c ∈ μ.transpose := hc
    rw [YoungDiagram.mem_transpose] at this
    exact this
  · intro a _ b _ h
    simpa using h
  · intro b hb
    refine ⟨b.swap, ?_, by simp⟩
    show b.swap ∈ μ.transpose
    rw [YoungDiagram.mem_transpose]
    simpa using hb
/-- For a measurable equivalence `e`, `IsProbabilityMeasure (μ.map e)` is found by instance search
(Mathlib d13f23b finds it for every map `f`: there `Measure.map` of a non-measurable map is a Dirac
mass, here it is `0`, so only the measurable case can be shimmed). -/
instance isProbabilityMeasure_map_measurableEquiv {α β : Type*} [MeasurableSpace α]
    [MeasurableSpace β] {μ : MeasureTheory.Measure α} [MeasureTheory.IsProbabilityMeasure μ]
    (e : α ≃ᵐ β) : MeasureTheory.IsProbabilityMeasure (μ.map e) :=
  MeasureTheory.Measure.isProbabilityMeasure_map e.measurable.aemeasurable
/-- `simp` closes `2 ≤ ∞` in `WithTop ℕ∞` (the smoothness order) in Mathlib d13f23b; ours has the
lemma only for `1` and casts (AffineBernstein, `isSymmSndFDerivAt (by simp)`, 2026-10-26). -/
@[simp]
theorem ofNat_le_infty (n : ℕ) [n.AtLeastTwo] : (no_index (OfNat.ofNat n) : WithTop ℕ∞) ≤ ((⊤ : ℕ∞) : WithTop ℕ∞) :=
  ENat.LEInfty.out
section Y
instance closedSubmoduleNormedAddCommGroup {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    (K : ClosedSubmodule 𝕜 E) : NormedAddCommGroup K :=
  inferInstanceAs (NormedAddCommGroup K.toSubmodule)
instance closedSubmoduleNormedSpace {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    (K : ClosedSubmodule 𝕜 E) : NormedSpace 𝕜 K :=
  inferInstanceAs (NormedSpace 𝕜 K.toSubmodule)
instance closedSubmoduleInner {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
    (K : ClosedSubmodule 𝕜 E) : InnerProductSpace 𝕜 K :=
  inferInstanceAs (InnerProductSpace 𝕜 K.toSubmodule)
end Y

/-- The underlying ⋆-subalgebra of a von Neumann algebra is norm closed, found by instance search in
d13f23b (Kadison similarity, oaiq-075). -/
instance vonNeumannToStarSubalgebraIsClosed {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] (P : VonNeumannAlgebra H) : IsClosed (P.toStarSubalgebra : Set (H →L[ℂ] H)) := by
  have := Set.isClosed_centralizer (Set.centralizer (P.carrier))
  rw [P.centralizer_centralizer'] at this
  exact this
/-- A closed commutative ⋆-subalgebra of a C⋆-algebra is a commutative C⋆-algebra, found by instance search
in d13f23b (Kadison similarity, oaiq-075). A def, made a local instance by the port only in modules naming
`CommCStarAlgebra` or `IsMulCommutative` (`oaiport.comm_cstar_line`): as a global instance it made `whnf` time out in
FactorGeneration modules with their own `CStarAlgebra` instances on a subalgebra (oaiq-122). -/
@[reducible]
noncomputable def starSubalgebraCommCStarAlgebra {B : Type*} [CStarAlgebra B] (A : StarSubalgebra ℂ B)
    [IsClosed (A : Set B)] [IsMulCommutative A] : CommCStarAlgebra A :=
  { StarSubalgebra.cstarAlgebra A with
    mul_comm := fun a b => IsMulCommutative.is_comm.comm a b }
section OAIVecLookup
variable {α : Type _}
@[simp] theorem vecCons3_one (a b c : α) : (![a, b, c] : Fin 3 → α) 1 = b := rfl
@[simp] theorem vecCons3_two (a b c : α) : (![a, b, c] : Fin 3 → α) 2 = c := rfl
@[simp] theorem vecCons4_one (a b c d : α) : (![a, b, c, d] : Fin 4 → α) 1 = b := rfl
@[simp] theorem vecCons4_two (a b c d : α) : (![a, b, c, d] : Fin 4 → α) 2 = c := rfl
@[simp] theorem vecCons4_three (a b c d : α) : (![a, b, c, d] : Fin 4 → α) 3 = d := rfl
end OAIVecLookup
section OAIVecTail
variable {α : Type _}
@[simp] theorem vecConsTail1_1 (x : α) (f : Fin 1 → α) : (Matrix.vecCons x f : Fin 2 → α) 1 = f 0 := rfl
@[simp] theorem vecConsTail2_1 (x : α) (f : Fin 2 → α) : (Matrix.vecCons x f : Fin 3 → α) 1 = f 0 := rfl
@[simp] theorem vecConsTail2_2 (x : α) (f : Fin 2 → α) : (Matrix.vecCons x f : Fin 3 → α) 2 = f 1 := rfl
@[simp] theorem vecConsTail3_1 (x : α) (f : Fin 3 → α) : (Matrix.vecCons x f : Fin 4 → α) 1 = f 0 := rfl
@[simp] theorem vecConsTail3_2 (x : α) (f : Fin 3 → α) : (Matrix.vecCons x f : Fin 4 → α) 2 = f 1 := rfl
@[simp] theorem vecConsTail3_3 (x : α) (f : Fin 3 → α) : (Matrix.vecCons x f : Fin 4 → α) 3 = f 2 := rfl
@[simp] theorem vecConsTail4_1 (x : α) (f : Fin 4 → α) : (Matrix.vecCons x f : Fin 5 → α) 1 = f 0 := rfl
@[simp] theorem vecConsTail4_2 (x : α) (f : Fin 4 → α) : (Matrix.vecCons x f : Fin 5 → α) 2 = f 1 := rfl
@[simp] theorem vecConsTail4_3 (x : α) (f : Fin 4 → α) : (Matrix.vecCons x f : Fin 5 → α) 3 = f 2 := rfl
@[simp] theorem vecConsTail4_4 (x : α) (f : Fin 4 → α) : (Matrix.vecCons x f : Fin 5 → α) 4 = f 3 := rfl
end OAIVecTail
@[simp] theorem fin3_mk_0 (h : 0 < 3) : (⟨0, h⟩ : Fin 3) = 0 := rfl
@[simp] theorem fin3_mk_1 (h : 1 < 3) : (⟨1, h⟩ : Fin 3) = 1 := rfl
@[simp] theorem fin3_mk_2 (h : 2 < 3) : (⟨2, h⟩ : Fin 3) = 2 := rfl
@[simp] theorem fin4_mk_0 (h : 0 < 4) : (⟨0, h⟩ : Fin 4) = 0 := rfl
@[simp] theorem fin4_mk_1 (h : 1 < 4) : (⟨1, h⟩ : Fin 4) = 1 := rfl
@[simp] theorem fin4_mk_2 (h : 2 < 4) : (⟨2, h⟩ : Fin 4) = 2 := rfl
@[simp] theorem fin4_mk_3 (h : 3 < 4) : (⟨3, h⟩ : Fin 4) = 3 := rfl
@[simp] theorem fin5_mk_0 (h : 0 < 5) : (⟨0, h⟩ : Fin 5) = 0 := rfl
@[simp] theorem fin5_mk_1 (h : 1 < 5) : (⟨1, h⟩ : Fin 5) = 1 := rfl
@[simp] theorem fin5_mk_2 (h : 2 < 5) : (⟨2, h⟩ : Fin 5) = 2 := rfl
@[simp] theorem fin5_mk_3 (h : 3 < 5) : (⟨3, h⟩ : Fin 5) = 3 := rfl
@[simp] theorem fin5_mk_4 (h : 4 < 5) : (⟨4, h⟩ : Fin 5) = 4 := rfl
/-- `norm_num` cannot decide equalities of `Fin` literals here (oaiq-091). -/
@[simp] theorem fin3_lit_0_1 : ((0 : Fin 3) = 1) ↔ False := by decide
@[simp] theorem fin3_lit_0_2 : ((0 : Fin 3) = 2) ↔ False := by decide
@[simp] theorem fin3_lit_1_0 : ((1 : Fin 3) = 0) ↔ False := by decide
@[simp] theorem fin3_lit_1_2 : ((1 : Fin 3) = 2) ↔ False := by decide
@[simp] theorem fin3_lit_2_0 : ((2 : Fin 3) = 0) ↔ False := by decide
@[simp] theorem fin3_lit_2_1 : ((2 : Fin 3) = 1) ↔ False := by decide
@[simp] theorem fin4_lit_0_1 : ((0 : Fin 4) = 1) ↔ False := by decide
@[simp] theorem fin4_lit_0_2 : ((0 : Fin 4) = 2) ↔ False := by decide
@[simp] theorem fin4_lit_0_3 : ((0 : Fin 4) = 3) ↔ False := by decide
@[simp] theorem fin4_lit_1_0 : ((1 : Fin 4) = 0) ↔ False := by decide
@[simp] theorem fin4_lit_1_2 : ((1 : Fin 4) = 2) ↔ False := by decide
@[simp] theorem fin4_lit_1_3 : ((1 : Fin 4) = 3) ↔ False := by decide
@[simp] theorem fin4_lit_2_0 : ((2 : Fin 4) = 0) ↔ False := by decide
@[simp] theorem fin4_lit_2_1 : ((2 : Fin 4) = 1) ↔ False := by decide
@[simp] theorem fin4_lit_2_3 : ((2 : Fin 4) = 3) ↔ False := by decide
@[simp] theorem fin4_lit_3_0 : ((3 : Fin 4) = 0) ↔ False := by decide
@[simp] theorem fin4_lit_3_1 : ((3 : Fin 4) = 1) ↔ False := by decide
@[simp] theorem fin4_lit_3_2 : ((3 : Fin 4) = 2) ↔ False := by decide
@[simp] theorem fin5_lit_0_1 : ((0 : Fin 5) = 1) ↔ False := by decide
@[simp] theorem fin5_lit_0_2 : ((0 : Fin 5) = 2) ↔ False := by decide
@[simp] theorem fin5_lit_0_3 : ((0 : Fin 5) = 3) ↔ False := by decide
@[simp] theorem fin5_lit_0_4 : ((0 : Fin 5) = 4) ↔ False := by decide
@[simp] theorem fin5_lit_1_0 : ((1 : Fin 5) = 0) ↔ False := by decide
@[simp] theorem fin5_lit_1_2 : ((1 : Fin 5) = 2) ↔ False := by decide
@[simp] theorem fin5_lit_1_3 : ((1 : Fin 5) = 3) ↔ False := by decide
@[simp] theorem fin5_lit_1_4 : ((1 : Fin 5) = 4) ↔ False := by decide
@[simp] theorem fin5_lit_2_0 : ((2 : Fin 5) = 0) ↔ False := by decide
@[simp] theorem fin5_lit_2_1 : ((2 : Fin 5) = 1) ↔ False := by decide
@[simp] theorem fin5_lit_2_3 : ((2 : Fin 5) = 3) ↔ False := by decide
@[simp] theorem fin5_lit_2_4 : ((2 : Fin 5) = 4) ↔ False := by decide
@[simp] theorem fin5_lit_3_0 : ((3 : Fin 5) = 0) ↔ False := by decide
@[simp] theorem fin5_lit_3_1 : ((3 : Fin 5) = 1) ↔ False := by decide
@[simp] theorem fin5_lit_3_2 : ((3 : Fin 5) = 2) ↔ False := by decide
@[simp] theorem fin5_lit_3_4 : ((3 : Fin 5) = 4) ↔ False := by decide
@[simp] theorem fin5_lit_4_0 : ((4 : Fin 5) = 0) ↔ False := by decide
@[simp] theorem fin5_lit_4_1 : ((4 : Fin 5) = 1) ↔ False := by decide
@[simp] theorem fin5_lit_4_2 : ((4 : Fin 5) = 2) ↔ False := by decide
@[simp] theorem fin5_lit_4_3 : ((4 : Fin 5) = 3) ↔ False := by decide
/-- Mathlib d13f23b's `MeasurableSpace Circle` (Mathlib.MeasureTheory.Group.Circle): the subtype structure. A def,
turned on as a local instance in the modules that use the characters `𝐞`/`fourierChar`/`probChar` (q141). -/
@[reducible] def circleMeasurableSpace : MeasurableSpace Circle :=
  inferInstanceAs <| MeasurableSpace <| Subtype (· ∈ Submonoid.unitSphere ℂ)
end OAICompat434

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Transfinite_OrdinalSetCodes
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PartitionPilot.SetRealization

universe u

noncomputable def ordinalCode (o : Ordinal.{u}) : ZFSet.{u} :=
  ZFSet.range (fun i : Set.Iio o => ordinalCode i.val)
termination_by o
decreasing_by exact i.property

theorem ordinalCode_eq (o : Ordinal.{u}) :
    ordinalCode o = ZFSet.range (fun i : Set.Iio o => ordinalCode i.val) := by
  exact ordinalCode.eq_def o

theorem rank_ordinalCode (o : Ordinal.{u}) : ZFSet.rank (ordinalCode o) = o := by
  have wf : WellFounded ((· < ·) : Ordinal.{u} → Ordinal.{u} → Prop) := wellFounded_lt
  induction o using wf.induction with
  | h o ih =>
    rw [ordinalCode_eq, ZFSet.rank_range]
    have ranks : (fun i : Set.Iio o => Order.succ (ZFSet.rank (ordinalCode i.val))) =
        (fun i : Set.Iio o => Order.succ i.val) := by
      funext i
      rw [ih i.val i.property]
    simp_rw [ranks, Order.succ_eq_add_one]
    apply le_antisymm (Ordinal.iSup_add_one_le fun index => index.property)
    by_contra! smaller
    exact lt_irrefl _ (Ordinal.lt_iSup_add_one
      (fun index : Set.Iio o => index.val) ⟨_, smaller⟩)

theorem ordinalCode_injective : Function.Injective (ordinalCode.{u}) := by
  intro a b eq
  have ranks := congrArg ZFSet.rank eq
  simpa only [rank_ordinalCode] using ranks

theorem mem_ordinalCode_iff (a b : Ordinal.{u}) :
    ordinalCode a ∈ ordinalCode b ↔ a < b := by
  rw [ordinalCode_eq b, ZFSet.mem_range]
  constructor
  · rintro ⟨i, eq⟩
    exact (ordinalCode_injective eq) ▸ i.property
  · intro h
    exact ⟨⟨a, h⟩, rfl⟩

theorem mem_ordinalCode {x : ZFSet.{u}} {o : Ordinal.{u}} :
    x ∈ ordinalCode o ↔ ∃ a < o, ordinalCode a = x := by
  rw [ordinalCode_eq o, ZFSet.mem_range]
  constructor
  · rintro ⟨i, eq⟩
    exact ⟨i.val, i.property, eq⟩
  · rintro ⟨a, h, eq⟩
    exact ⟨⟨a, h⟩, eq⟩

end PartitionPilot.SetRealization

end

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Transfinite_SetRankBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PartitionPilot.SetRealization

universe u
variable {o : Ordinal.{u}} (limit : Order.IsSuccLimit o) {x y : ZFSet.{u}}
include limit

theorem rank_product_lt (hx : ZFSet.rank x < o) (hy : ZFSet.rank y < o) :
    ZFSet.rank (ZFSet.prod x y) < o := by
  have sub : ZFSet.prod x y ⊆ ZFSet.powerset (ZFSet.powerset (x ∪ y)) := by
    intro z hz
    rw [ZFSet.prod, ZFSet.pairSep] at hz
    exact (ZFSet.mem_sep.1 hz).1
  have bound := ZFSet.rank_mono sub
  rw [ZFSet.rank_powerset, ZFSet.rank_powerset, ZFSet.rank_union] at bound
  exact bound.trans_lt (limit.succ_lt (limit.succ_lt (max_lt hx hy)))

end PartitionPilot.SetRealization

end

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Forcing_GenericPartialFunctions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace PartitionPilot.Forcing

section

universe u
variable {P : Type u} [Preorder P]

def Dense (D : Set P) : Prop := ∀ p, ∃ q, q ≤ p ∧ q ∈ D

structure ConditionFilter (P : Type u) [Preorder P] where
  mem : P → Prop
  nonempty : ∃ p, mem p
  upward : ∀ ⦃p q⦄, mem p → p ≤ q → mem q
  directed : ∀ ⦃p q⦄, mem p → mem q → ∃ r, mem r ∧ r ≤ p ∧ r ≤ q

namespace ConditionFilter

def Meets (F : ConditionFilter P) (D : Set P) : Prop := ∃ p, F.mem p ∧ p ∈ D

def GenericFor (F : ConditionFilter P) (family : Set (Set P)) : Prop :=
  ∀ D ∈ family, Dense D → F.Meets D

theorem top_mem [OrderTop P] (F : ConditionFilter P) : F.mem ⊤ := by
  rcases F.nonempty with ⟨p, hp⟩
  exact F.upward hp le_top

theorem compatible (F : ConditionFilter P) {p q : P} (hp : F.mem p) (hq : F.mem q) :
    ∃ r, r ≤ p ∧ r ≤ q := by
  rcases F.directed hp hq with ⟨r, _, rp, rq⟩
  exact ⟨r, rp, rq⟩

end ConditionFilter

end



section

universe u
variable {P : Type u} [Preorder P]






def Compatible (p q : P) : Prop := ∃ r, r ≤ p ∧ r ≤ q

def DenseBelow (p : P) (D : Set P) : Prop := ∀ q, q ≤ p → ∃ r, r ≤ q ∧ r ∈ D

def Localized (p : P) (D : Set P) : Set P := {q | q ∈ D ∨ ¬ Compatible q p}

theorem localized_dense {p : P} {D : Set P} (dense : DenseBelow p D) : Dense (Localized p D) := by
  classical
  intro q
  by_cases compat : Compatible q p
  · obtain ⟨r, rq, rp⟩ := compat
    obtain ⟨t, tr, ht⟩ := dense r rp
    exact ⟨t, tr.trans rq, Or.inl ht⟩
  · exact ⟨q, le_rfl, Or.inr compat⟩

theorem ConditionFilter.meets_below (H : ConditionFilter P) {family : Set (Set P)}
    (generic : H.GenericFor family) {p : P} (hp : H.mem p) {D : Set P}
    (registered : Localized p D ∈ family) (dense : DenseBelow p D) : H.Meets D := by
  obtain ⟨q, hq, good | bad⟩ := generic _ registered (localized_dense dense)
  · exact ⟨q, hq, good⟩
  · exact False.elim (bad (H.compatible hq hp))

theorem denseBelow_mono {p : P} {D E : Set P} (dense : DenseBelow p D) (included : D ⊆ E) :
    DenseBelow p E := by
  intro q qp
  obtain ⟨r, rq, hr⟩ := dense q qp
  exact ⟨r, rq, included hr⟩






end



end PartitionPilot.Forcing

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Definability_CountableSetFormulas
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace PartitionPilot.Forcing


namespace SetFormula

universe u v

theorem map_extend {A : Type u} {B : Type v} {n : Nat}
    (f : A → B) (x : A) (env : Fin n → A) :
    (fun i => f (extend x env i)) = extend (f x) (fun i => f (env i)) := by
  funext i
  refine Fin.cases ?_ (fun j => ?_) i
  · rfl
  · rfl

end SetFormula



namespace SetFormula

universe u v

def extendMany {n : Nat} {A : Type v} : (k : Nat) →
    (Fin k → A) → (Fin n → A) → Fin (n + k) → A
  | 0, _, env => env
  | k + 1, fields, env => extend (fields 0) (extendMany k (fun j => fields j.succ) env)

def prefixIndex (n : Nat) : (k : Nat) → Fin k → Fin (n + k)
  | 0, i => Fin.elim0 i
  | k + 1, i => Fin.cases 0 (fun j => (prefixIndex n k j).succ) i

def suffixIndex (n : Nat) : (k : Nat) → Fin n → Fin (n + k)
  | 0, i => i
  | k + 1, i => (suffixIndex n k i).succ

theorem extendMany_prefix {n : Nat} {A : Type v} (k : Nat)
    (fields : Fin k → A) (env : Fin n → A) (i : Fin k) :
    extendMany k fields env (prefixIndex n k i) = fields i := by
  induction k with
  | zero => exact Fin.elim0 i
  | succ k ih =>
    exact Fin.cases rfl (fun j => ih (fun a => fields a.succ) j) i

theorem extendMany_suffix {n : Nat} {A : Type v} (k : Nat)
    (fields : Fin k → A) (env : Fin n → A) (i : Fin n) :
    extendMany k fields env (suffixIndex n k i) = env i := by
  induction k with
  | zero => rfl
  | succ k ih => exact ih (fun a => fields a.succ)

theorem extendMany_members {n : Nat} {A : Type v} {U : Set A} (k : Nat)
    (fields : Fin k → A) (env : Fin n → A)
    (fieldMembers : ∀ i, fields i ∈ U) (envMembers : ∀ i, env i ∈ U) :
    ∀ i, extendMany k fields env i ∈ U := by
  induction k with
  | zero => exact envMembers
  | succ k ih =>
    intro i
    exact Fin.cases (fieldMembers 0)
      (ih (fun i => fields i.succ) (fun i => fieldMembers i.succ)) i

def exBlock {n : Nat} : (k : Nat) → SetFormula (n + k) → SetFormula n
  | 0, body => body
  | k + 1, body => exBlock k (ex body)

def conjBlock {n : Nat} : (k : Nat) → (Fin k → SetFormula n) → SetFormula n
  | 0, _ => .all (.equal 0 0)
  | k + 1, clauses => .conj (clauses 0) (conjBlock k (fun i => clauses i.succ))

theorem realize_conjBlock (U : Set ZFSet.{u}) {n : Nat} (k : Nat)
    (clauses : Fin k → SetFormula n) (env : Fin n → ZFSet.{u}) :
    Realize U (conjBlock k clauses) env ↔ ∀ i, Realize U (clauses i) env := by
  induction k with
  | zero =>
    exact ⟨fun _ i => Fin.elim0 i, fun _ _ _ => rfl⟩
  | succ k ih =>
    change (Realize U (clauses 0) env ∧ Realize U (conjBlock k (fun i => clauses i.succ)) env) ↔ _
    rw [ih]
    exact ⟨fun h => Fin.cases h.1 h.2, fun h => ⟨h 0, fun i => h i.succ⟩⟩

end SetFormula



namespace SetFormula
universe u

def allBlock {n : Nat} : (k : Nat) → SetFormula (n + k) → SetFormula n
  | 0, body => body
  | k + 1, body => allBlock k (.all body)

theorem realize_allBlock (U : Set ZFSet.{u}) {n : Nat} (k : Nat)
    (body : SetFormula (n + k)) (env : Fin n → ZFSet.{u}) :
    Realize U (allBlock k body) env ↔
      ∀ fields : Fin k → ZFSet.{u}, (∀ i, fields i ∈ U) →
        Realize U body (extendMany k fields env) := by
  induction k with
  | zero =>
    exact ⟨fun h _ _ => h, fun h => h Fin.elim0 (fun i => Fin.elim0 i)⟩
  | succ k ih =>
    rw [allBlock, ih]
    constructor
    · intro h fields ground
      exact h (fun i => fields i.succ) (fun i => ground i.succ) (fields 0) (ground 0)
    · intro h fields ground x hx
      exact h (Fin.cases x fields) (Fin.cases hx ground)

end SetFormula



end PartitionPilot.Forcing

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Definability_NatUnionCodes
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI



namespace PartitionPilot.Forcing

open scoped ZFSet

universe u

def graphRestriction (A f : ZFSet.{u}) : ZFSet.{u} :=
  ZFSet.sep (fun z => z ∈ ZFSet.prod A (⋃₀ ⋃₀ f)) f

theorem pair_first_mem_doubleUnion {x y f : ZFSet.{u}}
    (entry : ZFSet.pair x y ∈ f) : x ∈ ⋃₀ ⋃₀ f := by
  exact ZFSet.mem_sUnion.2 ⟨{x}, ZFSet.mem_sUnion.2
    ⟨ZFSet.pair x y, entry, ZFSet.mem_pair.2 (Or.inl rfl)⟩,
    ZFSet.mem_singleton.2 rfl⟩

theorem graphRestriction_subset (A f : ZFSet.{u}) : graphRestriction A f ⊆ f :=
  fun _ h => (ZFSet.mem_sep.1 h).1

end PartitionPilot.Forcing



namespace PartitionPilot.Forcing
universe u

def NatUnionCode (stages : Nat → ZFSet.{u}) (union : ZFSet.{u}) : Prop :=
  ∀ x, x ∈ union ↔ ∃ n, x ∈ stages n

namespace NatUnionCode

theorem subset {stages : Nat → ZFSet.{u}} {union : ZFSet.{u}}
    (code : NatUnionCode stages union) (n : Nat) : stages n ⊆ union :=
  fun _ hx => (code _).2 ⟨n, hx⟩

end NatUnionCode

end PartitionPilot.Forcing

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Definability_ExternalWordRewriteRelations
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section



namespace PartitionPilot.Forcing.ExternalWordRewrite

universe u
abbrev Alphabet (J S : Type u) := J ⊕ (S × Bool)

variable {J S : Type u} [Group J]

inductive Atomic : List (Alphabet J S) → List (Alphabet J S) → Prop
  | old_one : Atomic [.inl 1] []
  | old_mul (g h : J) : Atomic [.inl g, .inl h] [.inl (g * h)]
  | cancel (s : S) (b : Bool) : Atomic [.inr (s, b), .inr (s, !b)] []

def Step (xs ys : List (Alphabet J S)) : Prop :=
  ∃ pre post l r, Atomic l r ∧
    ((xs = pre ++ l ++ post ∧ ys = pre ++ r ++ post) ∨
      (ys = pre ++ l ++ post ∧ xs = pre ++ r ++ post))

def Path : List (Alphabet J S) → List (Alphabet J S) → Prop :=
  Relation.ReflTransGen Step

def congruence (J S : Type u) [Group J] : Con (FreeMonoid (Alphabet J S)) :=
  conGen Atomic

theorem Atomic.step {xs ys : List (Alphabet J S)} (h : Atomic xs ys) : Step xs ys :=
  ⟨[], [], xs, ys, h, Or.inl ⟨by simp, by simp⟩⟩

theorem Step.symm {xs ys : List (Alphabet J S)} (h : Step xs ys) : Step ys xs := by
  obtain ⟨pre, post, l, r, atom, eq⟩ := h
  exact ⟨pre, post, l, r, atom, eq.symm⟩

theorem Step.append_left (p : List (Alphabet J S)) {xs ys : List (Alphabet J S)}
    (h : Step xs ys) : Step (p ++ xs) (p ++ ys) := by
  obtain ⟨pre, post, l, r, atom, eq⟩ := h
  refine ⟨p ++ pre, post, l, r, atom, ?_⟩
  rcases eq with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact Or.inl ⟨by simp only [List.append_assoc], by simp only [List.append_assoc]⟩
  · exact Or.inr ⟨by simp only [List.append_assoc], by simp only [List.append_assoc]⟩

theorem Step.append_right (p : List (Alphabet J S)) {xs ys : List (Alphabet J S)}
    (h : Step xs ys) : Step (xs ++ p) (ys ++ p) := by
  obtain ⟨pre, post, l, r, atom, eq⟩ := h
  refine ⟨pre, post ++ p, l, r, atom, ?_⟩
  rcases eq with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact Or.inl ⟨by simp only [List.append_assoc], by simp only [List.append_assoc]⟩
  · exact Or.inr ⟨by simp only [List.append_assoc], by simp only [List.append_assoc]⟩

theorem Path.symm {xs ys : List (Alphabet J S)} (h : Path xs ys) : Path ys xs := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ step ih => exact ih.head step.symm

theorem Path.append {xs ys zs ws : List (Alphabet J S)} (first : Path xs ys)
    (second : Path zs ws) : Path (xs ++ zs) (ys ++ ws) :=
  (first.lift (fun l => l ++ zs) (fun _ _ step => step.append_right zs)).trans
    (second.lift (fun l => ys ++ l) (fun _ _ step => step.append_left ys))

theorem Step.to_congruence {xs ys : List (Alphabet J S)} (h : Step xs ys) :
    congruence J S xs ys := by
  obtain ⟨pre, post, l, r, atom, eq⟩ := h
  have core : congruence J S l r := ConGen.Rel.of (M := FreeMonoid (Alphabet J S)) _ _ atom
  have contextual : congruence J S (pre ++ l ++ post) (pre ++ r ++ post) :=
    (congruence J S).mul ((congruence J S).mul ((congruence J S).refl pre) core)
      ((congruence J S).refl post)
  rcases eq with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact contextual
  · exact (congruence J S).symm contextual

theorem path_iff_conGen (xs ys : List (Alphabet J S)) :
    Path xs ys ↔ congruence J S xs ys := by
  constructor
  · intro path
    induction path with
    | refl => exact (congruence J S).refl _
    | tail path step ih => exact (congruence J S).trans ih step.to_congruence
  · intro h
    change ConGen.Rel (M := FreeMonoid (Alphabet J S)) Atomic xs ys at h
    induction h with
    | of _ _ atom => exact Relation.ReflTransGen.single atom.step
    | refl _ => exact Relation.ReflTransGen.refl
    | symm _ ih => exact ih.symm
    | trans _ _ ih jh => exact ih.trans jh
    | mul _ _ ih jh => exact ih.append jh

end PartitionPilot.Forcing.ExternalWordRewrite

end

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Forcing_OrbitPairGraphNames
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI



namespace PartitionPilot.Forcing

open SetRealization
universe u

namespace TransitiveGround

variable (M : TransitiveGround.{u})
  {P : Type u}

theorem pair_left {x y : ZFSet.{u}} (h : ZFSet.pair x y ∈ M.sets) : x ∈ M.sets :=
  M.transitive (M.transitive h (ZFSet.mem_pair.2 (Or.inl rfl))) (ZFSet.mem_singleton.2 rfl)

theorem pair_right {x y : ZFSet.{u}} (h : ZFSet.pair x y ∈ M.sets) : y ∈ M.sets :=
  M.transitive (M.transitive h (ZFSet.mem_pair.2 (Or.inr rfl))) (ZFSet.mem_pair.2 (Or.inr rfl))

end TransitiveGround
end PartitionPilot.Forcing

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Definability_UnionEntryFormula
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


section

namespace PartitionPilot.Forcing.SetFormula

def unorderedPairFormula {n : Nat} (z x y : Fin n) : SetFormula n :=
  .all (.conj
    (imp (.mem 0 z.succ) (disj (.equal 0 x.succ) (.equal 0 y.succ)))
    (imp (disj (.equal 0 x.succ) (.equal 0 y.succ)) (.mem 0 z.succ)))

def orderedPairFormula {n : Nat} (z x y : Fin n) : SetFormula n :=
  ex (ex (.conj (unorderedPairFormula z.succ.succ 1 0)
    (.conj (unorderedPairFormula 1 x.succ.succ x.succ.succ)
      (unorderedPairFormula 0 x.succ.succ y.succ.succ))))

def pairMembershipFormula {n : Nat} (x y z : Fin n) : SetFormula n :=
  ex (.conj (orderedPairFormula 0 x.succ y.succ) (.mem 0 z.succ))

end PartitionPilot.Forcing.SetFormula

end



section

namespace PartitionPilot.Forcing.SetFormula

def unionEntryFormula : SetFormula 4 :=
  ex <| ex <| ex <| ex <| ex <|
    .conj (orderedPairFormula 5 4 3) <|
    .conj (.mem 3 7) <|
    .conj (.mem 1 7) <|
    .conj (.mem 0 7) <|
    .conj (pairMembershipFormula 2 1 6) <|
    .conj (pairMembershipFormula 4 0 2) <|
    .conj (pairMembershipFormula 3 1 8) (pairMembershipFormula 3 0 8)

end PartitionPilot.Forcing.SetFormula

end


end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Geometry_AssignmentNestedSplices
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PartitionPilot.Forcing
universe u

def assignmentCut (levels alpha A : ZFSet.{u}) : ZFSet.{u} :=
  ZFSet.sep (fun z => ∃ xi ∈ alpha, ZFSet.pair z xi ∈ levels) A

def assignmentUpper (levels alpha A : ZFSet.{u}) : ZFSet.{u} :=
  ZFSet.sep (fun z => z ∉ assignmentCut levels alpha A) A

def assignmentSplice (levels alpha Aq Ap : ZFSet.{u}) : ZFSet.{u} :=
  assignmentCut levels alpha Aq ∪ assignmentUpper levels alpha Ap

theorem mem_assignmentCut (levels alpha A z : ZFSet.{u}) :
    z ∈ assignmentCut levels alpha A ↔
      z ∈ A ∧ ∃ xi ∈ alpha, ZFSet.pair z xi ∈ levels :=
  ZFSet.mem_sep

theorem mem_assignmentUpper (levels alpha A z : ZFSet.{u}) :
    z ∈ assignmentUpper levels alpha A ↔
      z ∈ A ∧ ¬ ∃ xi ∈ alpha, ZFSet.pair z xi ∈ levels := by
  rw [assignmentUpper, ZFSet.mem_sep, mem_assignmentCut]
  constructor
  · rintro ⟨hz, outside⟩
    exact ⟨hz, fun lower => outside ⟨hz, lower⟩⟩
  · rintro ⟨hz, outside⟩
    exact ⟨hz, fun lower => outside lower.2⟩

theorem mem_assignmentSplice (levels alpha Aq Ap z : ZFSet.{u}) :
    z ∈ assignmentSplice levels alpha Aq Ap ↔
      (z ∈ Aq ∧ ∃ xi ∈ alpha, ZFSet.pair z xi ∈ levels) ∨
      (z ∈ Ap ∧ ¬ ∃ xi ∈ alpha, ZFSet.pair z xi ∈ levels) := by
  rw [assignmentSplice, ZFSet.mem_union, mem_assignmentCut, mem_assignmentUpper]

theorem assignmentCut_subset (levels alpha A : ZFSet.{u}) :
    assignmentCut levels alpha A ⊆ A :=
  fun _ hz => ((mem_assignmentCut levels alpha A _).1 hz).1

theorem assignmentSplice_subset (levels alpha Aq Ap : ZFSet.{u}) :
    assignmentSplice levels alpha Aq Ap ⊆ Aq ∪ Ap := by
  intro z hz
  rcases (mem_assignmentSplice levels alpha Aq Ap z).1 hz with lower | upper
  · exact ZFSet.mem_union.2 (Or.inl lower.1)
  · exact ZFSet.mem_union.2 (Or.inr upper.1)

theorem assignmentCut_mono {levels alpha A B : ZFSet.{u}} (subset : A ⊆ B) :
    assignmentCut levels alpha A ⊆ assignmentCut levels alpha B := by
  intro z hz
  obtain ⟨hz, lower⟩ := (mem_assignmentCut levels alpha A z).1 hz
  exact (mem_assignmentCut levels alpha B z).2 ⟨subset hz, lower⟩

theorem assignmentCut_nested {levels alpha beta A : ZFSet.{u}}
    (below : alpha ⊆ beta) :
    assignmentCut levels alpha (assignmentCut levels beta A) =
      assignmentCut levels alpha A := by
  apply ZFSet.ext
  intro z
  rw [mem_assignmentCut, mem_assignmentCut, mem_assignmentCut]
  constructor
  · rintro ⟨⟨hz, _⟩, lower⟩
    exact ⟨hz, lower⟩
  · rintro ⟨hz, xi, hxi, entry⟩
    exact ⟨⟨hz, xi, below hxi, entry⟩, xi, hxi, entry⟩

theorem assignmentCut_eq_of_lower {levels alpha A : ZFSet.{u}}
    (lower : ∀ z ∈ A, ∃ xi ∈ alpha, ZFSet.pair z xi ∈ levels) :
    assignmentCut levels alpha A = A := by
  apply ZFSet.ext
  intro z
  rw [mem_assignmentCut]
  exact ⟨fun hz => hz.1, fun hz => ⟨hz, lower z hz⟩⟩

theorem assignmentCut_full {J eta levels A : ZFSet.{u}}
    (function : ZFSet.IsFunc J eta levels) (subset : A ⊆ J) :
    assignmentCut levels eta A = A := by
  apply assignmentCut_eq_of_lower
  intro z hz
  obtain ⟨xi, entry, _⟩ := function.2 z (subset hz)
  exact ⟨xi, (ZFSet.pair_mem_prod.1 (function.1 entry)).2, entry⟩

theorem assignmentCut_splice (levels alpha Aq Ap : ZFSet.{u}) :
    assignmentCut levels alpha (assignmentSplice levels alpha Aq Ap) =
      assignmentCut levels alpha Aq := by
  apply ZFSet.ext
  intro z
  rw [mem_assignmentCut, mem_assignmentSplice, mem_assignmentCut]
  constructor
  · rintro ⟨lower | upper, level⟩
    · exact lower
    · exact False.elim (upper.2 level)
  · intro lower
    exact ⟨Or.inl lower, lower.2⟩

theorem assignmentSplice_extends {levels alpha Aq Ap : ZFSet.{u}}
    (contains : assignmentCut levels alpha Ap ⊆ assignmentCut levels alpha Aq) :
    Ap ⊆ assignmentSplice levels alpha Aq Ap := by
  classical
  intro z hz
  by_cases lower : ∃ xi ∈ alpha, ZFSet.pair z xi ∈ levels
  · exact ZFSet.mem_union.2 (Or.inl (contains
      ((mem_assignmentCut levels alpha Ap z).2 ⟨hz, lower⟩)))
  · exact (mem_assignmentSplice levels alpha Aq Ap z).2 (Or.inr ⟨hz, lower⟩)

end PartitionPilot.Forcing



namespace PartitionPilot.Forcing
universe u
variable {levels alpha beta : ZFSet.{u}} (below : alpha ⊆ beta)
include below

theorem assignmentCut_splice_below (Aq Ap : ZFSet.{u}) :
    assignmentCut levels alpha (assignmentSplice levels beta Aq Ap) =
      assignmentCut levels alpha Aq := by
  calc
    _ = assignmentCut levels alpha
        (assignmentCut levels beta (assignmentSplice levels beta Aq Ap)) :=
      (assignmentCut_nested below).symm
    _ = assignmentCut levels alpha (assignmentCut levels beta Aq) := by rw [assignmentCut_splice]
    _ = _ := assignmentCut_nested below

end PartitionPilot.Forcing

end

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Transfinite_OrdinalRecursionTraces
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PartitionPilot.SetRealization

universe u

theorem ordinalCode_zero : ordinalCode (0 : Ordinal.{u}) = ∅ := by
  apply ZFSet.ext
  intro x
  rw [mem_ordinalCode]
  exact ⟨fun ⟨_, lower, _⟩ => False.elim (not_lt_of_ge bot_le lower),
    fun h => False.elim (ZFSet.notMem_empty x h)⟩

theorem ordinalCode_succ (o : Ordinal.{u}) :
    ordinalCode (Order.succ o) = insert (ordinalCode o) (ordinalCode o) := by
  apply ZFSet.ext
  intro x
  rw [mem_ordinalCode, ZFSet.mem_insert_iff]
  constructor
  · rintro ⟨a, ha, rfl⟩
    rcases lt_or_eq_of_le (Order.lt_succ_iff.1 ha) with lower | eq
    · exact Or.inr ((mem_ordinalCode_iff a o).2 lower)
    · exact Or.inl (congrArg ordinalCode eq)
  · rintro (rfl | member)
    · exact ⟨o, Order.lt_succ o, rfl⟩
    · obtain ⟨a, ha, eq⟩ := mem_ordinalCode.1 member
      exact ⟨a, ha.trans (Order.lt_succ o), eq⟩

theorem ordinalCode_subset_iff (a b : Ordinal.{u}) : ordinalCode a ⊆ ordinalCode b ↔ a ≤ b := by
  constructor
  · intro subset
    have ranks := ZFSet.rank_mono subset
    simpa only [rank_ordinalCode] using ranks
  · intro lower x hx
    obtain ⟨o, ho, rfl⟩ := mem_ordinalCode.1 hx
    exact (mem_ordinalCode_iff o b).2 (ho.trans_le lower)

end PartitionPilot.SetRealization

namespace PartitionPilot.Forcing

open SetRealization
open scoped ZFSet
universe u

theorem ordinalSetProperty_member {x y : ZFSet.{u}}
    (hx : ordinalSetProperty x) (hy : y ∈ x) : ordinalSetProperty y :=
  ⟨hx.2 y hy, fun z hz => hx.2 z (hx.1 y hy z hz)⟩

theorem setTransitive_ordinalCode (o : Ordinal.{u}) : setTransitive (ordinalCode o) := by
  intro y hy z hz
  obtain ⟨b, hb, rfl⟩ := mem_ordinalCode.1 hy
  obtain ⟨a, ha, rfl⟩ := mem_ordinalCode.1 hz
  exact (mem_ordinalCode_iff a o).2 (ha.trans hb)

theorem ordinalSetProperty_ordinalCode (o : Ordinal.{u}) : ordinalSetProperty (ordinalCode o) := by
  refine ⟨setTransitive_ordinalCode o, ?_⟩
  intro y hy
  obtain ⟨a, _, rfl⟩ := mem_ordinalCode.1 hy
  exact setTransitive_ordinalCode a

theorem ordinalSetProperty_eq_code_rank (x : ZFSet.{u}) :
    ordinalSetProperty x → x = ordinalCode (ZFSet.rank x) := by
  induction x using ZFSet.inductionOn with
  | h x ih =>
    intro hx
    apply ZFSet.ext
    intro y
    constructor
    · intro hy
      have child := ih y hy (ordinalSetProperty_member hx hy)
      rw [child]
      exact (mem_ordinalCode_iff (ZFSet.rank y) (ZFSet.rank x)).2 (ZFSet.rank_lt_of_mem hy)
    · intro hy
      obtain ⟨o, ho, eq⟩ := mem_ordinalCode.1 hy
      obtain ⟨z, hz, lower⟩ := ZFSet.lt_rank_iff.1 ho
      have child := ih z hz (ordinalSetProperty_member hx hz)
      rcases lt_or_eq_of_le lower with less | equal
      · have member : y ∈ z := by
          rw [child, ← eq]
          exact (mem_ordinalCode_iff o (ZFSet.rank z)).2 less
        exact hx.1 z hz y member
      · have same : z = y := child.trans ((congrArg ordinalCode equal).symm.trans eq)
        exact same ▸ hz

theorem ordinalSetProperty_iff (x : ZFSet.{u}) :
    ordinalSetProperty x ↔ ∃ o : Ordinal.{u}, x = ordinalCode o := by
  constructor
  · intro hx
    exact ⟨ZFSet.rank x, ordinalSetProperty_eq_code_rank x hx⟩
  · rintro ⟨o, rfl⟩
    exact ordinalSetProperty_ordinalCode o

theorem ordinalSetProperty_empty : ordinalSetProperty (∅ : ZFSet.{u}) := by
  rw [← ordinalCode_zero]
  exact ordinalSetProperty_ordinalCode 0

theorem ordinalSetProperty_succ {x : ZFSet.{u}} (hx : ordinalSetProperty x) :
    ordinalSetProperty (insert x x) := by
  obtain ⟨o, rfl⟩ := (ordinalSetProperty_iff x).1 hx
  rw [← ordinalCode_succ]
  exact ordinalSetProperty_ordinalCode (Order.succ o)

theorem ordinalSetProperty_sUnion {x : ZFSet.{u}}
    (members : ∀ y ∈ x, ordinalSetProperty y) : ordinalSetProperty (⋃₀ x) := by
  constructor
  · intro y hy z hz
    obtain ⟨a, ha, ya⟩ := ZFSet.mem_sUnion.1 hy
    exact ZFSet.mem_sUnion.2 ⟨a, ha, (members a ha).1 y ya z hz⟩
  · intro y hy
    obtain ⟨a, ha, ya⟩ := ZFSet.mem_sUnion.1 hy
    exact (members a ha).2 y ya

end PartitionPilot.Forcing

end


end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Definability_PresentedGroupCodes
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI



namespace PartitionPilot.Forcing

universe u

namespace SetFormula

def exactSetFormula {n} (output : Fin n) (entry : SetFormula (n + 1)) : SetFormula n :=
  .all (.conj (imp (.mem 0 output.succ) entry) (imp entry (.mem 0 output.succ)))

end SetFormula

end PartitionPilot.Forcing



namespace PartitionPilot.Forcing

universe u

namespace BoundedFormula

open SetFormula

def topFormula {n} (c r t : Fin n) : BoundedFormula n :=
  .conj (.mem t c) (.allMem c (pairMembershipFormula 0 t.succ r.succ))

end BoundedFormula

end PartitionPilot.Forcing



namespace PartitionPilot.Forcing.BoundedFormula

open SetFormula
universe u

def nestedActionTripleFormula {n} (z g a b c d : Fin n) : BoundedFormula n :=
  let lift4 (j : Fin n) := j.succ.succ.succ.succ
  let lift6 (j : Fin n) := j.succ.succ.succ.succ.succ.succ
  exMem z (exMem 0 (exMem z.succ.succ (exMem 0
    (.conj (orderedPairFormula (lift4 z) 2 0)
      (.conj (orderedPairFormula 0 (lift4 c) (lift4 d))
        (exMem 2 (exMem 0 (.conj (orderedPairFormula 4 (lift6 g) 0)
          (orderedPairFormula 0 (lift6 a) (lift6 b))))))))))

end PartitionPilot.Forcing.BoundedFormula



end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Definability_GroundPartialFunctionSpaces
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace PartitionPilot.Forcing

open SetFormula
universe u

structure GroundDefinableFunction (M : TransitiveGround.{u}) {n : Nat}
    (f : (Fin n → ZFSet.{u}) → ZFSet.{u}) where
  formula : SetFormula (n + 1)
  closed : ∀ env, (∀ i, env i ∈ M.sets) → f env ∈ M.sets
  correct : ∀ env, (∀ i, env i ∈ M.sets) → ∀ z ∈ M.sets,
    Realize M.sets formula (extend z env) ↔ z = f env

namespace GroundDefinableFunction

def projection (M : TransitiveGround.{u}) {n : Nat} (j : Fin n) :
    GroundDefinableFunction M (fun env => env j) where
  formula := .equal 0 j.succ
  closed := fun _ members => members j
  correct := fun _ _ _ _ => Iff.rfl

end GroundDefinableFunction

end PartitionPilot.Forcing


namespace PartitionPilot.Forcing

universe u

namespace BoundedFormula

open SetFormula

def partialFunctionFormula {n} (x y p : Fin n) : BoundedFormula n :=
  .conj (relationBetweenFormula x y p) (.allMem x (.allMem y.succ (.allMem y.succ.succ
    (imp (.conj (pairMembershipFormula 2 1 p.succ.succ.succ)
      (pairMembershipFormula 2 0 p.succ.succ.succ)) (.equal 1 0)))))

end BoundedFormula

end PartitionPilot.Forcing



namespace PartitionPilot.Forcing
open SetRealization SetFormula
universe u
namespace BoundedFormula

def familySetEntryFormula {n} (z T one : Fin n) : BoundedFormula n :=
  exMem T (orderedPairFormula z.succ 0 one.succ)

end BoundedFormula

namespace SetFormula

def familySetCodeFormula : SetFormula 3 :=
  exactSetFormula 0 (BoundedFormula.familySetEntryFormula 0 2 3).toFormula

end SetFormula

end PartitionPilot.Forcing



end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Models_GroundInjectionRestrictions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PartitionPilot.Forcing.InjectionCode

universe u

theorem restrict {D N f Q : ZFSet.{u}} (h : InjectionCode D N f) (subset : Q ⊆ D) :
    InjectionCode Q N (ZFSet.sep (fun z => z ∈ ZFSet.prod Q N) f) := by
  refine ⟨⟨fun _ hz => (ZFSet.mem_sep.1 hz).2, ?_⟩, ?_⟩
  · intro x hx
    obtain ⟨y, rel, unique⟩ := h.function.2 x (subset hx)
    have hy := (ZFSet.pair_mem_prod.1 (h.function.1 rel)).2
    exact ⟨y, ZFSet.mem_sep.2 ⟨rel, ZFSet.pair_mem_prod.2 ⟨hx, hy⟩⟩,
      fun z hz => unique z (ZFSet.mem_sep.1 hz).1⟩
  · intro x y z hx hy
    exact h.injective x y z (ZFSet.mem_sep.1 hx).1 (ZFSet.mem_sep.1 hy).1

end PartitionPilot.Forcing.InjectionCode

end

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Definability_NonemptyTupleFields
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI



namespace PartitionPilot.Forcing
universe u

noncomputable def refinementIndexBound (L P V W : ZFSet.{u}) : ZFSet.{u} :=
  ZFSet.prod L (ZFSet.prod P (ZFSet.prod P (ZFSet.prod V (ZFSet.prod W W))))

end PartitionPilot.Forcing



namespace PartitionPilot.Forcing
open SetFormula
open scoped ZFSet
universe u

noncomputable def tupleFieldBound : Nat → ZFSet.{u} → ZFSet.{u}
  | 0, B => B
  | k + 1, B => (⋃₀ ⋃₀ B) ∪ tupleFieldBound k (⋃₀ ⋃₀ B)

end PartitionPilot.Forcing

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Definability_GroundFlatCopyGraphs
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace PartitionPilot.Forcing

universe u

noncomputable def relationConverse (A B r : ZFSet.{u}) : ZFSet.{u} :=
  ZFSet.sep (fun z => ∃ x ∈ A, ∃ y ∈ B,
    z = ZFSet.pair y x ∧ ZFSet.pair x y ∈ r) (ZFSet.prod B A)

theorem mem_relationConverse (A B r z : ZFSet.{u}) :
    z ∈ relationConverse A B r ↔ ∃ x ∈ A, ∃ y ∈ B,
      z = ZFSet.pair y x ∧ ZFSet.pair x y ∈ r := by
  rw [relationConverse, ZFSet.mem_sep]
  constructor
  · exact And.right
  · rintro ⟨x, hx, y, hy, eq, rel⟩
    exact ⟨eq.symm ▸ ZFSet.pair_mem_prod.2 ⟨hy, hx⟩, x, hx, y, hy, eq, rel⟩

theorem pair_mem_relationConverse (A B r x y : ZFSet.{u}) :
    ZFSet.pair y x ∈ relationConverse A B r ↔
      x ∈ A ∧ y ∈ B ∧ ZFSet.pair x y ∈ r := by
  rw [mem_relationConverse]
  constructor
  · rintro ⟨a, ha, b, hb, eq, rel⟩
    obtain ⟨rfl, rfl⟩ := ZFSet.pair_inj.1 eq
    exact ⟨ha, hb, rel⟩
  · rintro ⟨hx, hy, rel⟩
    exact ⟨x, hx, y, hy, rfl, rel⟩

noncomputable def relationCompose (A B C r f : ZFSet.{u}) : ZFSet.{u} :=
  ZFSet.sep (fun z => ∃ x ∈ A, ∃ y ∈ B, ∃ w ∈ C,
    z = ZFSet.pair x w ∧ ZFSet.pair x y ∈ r ∧ ZFSet.pair y w ∈ f) (ZFSet.prod A C)

theorem mem_relationCompose (A B C r f z : ZFSet.{u}) :
    z ∈ relationCompose A B C r f ↔ ∃ x ∈ A, ∃ y ∈ B, ∃ w ∈ C,
      z = ZFSet.pair x w ∧ ZFSet.pair x y ∈ r ∧ ZFSet.pair y w ∈ f := by
  rw [relationCompose, ZFSet.mem_sep]
  constructor
  · exact And.right
  · rintro ⟨x, hx, y, hy, w, hw, eq, xr, yf⟩
    exact ⟨eq.symm ▸ ZFSet.pair_mem_prod.2 ⟨hx, hw⟩, x, hx, y, hy, w, hw, eq, xr, yf⟩

theorem pair_mem_relationCompose (A B C r f x z : ZFSet.{u}) :
    ZFSet.pair x z ∈ relationCompose A B C r f ↔
      x ∈ A ∧ z ∈ C ∧ ∃ y ∈ B, ZFSet.pair x y ∈ r ∧ ZFSet.pair y z ∈ f := by
  rw [mem_relationCompose]
  constructor
  · rintro ⟨a, ha, y, hy, b, hb, eq, ar, yf⟩
    obtain ⟨rfl, rfl⟩ := ZFSet.pair_inj.1 eq
    exact ⟨ha, hb, y, hy, ar, yf⟩
  · rintro ⟨hx, hz, y, hy, xr, yf⟩
    exact ⟨x, hx, y, hy, z, hz, rfl, xr, yf⟩

namespace InjectionCode

theorem compose {A B C r f : ZFSet.{u}} (hr : InjectionCode A B r) (hf : InjectionCode B C f) :
    InjectionCode A C (relationCompose A B C r f) := by
  refine ⟨⟨fun _ hz => (ZFSet.mem_sep.1 hz).1, ?_⟩, ?_⟩
  · intro x hx
    obtain ⟨y, xy, uniqueY⟩ := hr.function.2 x hx
    have hy := (ZFSet.pair_mem_prod.1 (hr.function.1 xy)).2
    obtain ⟨z, yz, uniqueZ⟩ := hf.function.2 y hy
    have hz := (ZFSet.pair_mem_prod.1 (hf.function.1 yz)).2
    refine ⟨z, (pair_mem_relationCompose A B C r f x z).2 ⟨hx, hz, y, hy, xy, yz⟩, ?_⟩
    intro w hw
    obtain ⟨_, _, y', _, xy', y'w⟩ := (pair_mem_relationCompose A B C r f x w).1 hw
    exact uniqueZ w (uniqueY y' xy' ▸ y'w)
  · intro x y z hx hy
    obtain ⟨_, _, a, _, xa, az⟩ := (pair_mem_relationCompose A B C r f x z).1 hx
    obtain ⟨_, _, b, _, yb, bz⟩ := (pair_mem_relationCompose A B C r f y z).1 hy
    exact hr.injective x y b (hf.injective a b z az bz ▸ xa) yb

end InjectionCode

end PartitionPilot.Forcing



namespace PartitionPilot.Forcing
open SetFormula
universe u

def flatCopyOrderGraph (E U Q classifier r : ZFSet.{u}) : ZFSet.{u} :=
  ZFSet.sep (fun z => ∃ a ∈ Q, ∃ b ∈ Q, z = ZFSet.pair a b ∧
    ∃ w ∈ E, ∃ x ∈ U, ∃ y ∈ U, ZFSet.pair x y ∈ r ∧
      ZFSet.pair (ZFSet.pair w x) a ∈ classifier ∧
      ZFSet.pair (ZFSet.pair w y) b ∈ classifier) (ZFSet.prod Q Q)

def flatCopyActionGraph (E U Q classifier m : ZFSet.{u}) : ZFSet.{u} :=
  ZFSet.sep (fun z => ∃ g ∈ E, ∃ a ∈ Q, ∃ b ∈ Q, z = ZFSet.pair (ZFSet.pair g a) b ∧
    ∃ w ∈ E, ∃ v ∈ E, ∃ x ∈ U, ZFSet.pair (ZFSet.pair g w) v ∈ m ∧
      ZFSet.pair (ZFSet.pair w x) a ∈ classifier ∧
      ZFSet.pair (ZFSet.pair v x) b ∈ classifier) (ZFSet.prod (ZFSet.prod E Q) Q)

theorem mem_flatCopyOrderGraph (E U Q classifier r z : ZFSet.{u}) :
    z ∈ flatCopyOrderGraph E U Q classifier r ↔
      ∃ a ∈ Q, ∃ b ∈ Q, z = ZFSet.pair a b ∧
        ∃ w ∈ E, ∃ x ∈ U, ∃ y ∈ U, ZFSet.pair x y ∈ r ∧
          ZFSet.pair (ZFSet.pair w x) a ∈ classifier ∧
          ZFSet.pair (ZFSet.pair w y) b ∈ classifier := by
  rw [flatCopyOrderGraph, ZFSet.mem_sep]
  refine ⟨And.right, ?_⟩
  rintro ⟨a, ha, b, hb, equal, rest⟩
  exact ⟨equal.symm ▸ ZFSet.pair_mem_prod.2 ⟨ha, hb⟩, a, ha, b, hb, equal, rest⟩

theorem mem_flatCopyActionGraph (E U Q classifier m z : ZFSet.{u}) :
    z ∈ flatCopyActionGraph E U Q classifier m ↔
      ∃ g ∈ E, ∃ a ∈ Q, ∃ b ∈ Q, z = ZFSet.pair (ZFSet.pair g a) b ∧
        ∃ w ∈ E, ∃ v ∈ E, ∃ x ∈ U, ZFSet.pair (ZFSet.pair g w) v ∈ m ∧
          ZFSet.pair (ZFSet.pair w x) a ∈ classifier ∧
          ZFSet.pair (ZFSet.pair v x) b ∈ classifier := by
  rw [flatCopyActionGraph, ZFSet.mem_sep]
  refine ⟨And.right, ?_⟩
  rintro ⟨g, hg, a, ha, b, hb, equal, rest⟩
  exact ⟨equal.symm ▸ ZFSet.pair_mem_prod.2 ⟨ZFSet.pair_mem_prod.2 ⟨hg, ha⟩, hb⟩,
    g, hg, a, ha, b, hb, equal, rest⟩

theorem pair_mem_flatCopyOrderGraph (E U Q classifier r a b : ZFSet.{u}) :
    ZFSet.pair a b ∈ flatCopyOrderGraph E U Q classifier r ↔
      a ∈ Q ∧ b ∈ Q ∧ ∃ w ∈ E, ∃ x ∈ U, ∃ y ∈ U, ZFSet.pair x y ∈ r ∧
        ZFSet.pair (ZFSet.pair w x) a ∈ classifier ∧ ZFSet.pair (ZFSet.pair w y) b ∈ classifier := by
  rw [mem_flatCopyOrderGraph]
  constructor
  · rintro ⟨a', ha, b', hb, equal, rest⟩
    obtain ⟨rfl, rfl⟩ := ZFSet.pair_inj.1 equal
    exact ⟨ha, hb, rest⟩
  · rintro ⟨ha, hb, rest⟩
    exact ⟨a, ha, b, hb, rfl, rest⟩

theorem pair_mem_flatCopyActionGraph (E U Q classifier m g a b : ZFSet.{u}) :
    ZFSet.pair (ZFSet.pair g a) b ∈ flatCopyActionGraph E U Q classifier m ↔
      g ∈ E ∧ a ∈ Q ∧ b ∈ Q ∧ ∃ w ∈ E, ∃ v ∈ E, ∃ x ∈ U,
        ZFSet.pair (ZFSet.pair g w) v ∈ m ∧
          ZFSet.pair (ZFSet.pair w x) a ∈ classifier ∧ ZFSet.pair (ZFSet.pair v x) b ∈ classifier := by
  rw [mem_flatCopyActionGraph]
  constructor
  · rintro ⟨g', hg, a', ha, b', hb, equal, rest⟩
    obtain ⟨ga, rfl⟩ := ZFSet.pair_inj.1 equal
    obtain ⟨rfl, rfl⟩ := ZFSet.pair_inj.1 ga
    exact ⟨hg, ha, hb, rest⟩
  · rintro ⟨hg, ha, hb, rest⟩
    exact ⟨g, hg, a, ha, b, hb, rfl, rest⟩

end PartitionPilot.Forcing



end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Definability_GroundPairCompositions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open scoped ZFSet



namespace PartitionPilot.Forcing

universe u

theorem relationCompose_domain_eq {U B D L ell f : ZFSet.{u}}
    (subset : U ⊆ B) (shape : ell ⊆ ZFSet.prod U D) :
    relationCompose B D L ell f = relationCompose U D L ell f := by
  apply ZFSet.ext
  intro z
  rw [mem_relationCompose, mem_relationCompose]
  constructor
  · rintro ⟨x, _, y, hy, w, hw, equal, first, second⟩
    exact ⟨x, (ZFSet.pair_mem_prod.1 (shape first)).1, y, hy, w, hw, equal, first, second⟩
  · rintro ⟨x, hx, y, hy, w, hw, equal, first, second⟩
    exact ⟨x, subset hx, y, hy, w, hw, equal, first, second⟩

noncomputable def pairCompositionFamily (K I J B D L Es Ss W : ZFSet.{u}) : ZFSet.{u} :=
  ZFSet.sep (fun z => ∃ i ∈ I, ∃ j ∈ J, ∃ ell ∈ ⋃₀ ⋃₀ Es, ∃ f ∈ ⋃₀ ⋃₀ Ss,
    ∃ c ∈ W, z = ZFSet.pair (ZFSet.pair i j) c ∧ ZFSet.pair i j ∈ K ∧
      ZFSet.pair j ell ∈ Es ∧ ZFSet.pair i f ∈ Ss ∧ c = relationCompose B D L ell f)
    (ZFSet.prod K W)

end PartitionPilot.Forcing



namespace PartitionPilot.Forcing

universe u v w

noncomputable def literalTaskCode (a c ell e F label : ZFSet.{u}) : ZFSet.{u} :=
  ZFSet.pair a (ZFSet.pair c (ZFSet.pair ell (ZFSet.pair e (ZFSet.pair F label))))

noncomputable def literalTaskBound (P R U Labels : ZFSet.{u}) : ZFSet.{u} :=
  ZFSet.prod P (ZFSet.prod P (ZFSet.prod R (ZFSet.prod P (ZFSet.prod U Labels))))

theorem literalTaskCode_inj {a c ell e F label a' c' ell' e' F' label' : ZFSet.{u}} :
    literalTaskCode a c ell e F label = literalTaskCode a' c' ell' e' F' label' ↔
      a = a' ∧ c = c' ∧ ell = ell' ∧ e = e' ∧ F = F' ∧ label = label' := by
  simp only [literalTaskCode, ZFSet.pair_inj]

theorem literalTaskCode_mem_bound (P R U Labels a c ell e F label : ZFSet.{u}) :
    literalTaskCode a c ell e F label ∈ literalTaskBound P R U Labels ↔
      a ∈ P ∧ c ∈ P ∧ ell ∈ R ∧ e ∈ P ∧ F ∈ U ∧ label ∈ Labels := by
  simp only [literalTaskCode, literalTaskBound, ZFSet.pair_mem_prod]

theorem mem_literalTaskBound (P R U Labels z : ZFSet.{u}) :
    z ∈ literalTaskBound P R U Labels ↔
      ∃ a ∈ P, ∃ c ∈ P, ∃ ell ∈ R, ∃ e ∈ P, ∃ F ∈ U, ∃ label ∈ Labels,
        z = literalTaskCode a c ell e F label := by
  constructor
  · intro hz
    obtain ⟨a, ha, rest1, hrest1, rfl⟩ := ZFSet.mem_prod.1 hz
    obtain ⟨c, hc, rest2, hrest2, rfl⟩ := ZFSet.mem_prod.1 hrest1
    obtain ⟨ell, hell, rest3, hrest3, rfl⟩ := ZFSet.mem_prod.1 hrest2
    obtain ⟨e, he, rest4, hrest4, rfl⟩ := ZFSet.mem_prod.1 hrest3
    obtain ⟨F, hF, label, hlabel, rfl⟩ := ZFSet.mem_prod.1 hrest4
    exact ⟨a, ha, c, hc, ell, hell, e, he, F, hF, label, hlabel, rfl⟩
  · rintro ⟨a, ha, c, hc, ell, hell, e, he, F, hF, label, hlabel, rfl⟩
    exact (literalTaskCode_mem_bound P R U Labels a c ell e F label).2
      ⟨ha, hc, hell, he, hF, hlabel⟩

def literalTaskField {α : Type v} (a c ell e F label : α) : Fin 6 → α :=
  Fin.cases a (Fin.cases c (Fin.cases ell (Fin.cases e (Fin.cases F (Fin.cases label Fin.elim0)))))

def literalTaskFieldBound (P R U Labels : ZFSet.{u}) (j : Fin 6) : ZFSet.{u} :=
  literalTaskField P P R P U Labels j

theorem literalTaskField_mem {P R U Labels a c ell e F label : ZFSet.{u}}
    (ha : a ∈ P) (hc : c ∈ P) (hell : ell ∈ R) (he : e ∈ P) (hF : F ∈ U)
    (hlabel : label ∈ Labels) (j : Fin 6) :
    literalTaskField a c ell e F label j ∈ literalTaskFieldBound P R U Labels j := by
  exact Fin.cases ha (Fin.cases hc (Fin.cases hell (Fin.cases he
    (Fin.cases hF (Fin.cases hlabel (fun i => Fin.elim0 i)))))) j

noncomputable def literalTaskFieldGraph (I P R U Labels : ZFSet.{u}) (j : Fin 6) : ZFSet.{u} :=
  ZFSet.sep (fun z => ∃ i ∈ I, ∃ a ∈ P, ∃ c ∈ P, ∃ ell ∈ R, ∃ e ∈ P,
    ∃ F ∈ U, ∃ label ∈ Labels,
      z = ZFSet.pair i (literalTaskField a c ell e F label j) ∧
        i = literalTaskCode a c ell e F label)
    (ZFSet.prod I (literalTaskFieldBound P R U Labels j))

theorem mem_literalTaskFieldGraph (I P R U Labels z : ZFSet.{u}) (j : Fin 6) :
    z ∈ literalTaskFieldGraph I P R U Labels j ↔
      ∃ i ∈ I, ∃ a ∈ P, ∃ c ∈ P, ∃ ell ∈ R, ∃ e ∈ P, ∃ F ∈ U, ∃ label ∈ Labels,
        z = ZFSet.pair i (literalTaskField a c ell e F label j) ∧
          i = literalTaskCode a c ell e F label := by
  rw [literalTaskFieldGraph, ZFSet.mem_sep]
  refine ⟨And.right, ?_⟩
  rintro ⟨i, hi, a, ha, c, hc, ell, hell, e, he, F, hF, label, hlabel, equal, code⟩
  exact ⟨equal.symm ▸ ZFSet.pair_mem_prod.2
    ⟨hi, literalTaskField_mem ha hc hell he hF hlabel j⟩,
    i, hi, a, ha, c, hc, ell, hell, e, he, F, hF, label, hlabel, equal, code⟩

theorem pair_mem_literalTaskFieldGraph (I P R U Labels i x : ZFSet.{u}) (j : Fin 6) :
    ZFSet.pair i x ∈ literalTaskFieldGraph I P R U Labels j ↔
      i ∈ I ∧ ∃ a ∈ P, ∃ c ∈ P, ∃ ell ∈ R, ∃ e ∈ P, ∃ F ∈ U, ∃ label ∈ Labels,
        i = literalTaskCode a c ell e F label ∧ x = literalTaskField a c ell e F label j := by
  rw [mem_literalTaskFieldGraph]
  constructor
  · rintro ⟨i', hi, a, ha, c, hc, ell, hell, e, he, F, hF, label, hlabel, equal, code⟩
    obtain ⟨same, value⟩ := ZFSet.pair_inj.1 equal
    exact ⟨same.symm ▸ hi, a, ha, c, hc, ell, hell, e, he, F, hF, label, hlabel,
      same.trans code, value⟩
  · rintro ⟨hi, a, ha, c, hc, ell, hell, e, he, F, hF, label, hlabel, code, value⟩
    exact ⟨i, hi, a, ha, c, hc, ell, hell, e, he, F, hF, label, hlabel,
      congrArg (ZFSet.pair i) value, code⟩

theorem literalTaskFieldGraph_entry_iff
    {I P R U Labels a c ell e F label x : ZFSet.{u}}
    (ha : a ∈ P) (hc : c ∈ P) (hell : ell ∈ R) (he : e ∈ P) (hF : F ∈ U)
    (hlabel : label ∈ Labels) (j : Fin 6) :
    ZFSet.pair (literalTaskCode a c ell e F label) x ∈ literalTaskFieldGraph I P R U Labels j ↔
      literalTaskCode a c ell e F label ∈ I ∧ x = literalTaskField a c ell e F label j := by
  rw [pair_mem_literalTaskFieldGraph]
  constructor
  · rintro ⟨hi, a', _, c', _, ell', _, e', _, F', _, label', _, equal, value⟩
    obtain ⟨sameA, sameC, sameEll, sameE, sameF, sameLabel⟩ := literalTaskCode_inj.1 equal
    subst a' c' ell' e' F' label'
    exact ⟨hi, value⟩
  · rintro ⟨hi, value⟩
    exact ⟨hi, a, ha, c, hc, ell, hell, e, he, F, hF, label, hlabel, rfl, value⟩

theorem literalTaskFieldGraph_function {I P R U Labels : ZFSet.{u}}
    (subset : I ⊆ literalTaskBound P R U Labels) (j : Fin 6) :
    ZFSet.IsFunc I (literalTaskFieldBound P R U Labels j) (literalTaskFieldGraph I P R U Labels j) := by
  refine ⟨fun _ h => (ZFSet.mem_sep.1 h).1, ?_⟩
  intro i hi
  obtain ⟨a, ha, c, hc, ell, hell, e, he, F, hF, label, hlabel, equal⟩ :=
    (mem_literalTaskBound P R U Labels i).1 (subset hi)
  subst i
  refine ⟨literalTaskField a c ell e F label j,
    (literalTaskFieldGraph_entry_iff ha hc hell he hF hlabel j).2 ⟨hi, rfl⟩, ?_⟩
  intro y entry
  exact ((literalTaskFieldGraph_entry_iff ha hc hell he hF hlabel j).1 entry).2

noncomputable abbrev literalTaskSourceGraph (I P R U Labels : ZFSet.{u}) :=
  literalTaskFieldGraph I P R U Labels 0
noncomputable abbrev literalTaskTargetGraph (I P R U Labels : ZFSet.{u}) :=
  literalTaskFieldGraph I P R U Labels 1
noncomputable abbrev literalTaskBaseGraph (I P R U Labels : ZFSet.{u}) :=
  literalTaskFieldGraph I P R U Labels 2
noncomputable abbrev literalTaskSeparatorGraph (I P R U Labels : ZFSet.{u}) :=
  literalTaskFieldGraph I P R U Labels 3
noncomputable abbrev literalTaskFilterGraph (I P R U Labels : ZFSet.{u}) :=
  literalTaskFieldGraph I P R U Labels 4

namespace BoundedFormula

open SetFormula

def literalTaskFormula {n} (z a c ell e F label : Fin n) : BoundedFormula n :=
  let lift2 (j : Fin n) := j.succ.succ
  let lift4 (j : Fin n) := j.succ.succ.succ.succ
  let lift6 (j : Fin n) := j.succ.succ.succ.succ.succ.succ
  let lift8 (j : Fin n) := j.succ.succ.succ.succ.succ.succ.succ.succ
  exMem z (exMem 0 (.conj (orderedPairFormula (lift2 z) (lift2 a) 0)
    (exMem 0 (exMem 0 (.conj (orderedPairFormula 2 (lift4 c) 0)
      (exMem 0 (exMem 0 (.conj (orderedPairFormula 2 (lift6 ell) 0)
        (exMem 0 (exMem 0 (.conj (orderedPairFormula 2 (lift8 e) 0)
          (orderedPairFormula 0 (lift8 F) (lift8 label)))))))))))))

def literalTaskFieldEntryFormula {n} (j : Fin 6) (z I P R U Labels : Fin n) : BoundedFormula n :=
  let lift (i : Fin n) := i.succ.succ.succ.succ.succ.succ.succ
  exMem I (exMem P.succ (exMem P.succ.succ (exMem R.succ.succ.succ
    (exMem P.succ.succ.succ.succ (exMem U.succ.succ.succ.succ.succ
      (exMem Labels.succ.succ.succ.succ.succ.succ
        (.conj (orderedPairFormula (lift z) 6 (literalTaskField 5 4 3 2 1 0 j))
          (literalTaskFormula 6 5 4 3 2 1 0))))))))

end BoundedFormula

end PartitionPilot.Forcing



end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Definability_ParentSupportCodes
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI



namespace PartitionPilot.Forcing

open scoped ZFSet

universe u

structure ChoiceFunctionCode (A f : ZFSet.{u}) : Prop where
  function : ZFSet.IsFunc A (⋃₀ A) f
  chosen : ∀ x y, ZFSet.pair x y ∈ f → y ∈ x

end PartitionPilot.Forcing



namespace PartitionPilot.Forcing

universe u

noncomputable def relationFiber (B r x : ZFSet.{u}) : ZFSet.{u} :=
  ZFSet.sep (fun y => ZFSet.pair x y ∈ r) B

theorem mem_relationFiber (B r x y : ZFSet.{u}) :
    y ∈ relationFiber B r x ↔ y ∈ B ∧ ZFSet.pair x y ∈ r := ZFSet.mem_sep

noncomputable def choiceUniformGraph (A B r F c : ZFSet.{u}) : ZFSet.{u} :=
  ZFSet.sep (fun z => ∃ x ∈ A, ∃ y ∈ B, z = ZFSet.pair x y ∧
    relationFiber B r x ∈ F ∧ ZFSet.pair (relationFiber B r x) y ∈ c) (ZFSet.prod A B)

theorem pair_mem_choiceUniformGraph (A B r F c x y : ZFSet.{u}) :
    ZFSet.pair x y ∈ choiceUniformGraph A B r F c ↔
      x ∈ A ∧ y ∈ B ∧ relationFiber B r x ∈ F ∧ ZFSet.pair (relationFiber B r x) y ∈ c := by
  rw [choiceUniformGraph, ZFSet.mem_sep]
  constructor
  · rintro ⟨_, a, ha, b, hb, eq, hf, rel⟩
    obtain ⟨rfl, rfl⟩ := ZFSet.pair_inj.1 eq
    exact ⟨ha, hb, hf, rel⟩
  · rintro ⟨hx, hy, hf, rel⟩
    exact ⟨ZFSet.pair_mem_prod.2 ⟨hx, hy⟩, x, hx, y, hy, rfl, hf, rel⟩

theorem choiceUniformGraph_function {A B r F c : ZFSet.{u}} (choice : ChoiceFunctionCode F c)
    (fibers : ∀ x ∈ A, relationFiber B r x ∈ F) :
    ZFSet.IsFunc A B (choiceUniformGraph A B r F c) ∧ choiceUniformGraph A B r F c ⊆ r := by
  refine ⟨⟨fun _ hz => (ZFSet.mem_sep.1 hz).1, ?_⟩, ?_⟩
  · intro x hx
    obtain ⟨y, rel, unique⟩ := choice.function.2 (relationFiber B r x) (fibers x hx)
    have hy := (mem_relationFiber B r x y).1 (choice.chosen _ _ rel)
    exact ⟨y, (pair_mem_choiceUniformGraph A B r F c x y).2 ⟨hx, hy.1, fibers x hx, rel⟩,
      fun z hz => unique z ((pair_mem_choiceUniformGraph A B r F c x z).1 hz).2.2.2⟩
  · intro z hz
    obtain ⟨_, x, _, y, _, eq, _, rel⟩ := ZFSet.mem_sep.1 hz
    exact eq.symm ▸ ((mem_relationFiber B r x y).1 (choice.chosen _ _ rel)).2

namespace TransitiveGround

open SetFormula
variable (M : TransitiveGround.{u})

noncomputable def nonemptyGroundSubsets (B : ZFSet.{u}) : ZFSet.{u} :=
  ZFSet.sep ZFSet.Nonempty (M.groundPower B)

end TransitiveGround

end PartitionPilot.Forcing



namespace PartitionPilot.Forcing
open SetFormula
universe u

namespace TransitiveGround
variable (M : TransitiveGround.{u})

noncomputable def relationFiberFamily (I B R : ZFSet.{u}) : ZFSet.{u} :=
  ZFSet.sep (fun z => ∃ i ∈ I, ∃ f ∈ M.groundPower B,
    z = ZFSet.pair i f ∧ f = relationFiber B R i) (ZFSet.prod I (M.groundPower B))

theorem pair_mem_relationFiberFamily (I B R i f : ZFSet.{u}) :
    ZFSet.pair i f ∈ M.relationFiberFamily I B R ↔
      i ∈ I ∧ f ∈ M.groundPower B ∧ f = relationFiber B R i := by
  rw [relationFiberFamily, ZFSet.mem_sep, ZFSet.pair_mem_prod]
  constructor
  · rintro ⟨_, j, hj, g, hg, equal, value⟩
    obtain ⟨rfl, rfl⟩ := ZFSet.pair_inj.1 equal
    exact ⟨hj, hg, value⟩
  · rintro ⟨hi, hf, equal⟩
    exact ⟨⟨hi, hf⟩, i, hi, f, hf, rfl, equal⟩

end TransitiveGround





def ExternalCosetSupport (E U C classifier copies zero v y : ZFSet.{u}) : Prop :=
  ∃ c ∈ C, ∃ w ∈ E, ∃ x ∈ U, v = ZFSet.pair zero c ∧
    ZFSet.pair w c ∈ classifier ∧ ZFSet.pair (ZFSet.pair w x) y ∈ copies

def ExternalTileSupport (E Q Requests localPoints action first v y : ZFSet.{u}) : Prop :=
  ∃ w ∈ E, ∃ r ∈ Requests, ∃ x ∈ Q, v = ZFSet.pair first (ZFSet.pair w r) ∧
    ZFSet.pair r x ∈ localPoints ∧ ZFSet.pair (ZFSet.pair w x) y ∈ action

def externalStarSupportGraph (V Q E U C Requests classifier copies localPoints action zero first : ZFSet.{u}) : ZFSet.{u} :=
  ZFSet.sep (fun z => ∃ v ∈ V, ∃ y ∈ Q, z = ZFSet.pair v y ∧
    (ExternalCosetSupport E U C classifier copies zero v y ∨
      ExternalTileSupport E Q Requests localPoints action first v y)) (ZFSet.prod V Q)

theorem pair_mem_externalStarSupportGraph (V Q E U C Requests classifier copies localPoints action zero first v y : ZFSet.{u}) :
    ZFSet.pair v y ∈ externalStarSupportGraph V Q E U C Requests classifier copies localPoints action zero first ↔
      v ∈ V ∧ y ∈ Q ∧ (ExternalCosetSupport E U C classifier copies zero v y ∨
        ExternalTileSupport E Q Requests localPoints action first v y) := by
  rw [externalStarSupportGraph, ZFSet.mem_sep]
  constructor
  · rintro ⟨_, v', hv, y', hy, equal, body⟩
    obtain ⟨rfl, rfl⟩ := ZFSet.pair_inj.1 equal
    exact ⟨hv, hy, body⟩
  · rintro ⟨hv, hy, body⟩
    exact ⟨ZFSet.pair_mem_prod.2 ⟨hv, hy⟩, v, hv, y, hy, rfl, body⟩

end PartitionPilot.Forcing

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Forcing_UniqueFiberForcing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PartitionPilot.Forcing.BoundedFormula

open SetFormula
universe u

def uniqueFiberFormula {n} (s x f : Fin n) : BoundedFormula n :=
  .conj (.mem x s) (.conj (pairMembershipFormula s x f)
    (.allMem s (imp (pairMembershipFormula s.succ 0 f.succ) (.equal 0 x.succ))))

end PartitionPilot.Forcing.BoundedFormula

end

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Definability_GraphValueMembershipFormula
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PartitionPilot.Forcing.BoundedFormula
open SetFormula
universe u

def graphValueMemberFormula {n} (x z beta : Fin n) : BoundedFormula n :=
  exMem z (exMem 0 (exMem 0
    (.conj (pairMembershipFormula beta.succ.succ.succ 0 z.succ.succ.succ)
      (.mem x.succ.succ.succ 0))))

end PartitionPilot.Forcing.BoundedFormula

end

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Definability_MapFamilyApplicationGraphs
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace PartitionPilot.Forcing



open SetFormula
universe u

noncomputable def indexedCarrierLabels (T U A : ZFSet.{u}) : ZFSet.{u} :=
  ZFSet.sep (fun z => ∃ i ∈ T, ∃ X ∈ ZFSet.sUnion (ZFSet.sUnion A), ∃ x ∈ X,
    z = ZFSet.pair i x ∧ ZFSet.pair i X ∈ A) (ZFSet.prod T U)

theorem indexedCarrierLabels_subset (T U A : ZFSet.{u}) :
    indexedCarrierLabels T U A ⊆ ZFSet.prod T U :=
  fun _ hz => (ZFSet.mem_sep.1 hz).1

theorem mem_indexedCarrierLabels (T U A z : ZFSet.{u}) :
    z ∈ indexedCarrierLabels T U A ↔
      ∃ i ∈ T, ∃ X ∈ ZFSet.sUnion (ZFSet.sUnion A), ∃ x ∈ X,
        x ∈ U ∧ z = ZFSet.pair i x ∧ ZFSet.pair i X ∈ A := by
  constructor
  · intro hz
    obtain ⟨bound, i, hi, X, hX, x, hx, rfl, entry⟩ := ZFSet.mem_sep.1 hz
    exact ⟨i, hi, X, hX, x, hx, (ZFSet.pair_mem_prod.1 bound).2, rfl, entry⟩
  · rintro ⟨i, hi, X, hX, x, hx, hu, rfl, entry⟩
    exact ZFSet.mem_sep.2 ⟨ZFSet.pair_mem_prod.2 ⟨hi, hu⟩, i, hi, X, hX, x, hx, rfl, entry⟩

namespace BoundedFormula

def indexedCarrierLabelFormula {n} (z T U A V : Fin n) : BoundedFormula n :=
  exMem T (exMem V.succ (exMem 0
    (.conj (.mem 0 U.succ.succ.succ)
      (.conj (orderedPairFormula z.succ.succ.succ 2 0)
        (pairMembershipFormula 2 1 A.succ.succ.succ)))))

end BoundedFormula





noncomputable def mapFamilyApplicationGraph (I P Q family : ZFSet.{u}) : ZFSet.{u} :=
  ZFSet.sep (fun z => ∃ i ∈ I, ∃ x ∈ P, ∃ y ∈ Q, ∃ f ∈ ZFSet.sUnion (ZFSet.sUnion family),
    z = ZFSet.pair (ZFSet.pair i x) y ∧ ZFSet.pair i f ∈ family ∧ ZFSet.pair x y ∈ f)
    (ZFSet.prod (ZFSet.prod I P) Q)


end PartitionPilot.Forcing

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Forcing_ConditionQuantifiers
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace PartitionPilot.Forcing.SetFormula

def allConditions {n : Nat} (carrier : Fin n) (φ : SetFormula (n + 1)) : SetFormula n :=
  .all (imp (.mem 0 carrier.succ) φ)

def exConditions {n : Nat} (carrier : Fin n) (φ : SetFormula (n + 1)) : SetFormula n :=
  ex (.conj (.mem 0 carrier.succ) φ)

end PartitionPilot.Forcing.SetFormula

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Geometry_CompleteProjectionPredensity
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace PartitionPilot.Forcing

section
universe u v
variable {Upper : Type u} {Lower : Type v} [PartialOrder Upper] [PartialOrder Lower]

structure CompleteProjection (restriction : Upper →o Lower)
    (inclusion : Lower ↪o Upper) : Prop where
  retract : ∀ q, restriction (inclusion q) = q
  le_include_iff : ∀ p q, p ≤ inclusion q ↔ restriction p ≤ q
  lift : ∀ p q, q ≤ restriction p → ∃ r, r ≤ p ∧ restriction r = q

namespace CompleteProjection
variable {restriction : Upper →o Lower} {inclusion : Lower ↪o Upper}
variable (projection : CompleteProjection restriction inclusion)
include projection

theorem le_include_restriction (p : Upper) : p ≤ inclusion (restriction p) :=
  (projection.le_include_iff p (restriction p)).2 le_rfl

def projectedFilter (H : ConditionFilter Upper) : ConditionFilter Lower where
  mem q := H.mem (inclusion q)
  nonempty := by
    obtain ⟨p, member⟩ := H.nonempty
    exact ⟨restriction p, H.upward member (projection.le_include_restriction p)⟩
  upward := by
    intro p q member below
    exact H.upward member (inclusion.monotone below)
  directed := by
    intro p q hp hq
    obtain ⟨r, member, rp, rq⟩ := H.directed hp hq
    exact ⟨restriction r, H.upward member (projection.le_include_restriction r),
      (projection.le_include_iff r p).1 rp, (projection.le_include_iff r q).1 rq⟩

end CompleteProjection
end



end PartitionPilot.Forcing

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Transfinite_GroundChronologyPairs
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PartitionPilot.Forcing
open SetFormula SetRealization
universe u

noncomputable def chronologyPairs (T : ZFSet.{u}) : ZFSet.{u} :=
  ZFSet.sep (fun z => ∃ s ∈ T, ∃ t ∈ T,
    z = ZFSet.pair s t ∧ (t = s ∨ t ∈ s)) (ZFSet.prod T T)

theorem mem_chronologyPairs (T z : ZFSet.{u}) :
    z ∈ chronologyPairs T ↔ ∃ s ∈ T, ∃ t ∈ T,
      z = ZFSet.pair s t ∧ (t = s ∨ t ∈ s) := by
  rw [chronologyPairs, ZFSet.mem_sep]
  constructor
  · exact And.right
  · rintro ⟨s, hs, t, ht, equal, before⟩
    exact ⟨equal.symm ▸ ZFSet.pair_mem_prod.2 ⟨hs, ht⟩, s, hs, t, ht, equal, before⟩

theorem pair_mem_chronologyPairs (T s t : ZFSet.{u}) :
    ZFSet.pair s t ∈ chronologyPairs T ↔ s ∈ T ∧ t ∈ T ∧ (t = s ∨ t ∈ s) := by
  rw [mem_chronologyPairs]
  constructor
  · rintro ⟨a, ha, b, hb, equal, before⟩
    obtain ⟨rfl, rfl⟩ := ZFSet.pair_inj.1 equal
    exact ⟨ha, hb, before⟩
  · rintro ⟨hs, ht, before⟩
    exact ⟨s, hs, t, ht, rfl, before⟩

theorem chronologyPairs_subset (T : ZFSet.{u}) : chronologyPairs T ⊆ ZFSet.prod T T :=
  fun _ hz => (ZFSet.mem_sep.1 hz).1

end PartitionPilot.Forcing

end

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Definability_CodedInjectiveCones
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace PartitionPilot.Forcing

section
open SetFormula
universe u

def GraphDiagonalCode (f : ZFSet.{u}) : Prop :=
  ∀ x y, ZFSet.pair x y ∈ f → x = y

def GraphCompositionCode (f g h : ZFSet.{u}) : Prop :=
  ∀ x y, ZFSet.pair x y ∈ f → ∀ z,
    (ZFSet.pair y z ∈ g ↔ ZFSet.pair x z ∈ h)

namespace BoundedFormula

def graphDiagonalFormula {n} (f : Fin n) : BoundedFormula n :=
  .allMem f (.allMem 0 (.allMem 0 (.allMem 2 (.allMem 0
    (imp (orderedPairFormula 4 2 0) (.equal 2 0))))))

end BoundedFormula

end



section
universe u

theorem GraphCompositionCode.eq_relationCompose {A B C f g h : ZFSet.{u}}
    (coherent : GraphCompositionCode f g h) (first : ZFSet.IsFunc A B f)
    (shape : h ⊆ ZFSet.prod A C) : h = relationCompose A B C f g := by
  apply ZFSet.ext
  intro z
  constructor
  · intro hz
    obtain ⟨x, hx, v, hv, rfl⟩ := ZFSet.mem_prod.1 (shape hz)
    obtain ⟨y, entry, _⟩ := first.2 x hx
    have hy := (ZFSet.pair_mem_prod.1 (first.1 entry)).2
    exact (pair_mem_relationCompose A B C f g x v).2
      ⟨hx, hv, y, hy, entry, (coherent x y entry v).2 hz⟩
  · intro hz
    obtain ⟨x, _, y, _, v, _, rfl, xy, yv⟩ := (mem_relationCompose A B C f g z).1 hz
    exact (coherent x y xy v).1 yv





theorem relationCompose_assoc (A B C D r s t : ZFSet.{u}) :
    relationCompose A C D (relationCompose A B C r s) t =
      relationCompose A B D r (relationCompose B C D s t) := by
  apply ZFSet.ext
  intro z
  constructor
  · intro entry
    obtain ⟨x, hx, y, hy, w, hw, rfl, xy, yw⟩ := (mem_relationCompose _ _ _ _ _ z).1 entry
    obtain ⟨_, _, a, ha, xa, ay⟩ := (pair_mem_relationCompose _ _ _ _ _ x y).1 xy
    exact (pair_mem_relationCompose _ _ _ _ _ x w).2
      ⟨hx, hw, a, ha, xa, (pair_mem_relationCompose _ _ _ _ _ a w).2 ⟨ha, hw, y, hy, ay, yw⟩⟩
  · intro entry
    obtain ⟨x, hx, a, ha, w, hw, rfl, xa, aw⟩ := (mem_relationCompose _ _ _ _ _ z).1 entry
    obtain ⟨_, _, y, hy, ay, yw⟩ := (pair_mem_relationCompose _ _ _ _ _ a w).1 aw
    exact (pair_mem_relationCompose _ _ _ _ _ x w).2
      ⟨hx, hw, y, hy, (pair_mem_relationCompose _ _ _ _ _ x y).2 ⟨hx, hy, a, ha, xa, ay⟩, yw⟩

end



end PartitionPilot.Forcing

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Forcing_GroundFixedPoints
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PartitionPilot.Forcing.SetFormula

universe u

def postfixedFormula {k : Nat} (φ : SetFormula (k + 2)) : SetFormula (k + 1) :=
  .all (imp (.mem 0 1) φ)

def definableOperator {k : Nat} (U : Set ZFSet.{u}) (φ : SetFormula (k + 2))
    (params : Fin k → ZFSet.{u}) (B S : ZFSet.{u}) : ZFSet.{u} :=
  ZFSet.sep (fun x => Realize U φ (extend x (extend S params))) B

theorem definableOperator_subset {k : Nat} (U : Set ZFSet.{u}) (φ : SetFormula (k + 2))
    (params : Fin k → ZFSet.{u}) (B S : ZFSet.{u}) : definableOperator U φ params B S ⊆ B :=
  fun _ hx => (ZFSet.mem_sep.1 hx).1

end PartitionPilot.Forcing.SetFormula

end

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Definability_CodedEqualityRelations
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PartitionPilot.Forcing.SetFormula

def tripleMembershipFormula {n : Nat} (p x y r : Fin n) : SetFormula n :=
  ex (.conj (orderedPairFormula 0 x.succ y.succ)
    (pairMembershipFormula p.succ 0 r.succ))

end PartitionPilot.Forcing.SetFormula

end

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Definability_BoundedAtomicEquality
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PartitionPilot.Forcing.SetFormula

def orderedTripleFormula {n : Nat} (z p x y : Fin n) : SetFormula n :=
  ex (.conj (orderedPairFormula 0 x.succ y.succ)
    (orderedPairFormula z.succ p.succ 0))

def codedRelationFormula : SetFormula 6 := tripleMembershipFormula 0 1 2 3

end PartitionPilot.Forcing.SetFormula

end

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Geometry_UniformAtomicEquality
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI



namespace PartitionPilot.Forcing.TransitiveGround

open SetFormula
universe u
variable (M : TransitiveGround.{u})

theorem collection_witness (collection : CollectionSchema M.sets)
    {n : Nat} (φ : SetFormula (n + 2)) (params : Fin n → ZFSet.{u})
    (members : ∀ i, params i ∈ M.sets) {a : ZFSet.{u}} (ha : a ∈ M.sets)
    (existsWitness : ∀ x ∈ a, ∃ y ∈ M.sets, Realize M.sets φ (extend x (extend y params))) :
    ∃ b ∈ M.sets, ∀ x ∈ a, ∃ y ∈ b, Realize M.sets φ (extend x (extend y params)) := by
  obtain ⟨b, hb, spec⟩ := collection φ params members a ha (fun x _ hx => existsWitness x hx)
  refine ⟨b, hb, ?_⟩
  intro x hx
  obtain ⟨y, _, hy, rel⟩ := spec x (M.transitive ha hx) hx
  exact ⟨y, hy, rel⟩

end PartitionPilot.Forcing.TransitiveGround


section

namespace PartitionPilot.Forcing.SetFormula

def transitiveSetFormula {n : Nat} (t : Fin n) : SetFormula n :=
  .all (imp (.mem 0 t.succ) (.all (imp (.mem 0 1) (.mem 0 t.succ.succ))))

def transitiveCoverFormula : SetFormula 2 :=
  .conj (.mem 0 1) (transitiveSetFormula 1)

end PartitionPilot.Forcing.SetFormula

end



namespace PartitionPilot.Forcing.SetFormula

universe u v

theorem map_empty {A : Type u} {B : Type v} (f : A → B) :
    (fun i : Fin 0 => f (Fin.elim0 i)) = (Fin.elim0 : Fin 0 → B) := by
  funext i
  exact Fin.elim0 i

end PartitionPilot.Forcing.SetFormula

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Forcing_UniformGroundNames
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace PartitionPilot.Forcing

open SetRealization
universe u
variable {P : Type u}

namespace SetFormula

def nameCodeStepFormula : SetFormula 3 :=
  .all (imp (.mem 0 1) (ex (.conj (.mem 0 3)
    (exConditions 4 (orderedPairFormula 2 1 0)))))

def nameCertificateFormula : SetFormula 2 := postfixedFormula nameCodeStepFormula

end SetFormula

end PartitionPilot.Forcing



namespace PartitionPilot.Forcing.SetFormula

universe u

structure ForcingPrimitives (k : Nat) where
  carrier : Fin k
  order : Fin k
  equality : SetFormula (k + 3)
  domain : SetFormula (k + 1)

end PartitionPilot.Forcing.SetFormula



end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Definability_RawRenameFormulas
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PartitionPilot.Forcing.SetFormula

def orientedPairFormula {n : Nat} (reverse : Bool) (x y r : Fin n) : SetFormula n :=
  if reverse then pairMembershipFormula y x r else pairMembershipFormula x y r

end PartitionPilot.Forcing.SetFormula



namespace PartitionPilot.Forcing.SetFormula

def renameMatchFormula {n : Nat} (reverse : Bool) (c f r x y : Fin n) : SetFormula n :=
  .all (allConditions c.succ (imp (pairMembershipFormula 1 0 x.succ.succ)
    (ex (exConditions c.succ.succ.succ
      (.conj (pairMembershipFormula 1 0 y.succ.succ.succ.succ)
        (.conj (orientedPairFormula reverse 2 0 f.succ.succ.succ.succ)
          (orientedPairFormula reverse 3 1 r.succ.succ.succ.succ)))))))

def renameStepFormula {n : Nat} (c f r x y : Fin n) : SetFormula n :=
  .conj (renameMatchFormula false c f r x y) (renameMatchFormula true c f r y x)

end PartitionPilot.Forcing.SetFormula

end

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Definability_SeparationFulfillmentCodes
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace PartitionPilot.Forcing




universe u





def SeparationActorCode (P r Q R ν A e W k : ZFSet.{u}) : Prop :=
  ∀ w ∈ Q, ZFSet.pair W w ∈ e →
    (∀ z ∈ Q, ZFSet.pair z w ∈ R → ZFSet.pair (ZFSet.pair k z) z ∈ A) ∧
    ∀ x ∈ P, ∀ y ∈ P, ∀ x' ∈ Q, ∀ y' ∈ Q, ∀ z ∈ Q,
      ZFSet.pair W x ∈ r → ZFSet.pair W y ∈ r →
      ZFSet.pair x x' ∈ e → ZFSet.pair y y' ∈ e →
      ZFSet.pair (ZFSet.pair k x') z ∈ A → ZFSet.pair (ZFSet.pair z y') w ∈ ν

def SeparationFulfillmentCode (P r Q R ν H A e : ZFSet.{u}) : Prop :=
  ∀ W ∈ P, ∃ k ∈ H, SeparationActorCode P r Q R ν A e W k


end PartitionPilot.Forcing

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Forcing_GroundProductActions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PartitionPilot.Forcing.SetFormula

def renameStateFormula : SetFormula 4 :=
  ex (ex (.conj (orderedPairFormula 2 1 0) (renameStepFormula 4 5 3 1 0)))

def renameCertificateFormula : SetFormula 3 := postfixedFormula renameStateFormula

end PartitionPilot.Forcing.SetFormula

end


end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Definability_RawCheckFormulas
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace PartitionPilot.Forcing.SetFormula

def checkStepFormula {n : Nat} (top r x y : Fin n) : SetFormula n :=
  .conj
    (.all (imp (.mem 0 x.succ) (ex (.conj (pairMembershipFormula 1 0 r.succ.succ)
      (pairMembershipFormula 0 top.succ.succ y.succ.succ)))))
    (.all (imp (.mem 0 y.succ) (ex (ex (.conj (.mem 1 x.succ.succ.succ)
      (.conj (pairMembershipFormula 1 0 r.succ.succ.succ)
        (orderedPairFormula 2 0 top.succ.succ.succ)))))))

end PartitionPilot.Forcing.SetFormula

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Geometry_CheckCertificates
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace PartitionPilot.Forcing.SetFormula

def checkStateFormula : SetFormula 3 :=
  ex (ex (.conj (orderedPairFormula 2 1 0) (checkStepFormula 4 3 1 0)))

def checkCertificateFormula : SetFormula 2 := postfixedFormula checkStateFormula

end PartitionPilot.Forcing.SetFormula

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Forcing_IndexedTupleNames
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace PartitionPilot.Forcing
open SetRealization SetFormula
universe u

noncomputable def pairNameCode (one x y : ZFSet.{u}) : ZFSet.{u} :=
  {ZFSet.pair x one, ZFSet.pair y one}

noncomputable def orderedPairNameCode (one x y : ZFSet.{u}) : ZFSet.{u} :=
  pairNameCode one (pairNameCode one x x) (pairNameCode one x y)

namespace SetFormula

def pairNameCodeFormula {n} (z x y one : Fin n) : SetFormula n :=
  ex (ex (.conj (orderedPairFormula 1 x.succ.succ one.succ.succ)
    (.conj (orderedPairFormula 0 y.succ.succ one.succ.succ)
      (unorderedPairFormula z.succ.succ 1 0))))

def orderedPairNameCodeFormula {n} (z x y one : Fin n) : SetFormula n :=
  ex (ex (.conj (pairNameCodeFormula 1 x.succ.succ x.succ.succ one.succ.succ)
    (.conj (pairNameCodeFormula 0 x.succ.succ y.succ.succ one.succ.succ)
      (pairNameCodeFormula z.succ.succ 1 0 one.succ.succ))))

end SetFormula

end PartitionPilot.Forcing



namespace PartitionPilot.Forcing
universe u

noncomputable def orderedPairNameFamily (one X Y : ZFSet.{u}) : ZFSet.{u} :=
  ZFSet.range (fun p : X × Y => orderedPairNameCode one p.1.val p.2.val)

theorem mem_orderedPairNameFamily (one X Y z : ZFSet.{u}) :
    z ∈ orderedPairNameFamily one X Y ↔
      ∃ x ∈ X, ∃ y ∈ Y, z = orderedPairNameCode one x y := by
  rw [orderedPairNameFamily, ZFSet.mem_range]
  constructor
  · rintro ⟨p, equal⟩
    exact ⟨p.1.val, p.1.property, p.2.val, p.2.property, equal.symm⟩
  · rintro ⟨x, hx, y, hy, equal⟩
    exact ⟨(⟨x, hx⟩, ⟨y, hy⟩), equal.symm⟩

theorem pairNameCode_subset {one x y B : ZFSet.{u}} (hx : x ∈ B) (hy : y ∈ B) :
    pairNameCode one x y ⊆ ZFSet.prod B {one} := by
  intro z hz
  rcases ZFSet.mem_pair.1 hz with rfl | rfl
  · exact ZFSet.pair_mem_prod.2 ⟨hx, ZFSet.mem_singleton.2 rfl⟩
  · exact ZFSet.pair_mem_prod.2 ⟨hy, ZFSet.mem_singleton.2 rfl⟩

noncomputable def iteratedPairNameFamily (one T : ZFSet.{u}) : Nat → ZFSet.{u}
  | 0 => T
  | n + 1 => orderedPairNameFamily one (iteratedPairNameFamily one T n) T

end PartitionPilot.Forcing



end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Transfinite_GroundOrdinalOrderCodes
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace PartitionPilot.Forcing

universe u

noncomputable def ordinalImageOrder (A N f : ZFSet.{u}) : ZFSet.{u} :=
  ZFSet.sep (fun z => ∃ m ∈ N, ∃ n ∈ N, z = ZFSet.pair m n ∧
    ∃ x ∈ A, ∃ y ∈ A, ZFSet.pair x m ∈ f ∧ ZFSet.pair y n ∈ f ∧ (x = y ∨ x ∈ y))
    (ZFSet.prod N N)

theorem ordinalImageOrder_subset (A N f : ZFSet.{u}) :
    ordinalImageOrder A N f ⊆ ZFSet.prod N N := fun _ hz => (ZFSet.mem_sep.1 hz).1

theorem mem_ordinalImageOrder (A N f z : ZFSet.{u}) :
    z ∈ ordinalImageOrder A N f ↔ ∃ m ∈ N, ∃ n ∈ N, z = ZFSet.pair m n ∧
      ∃ x ∈ A, ∃ y ∈ A, ZFSet.pair x m ∈ f ∧ ZFSet.pair y n ∈ f ∧ (x = y ∨ x ∈ y) := by
  rw [ordinalImageOrder, ZFSet.mem_sep]
  exact ⟨And.right, fun h => ⟨by
    obtain ⟨m, hm, n, hn, eq, _⟩ := h
    exact eq.symm ▸ ZFSet.pair_mem_prod.2 ⟨hm, hn⟩, h⟩⟩

theorem pair_mem_ordinalImageOrder {A N f : ZFSet.{u}} (injection : InjectionCode A N f)
    (m n : ZFSet.{u}) :
    ZFSet.pair m n ∈ ordinalImageOrder A N f ↔
      ∃ x ∈ A, ∃ y ∈ A, ZFSet.pair x m ∈ f ∧ ZFSet.pair y n ∈ f ∧ (x = y ∨ x ∈ y) := by
  rw [mem_ordinalImageOrder]
  constructor
  · rintro ⟨a, _, b, _, eq, witnesses⟩
    obtain ⟨rfl, rfl⟩ := ZFSet.pair_inj.1 eq
    exact witnesses
  · rintro ⟨x, hx, y, hy, xm, yn, order⟩
    exact ⟨m, (ZFSet.pair_mem_prod.1 (injection.function.1 xm)).2,
      n, (ZFSet.pair_mem_prod.1 (injection.function.1 yn)).2, rfl, x, hx, y, hy, xm, yn, order⟩

structure OrdinalOrderCode (A N f r : ZFSet.{u}) : Prop where
  ordinal : ordinalSetProperty A
  injection : InjectionCode A N f
  shape : r ⊆ ZFSet.prod N N
  order : ∀ m n, ZFSet.pair m n ∈ r ↔
    ∃ x ∈ A, ∃ y ∈ A, ZFSet.pair x m ∈ f ∧ ZFSet.pair y n ∈ f ∧ (x = y ∨ x ∈ y)

theorem ordinalImageOrder_code {A N f : ZFSet.{u}}
    (ordinal : ordinalSetProperty A) (injection : InjectionCode A N f) :
    OrdinalOrderCode A N f (ordinalImageOrder A N f) :=
  ⟨ordinal, injection, ordinalImageOrder_subset A N f, pair_mem_ordinalImageOrder injection⟩

end PartitionPilot.Forcing


section

namespace PartitionPilot.Forcing.OrdinalOrderCode

universe u
variable {A B N f g r : ZFSet.{u}}

theorem predecessor_exists (ha : OrdinalOrderCode A N f r) (hb : OrdinalOrderCode B N g r)
    {x y m : ZFSet.{u}} (hx : x ∈ A) (hy : y ∈ B)
    (fx : ZFSet.pair x m ∈ f) (gy : ZFSet.pair y m ∈ g)
    (z : ZFSet.{u}) (hz : z ∈ x) :
    ∃ w ∈ y, ∃ n, ZFSet.pair z n ∈ f ∧ ZFSet.pair w n ∈ g := by
  have hzA : z ∈ A := ha.ordinal.1 x hx z hz
  obtain ⟨n, fz, _⟩ := ha.injection.function.2 z hzA
  have relation : ZFSet.pair n m ∈ r :=
    (ha.order n m).2 ⟨z, hzA, x, hx, fz, fx, Or.inr hz⟩
  obtain ⟨w, _, v, _, gw, gv, lower⟩ := (hb.order n m).1 relation
  have vy : v = y := hb.injection.injective v y m gv gy
  rw [vy] at lower
  have different : w ≠ y := by
    intro same
    obtain ⟨k, _, unique⟩ := hb.injection.function.2 y hy
    have nm : n = m := (unique n (same ▸ gw)).trans (unique m gy).symm
    have zx : z = x := ha.injection.injective z x m (nm ▸ fz) fx
    exact ZFSet.mem_irrefl x (zx ▸ hz)
  exact ⟨w, lower.resolve_left different, n, fz, gw⟩

theorem matched_value_unique (ha : OrdinalOrderCode A N f r) (hb : OrdinalOrderCode B N g r) :
    ∀ x ∈ A, ∀ y ∈ B, ∀ m, ZFSet.pair x m ∈ f → ZFSet.pair y m ∈ g → x = y := by
  intro x
  induction x using ZFSet.inductionOn with
  | h x ih =>
    intro hx y hy m fx gy
    apply ZFSet.ext
    intro z
    constructor
    · intro hz
      obtain ⟨w, hw, n, fz, gw⟩ := ha.predecessor_exists hb hx hy fx gy z hz
      have same := ih z hz (ha.ordinal.1 x hx z hz) w (hb.ordinal.1 y hy w hw) n fz gw
      exact same.symm ▸ hw
    · intro hz
      obtain ⟨w, hw, n, gz, fw⟩ := hb.predecessor_exists ha hy hx gy fx z hz
      have same := ih w hw (ha.ordinal.1 x hx w hw) z (hb.ordinal.1 y hy z hz) n fw gz
      exact same ▸ hw

theorem domain_unique (ha : OrdinalOrderCode A N f r) (hb : OrdinalOrderCode B N g r) : A = B := by
  apply ZFSet.ext
  intro x
  constructor
  · intro hx
    obtain ⟨m, fx, _⟩ := ha.injection.function.2 x hx
    have diagonal : ZFSet.pair m m ∈ r :=
      (ha.order m m).2 ⟨x, hx, x, hx, fx, fx, Or.inl rfl⟩
    obtain ⟨y, hy, _, _, gy, _, _⟩ := (hb.order m m).1 diagonal
    exact (ha.matched_value_unique hb x hx y hy m fx gy).symm ▸ hy
  · intro hx
    obtain ⟨m, gx, _⟩ := hb.injection.function.2 x hx
    have diagonal : ZFSet.pair m m ∈ r :=
      (hb.order m m).2 ⟨x, hx, x, hx, gx, gx, Or.inl rfl⟩
    obtain ⟨y, hy, _, _, fy, _, _⟩ := (ha.order m m).1 diagonal
    exact (hb.matched_value_unique ha x hx y hy m gx fy).symm ▸ hy

end PartitionPilot.Forcing.OrdinalOrderCode

namespace PartitionPilot.Forcing

universe u

theorem ordinalImageOrder_domain_unique {A B N f g : ZFSet.{u}}
    (hA : ordinalSetProperty A) (hB : ordinalSetProperty B)
    (hf : InjectionCode A N f) (hg : InjectionCode B N g)
    (eq : ordinalImageOrder A N f = ordinalImageOrder B N g) : A = B := by
  have right : OrdinalOrderCode B N g (ordinalImageOrder A N f) :=
    eq.symm ▸ ordinalImageOrder_code hB hg
  exact (ordinalImageOrder_code hA hf).domain_unique right

end PartitionPilot.Forcing

end


namespace PartitionPilot.Forcing.BoundedFormula

open SetFormula
universe u

def ordinalImagePairFormula {k} (m n a f : Fin k) : BoundedFormula k :=
  exMem a (exMem a.succ (.conj (pairMembershipFormula 1 m.succ.succ f.succ.succ)
    (.conj (pairMembershipFormula 0 n.succ.succ f.succ.succ) (disj (.equal 1 0) (.mem 1 0)))))

def ordinalImageEntryFormula {k} (z a n f : Fin k) : BoundedFormula k :=
  exMem n (exMem n.succ (.conj (orderedPairFormula z.succ.succ 1 0)
    (ordinalImagePairFormula 1 0 a.succ.succ f.succ.succ)))

def ordinalImageFormula {k} (r a n f : Fin k) : BoundedFormula k :=
  .conj (.allMem r (ordinalImageEntryFormula 0 a.succ n.succ f.succ))
    (.allMem n (.allMem n.succ (imp (ordinalImagePairFormula 1 0 a.succ.succ f.succ.succ)
      (pairMembershipFormula 1 0 r.succ.succ))))

end PartitionPilot.Forcing.BoundedFormula

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Forcing_GroundMixtureNames
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open scoped ZFSet


section

namespace PartitionPilot.Forcing.SetFormula

def restrictionEntryFormula : SetFormula 5 :=
  ex (exConditions 4 (exConditions 5 (.conj (orderedPairFormula 3 2 1)
    (.conj (pairMembershipFormula 2 0 4)
      (.conj (pairMembershipFormula 1 0 7) (pairMembershipFormula 1 5 7))))))

end PartitionPilot.Forcing.SetFormula

end


end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Models_GroundSuccessorInjections
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace PartitionPilot.Forcing

universe u

noncomputable def shiftedInjectionGraph (D f : ZFSet.{u}) : ZFSet.{u} :=
  ZFSet.sep (fun z => ∃ x ∈ D, ∃ n ∈ ZFSet.omega,
    z = ZFSet.pair x (insert n n) ∧ ZFSet.pair x n ∈ f) (ZFSet.prod D ZFSet.omega)

theorem mem_shiftedInjectionGraph (D f z : ZFSet.{u}) :
    z ∈ shiftedInjectionGraph D f ↔ ∃ x ∈ D, ∃ n ∈ ZFSet.omega,
      z = ZFSet.pair x (insert n n) ∧ ZFSet.pair x n ∈ f := by
  rw [shiftedInjectionGraph, ZFSet.mem_sep]
  constructor
  · exact And.right
  · intro h
    obtain ⟨x, hx, n, hn, eq, rel⟩ := h
    exact ⟨eq.symm ▸ ZFSet.pair_mem_prod.2 ⟨hx, ZFSet.omega_succ hn⟩,
      x, hx, n, hn, eq, rel⟩

theorem pair_mem_shiftedInjectionGraph (D f x y : ZFSet.{u}) :
    ZFSet.pair x y ∈ shiftedInjectionGraph D f ↔
      x ∈ D ∧ ∃ n ∈ ZFSet.omega, y = insert n n ∧ ZFSet.pair x n ∈ f := by
  rw [mem_shiftedInjectionGraph]
  constructor
  · rintro ⟨a, ha, n, hn, eq, rel⟩
    obtain ⟨rfl, rfl⟩ := ZFSet.pair_inj.1 eq
    exact ⟨ha, n, hn, rfl, rel⟩
  · rintro ⟨hx, n, hn, rfl, rel⟩
    exact ⟨x, hx, n, hn, rfl, rel⟩

noncomputable def adjoinInjectionGraph (D f a : ZFSet.{u}) : ZFSet.{u} :=
  insert (ZFSet.pair a ∅) (shiftedInjectionGraph D f)

theorem pair_mem_adjoinInjectionGraph (D f a x y : ZFSet.{u}) :
    ZFSet.pair x y ∈ adjoinInjectionGraph D f a ↔
      (x = a ∧ y = ∅) ∨ ZFSet.pair x y ∈ shiftedInjectionGraph D f := by
  rw [adjoinInjectionGraph, ZFSet.mem_insert_iff, ZFSet.pair_inj]

end PartitionPilot.Forcing



end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Definability_TaggedSumPresentations
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI



namespace PartitionPilot.Forcing
open SetRealization SetFormula
universe u






namespace BoundedFormula

def finiteWordFormula {n} (omega alphabet graph : Fin n) : BoundedFormula n :=
  exMem omega (functionFormula 0 alphabet.succ graph.succ)

end BoundedFormula

end PartitionPilot.Forcing


end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Models_GroundCountableQuotients
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PartitionPilot.Forcing

universe u

structure EquivalenceRelationCode (S E : ZFSet.{u}) : Prop where
  shape : E ⊆ ZFSet.prod S S
  refl : ∀ x ∈ S, ZFSet.pair x x ∈ E
  symm : ∀ x y, ZFSet.pair x y ∈ E → ZFSet.pair y x ∈ E
  trans : ∀ x y z, ZFSet.pair x y ∈ E → ZFSet.pair y z ∈ E → ZFSet.pair x z ∈ E

def canonicalRepresentativeProperty (S E c x : ZFSet.{u}) : Prop :=
  ∃ n ∈ ZFSet.omega, ZFSet.pair x n ∈ c ∧
    ∀ y ∈ S, ZFSet.pair x y ∈ E → ∀ m ∈ n, ZFSet.pair y m ∉ c

noncomputable def canonicalRepresentatives (S E c : ZFSet.{u}) : ZFSet.{u} :=
  ZFSet.sep (canonicalRepresentativeProperty S E c) S

theorem mem_canonicalRepresentatives (S E c x : ZFSet.{u}) :
    x ∈ canonicalRepresentatives S E c ↔ x ∈ S ∧ canonicalRepresentativeProperty S E c x :=
  ZFSet.mem_sep

theorem canonicalRepresentatives_subset (S E c : ZFSet.{u}) :
    canonicalRepresentatives S E c ⊆ S :=
  fun _ h => (ZFSet.mem_sep.1 h).1

noncomputable def canonicalRepresentativesInjection (S E c : ZFSet.{u}) : ZFSet.{u} :=
  ZFSet.sep (fun z => z ∈ ZFSet.prod (canonicalRepresentatives S E c) ZFSet.omega) c

end PartitionPilot.Forcing

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Forcing_CodedDenseOrders
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace PartitionPilot.Forcing

universe u

structure StrictLinearOrderCode (D r : ZFSet.{u}) : Prop where
  shape : r ⊆ ZFSet.prod D D
  irrefl : ∀ x ∈ D, ZFSet.pair x x ∉ r
  trans : ∀ x y z, ZFSet.pair x y ∈ r → ZFSet.pair y z ∈ r → ZFSet.pair x z ∈ r
  compare : ∀ x ∈ D, ∀ y ∈ D, ZFSet.pair x y ∈ r ∨ x = y ∨ ZFSet.pair y x ∈ r

structure DenseOrderCode (D r : ZFSet.{u}) : Prop extends StrictLinearOrderCode D r where
  between : ∀ x y, ZFSet.pair x y ∈ r → ∃ z ∈ D, ZFSet.pair x z ∈ r ∧ ZFSet.pair z y ∈ r

end PartitionPilot.Forcing

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Forcing_GroundPairNameFamilies
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace PartitionPilot.Forcing
open SetFormula
universe u

namespace SetFormula

def orderedPairNameFamilyMemberFormula {n} (z one X Y : Fin n) : SetFormula n :=
  ex (.conj (.mem 0 X.succ) (ex (.conj (.mem 0 Y.succ.succ)
    (orderedPairNameCodeFormula z.succ.succ 1 0 one.succ.succ))))

end SetFormula

end PartitionPilot.Forcing

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Definability_EquivalenceClassCodes
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace PartitionPilot.Forcing

universe u

noncomputable def equivalenceClass (A E y : ZFSet.{u}) : ZFSet.{u} :=
  ZFSet.sep (fun x => ZFSet.pair x y ∈ E) A

theorem mem_equivalenceClass (A E y x : ZFSet.{u}) :
    x ∈ equivalenceClass A E y ↔ x ∈ A ∧ ZFSet.pair x y ∈ E :=
  ZFSet.mem_sep

theorem equivalenceClass_subset (A E y : ZFSet.{u}) : equivalenceClass A E y ⊆ A :=
  fun _ h => (mem_equivalenceClass A E y _).1 h |>.1

noncomputable def equivalenceClasses (A E : ZFSet.{u}) : ZFSet.{u} :=
  ZFSet.sep (fun C => ∃ y ∈ A, C = equivalenceClass A E y) (ZFSet.powerset A)

theorem mem_equivalenceClasses (A E C : ZFSet.{u}) :
    C ∈ equivalenceClasses A E ↔ ∃ y ∈ A, C = equivalenceClass A E y := by
  rw [equivalenceClasses, ZFSet.mem_sep, ZFSet.mem_powerset]
  exact ⟨And.right, fun ⟨y, hy, equal⟩ =>
    ⟨equal ▸ equivalenceClass_subset A E y, y, hy, equal⟩⟩

theorem equivalenceClass_mem {A E y : ZFSet.{u}} (hy : y ∈ A) :
    equivalenceClass A E y ∈ equivalenceClasses A E :=
  (mem_equivalenceClasses A E _).2 ⟨y, hy, rfl⟩

noncomputable def equivalenceClassifier (A E : ZFSet.{u}) : ZFSet.{u} :=
  ZFSet.sep (fun z => ∃ y ∈ A, z = ZFSet.pair y (equivalenceClass A E y))
    (ZFSet.prod A (equivalenceClasses A E))

theorem mem_equivalenceClassifier (A E z : ZFSet.{u}) :
    z ∈ equivalenceClassifier A E ↔
      ∃ y ∈ A, z = ZFSet.pair y (equivalenceClass A E y) := by
  rw [equivalenceClassifier, ZFSet.mem_sep]
  refine ⟨And.right, ?_⟩
  rintro ⟨y, hy, rfl⟩
  exact ⟨ZFSet.pair_mem_prod.2 ⟨hy, equivalenceClass_mem hy⟩, y, hy, rfl⟩

theorem pair_mem_equivalenceClassifier (A E y C : ZFSet.{u}) :
    ZFSet.pair y C ∈ equivalenceClassifier A E ↔
      y ∈ A ∧ C = equivalenceClass A E y := by
  rw [mem_equivalenceClassifier]
  constructor
  · rintro ⟨x, hx, equal⟩
    obtain ⟨rfl, equal⟩ := ZFSet.pair_inj.1 equal
    exact ⟨hx, equal⟩
  · rintro ⟨hy, rfl⟩
    exact ⟨y, hy, rfl⟩

theorem equivalenceClassifier_function (A E : ZFSet.{u}) :
    ZFSet.IsFunc A (equivalenceClasses A E) (equivalenceClassifier A E) := by
  refine ⟨fun _ h => (ZFSet.mem_sep.1 h).1, ?_⟩
  intro y hy
  exact ⟨equivalenceClass A E y,
    (pair_mem_equivalenceClassifier A E y _).2 ⟨hy, rfl⟩,
    fun C hC => ((pair_mem_equivalenceClassifier A E y C).1 hC).2⟩

theorem equivalenceClassifier_onto {A E C : ZFSet.{u}}
    (hC : C ∈ equivalenceClasses A E) :
    ∃ y ∈ A, ZFSet.pair y C ∈ equivalenceClassifier A E := by
  obtain ⟨y, hy, rfl⟩ := (mem_equivalenceClasses A E C).1 hC
  exact ⟨y, hy, (pair_mem_equivalenceClassifier A E y _).2 ⟨hy, rfl⟩⟩

namespace EquivalenceRelationCode

theorem class_self {A E : ZFSet.{u}} (equivalence : EquivalenceRelationCode A E)
    {x : ZFSet.{u}} (hx : x ∈ A) : x ∈ equivalenceClass A E x :=
  (mem_equivalenceClass A E x x).2 ⟨hx, equivalence.refl x hx⟩

theorem class_eq_iff {A E : ZFSet.{u}} (equivalence : EquivalenceRelationCode A E)
    {x y : ZFSet.{u}} (hx : x ∈ A) (_hy : y ∈ A) :
    equivalenceClass A E x = equivalenceClass A E y ↔ ZFSet.pair x y ∈ E := by
  constructor
  · intro equal
    exact ((mem_equivalenceClass A E y x).1 (equal ▸ equivalence.class_self hx)).2
  · intro related
    apply ZFSet.ext
    intro z
    rw [mem_equivalenceClass, mem_equivalenceClass]
    exact and_congr_right (fun _ => ⟨
      fun h => equivalence.trans z x y h related,
      fun h => equivalence.trans z y x h (equivalence.symm x y related)⟩)

theorem classifier_kernel {A E : ZFSet.{u}} (equivalence : EquivalenceRelationCode A E)
    {x y C D : ZFSet.{u}}
    (first : ZFSet.pair x C ∈ equivalenceClassifier A E)
    (second : ZFSet.pair y D ∈ equivalenceClassifier A E) :
    C = D ↔ ZFSet.pair x y ∈ E := by
  obtain ⟨hx, rfl⟩ := (pair_mem_equivalenceClassifier A E x C).1 first
  obtain ⟨hy, rfl⟩ := (pair_mem_equivalenceClassifier A E y D).1 second
  exact equivalence.class_eq_iff hx hy

end EquivalenceRelationCode

end PartitionPilot.Forcing

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Geometry_RowPositionBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace PartitionPilot.Forcing
open SetFormula SetRealization
universe u

def RowPositionSequenceAt (L r I delta f : ZFSet.{u}) : Prop :=
  ZFSet.IsFunc delta I f ∧ ∃ D ∈ L, ∀ a x, ZFSet.pair a x ∈ f → ZFSet.pair x D ∈ r

def RowPositionSequenceCode (L r I mu f : ZFSet.{u}) : Prop :=
  ∃ delta ∈ insert mu mu, RowPositionSequenceAt L r I delta f

namespace BoundedFormula

def rowPositionSequenceAtFormula {n} (L r I delta f : Fin n) : BoundedFormula n :=
  .conj (functionFormula delta I f)
    (exMem L (.allMem delta.succ (.allMem I.succ.succ
      (imp (pairMembershipFormula 1 0 f.succ.succ.succ)
        (pairMembershipFormula 0 2 r.succ.succ.succ)))))

def rowPositionSequenceFormula {n} (L r I mu f : Fin n) : BoundedFormula n :=
  disj (rowPositionSequenceAtFormula L r I mu f)
    (exMem mu (rowPositionSequenceAtFormula L.succ r.succ I.succ 0 f.succ))

end BoundedFormula

end PartitionPilot.Forcing



namespace PartitionPilot.Forcing
open SetRealization SetFormula
universe u

def RowPositionBound (mu I r f D : ZFSet.{u}) : Prop :=
  f ⊆ ZFSet.prod mu I ∧ ∀ a x, ZFSet.pair a x ∈ f → ZFSet.pair x D ∈ r

namespace BoundedFormula

def rowPositionBoundFormula {n} (mu I r f D : Fin n) : BoundedFormula n :=
  .conj (relationBetweenFormula mu I f)
    (.allMem mu (.allMem I.succ
      (imp (pairMembershipFormula 1 0 f.succ.succ) (pairMembershipFormula 0 D.succ.succ r.succ.succ))))

end BoundedFormula

end PartitionPilot.Forcing

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Geometry_GroundLiteralTaskFieldRecognition
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI



namespace PartitionPilot.Forcing
open SetFormula
universe u
namespace SetFormula

def literalTaskFieldSetFormula {n} (j : Fin 6) (output I P R U Labels : Fin n) : SetFormula n :=
  exactSetFormula output
    (BoundedFormula.literalTaskFieldEntryFormula j 0 I.succ P.succ R.succ U.succ Labels.succ).toFormula

end SetFormula

end PartitionPilot.Forcing

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Definability_GroundRefinementPairClassGraphs
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace PartitionPilot.Forcing



section
open SetFormula SetRealization
universe u v

noncomputable def familyCodeGraph {I : Type v} [Small.{u} I]
    (key value : I → ZFSet.{u}) : ZFSet.{u} :=
  ZFSet.range (fun i => ZFSet.pair (key i) (value i))

theorem mem_familyCodeGraph {I : Type v} [Small.{u} I]
    (key value : I → ZFSet.{u}) (z : ZFSet.{u}) :
    z ∈ familyCodeGraph key value ↔ ∃ i, ZFSet.pair (key i) (value i) = z :=
  ZFSet.mem_range

theorem pair_mem_familyCodeGraph {I : Type v} [Small.{u} I]
    (key value : I → ZFSet.{u}) (injective : Function.Injective key)
    (i : I) (y : ZFSet.{u}) :
    ZFSet.pair (key i) y ∈ familyCodeGraph key value ↔ y = value i := by
  rw [mem_familyCodeGraph]
  constructor
  · rintro ⟨j, equal⟩
    obtain ⟨keys, values⟩ := ZFSet.pair_inj.1 equal
    have equalIndex := injective keys
    simpa only [equalIndex] using values.symm
  · intro equal
    exact ⟨i, congrArg (ZFSet.pair (key i)) equal.symm⟩

theorem familyCodeGraph_isFunc {I : Type v} [Small.{u} I]
    (key value : I → ZFSet.{u}) (injective : Function.Injective key) :
    ZFSet.IsFunc (ZFSet.range key) (ZFSet.range value) (familyCodeGraph key value) := by
  refine ⟨?_, ?_⟩
  · intro z hz
    obtain ⟨i, rfl⟩ := (mem_familyCodeGraph key value z).1 hz
    exact ZFSet.pair_mem_prod.2 ⟨ZFSet.mem_range.2 ⟨i, rfl⟩, ZFSet.mem_range.2 ⟨i, rfl⟩⟩
  · intro x hx
    obtain ⟨i, rfl⟩ := ZFSet.mem_range.1 hx
    exact ⟨value i, (pair_mem_familyCodeGraph key value injective i _).2 rfl,
      fun y hy => (pair_mem_familyCodeGraph key value injective i y).1 hy⟩

end



open SetRealization SetFormula
universe u

namespace SetFormula

def orderedPairNameGraphEntryFormula : SetFormula 5 :=
  ex (ex (ex (ex (.conj (.mem 3 5)
    (.conj (pairMembershipFormula 3 2 6) (.conj (pairMembershipFormula 3 1 7)
      (.conj (orderedPairNameCodeFormula 0 2 1 8) (orderedPairFormula 4 3 0))))))))

end SetFormula


end PartitionPilot.Forcing

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Geometry_FiniteIterationTraces
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace PartitionPilot.Forcing

open SetRealization
universe u

def natIterate {B : Type u} (f : B → B) (b : B) : Nat → B
  | 0 => b
  | n + 1 => f (natIterate f b n)

end PartitionPilot.Forcing

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Definability_DepthSlotCodes
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PartitionPilot.Forcing

open SetRealization
universe u

theorem natIterate_successor (a b : Nat) :
    natIterate (fun n : ULift.{u} Nat => ⟨n.down + 1⟩) ⟨a⟩ b = ⟨a + b⟩ := by
  induction b with
  | zero => rfl
  | succ b ih => simp only [natIterate, ih, Nat.add_succ]

theorem natIterate_add (a b : Nat) :
    natIterate (fun n : ULift.{u} Nat => ⟨a + n.down⟩) ⟨0⟩ b = ⟨a * b⟩ := by
  induction b with
  | zero => rfl
  | succ b ih => simp only [natIterate, ih, Nat.mul_succ, Nat.add_comm]

def depthSlotIndex (n j : Nat) : Nat := 3 * n + j

theorem depthSlotIndex_lt_iff {n m j k : Nat} (hj : j < 3) (hk : k < 3) :
    depthSlotIndex n j < depthSlotIndex m k ↔ n < m ∨ (n = m ∧ j < k) := by
  unfold depthSlotIndex
  omega

theorem depthSlotIndex_eq_iff {n m j k : Nat} (hj : j < 3) (hk : k < 3) :
    depthSlotIndex n j = depthSlotIndex m k ↔ n = m ∧ j = k := by
  unfold depthSlotIndex
  omega

theorem depthSlotIndex_le_iff {n m j k : Nat} (hj : j < 3) (hk : k < 3) :
    depthSlotIndex n j ≤ depthSlotIndex m k ↔ n < m ∨ (n = m ∧ j ≤ k) := by
  unfold depthSlotIndex
  omega

end PartitionPilot.Forcing

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Definability_FiniteWordMapCodes
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PartitionPilot.Forcing

open SetRealization SetFormula
universe u

def FiniteWordMapCode (omega A B e f g : ZFSet.{u}) : Prop :=
  ∃ n ∈ omega, ZFSet.IsFunc n A f ∧ ZFSet.IsFunc n B g ∧
    ∀ i ∈ n, ∀ x ∈ A, ∀ y ∈ B,
      ZFSet.pair i x ∈ f → ZFSet.pair i y ∈ g → ZFSet.pair x y ∈ e

namespace BoundedFormula

def finiteWordMapFormula {k} (omega a b e f g : Fin k) : BoundedFormula k :=
  exMem omega (.conj (functionFormula 0 a.succ f.succ)
    (.conj (functionFormula 0 b.succ g.succ)
      (.allMem 0 (.allMem a.succ.succ (.allMem b.succ.succ.succ
        (imp (pairMembershipFormula 2 1 f.succ.succ.succ.succ)
          (imp (pairMembershipFormula 2 0 g.succ.succ.succ.succ)
            (pairMembershipFormula 1 0 e.succ.succ.succ.succ))))))))

end BoundedFormula

end PartitionPilot.Forcing

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Geometry_FiniteWordOperations
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace PartitionPilot.Forcing
open SetRealization
universe u

def FiniteWordAppendCode (A omega add f g h : ZFSet.{u}) : Prop :=
  ∃ m ∈ omega, ∃ n ∈ omega, ∃ p ∈ omega,
    ZFSet.IsFunc m A f ∧ ZFSet.IsFunc n A g ∧ ZFSet.IsFunc p A h ∧
      ZFSet.pair (ZFSet.pair m n) p ∈ add ∧
      ∀ i ∈ p, ∀ a ∈ A, ZFSet.pair i a ∈ h ↔
        ZFSet.pair i a ∈ f ∨ ∃ j ∈ n,
          ZFSet.pair (ZFSet.pair m j) i ∈ add ∧ ZFSet.pair j a ∈ g

def FiniteWordReverseCode (A omega add f h : ZFSet.{u}) : Prop :=
  ∃ n ∈ omega, ZFSet.IsFunc n A f ∧ ZFSet.IsFunc n A h ∧
    ∀ i ∈ n, ∀ a ∈ A, ZFSet.pair i a ∈ h ↔
      ∃ j ∈ n, ∃ k ∈ n, ZFSet.pair (ZFSet.pair i j) k ∈ add ∧
        n = insert k k ∧ ZFSet.pair j a ∈ f

end PartitionPilot.Forcing

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Geometry_GroundExternalAlphabetInversion
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PartitionPilot.Forcing

open SetRealization
universe u

def externalSymbolInverse {J L : Type u} [Inv J] : J ⊕ (L × Bool) → J ⊕ (L × Bool)
  | .inl g => .inl g⁻¹
  | .inr p => .inr (p.1, !p.2)

end PartitionPilot.Forcing



end

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Geometry_GroundFiniteWordLength
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

def finiteWordLengthEntryFormula {n} (z omega alphabet words : Fin n) : BoundedFormula n :=
  exMem words (exMem omega.succ
    (.conj (orderedPairFormula z.succ.succ 1 0) (functionFormula 0 alphabet.succ.succ 1)))

end BoundedFormula

end PartitionPilot.Forcing

end

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Geometry_GroundFiniteWordLaws
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace PartitionPilot.Forcing
open SetRealization SetFormula
universe u

namespace BoundedFormula

def finiteWordMapEntryFormula {k} (z wordsA wordsB omega a b e : Fin k) : BoundedFormula k :=
  exMem wordsA (exMem wordsB.succ (.conj (orderedPairFormula z.succ.succ 1 0)
    (finiteWordMapFormula omega.succ.succ a.succ.succ b.succ.succ e.succ.succ 1 0)))

end BoundedFormula






def externalWordInverse {J L : Type u} [Inv J] (xs : List (J ⊕ (L × Bool))) :
    List (J ⊕ (L × Bool)) := (xs.map externalSymbolInverse).reverse

end PartitionPilot.Forcing



end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Definability_GroundRationalCodes
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace PartitionPilot.Forcing

section

universe u

def gridStep (p : Nat × Nat) : Nat × Nat :=
  if p.1 < p.2 then
    if p.1 + 1 < p.2 then (p.1 + 1, p.2) else (p.2, 0)
  else if p.2 < p.1 then (p.1, p.2 + 1) else (0, p.1 + 1)

theorem gridStep_pair (a b : Nat) :
    Nat.pair (gridStep (a, b)).1 (gridStep (a, b)).2 = Nat.pair a b + 1 := by
  by_cases h : a < b
  · by_cases next : a + 1 < b
    · simp [gridStep, h, next, Nat.pair, Nat.add_assoc]
    · have eq : b = a + 1 := by omega
      simp [gridStep, Nat.pair, eq, Nat.add_assoc]
  · by_cases next : b < a
    · have hnext : ¬ a < b + 1 := by omega
      simp [gridStep, h, next, Nat.pair, hnext, Nat.add_assoc]
    · have eq : b = a := by omega
      subst b
      simp [gridStep, Nat.pair, Nat.mul_add, Nat.add_mul, Nat.add_assoc]

theorem gridStep_eq_iff (a b c d : Nat) : gridStep (a, b) = (c, d) ↔
    (c = a + 1 ∧ c < b ∧ d = b) ∨ (b = a + 1 ∧ c = b ∧ d = 0) ∨
    (b < a ∧ c = a ∧ d = b + 1) ∨ (a = b ∧ c = 0 ∧ d = a + 1) := by
  simp only [gridStep]
  split_ifs <;> simp only [Prod.mk.injEq] <;> omega

def liftedGridStep (p : ULift.{u} Nat × ULift.{u} Nat) : ULift.{u} Nat × ULift.{u} Nat :=
  (⟨(gridStep (p.1.down, p.2.down)).1⟩, ⟨(gridStep (p.1.down, p.2.down)).2⟩)

theorem gridIteration_pair (n : Nat) :
    Nat.pair (natIterate liftedGridStep ((⟨0⟩, ⟨0⟩) : ULift.{u} Nat × ULift.{u} Nat) n).1.down
      (natIterate liftedGridStep ((⟨0⟩, ⟨0⟩) : ULift.{u} Nat × ULift.{u} Nat) n).2.down = n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change Nat.pair (gridStep _).1 (gridStep _).2 = n + 1
    exact (gridStep_pair _ _).trans (congrArg (fun k => k + 1) ih)

def omegaGridEquiv : ULift.{u} Nat ≃ (ULift.{u} Nat × ULift.{u} Nat) where
  toFun n := (⟨(Nat.unpair n.down).1⟩, ⟨(Nat.unpair n.down).2⟩)
  invFun p := ⟨Nat.pair p.1.down p.2.down⟩
  left_inv n := ULift.ext _ _ (Nat.pair_unpair n.down)
  right_inv p := by
    apply Prod.ext
    · apply ULift.ext
      exact congrArg Prod.fst (Nat.unpair_pair p.1.down p.2.down)
    · apply ULift.ext
      exact congrArg Prod.snd (Nat.unpair_pair p.1.down p.2.down)

theorem gridIteration_eq (n : ULift.{u} Nat) :
    natIterate liftedGridStep (⟨0⟩, ⟨0⟩) n.down = omegaGridEquiv n := by
  apply omegaGridEquiv.symm.injective
  apply ULift.ext
  exact (gridIteration_pair n.down).trans (Nat.pair_unpair n.down).symm

end



section

universe u

def positiveMagnitude (code magnitude add : ZFSet.{u}) : Prop :=
  ZFSet.pair (ZFSet.pair magnitude magnitude) code ∈ add

def negativeMagnitude (code magnitude W add one : ZFSet.{u}) : Prop :=
  ∃ k ∈ W, ∃ d ∈ W,
    ZFSet.pair (ZFSet.pair k one) magnitude ∈ add ∧
    ZFSet.pair (ZFSet.pair k k) d ∈ add ∧
    ZFSet.pair (ZFSet.pair d one) code ∈ add

def fractionComparison (strict : Bool) (a ad b bd W add mul one : ZFSet.{u}) : Prop :=
  ∃ m ∈ W, ∃ n ∈ W, ∃ x ∈ W, ∃ y ∈ W,
    ZFSet.pair (ZFSet.pair m bd) x ∈ mul ∧
    ZFSet.pair (ZFSet.pair n ad) y ∈ mul ∧
    ((positiveMagnitude a m add ∧ positiveMagnitude b n add ∧
        (if strict then x ∈ y else x = y)) ∨
      (negativeMagnitude a m W add one ∧ negativeMagnitude b n W add one ∧
        (if strict then y ∈ x else x = y)) ∨
      (if strict then negativeMagnitude a m W add one ∧ positiveMagnitude b n add else False))

end



section

open SetRealization
universe u

def GridStepCode (a b c d : ZFSet.{u}) : Prop :=
  (c = insert a a ∧ c ∈ b ∧ d = b) ∨ (b = insert a a ∧ c = b ∧ d = ∅) ∨
  (b ∈ a ∧ c = a ∧ d = insert b b) ∨ (a = b ∧ c = ∅ ∧ d = insert a a)

end



end PartitionPilot.Forcing

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Forcing_UniformGroundSizeWitnesses
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PartitionPilot.Forcing

universe u

noncomputable def sizeWitnessRelation (R W N : ZFSet.{u}) : ZFSet.{u} :=
  ZFSet.sep (fun z => ∃ p ∈ R, ∃ f ∈ W, z = ZFSet.pair p f ∧ InjectionCode p N f) (ZFSet.prod R W)

theorem pair_mem_sizeWitnessRelation (R W N p f : ZFSet.{u}) :
    ZFSet.pair p f ∈ sizeWitnessRelation R W N ↔ p ∈ R ∧ f ∈ W ∧ InjectionCode p N f := by
  rw [sizeWitnessRelation, ZFSet.mem_sep]
  constructor
  · rintro ⟨_, q, hq, g, hg, eq, code⟩
    obtain ⟨rfl, rfl⟩ := ZFSet.pair_inj.1 eq
    exact ⟨hq, hg, code⟩
  · rintro ⟨hp, hf, code⟩
    exact ⟨ZFSet.pair_mem_prod.2 ⟨hp, hf⟩, p, hp, f, hf, rfl, code⟩

namespace BoundedFormula

open SetFormula

def sizeWitnessEntryFormula {k} (z r w n : Fin k) : BoundedFormula k :=
  exMem r (exMem w.succ (.conj (orderedPairFormula z.succ.succ 1 0)
    (injectionFormula 1 n.succ.succ 0)))

end BoundedFormula

end PartitionPilot.Forcing

end

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Transfinite_GroundCountableFunctionClosure
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open scoped ZFSet


namespace PartitionPilot.Forcing

universe u

noncomputable def indexedSizeRelation (U R W N g F : ZFSet.{u}) : ZFSet.{u} :=
  ZFSet.sep (fun z => ∃ x ∈ U, ∃ n ∈ N, ∃ k ∈ N, ∃ p ∈ R, ∃ f ∈ W,
    z = ZFSet.pair (ZFSet.pair n k) x ∧ ZFSet.pair n p ∈ g ∧
      ZFSet.pair p f ∈ F ∧ ZFSet.pair x k ∈ f) (ZFSet.prod (ZFSet.prod N N) U)

theorem pair_mem_indexedSizeRelation (U R W N g F v x : ZFSet.{u}) :
    ZFSet.pair v x ∈ indexedSizeRelation U R W N g F ↔
      x ∈ U ∧ ∃ n ∈ N, ∃ k ∈ N, v = ZFSet.pair n k ∧ ∃ p ∈ R, ∃ f ∈ W,
        ZFSet.pair n p ∈ g ∧ ZFSet.pair p f ∈ F ∧ ZFSet.pair x k ∈ f := by
  rw [indexedSizeRelation, ZFSet.mem_sep]
  constructor
  · rintro ⟨_, y, hy, n, hn, k, hk, p, hp, f, hf, eq, ng, pf, yk⟩
    obtain ⟨first, second⟩ := ZFSet.pair_inj.1 eq
    exact ⟨second.symm ▸ hy, n, hn, k, hk, first, p, hp, f, hf, ng, pf, second.symm ▸ yk⟩
  · rintro ⟨hx, n, hn, k, hk, rfl, p, hp, f, hf, ng, pf, xk⟩
    exact ⟨ZFSet.pair_mem_prod.2 ⟨ZFSet.pair_mem_prod.2 ⟨hn, hk⟩, hx⟩,
      x, hx, n, hn, k, hk, p, hp, f, hf, rfl, ng, pf, xk⟩

theorem indexedSizeRelation_onto {R W N g F : ZFSet.{u}}
    (onto : ∀ p ∈ R, ∃ n ∈ N, ZFSet.pair n p ∈ g) (family : ZFSet.IsFunc R W F)
    (codes : ∀ p f, ZFSet.pair p f ∈ F → InjectionCode p N f) :
    ∀ x ∈ ⋃₀ R, ∃ v ∈ ZFSet.prod N N,
      ZFSet.pair v x ∈ indexedSizeRelation (⋃₀ R) R W N g F := by
  intro x hx
  obtain ⟨p, hp, xp⟩ := ZFSet.mem_sUnion.1 hx
  obtain ⟨n, hn, np⟩ := onto p hp
  obtain ⟨f, pf, _⟩ := family.2 p hp
  have hf := (ZFSet.pair_mem_prod.1 (family.1 pf)).2
  have code := codes p f pf
  obtain ⟨k, xk, _⟩ := code.function.2 x xp
  have hk := (ZFSet.pair_mem_prod.1 (code.function.1 xk)).2
  exact ⟨ZFSet.pair n k, ZFSet.pair_mem_prod.2 ⟨hn, hk⟩,
    (pair_mem_indexedSizeRelation (⋃₀ R) R W N g F _ x).2
      ⟨hx, n, hn, k, hk, rfl, p, hp, f, hf, np, pf, xk⟩⟩





noncomputable def unionSizeRelation (U R W D F : ZFSet.{u}) : ZFSet.{u} :=
  ZFSet.sep (fun z => ∃ x ∈ U, ∃ A ∈ R, ∃ k ∈ D, ∃ f ∈ W,
    z = ZFSet.pair (ZFSet.pair A k) x ∧ ZFSet.pair A f ∈ F ∧ ZFSet.pair x k ∈ f)
    (ZFSet.prod (ZFSet.prod R D) U)

theorem pair_mem_unionSizeRelation (U R W D F v x : ZFSet.{u}) :
    ZFSet.pair v x ∈ unionSizeRelation U R W D F ↔
      x ∈ U ∧ ∃ A ∈ R, ∃ k ∈ D, v = ZFSet.pair A k ∧
        ∃ f ∈ W, ZFSet.pair A f ∈ F ∧ ZFSet.pair x k ∈ f := by
  rw [unionSizeRelation, ZFSet.mem_sep]
  constructor
  · rintro ⟨_, y, hy, A, hA, k, hk, f, hf, equal, selected, value⟩
    obtain ⟨first, second⟩ := ZFSet.pair_inj.1 equal
    exact ⟨second.symm ▸ hy, A, hA, k, hk, first, f, hf, selected, second.symm ▸ value⟩
  · rintro ⟨hx, A, hA, k, hk, rfl, f, hf, selected, value⟩
    exact ⟨ZFSet.pair_mem_prod.2 ⟨ZFSet.pair_mem_prod.2 ⟨hA, hk⟩, hx⟩,
      x, hx, A, hA, k, hk, f, hf, rfl, selected, value⟩

theorem unionSizeRelation_onto {R W D F : ZFSet.{u}}
    (family : ZFSet.IsFunc R W F)
    (codes : ∀ A f, ZFSet.pair A f ∈ F → InjectionCode A D f) :
    ∀ x ∈ ⋃₀ R, ∃ v ∈ ZFSet.prod R D,
      ZFSet.pair v x ∈ unionSizeRelation (⋃₀ R) R W D F := by
  intro x hx
  obtain ⟨A, hA, member⟩ := ZFSet.mem_sUnion.1 hx
  obtain ⟨f, selected, _⟩ := family.2 A hA
  have hf := (ZFSet.pair_mem_prod.1 (family.1 selected)).2
  have code := codes A f selected
  obtain ⟨k, value, _⟩ := code.function.2 x member
  have hk := (ZFSet.pair_mem_prod.1 (code.function.1 value)).2
  exact ⟨ZFSet.pair A k, ZFSet.pair_mem_prod.2 ⟨hA, hk⟩,
    (pair_mem_unionSizeRelation (⋃₀ R) R W D F _ x).2
      ⟨hx, A, hA, k, hk, rfl, f, hf, selected, value⟩⟩

end PartitionPilot.Forcing



end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Definability_GroundBelowFunctionGraphs
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI



namespace PartitionPilot.Forcing
open SetFormula
universe u

namespace SetFormula

def groundBelowFormula {n} (a k : Fin n) : SetFormula n :=
  ex (.conj (.mem 0 k.succ) (hasInjectionFormula a.succ 0))

end SetFormula

end PartitionPilot.Forcing



end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Transfinite_GroundCoinitialOperations
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace PartitionPilot.Forcing

section

universe u

def CoinitialBelowCode (order F target B : ZFSet.{u}) : Prop :=
  B ⊆ F ∧ ∀ x ∈ target, ∃ b ∈ B, ZFSet.pair b x ∈ order






def FiberCoveredCode (order target parts i B : ZFSet.{u}) : Prop :=
  ∀ x ∈ target, ZFSet.pair i x ∈ parts → ∃ b ∈ B, ZFSet.pair b x ∈ order

noncomputable def basisChoiceRelation (I W order target parts : ZFSet.{u}) : ZFSet.{u} :=
  ZFSet.sep (fun z => ∃ i ∈ I, ∃ B ∈ W, z = ZFSet.pair i B ∧
    FiberCoveredCode order target parts i B) (ZFSet.prod I W)

end



end PartitionPilot.Forcing

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Transfinite_GroundChronologicalBasis
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PartitionPilot.Forcing

universe u

noncomputable def birthEssentialSet (F T r birth : ZFSet.{u}) : ZFSet.{u} :=
  ZFSet.sep (fun x => ∀ y ∈ F, ∀ a ∈ T, ∀ b ∈ T,
    ZFSet.pair y x ∈ r → ZFSet.pair y a ∈ birth → ZFSet.pair x b ∈ birth → a ∉ b) F

end PartitionPilot.Forcing



end

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Geometry_GroundNaturalFamilyShift
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace PartitionPilot.Forcing



section

open SetRealization
universe u

theorem ordinalSetProperty_mem_compare {T i j : ZFSet.{u}}
    (ordinal : ordinalSetProperty T) (hi : i ∈ T) (hj : j ∈ T) :
    i ∈ j ∨ i = j ∨ j ∈ i := by
  obtain ⟨a, rfl⟩ := (ordinalSetProperty_iff i).1 (ordinalSetProperty_member ordinal hi)
  obtain ⟨b, rfl⟩ := (ordinalSetProperty_iff j).1 (ordinalSetProperty_member ordinal hj)
  rcases lt_trichotomy a b with less | eq | greater
  · exact Or.inl ((mem_ordinalCode_iff a b).2 less)
  · exact Or.inr (Or.inl (congrArg ordinalCode eq))
  · exact Or.inr (Or.inr ((mem_ordinalCode_iff b a).2 greater))

noncomputable def ordinalIndexTail (S i : ZFSet.{u}) : ZFSet.{u} :=
  ZFSet.sep (fun j => i = j ∨ i ∈ j) S






def EssentialHeightDescent (E birth height qlt : ZFSet.{u}) : Prop :=
  ∀ x ∈ E, ∀ y ∈ E, ∀ i j c q d v,
    ZFSet.pair x i ∈ birth → ZFSet.pair y j ∈ birth → i ∈ j →
    ZFSet.pair x (ZFSet.pair c q) ∈ height → ZFSet.pair y (ZFSet.pair d v) ∈ height →
      d ∈ c ∨ (d = c ∧ ZFSet.pair v q ∈ qlt)

theorem relationCompose_function_of_subset {A B D C f g : ZFSet.{u}}
    (first : ZFSet.IsFunc A B f) (second : ZFSet.IsFunc D C g) (subset : B ⊆ D) :
    ZFSet.IsFunc A C (relationCompose A B C f g) := by
  refine ⟨fun _ hz => (ZFSet.mem_sep.1 hz).1, ?_⟩
  intro x hx
  obtain ⟨y, xy, uniqueY⟩ := first.2 x hx
  have hy := (ZFSet.pair_mem_prod.1 (first.1 xy)).2
  obtain ⟨z, yz, uniqueZ⟩ := second.2 y (subset hy)
  have hz := (ZFSet.pair_mem_prod.1 (second.1 yz)).2
  refine ⟨z, (pair_mem_relationCompose A B C f g x z).2 ⟨hx, hz, y, hy, xy, yz⟩, ?_⟩
  intro w hw
  obtain ⟨_, _, y', _, xy', y'w⟩ := (pair_mem_relationCompose A B C f g x w).1 hw
  exact uniqueZ w (uniqueY y' xy' ▸ y'w)

end



open SetFormula
universe u


end PartitionPilot.Forcing

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Transfinite_GroundMainStageFromCodes
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace PartitionPilot.Forcing

section

universe u

def OldMeetCode (r μ birth : ZFSet.{u}) : Prop :=
  ∀ x y z a b c, ZFSet.pair y a ∈ birth → ZFSet.pair x b ∈ birth →
    a ∈ b → ZFSet.pair x y ∉ r → ZFSet.pair (ZFSet.pair x y) z ∈ μ →
      ZFSet.pair z c ∈ birth → c ∈ b

end



end PartitionPilot.Forcing

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Definability_NaturalStepFormulas
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace PartitionPilot.Forcing

section

universe u

namespace SetFormula

def functionGraphOnFormula {n} (a f : Fin n) : SetFormula n :=
  ex (BoundedFormula.functionFormula a.succ 0 f.succ).toFormula

end SetFormula

end




open SetFormula
universe u


end PartitionPilot.Forcing

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Definability_IntervalSequenceFormulas
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PartitionPilot.Forcing

universe u

structure IntervalSequenceCode (N A D rA rD e lo hi t : ZFSet.{u}) : Prop where
  function : ZFSet.IsFunc N D t
  inside : ∀ i q, ZFSet.pair i q ∈ t → ZFSet.pair lo q ∈ rD ∧ ZFSet.pair q hi ∈ rD
  agree : ∀ i j a b q z, ZFSet.pair i a ∈ e → ZFSet.pair j b ∈ e →
    ZFSet.pair i q ∈ t → ZFSet.pair j z ∈ t → (a = b ↔ q = z)
  order : ∀ i j a b q z, ZFSet.pair i a ∈ e → ZFSet.pair j b ∈ e →
    ZFSet.pair i q ∈ t → ZFSet.pair j z ∈ t →
      (ZFSet.pair a b ∈ rA ↔ ZFSet.pair q z ∈ rD)

def intervalNextCandidate (N A D rA rD e lo hi p y : ZFSet.{u}) : Prop :=
  y ∈ D ∧ ZFSet.pair lo y ∈ rD ∧ ZFSet.pair y hi ∈ rD ∧
    ∀ i ∈ N, ∀ a ∈ A, ∀ b ∈ A, ∀ z ∈ D,
      ZFSet.pair i a ∈ e → ZFSet.pair N b ∈ e → ZFSet.pair i z ∈ p →
        ((a = b ↔ z = y) ∧ (ZFSet.pair a b ∈ rA ↔ ZFSet.pair z y ∈ rD) ∧
          (ZFSet.pair b a ∈ rA ↔ ZFSet.pair y z ∈ rD))

end PartitionPilot.Forcing



namespace PartitionPilot.Forcing

universe u

def leastIntervalNextCandidate (N A D rA rD e lo hi p c y : ZFSet.{u}) : Prop :=
  intervalNextCandidate N A D rA rD e lo hi p y ∧
    ∃ n ∈ ZFSet.omega, ZFSet.pair y n ∈ c ∧
      ∀ z ∈ D, intervalNextCandidate N A D rA rD e lo hi p z →
        ∀ m ∈ n, ZFSet.pair z m ∉ c

namespace BoundedFormula

open SetFormula

def iffFormula {n} (φ ψ : BoundedFormula n) : BoundedFormula n :=
  .conj (imp φ ψ) (imp ψ φ)

def intervalNextCandidateFormula {n} (N A D rA rD e lo hi p y : Fin n) : BoundedFormula n :=
  let lift (i : Fin n) : Fin (n + 4) := i.succ.succ.succ.succ
  .conj (.mem y D) (.conj (pairMembershipFormula lo y rD)
    (.conj (pairMembershipFormula y hi rD)
      (.allMem N (.allMem A.succ (.allMem A.succ.succ (.allMem D.succ.succ.succ
        (imp (pairMembershipFormula 3 2 (lift e))
          (imp (pairMembershipFormula (lift N) 1 (lift e))
            (imp (pairMembershipFormula 3 0 (lift p))
              (.conj (iffFormula (.equal 2 1) (.equal 0 (lift y)))
                (.conj (iffFormula (pairMembershipFormula 2 1 (lift rA))
                    (pairMembershipFormula 0 (lift y) (lift rD)))
                  (iffFormula (pairMembershipFormula 1 2 (lift rA))
                    (pairMembershipFormula (lift y) 0 (lift rD))))))))))))))

def leastIntervalNextCandidateFormula {n} (N A D rA rD e lo hi p c y omega : Fin n) : BoundedFormula n :=
  .conj (intervalNextCandidateFormula N A D rA rD e lo hi p y)
    (exMem omega (.conj (pairMembershipFormula y.succ 0 c.succ)
      (.allMem D.succ (imp
        (intervalNextCandidateFormula N.succ.succ A.succ.succ D.succ.succ rA.succ.succ
          rD.succ.succ e.succ.succ lo.succ.succ hi.succ.succ p.succ.succ 0)
        (.allMem 1 (.neg (pairMembershipFormula 1 0 c.succ.succ.succ)))))))

end BoundedFormula

namespace SetFormula

def intervalSequenceStepFormula : SetFormula 12 :=
  (BoundedFormula.leastIntervalNextCandidateFormula 0 3 4 5 6 7 8 9 1 10 2 11).toFormula

end SetFormula

end PartitionPilot.Forcing

end

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Transfinite_GroundIntervalRecursion
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section



namespace PartitionPilot.Forcing

open SetFormula SetRealization
universe u

def intervalSequenceParams (A D rA rD e lo hi c : ZFSet.{u}) : Fin 9 → ZFSet.{u} :=
  extend A (extend D (extend rA (extend rD (extend e
    (extend lo (extend hi (extend c (extend ZFSet.omega Fin.elim0))))))))

end PartitionPilot.Forcing

end

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Geometry_IntervalEmbeddingFamilyCodes
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open scoped ZFSet


namespace PartitionPilot.Forcing

universe u

def leastInjectionMember (A f d : ZFSet.{u}) : Prop :=
  d ∈ A ∧ ∃ n ∈ ZFSet.omega, ZFSet.pair d n ∈ f ∧
    ∀ x ∈ A, ∀ m ∈ n, ZFSet.pair x m ∉ f

noncomputable def canonicalEnumerationDefault (A f : ZFSet.{u}) : ZFSet.{u} := by
  classical
  exact if h : ∃ d, leastInjectionMember A f d then Classical.choose h else ∅






noncomputable def intervalSequenceGraph (A D e t : ZFSet.{u}) : ZFSet.{u} :=
  ZFSet.sep (fun z => ∃ n ∈ ZFSet.omega, ∃ a ∈ A, ∃ q ∈ D,
    z = ZFSet.pair a q ∧ ZFSet.pair n a ∈ e ∧ ZFSet.pair n q ∈ t)
    (ZFSet.prod A D)






namespace BoundedFormula

open SetFormula

def intervalSequenceEntryFormula {n} (z a d e t omega : Fin n) : BoundedFormula n :=
  exMem omega (exMem a.succ (exMem d.succ.succ
    (.conj (orderedPairFormula z.succ.succ.succ 1 0)
      (.conj (pairMembershipFormula 2 1 e.succ.succ.succ)
        (pairMembershipFormula 2 0 t.succ.succ.succ)))))

end BoundedFormula

end PartitionPilot.Forcing



namespace PartitionPilot.Forcing

open SetFormula SetRealization
universe u

structure IntervalEmbeddingCode (A D rA rD lo hi f : ZFSet.{u}) : Prop where
  injection : InjectionCode A D f
  order : ∀ a b q z, ZFSet.pair a q ∈ f → ZFSet.pair b z ∈ f →
    (ZFSet.pair a b ∈ rA ↔ ZFSet.pair q z ∈ rD)
  inside : ∀ a q, ZFSet.pair a q ∈ f → ZFSet.pair lo q ∈ rD ∧ ZFSet.pair q hi ∈ rD

end PartitionPilot.Forcing



namespace PartitionPilot.Forcing

universe u

def intervalEmbeddingCandidate (As rs los his D rD i f : ZFSet.{u}) : Prop :=
  ∃ A ∈ ⋃₀ ⋃₀ As, ∃ rA ∈ ⋃₀ ⋃₀ rs, ∃ lo ∈ D, ∃ hi ∈ D,
    ZFSet.pair i A ∈ As ∧ ZFSet.pair i rA ∈ rs ∧
    ZFSet.pair i lo ∈ los ∧ ZFSet.pair i hi ∈ his ∧
    IntervalEmbeddingCode A D rA rD lo hi f

noncomputable def intervalEmbeddingRelation (I W As rs los his D rD : ZFSet.{u}) : ZFSet.{u} :=
  ZFSet.sep (fun z => ∃ i ∈ I, ∃ f ∈ W, z = ZFSet.pair i f ∧
    intervalEmbeddingCandidate As rs los his D rD i f) (ZFSet.prod I W)

end PartitionPilot.Forcing

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Definability_IntervalEmbeddingFormulas
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PartitionPilot.Forcing.BoundedFormula

open SetFormula
universe u

def intervalEmbeddingFormula {n} (A D rA rD lo hi f : Fin n) : BoundedFormula n :=
  let lift (i : Fin n) : Fin (n + 4) := i.succ.succ.succ.succ
  let order : BoundedFormula n :=
    .allMem A (.allMem A.succ (.allMem D.succ.succ (.allMem D.succ.succ.succ
      (imp (pairMembershipFormula 3 1 (lift f))
        (imp (pairMembershipFormula 2 0 (lift f))
          (iffFormula (pairMembershipFormula 3 2 (lift rA))
            (pairMembershipFormula 1 0 (lift rD))))))))
  let inside : BoundedFormula n :=
    .allMem A (.allMem D.succ (imp (pairMembershipFormula 1 0 f.succ.succ)
      (.conj (pairMembershipFormula lo.succ.succ 0 rD.succ.succ)
        (pairMembershipFormula 0 hi.succ.succ rD.succ.succ))))
  .conj (injectionFormula A D f) (.conj order inside)

end PartitionPilot.Forcing.BoundedFormula

end

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Geometry_GroundIntervalEmbeddingRelation
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

def intervalEmbeddingCandidateFormula {n}
    (As rs los his D rD i f boundAs boundRs : Fin n) : BoundedFormula n :=
  let lift (j : Fin n) : Fin (n + 4) := j.succ.succ.succ.succ
  exMem boundAs (exMem boundRs.succ (exMem D.succ.succ (exMem D.succ.succ.succ
    (.conj (pairMembershipFormula (lift i) 3 (lift As))
      (.conj (pairMembershipFormula (lift i) 2 (lift rs))
        (.conj (pairMembershipFormula (lift i) 1 (lift los))
          (.conj (pairMembershipFormula (lift i) 0 (lift his))
            (intervalEmbeddingFormula 3 (lift D) 2 (lift rD) 1 0 (lift f)))))))))

def intervalEmbeddingRelationEntryFormula {n}
    (z I W As rs los his D rD boundAs boundRs : Fin n) : BoundedFormula n :=
  exMem I (exMem W.succ
    (.conj (orderedPairFormula z.succ.succ 1 0)
      (intervalEmbeddingCandidateFormula As.succ.succ rs.succ.succ
        los.succ.succ his.succ.succ D.succ.succ rD.succ.succ 1 0
        boundAs.succ.succ boundRs.succ.succ)))

end BoundedFormula

end PartitionPilot.Forcing

end

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Definability_PairPushFilterFamilies
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PartitionPilot.Forcing

universe u

noncomputable def pushFilterCode (L rL S F : ZFSet.{u}) : ZFSet.{u} :=
  ZFSet.sep (fun y => ∃ f ∈ F, ∃ z ∈ L,
    ZFSet.pair f z ∈ S ∧ ZFSet.pair z y ∈ rL) L

theorem mem_pushFilterCode (L rL S F y : ZFSet.{u}) :
    y ∈ pushFilterCode L rL S F ↔ y ∈ L ∧ ∃ f ∈ F, ∃ z ∈ L,
      ZFSet.pair f z ∈ S ∧ ZFSet.pair z y ∈ rL := ZFSet.mem_sep

theorem pushFilterCode_subset (L rL S F : ZFSet.{u}) : pushFilterCode L rL S F ⊆ L :=
  fun _ hy => ((mem_pushFilterCode L rL S F _).1 hy).1

noncomputable def pairPushFilterFamily (K I J L rL Ss Fs B : ZFSet.{u}) : ZFSet.{u} :=
  ZFSet.sep (fun z => ∃ i ∈ I, ∃ j ∈ J, ∃ S ∈ Ss.sUnion.sUnion,
    ∃ F ∈ Fs.sUnion.sUnion, ∃ V ∈ B,
    z = ZFSet.pair (ZFSet.pair i j) V ∧ ZFSet.pair i S ∈ Ss ∧ ZFSet.pair j F ∈ Fs ∧
      V = pushFilterCode L rL S F) (ZFSet.prod K B)

end PartitionPilot.Forcing

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Geometry_TemplateHeightRangeCodes
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open scoped ZFSet

namespace PartitionPilot.Forcing

universe u

noncomputable def heightOrderRestriction (R r : ZFSet.{u}) : ZFSet.{u} :=
  ZFSet.sep (fun z => z ∈ ZFSet.prod R R) r

theorem pair_mem_heightOrderRestriction (R r a b : ZFSet.{u}) :
    ZFSet.pair a b ∈ heightOrderRestriction R r ↔
      ZFSet.pair a b ∈ r ∧ a ∈ R ∧ b ∈ R := by
  rw [heightOrderRestriction, ZFSet.mem_sep, ZFSet.pair_mem_prod]

def heightOrderCandidate (Rs brs i r : ZFSet.{u}) : Prop :=
  ∃ R ∈ ⋃₀ ⋃₀ Rs, ∃ s ∈ ⋃₀ ⋃₀ brs,
    ZFSet.pair i R ∈ Rs ∧ ZFSet.pair i s ∈ brs ∧ r = heightOrderRestriction R s

noncomputable def heightOrderFamily (I W Rs brs : ZFSet.{u}) : ZFSet.{u} :=
  ZFSet.sep (fun z => ∃ i ∈ I, ∃ r ∈ W,
    z = ZFSet.pair i r ∧ heightOrderCandidate Rs brs i r) (ZFSet.prod I W)

end PartitionPilot.Forcing

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Geometry_GroundTemplateIntervalFamilies
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace PartitionPilot.Forcing

section

universe u






noncomputable def batchHeightEndpointRelation
    (I P C D As Es Ss oldH rD : ZFSet.{u}) : ZFSet.{u} :=
  ZFSet.sep (fun z =>
    ∃ i ∈ I, ∃ a ∈ ZFSet.sUnion (ZFSet.sUnion As),
    ∃ ell ∈ ZFSet.sUnion (ZFSet.sUnion Es), ∃ b ∈ P, ∃ e ∈ P,
    ∃ c ∈ C, ∃ lo ∈ D, ∃ hi ∈ D, ∃ d ∈ C, ∃ v ∈ D,
      z = ZFSet.pair i (ZFSet.pair c (ZFSet.pair lo hi)) ∧
      ZFSet.pair i a ∈ As ∧ ZFSet.pair i ell ∈ Es ∧ ZFSet.pair a b ∈ ell ∧
      ZFSet.pair i e ∈ Ss ∧ ZFSet.pair b (ZFSet.pair c lo) ∈ oldH ∧
      ZFSet.pair e (ZFSet.pair d v) ∈ oldH ∧ ZFSet.pair lo hi ∈ rD ∧
      ((c = d ∧ hi = v) ∨ c ∈ d))
    (ZFSet.prod I (ZFSet.prod C (ZFSet.prod D D)))

end




universe u


end PartitionPilot.Forcing

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Definability_BatchGraphSetFormulas
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace PartitionPilot.Forcing



open SetFormula
universe u

namespace SetFormula

def sUnionSetFormula {n} (output source : Fin n) : SetFormula n :=
  exactSetFormula output (BoundedFormula.exMem source.succ (.mem 1 0)).toFormula

end SetFormula

end PartitionPilot.Forcing

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Forcing_ActionPostcompositionCodes
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PartitionPilot.Forcing

universe u

structure RestrictedActionCode (P r A g source target base : ZFSet.{u}) : Prop where
  shape : base ⊆ ZFSet.prod P P
  target_entry : ZFSet.pair (ZFSet.pair g source) target ∈ A
  entries : ∀ x ∈ P, ∀ y ∈ P, ZFSet.pair x y ∈ base ↔
    ZFSet.pair x source ∈ r ∧ ZFSet.pair (ZFSet.pair g x) y ∈ A

namespace RestrictedActionCode

variable {P r A g source target base : ZFSet.{u}}
variable (code : RestrictedActionCode P r A g source target base)
include code

theorem entry_action {x y : ZFSet.{u}} (entry : ZFSet.pair x y ∈ base) :
    ZFSet.pair (ZFSet.pair g x) y ∈ A := by
  have shape := ZFSet.pair_mem_prod.1 (code.shape entry)
  exact ((code.entries x shape.1 y shape.2).1 entry).2

end RestrictedActionCode

noncomputable def actionPostcompose (P A g base : ZFSet.{u}) : ZFSet.{u} :=
  ZFSet.sep (fun v => ∃ x ∈ P, ∃ z ∈ P, v = ZFSet.pair x z ∧
    ∃ y ∈ P, ZFSet.pair x y ∈ base ∧ ZFSet.pair (ZFSet.pair g y) z ∈ A) (ZFSet.prod P P)

end PartitionPilot.Forcing

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Definability_CodedFilterImages
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PartitionPilot.Forcing

open SetRealization
universe u

noncomputable def actionImage (P A g F : ZFSet.{u}) : ZFSet.{u} :=
  ZFSet.sep (fun y => ∃ x ∈ F, ZFSet.pair (ZFSet.pair g x) y ∈ A) P

end PartitionPilot.Forcing

end

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Definability_CodedRangeCompletion
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PartitionPilot.Forcing
universe u

structure CompressionRangeAccounting (P0 I U R MU Maps Bases Caps : ZFSet.{u}) : Prop where
  original_subset : P0 ⊆ U
  base_filled : ∀ i ∈ I, ∀ f b,
    ZFSet.pair i f ∈ Maps → ZFSet.pair i b ∈ Bases →
    ∀ x ∈ U, ZFSet.pair x b ∈ R → ∃ y ∈ U, ZFSet.pair y x ∈ f
  old_shadow : ∀ i ∈ I, ∀ b k,
    ZFSet.pair i b ∈ Bases → ZFSet.pair i k ∈ Caps →
    ∀ x ∈ P0, ZFSet.pair x k ∈ R → ZFSet.pair x b ∈ R
  cap_separation : ∀ i ∈ I, ∀ j ∈ I, i ≠ j → ∀ b c k l,
    ZFSet.pair i b ∈ Bases → ZFSet.pair j c ∈ Bases →
    ZFSet.pair i k ∈ Caps → ZFSet.pair j l ∈ Caps →
    ZFSet.pair k c ∈ R ∨ ZFSet.pair l b ∈ R ∨
      ∃ z, ZFSet.pair (ZFSet.pair k l) z ∈ MU ∧ ZFSet.pair (ZFSet.pair b c) z ∈ MU
  fresh_accounting : ∀ x ∈ U, x ∈ P0 ∨
    ∃ i ∈ I, ∃ f k b, ∃ y ∈ U,
      ZFSet.pair i f ∈ Maps ∧ ZFSet.pair i k ∈ Caps ∧ ZFSet.pair i b ∈ Bases ∧
      ZFSet.pair y x ∈ f ∧ ZFSet.pair x k ∈ R ∧ ZFSet.pair x b ∉ R

end PartitionPilot.Forcing

end

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Definability_GroundRegularFormulas
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PartitionPilot.Forcing

open SetFormula SetRealization
universe u

noncomputable def cumulativeRankGraph (A K : ZFSet.{u}) : ZFSet.{u} :=
  ZFSet.sep (fun z => ∃ x ∈ A, ∃ b ∈ K,
    z = ZFSet.pair x b ∧ b = ordinalCode (ZFSet.rank x)) (ZFSet.prod A K)

end PartitionPilot.Forcing

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Geometry_GroundCompressionStampBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace PartitionPilot.Forcing
universe u

noncomputable def compressionStamp (base : ZFSet.{u}) : Nat → ZFSet.{u}
  | 0 => insert base base
  | n + 1 => insert (compressionStamp base n) (compressionStamp base n)

theorem compressionStamp_zero (base : ZFSet.{u}) :
    compressionStamp base 0 = insert base base := rfl

theorem compressionStamp_succ (base : ZFSet.{u}) (n : Nat) :
    compressionStamp base (n + 1) = insert (compressionStamp base n) (compressionStamp base n) := rfl

theorem compressionStamp_subset (base : ZFSet.{u}) {n m : Nat} (before : n ≤ m) :
    compressionStamp base n ⊆ compressionStamp base m := by
  induction m, before using Nat.le_induction with
  | base => exact fun _ hx => hx
  | succ m _ ih => exact fun _ hx => ZFSet.mem_insert_of_mem _ (ih hx)

theorem compressionStamp_mem_iff (base : ZFSet.{u}) (n m : Nat) :
    compressionStamp base n ∈ compressionStamp base m ↔ n < m := by
  constructor
  · intro member
    by_contra notBefore
    exact ZFSet.mem_irrefl _ (compressionStamp_subset base (Nat.le_of_not_gt notBefore) member)
  · intro before
    exact compressionStamp_subset base before (ZFSet.mem_insert _ _)

theorem compressionStamp_base_mem (base : ZFSet.{u}) (n : Nat) : base ∈ compressionStamp base n :=
  compressionStamp_subset base (Nat.zero_le n) (ZFSet.mem_insert _ _)

theorem compressionStamp_old_mem {base t : ZFSet.{u}} (old : t ∈ base ∨ t = base) (n : Nat) :
    t ∈ compressionStamp base n := by
  apply compressionStamp_subset base (Nat.zero_le n)
  exact ZFSet.mem_insert_iff.2 old.symm





theorem mem_compressionStamp_iff (base s : ZFSet.{u}) (n : Nat) :
    s ∈ compressionStamp base n ↔
      s ∈ base ∨ s = base ∨ ∃ m, m < n ∧ s = compressionStamp base m := by
  induction n with
  | zero =>
    rw [compressionStamp_zero, ZFSet.mem_insert_iff]
    simp only [Nat.not_lt_zero, false_and, exists_false, or_false]
    exact or_comm
  | succ n ih =>
    rw [compressionStamp_succ, ZFSet.mem_insert_iff, ih]
    constructor
    · rintro (equal | old | equal | ⟨m, before, equal⟩)
      · exact Or.inr (Or.inr ⟨n, Nat.lt_succ_self n, equal⟩)
      · exact Or.inl old
      · exact Or.inr (Or.inl equal)
      · exact Or.inr (Or.inr ⟨m, before.trans (Nat.lt_succ_self n), equal⟩)
    · rintro (old | equal | ⟨m, before, equal⟩)
      · exact Or.inr (Or.inl old)
      · exact Or.inr (Or.inr (Or.inl equal))
      · rcases lt_or_eq_of_le (Nat.le_of_lt_succ before) with lower | same
        · exact Or.inr (Or.inr (Or.inr ⟨m, lower, equal⟩))
        · exact Or.inl (same ▸ equal)

theorem compressionStamp_not_old (base : ZFSet.{u}) (n : Nat) :
    compressionStamp base n ∉ base ∧ compressionStamp base n ≠ base := by
  constructor
  · exact fun member => ZFSet.mem_asymm member (compressionStamp_base_mem base n)
  · intro equal
    have member := compressionStamp_base_mem base n
    rw [equal] at member
    exact ZFSet.mem_irrefl base member

theorem compressionStamp_injective (base : ZFSet.{u}) : Function.Injective (compressionStamp base) := by
  intro n m equal
  rcases lt_trichotomy n m with before | same | after
  · have member := (compressionStamp_mem_iff base n m).2 before
    exact False.elim (ZFSet.mem_irrefl _ (equal ▸ member))
  · exact same
  · have member := (compressionStamp_mem_iff base m n).2 after
    exact False.elim (ZFSet.mem_irrefl _ (equal ▸ member))

end PartitionPilot.Forcing



end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Geometry_GroundFinalInsertionExceptions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI



namespace PartitionPilot.Forcing
universe u v w

def CodedInsertionProfile (L r μ c e K F : ZFSet.{u}) : Prop :=
  ∀ x ∈ L, ZFSet.pair e x ∈ r →
    ((∃ f ∈ F, ZFSet.pair f x ∈ r) → ZFSet.pair K x ∈ r) ∧
    (¬ (∃ f ∈ F, ZFSet.pair f x ∈ r) → ZFSet.pair (ZFSet.pair K x) c ∈ μ)

end PartitionPilot.Forcing



namespace PartitionPilot.Forcing
universe u

structure CodedCapProfile (L r μ c e K F : ZFSet.{u}) : Prop where
  target_mem : c ∈ L
  separator_mem : e ∈ L
  cap_mem : K ∈ L
  filter_subset : F ⊆ L
  nonempty : ∃ f, f ∈ F
  profile : CodedInsertionProfile L r μ c e K F
  target_below_cap : ZFSet.pair c K ∈ r
  cap_not_below_target : ZFSet.pair K c ∉ r
  separator_not_below_cap : ZFSet.pair e K ∉ r

def CodedCompressionProfiles (L r μ Caps Targets Separators Filters : ZFSet.{u}) : Prop :=
  ∀ i c e K F, ZFSet.pair i K ∈ Caps → ZFSet.pair i c ∈ Targets →
    ZFSet.pair i e ∈ Separators → ZFSet.pair i F ∈ Filters →
      CodedCapProfile L r μ c e K F

end PartitionPilot.Forcing



namespace PartitionPilot.Forcing
universe u

structure FinalInsertionFamiliesCode
    (Labels P G r μ A c e d F caps actors : ZFSet.{u}) : Prop where
  cap_injection : InjectionCode Labels P caps
  actor_injection : InjectionCode Labels G actors
  fixes : ∀ label k, ZFSet.pair label k ∈ actors →
    ∀ z ∈ P, ZFSet.pair z c ∈ r → ZFSet.pair (ZFSet.pair k z) z ∈ A
  dominates : ∀ label k cap, ZFSet.pair label k ∈ actors → ZFSet.pair label cap ∈ caps →
    ∀ y ∈ P, ZFSet.pair (ZFSet.pair k d) y ∈ A → ZFSet.pair y cap ∈ r
  profiles : ∀ label cap, ZFSet.pair label cap ∈ caps → CodedCapProfile P r μ c e cap F
  meets : ∀ first second cap₁ cap₂, ZFSet.pair first cap₁ ∈ caps →
    ZFSet.pair second cap₂ ∈ caps → first ≠ second → ZFSet.pair (ZFSet.pair cap₁ cap₂) c ∈ μ

end PartitionPilot.Forcing



namespace PartitionPilot.Forcing
open SetFormula
universe u

def capExceptionTest (profiles : Bool) (r c x cap : ZFSet.{u}) : Prop :=
  if profiles then c ∉ x ∧ cap ∈ x
  else ZFSet.pair x c ∉ r ∧ ZFSet.pair x cap ∈ r

noncomputable def capExceptionRelation
    (profiles : Bool) (S Labels P r c caps : ZFSet.{u}) : ZFSet.{u} :=
  ZFSet.sep (fun z => ∃ x ∈ S, ∃ label ∈ Labels, ∃ cap ∈ P,
    z = ZFSet.pair x label ∧ ZFSet.pair label cap ∈ caps ∧
      capExceptionTest profiles r c x cap) (ZFSet.prod S Labels)

def capExceptionEntryFormula {n}
    (profiles : Bool) (z s labels p r c caps : Fin n) : BoundedFormula n :=
  BoundedFormula.exMem s (BoundedFormula.exMem labels.succ
    (BoundedFormula.exMem p.succ.succ
      (.conj (BoundedFormula.orderedPairFormula z.succ.succ.succ 2 1)
        (.conj (BoundedFormula.pairMembershipFormula 1 0 caps.succ.succ.succ)
          (if profiles then .conj (.neg (.mem c.succ.succ.succ 2)) (.mem 0 2)
          else .conj (.neg (BoundedFormula.pairMembershipFormula 2 c.succ.succ.succ r.succ.succ.succ))
            (BoundedFormula.pairMembershipFormula 2 0 r.succ.succ.succ))))))

end PartitionPilot.Forcing

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Forcing_GroundPushFilters
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PartitionPilot.Forcing

universe u

namespace BoundedFormula

def pushFilterMemberFormula {n} (y L r S F : Fin n) : BoundedFormula n :=
  .conj (.mem y L) (exMem F (exMem L.succ
    (.conj (pairMembershipFormula 1 0 S.succ.succ)
      (pairMembershipFormula 0 y.succ.succ r.succ.succ))))

def pushFilterFormula {n} (V L r S F : Fin n) : BoundedFormula n :=
  .conj (.allMem V (pushFilterMemberFormula 0 L.succ r.succ S.succ F.succ))
    (.allMem L (imp (pushFilterMemberFormula 0 L.succ r.succ S.succ F.succ) (.mem 0 V.succ)))

end BoundedFormula

end PartitionPilot.Forcing

end

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Geometry_GroundIndexedClassInclusions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace PartitionPilot.Forcing

universe u

namespace BoundedFormula

open SetFormula

def equivalenceClassFormula {n} (C A E y : Fin n) : BoundedFormula n :=
  .conj (.allMem C (.mem 0 A.succ))
    (.allMem A (.conj
      (imp (.mem 0 C.succ) (pairMembershipFormula 0 y.succ E.succ))
      (imp (pairMembershipFormula 0 y.succ E.succ) (.mem 0 C.succ))))

def equivalenceClassesFormula {n} (C A E : Fin n) : BoundedFormula n :=
  exMem A (equivalenceClassFormula C.succ A.succ E.succ 0)

def equivalenceClassifierEntryFormula {n} (z A E Q : Fin n) : BoundedFormula n :=
  exMem A (exMem Q.succ (.conj (orderedPairFormula z.succ.succ 1 0)
    (equivalenceClassFormula 0 A.succ.succ E.succ.succ 1)))

end BoundedFormula

end PartitionPilot.Forcing



end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Geometry_TileStarIncomingCodes
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI



namespace PartitionPilot.Forcing
open SetRealization SetFormula
universe u

namespace BoundedFormula
def shortestLengthEntryFormula {k} (z A omega lengths : Fin k) : BoundedFormula k :=
  exMem A (exMem omega.succ (.conj (orderedPairFormula z.succ.succ 1 0)
    (.conj (pairMembershipFormula 0 1 lengths.succ.succ)
      (.allMem 0 (.neg (pairMembershipFormula 0 2 lengths.succ.succ.succ))))))

end BoundedFormula

end PartitionPilot.Forcing



end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Models_GroundExternalWordQuotient
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PartitionPilot.Forcing.ExternalWordRewrite

universe u
variable (J S : Type u) [Group J]

abbrev WordQuotient := (congruence J S).Quotient

def quotientMap : FreeMonoid (Alphabet J S) →* WordQuotient J S :=
  (congruence J S).mk'

def oldClass : J →* WordQuotient J S where
  toFun g := quotientMap J S [.inl g]
  map_one' := (Con.eq _).2
    (ConGen.Rel.of (M := FreeMonoid (Alphabet J S)) _ _ Atomic.old_one)
  map_mul' g h := ((Con.eq _).2
    (ConGen.Rel.of (M := FreeMonoid (Alphabet J S)) _ _ (Atomic.old_mul g h))).symm

def freeWordMap : FreeMonoid (S × Bool) →* WordQuotient J S :=
  (quotientMap J S).comp (FreeMonoid.map Sum.inr)

theorem freeWordMap_step {xs ys : List (S × Bool)} (h : FreeGroup.Red.Step xs ys) :
    freeWordMap J S xs = freeWordMap J S ys := by
  cases h with
  | @not pre post s b =>
    apply (Con.eq _).2
    change congruence J S ((pre ++ (s, b) :: (s, !b) :: post).map Sum.inr)
      ((pre ++ post).map Sum.inr)
    have step := ((Atomic.cancel (J := J) s b).step.append_left (pre.map Sum.inr)).append_right
      (post.map Sum.inr)
    simpa only [List.map_append, List.map_cons, List.map_nil, List.append_assoc,
      List.cons_append, List.nil_append] using step.to_congruence

def freeClass : FreeGroup S →* WordQuotient J S where
  toFun := Quot.lift (fun xs => freeWordMap J S xs) (fun _ _ h => freeWordMap_step J S h)
  map_one' := (freeWordMap J S).map_one
  map_mul' := by
    rintro ⟨xs⟩ ⟨ys⟩
    exact (freeWordMap J S).map_mul xs ys

theorem freeClass_mk (xs : List (S × Bool)) :
    freeClass J S (FreeGroup.mk xs) = quotientMap J S (xs.map Sum.inr) := rfl

end PartitionPilot.Forcing.ExternalWordRewrite



end

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Models_GroundQuotientBinaryOperations
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PartitionPilot.Forcing
open SetRealization
universe u

def quotientBinaryGraph (W Q classifier op : ZFSet.{u}) : ZFSet.{u} :=
  ZFSet.sep (fun z => ∃ a ∈ Q, ∃ b ∈ Q, ∃ c ∈ Q,
    z = ZFSet.pair (ZFSet.pair a b) c ∧
      ∃ x ∈ W, ∃ y ∈ W, ∃ t ∈ W,
        ZFSet.pair x a ∈ classifier ∧ ZFSet.pair y b ∈ classifier ∧
          ZFSet.pair t c ∈ classifier ∧ ZFSet.pair (ZFSet.pair x y) t ∈ op)
    (ZFSet.prod (ZFSet.prod Q Q) Q)

theorem mem_quotientBinaryGraph (W Q classifier op z : ZFSet.{u}) :
    z ∈ quotientBinaryGraph W Q classifier op ↔
      ∃ a ∈ Q, ∃ b ∈ Q, ∃ c ∈ Q, z = ZFSet.pair (ZFSet.pair a b) c ∧
        ∃ x ∈ W, ∃ y ∈ W, ∃ t ∈ W,
          ZFSet.pair x a ∈ classifier ∧ ZFSet.pair y b ∈ classifier ∧
            ZFSet.pair t c ∈ classifier ∧ ZFSet.pair (ZFSet.pair x y) t ∈ op := by
  rw [quotientBinaryGraph, ZFSet.mem_sep]
  refine ⟨And.right, ?_⟩
  rintro ⟨a, ha, b, hb, c, hc, eq, rest⟩
  exact ⟨eq.symm ▸ ZFSet.pair_mem_prod.2 ⟨ZFSet.pair_mem_prod.2 ⟨ha, hb⟩, hc⟩,
    a, ha, b, hb, c, hc, eq, rest⟩

end PartitionPilot.Forcing



end

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Models_GroundQuotientUnaryOperations
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PartitionPilot.Forcing
open SetRealization
universe u

def quotientUnaryGraph (W Q classifier op : ZFSet.{u}) : ZFSet.{u} :=
  ZFSet.sep (fun z => ∃ a ∈ Q, ∃ b ∈ Q, z = ZFSet.pair a b ∧
    ∃ x ∈ W, ∃ y ∈ W, ZFSet.pair x a ∈ classifier ∧
      ZFSet.pair y b ∈ classifier ∧ ZFSet.pair x y ∈ op) (ZFSet.prod Q Q)

end PartitionPilot.Forcing



namespace PartitionPilot.Forcing
open SetFormula
universe u

namespace BoundedFormula

def quotientUnaryEntryFormula {n} (z w q classifier op : Fin n) : BoundedFormula n :=
  exMem q (exMem q.succ (.conj (orderedPairFormula z.succ.succ 1 0)
    (exMem w.succ.succ (exMem w.succ.succ.succ
      (.conj (pairMembershipFormula 1 3 classifier.succ.succ.succ.succ)
        (.conj (pairMembershipFormula 0 2 classifier.succ.succ.succ.succ)
          (pairMembershipFormula 1 0 op.succ.succ.succ.succ)))))))

end BoundedFormula

end PartitionPilot.Forcing

end

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Geometry_GroundExternalGenerators
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PartitionPilot.Forcing

open SetRealization SetFormula
universe u

namespace BoundedFormula

def externalActorSymbolEntryFormula {n} (z G alphabet zero : Fin n) : BoundedFormula n :=
  exMem G (exMem alphabet.succ (.conj (orderedPairFormula z.succ.succ 1 0)
    (orderedPairFormula 0 zero.succ.succ 1)))

end BoundedFormula

end PartitionPilot.Forcing

section

namespace PartitionPilot.Forcing

open SetRealization SetFormula
universe u

namespace BoundedFormula

def singletonWordFormula {n} (w zero x : Fin n) : BoundedFormula n :=
  exMem w (.conj (orderedPairFormula 0 zero.succ x.succ) (singletonFormula w.succ 0))

def singletonWordEntryFormula {n} (z A W zero : Fin n) : BoundedFormula n :=
  exMem A (exMem W.succ (.conj (orderedPairFormula z.succ.succ 1 0)
    (singletonWordFormula 0 zero.succ.succ 1)))

end BoundedFormula

end PartitionPilot.Forcing

end

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Geometry_GroundExternalGroupEmbeddings
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PartitionPilot.Forcing
open SetRealization
universe u

structure GroupEmbeddingCode (G H mG mH oneG oneH e : ZFSet.{u}) : Prop where
  injection : InjectionCode G H e
  one : ZFSet.pair oneG oneH ∈ e
  mul : ∀ a b c a' b' c', ZFSet.pair (ZFSet.pair a b) c ∈ mG →
    ZFSet.pair a a' ∈ e → ZFSet.pair b b' ∈ e → ZFSet.pair c c' ∈ e →
      ZFSet.pair (ZFSet.pair a' b') c' ∈ mH

namespace GroupEmbeddingCode

theorem compose {G H K mG mH mK oneG oneH oneK e f : ZFSet.{u}}
    (first : GroupEmbeddingCode G H mG mH oneG oneH e)
    (second : GroupEmbeddingCode H K mH mK oneH oneK f) :
    GroupEmbeddingCode G K mG mK oneG oneK (relationCompose G H K e f) := by
  refine ⟨first.injection.compose second.injection, ?_, ?_⟩
  · have oneG := (ZFSet.pair_mem_prod.1 (first.injection.function.1 first.one)).1
    have oneH := (ZFSet.pair_mem_prod.1 (first.injection.function.1 first.one)).2
    have oneK := (ZFSet.pair_mem_prod.1 (second.injection.function.1 second.one)).2
    exact (pair_mem_relationCompose _ _ _ _ _ _ _).2 ⟨oneG, oneK, _, oneH, first.one, second.one⟩
  · intro a b c a' b' c' product aa bb cc
    obtain ⟨_, _, x, _, ax, xa⟩ := (pair_mem_relationCompose _ _ _ _ _ _ _).1 aa
    obtain ⟨_, _, y, _, by', yb⟩ := (pair_mem_relationCompose _ _ _ _ _ _ _).1 bb
    obtain ⟨_, _, z, _, cz, zc⟩ := (pair_mem_relationCompose _ _ _ _ _ _ _).1 cc
    exact second.mul x y z a' b' c' (first.mul a b c x y z product ax by' cz) xa yb zc

end GroupEmbeddingCode
end PartitionPilot.Forcing

end

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Transfinite_GroundCountableLayerCodes
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PartitionPilot.Forcing
open SetFormula
universe u

structure CountableLayerCode (L birth t D N injection : ZFSet.{u}) : Prop where
  small : InjectionCode D N injection
  cover : ∀ x ∈ L, ZFSet.pair x t ∈ birth → x ∈ D

end PartitionPilot.Forcing

end

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Transfinite_GroundLayerBirthFibers
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PartitionPilot.Forcing
open SetFormula
universe u

noncomputable def layerBirthFiber (L birth t : ZFSet.{u}) : ZFSet.{u} :=
  ZFSet.sep (fun x => ZFSet.pair x t ∈ birth) L

theorem mem_layerBirthFiber (L birth t x : ZFSet.{u}) :
    x ∈ layerBirthFiber L birth t ↔ x ∈ L ∧ ZFSet.pair x t ∈ birth := ZFSet.mem_sep

namespace BoundedFormula

def layerBirthFiberFormula {n} (F L birth t : Fin n) : BoundedFormula n :=
  .conj (.allMem F (.mem 0 L.succ)) (.allMem L
    (.conj (imp (.mem 0 F.succ) (pairMembershipFormula 0 t.succ birth.succ))
      (imp (pairMembershipFormula 0 t.succ birth.succ) (.mem 0 F.succ))))

end BoundedFormula

end PartitionPilot.Forcing

end

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Transfinite_NonzeroLimitOrdinalCodes
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PartitionPilot.Forcing
open SetRealization
universe u v

abbrev MainTransitionIndex (I : Type v) [Preorder I] := {p : I × I // p.1 ≤ p.2}

def mainTransitionIndexKey {I : Type v} [Preorder I] (key : I → ZFSet.{u})
    (p : MainTransitionIndex I) : ZFSet.{u} := ZFSet.pair (key p.val.2) (key p.val.1)

theorem mainTransitionIndexKey_injective {I : Type v} [Preorder I]
    (key : I → ZFSet.{u}) (injective : Function.Injective key) :
    Function.Injective (mainTransitionIndexKey key) := by
  intro p q equal
  obtain ⟨target, source⟩ := ZFSet.pair_inj.1 equal
  exact Subtype.ext (Prod.ext (injective source) (injective target))

theorem mainTransitionIndex_range {I : Type v} [Small.{u} I] [Preorder I]
    (key : I → ZFSet.{u})
    (order : ∀ i j, i ≤ j ↔ key i = key j ∨ key i ∈ key j) :
    ZFSet.range (mainTransitionIndexKey key) = chronologyPairs (ZFSet.range key) := by
  apply ZFSet.ext
  intro z
  constructor
  · intro hz
    obtain ⟨p, rfl⟩ := ZFSet.mem_range.1 hz
    exact (pair_mem_chronologyPairs _ _ _).2
      ⟨ZFSet.mem_range.2 ⟨p.val.2, rfl⟩, ZFSet.mem_range.2 ⟨p.val.1, rfl⟩,
        (order _ _).1 p.property⟩
  · intro hz
    obtain ⟨target, ht, source, hs, rfl, before⟩ := (mem_chronologyPairs _ z).1 hz
    obtain ⟨j, rfl⟩ := ZFSet.mem_range.1 ht
    obtain ⟨i, rfl⟩ := ZFSet.mem_range.1 hs
    exact ZFSet.mem_range.2 ⟨⟨(i, j), (order i j).2 before⟩, rfl⟩

end PartitionPilot.Forcing

namespace PartitionPilot.Forcing
open SetRealization
universe u

def NonzeroLimitOrdinalCode (T : ZFSet.{u}) : Prop :=
  T ≠ ∅ ∧ ∀ b ∈ T, ∃ c ∈ T, b ∈ c

end PartitionPilot.Forcing

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Definability_GroundFunctionRangeFamilies
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open scoped ZFSet

namespace PartitionPilot.Forcing
open SetFormula
universe u v

theorem familyCodeGraph_rank_mono {I : Type v} [Small.{u} I]
    (key left right : I → ZFSet.{u})
    (bounds : ∀ i, ZFSet.rank (left i) ≤ ZFSet.rank (right i)) :
    ZFSet.rank (familyCodeGraph key left) ≤ ZFSet.rank (familyCodeGraph key right) := by
  rw [familyCodeGraph, familyCodeGraph, ZFSet.rank_range, ZFSet.rank_range]
  apply Ordinal.iSup_le
  intro i
  have point : ZFSet.rank (ZFSet.pair (key i) (left i)) ≤
      ZFSet.rank (ZFSet.pair (key i) (right i)) := by
    change ZFSet.rank {{key i}, {key i, left i}} ≤ ZFSet.rank {{key i}, {key i, right i}}
    simp only [ZFSet.rank_pair, ZFSet.rank_singleton]
    exact max_le_max le_rfl (Order.succ_le_succ (max_le_max le_rfl (Order.succ_le_succ (bounds i))))
  exact (Order.succ_le_succ point).trans (Ordinal.le_iSup _ i)

end PartitionPilot.Forcing

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Forcing_GroundVaryingFamilyEvaluation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PartitionPilot.Forcing

section

universe u

def familyEvaluationGraph (K P L V Ss Es : ZFSet.{u}) : ZFSet.{u} :=
  ZFSet.sep (fun z => ∃ k ∈ K, ∃ S ∈ V, ∃ e ∈ P, ∃ y ∈ L,
    z = ZFSet.pair k y ∧ ZFSet.pair k S ∈ Ss ∧
      ZFSet.pair k e ∈ Es ∧ ZFSet.pair e y ∈ S) (ZFSet.prod K L)

theorem pair_mem_familyEvaluationGraph (K P L V Ss Es k y : ZFSet.{u}) :
    ZFSet.pair k y ∈ familyEvaluationGraph K P L V Ss Es ↔
      k ∈ K ∧ y ∈ L ∧ ∃ S ∈ V, ∃ e ∈ P,
        ZFSet.pair k S ∈ Ss ∧ ZFSet.pair k e ∈ Es ∧ ZFSet.pair e y ∈ S := by
  rw [familyEvaluationGraph, ZFSet.mem_sep, ZFSet.pair_mem_prod]
  constructor
  · rintro ⟨⟨hk, hy⟩, k', _, S, hS, e, he, y', _, eq, ks, ke, ey⟩
    obtain ⟨rfl, rfl⟩ := ZFSet.pair_inj.1 eq
    exact ⟨hk, hy, S, hS, e, he, ks, ke, ey⟩
  · rintro ⟨hk, hy, S, hS, e, he, ks, ke, ey⟩
    exact ⟨⟨hk, hy⟩, k, hk, S, hS, e, he, y, hy, rfl, ks, ke, ey⟩

namespace BoundedFormula

open SetFormula

def familyEvaluationEntryFormula {n} (z k p l v ss es : Fin n) : BoundedFormula n :=
  exMem k (exMem v.succ (exMem p.succ.succ (exMem l.succ.succ.succ
    (.conj (orderedPairFormula z.succ.succ.succ.succ 3 0)
      (.conj (pairMembershipFormula 3 2 ss.succ.succ.succ.succ)
        (.conj (pairMembershipFormula 3 1 es.succ.succ.succ.succ)
          (pairMembershipFormula 1 0 2)))))))

end BoundedFormula

end

open SetFormula
universe u v

end PartitionPilot.Forcing

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Geometry_LiftedCompressionFunctions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PartitionPilot.Forcing

universe u

def liftOldEntry (D Maps i x y : ZFSet.{u}) : Prop :=
  x ∈ D ∧ ∃ S ∈ ZFSet.sUnion (ZFSet.sUnion Maps), ZFSet.pair i S ∈ Maps ∧ ZFSet.pair x y ∈ S

def liftFreshEntry (D L J B N Sources Fs Reps G A i x y : ZFSet.{u}) : Prop :=
  ∃ j ∈ J, ∃ q ∈ B, ∃ a ∈ D, ∃ F ∈ ZFSet.sUnion (ZFSet.sUnion Fs),
    x = ZFSet.pair D (ZFSet.pair j q) ∧ ZFSet.pair j q ∈ N ∧
    ZFSet.pair i a ∈ Sources ∧ ZFSet.pair j F ∈ Fs ∧
    ((a ∈ F ∧ ∃ g ∈ G, ZFSet.pair i g ∈ Reps ∧ ZFSet.pair (ZFSet.pair g x) y ∈ A) ∨
      (a ∉ F ∧ y = ZFSet.pair L (ZFSet.pair (ZFSet.pair i j) q)))

def liftedCompressionGraph (I J D L C N B Maps Sources Fs Reps G A : ZFSet.{u}) : ZFSet.{u} :=
  ZFSet.sep (fun z => ∃ i ∈ I, ∃ x ∈ L, ∃ y ∈ C,
    z = ZFSet.pair (ZFSet.pair i x) y ∧
      (liftOldEntry D Maps i x y ∨ liftFreshEntry D L J B N Sources Fs Reps G A i x y))
    (ZFSet.prod (ZFSet.prod I L) C)

theorem pair_mem_liftedCompressionGraph (I J D L C N B Maps Sources Fs Reps G A i x y : ZFSet.{u}) :
    ZFSet.pair (ZFSet.pair i x) y ∈ liftedCompressionGraph I J D L C N B Maps Sources Fs Reps G A ↔
      i ∈ I ∧ x ∈ L ∧ y ∈ C ∧
        (liftOldEntry D Maps i x y ∨ liftFreshEntry D L J B N Sources Fs Reps G A i x y) := by
  rw [liftedCompressionGraph, ZFSet.mem_sep]
  constructor
  · rintro ⟨_, i', hi, x', hx, y', hy, eq, entry⟩
    obtain ⟨ix, rfl⟩ := ZFSet.pair_inj.1 eq
    obtain ⟨rfl, rfl⟩ := ZFSet.pair_inj.1 ix
    exact ⟨hi, hx, hy, entry⟩
  · rintro ⟨hi, hx, hy, entry⟩
    exact ⟨ZFSet.pair_mem_prod.2 ⟨ZFSet.pair_mem_prod.2 ⟨hi, hx⟩, hy⟩,
      i, hi, x, hx, y, hy, rfl, entry⟩

end PartitionPilot.Forcing

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Transfinite_RecursiveLiftAgreement
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace PartitionPilot.Forcing

universe u

def recursiveAttachmentIndices (I J P U As Fs : ZFSet.{u}) : ZFSet.{u} :=
  ZFSet.sep (fun k => ∃ i ∈ I, ∃ j ∈ J, ∃ a ∈ P, ∃ F ∈ U,
    k = ZFSet.pair i j ∧ ZFSet.pair i a ∈ As ∧ ZFSet.pair j F ∈ Fs ∧ a ∉ F)
    (ZFSet.prod I J)

theorem recursiveAttachmentIndices_subset (I J P U As Fs : ZFSet.{u}) :
    recursiveAttachmentIndices I J P U As Fs ⊆ ZFSet.prod I J :=
  fun _ hz => (ZFSet.mem_sep.1 hz).1

theorem pair_mem_recursiveAttachmentIndices (I J P U As Fs i j : ZFSet.{u}) :
    ZFSet.pair i j ∈ recursiveAttachmentIndices I J P U As Fs ↔
      i ∈ I ∧ j ∈ J ∧ ∃ a ∈ P, ∃ F ∈ U,
        ZFSet.pair i a ∈ As ∧ ZFSet.pair j F ∈ Fs ∧ a ∉ F := by
  rw [recursiveAttachmentIndices, ZFSet.mem_sep, ZFSet.pair_mem_prod]
  constructor
  · rintro ⟨⟨hi, hj⟩, i', _, j', _, a, ha, F, hF, eq, ai, Fj, neg⟩
    obtain ⟨rfl, rfl⟩ := ZFSet.pair_inj.1 eq
    exact ⟨hi, hj, a, ha, F, hF, ai, Fj, neg⟩
  · rintro ⟨hi, hj, a, ha, F, hF, ai, Fj, neg⟩
    exact ⟨⟨hi, hj⟩, i, hi, j, hj, a, ha, F, hF, rfl, ai, Fj, neg⟩

def pairFieldGraph (left : Bool) (I J K B H : ZFSet.{u}) : ZFSet.{u} :=
  ZFSet.sep (fun z => ∃ k ∈ K, ∃ i ∈ I, ∃ j ∈ J, ∃ x ∈ B,
    z = ZFSet.pair k x ∧ k = ZFSet.pair i j ∧
      ZFSet.pair (if left then i else j) x ∈ H) (ZFSet.prod K B)

theorem pair_mem_pairFieldGraph (left : Bool) (I J K B H k x : ZFSet.{u}) :
    ZFSet.pair k x ∈ pairFieldGraph left I J K B H ↔
      k ∈ K ∧ x ∈ B ∧ ∃ i ∈ I, ∃ j ∈ J,
        k = ZFSet.pair i j ∧ ZFSet.pair (if left then i else j) x ∈ H := by
  rw [pairFieldGraph, ZFSet.mem_sep, ZFSet.pair_mem_prod]
  constructor
  · rintro ⟨⟨hk, hx⟩, k', _, i, hi, j, hj, x', _, eq, kij, entry⟩
    obtain ⟨rfl, rfl⟩ := ZFSet.pair_inj.1 eq
    exact ⟨hk, hx, i, hi, j, hj, kij, entry⟩
  · rintro ⟨hk, hx, i, hi, j, hj, kij, entry⟩
    exact ⟨⟨hk, hx⟩, k, hk, i, hi, j, hj, x, hx, rfl, kij, entry⟩

theorem pairFieldGraph_entry_iff (left : Bool) {I J K B H i j x : ZFSet.{u}}
    (hi : i ∈ I) (hj : j ∈ J) :
    ZFSet.pair (ZFSet.pair i j) x ∈ pairFieldGraph left I J K B H ↔
      ZFSet.pair i j ∈ K ∧ x ∈ B ∧ ZFSet.pair (if left then i else j) x ∈ H := by
  rw [pair_mem_pairFieldGraph]
  constructor
  · rintro ⟨hk, hx, i', _, j', _, eq, entry⟩
    obtain ⟨rfl, rfl⟩ := ZFSet.pair_inj.1 eq
    exact ⟨hk, hx, entry⟩
  · rintro ⟨hk, hx, entry⟩
    exact ⟨hk, hx, i, hi, j, hj, rfl, entry⟩

theorem pairFieldGraph_function (left : Bool) {I J K B H : ZFSet.{u}}
    (subset : K ⊆ ZFSet.prod I J)
    (function : ZFSet.IsFunc (if left then I else J) B H) :
    ZFSet.IsFunc K B (pairFieldGraph left I J K B H) := by
  refine ⟨fun _ hz => (ZFSet.mem_sep.1 hz).1, ?_⟩
  intro k hk
  obtain ⟨i, hi, j, hj, rfl⟩ := ZFSet.mem_prod.1 (subset hk)
  have hs : (if left then i else j) ∈ (if left then I else J) := by
    cases left <;> assumption
  obtain ⟨x, entry, unique⟩ := function.2 _ hs
  have hx := (ZFSet.pair_mem_prod.1 (function.1 entry)).2
  refine ⟨x, (pairFieldGraph_entry_iff left hi hj).2 ⟨hk, hx, entry⟩, ?_⟩
  intro y hy
  exact unique y ((pairFieldGraph_entry_iff left hi hj).1 hy).2.2






namespace BoundedFormula

open SetFormula

def recursiveAttachmentIndexFormula {n} (k i j p u a f : Fin n) : BoundedFormula n :=
  exMem i (exMem j.succ (exMem p.succ.succ (exMem u.succ.succ.succ
    (.conj (orderedPairFormula k.succ.succ.succ.succ 3 2)
      (.conj (pairMembershipFormula 3 1 a.succ.succ.succ.succ)
        (.conj (pairMembershipFormula 2 0 f.succ.succ.succ.succ) (.neg (.mem 1 0))))))))

def pairFieldEntryFormula {n} (left : Bool) (z k i j b h : Fin n) : BoundedFormula n :=
  exMem k (exMem i.succ (exMem j.succ.succ (exMem b.succ.succ.succ
    (.conj (orderedPairFormula z.succ.succ.succ.succ 3 0)
      (.conj (orderedPairFormula 3 2 1)
        (pairMembershipFormula (if left then 2 else 1) 0 h.succ.succ.succ.succ))))))

end BoundedFormula






def pairSecondField (I J K H : ZFSet.{u}) : ZFSet.{u} :=
  pairFieldGraph false I J K (ZFSet.sUnion (ZFSet.sUnion H)) H

def pairFirstField (I J K H : ZFSet.{u}) : ZFSet.{u} :=
  pairFieldGraph true I J K (ZFSet.sUnion (ZFSet.sUnion H)) H

def recursiveSeparatorFamily (K I J D L Maps Ss : ZFSet.{u}) : ZFSet.{u} :=
  familyEvaluationGraph K D L (ZFSet.sUnion (ZFSet.sUnion Maps))
    (pairFirstField I J K Maps) (pairFieldGraph false I J K D Ss)

end PartitionPilot.Forcing



end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Definability_TaskRepresentativeCodes
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PartitionPilot.Forcing

universe u

def TaskRepresentative (P r A R U Labels task g : ZFSet.{u}) : Prop :=
  ∃ a ∈ P, ∃ c ∈ P, ∃ base ∈ R, ∃ e ∈ P, ∃ F ∈ U, ∃ label ∈ Labels,
    task = literalTaskCode a c base e F label ∧ RestrictedActionCode P r A g a c base

noncomputable def taskRepresentativeRelation (I P G r A R U Labels : ZFSet.{u}) : ZFSet.{u} :=
  ZFSet.sep (fun z => ∃ task ∈ I, ∃ g ∈ G,
    z = ZFSet.pair task g ∧ TaskRepresentative P r A R U Labels task g) (ZFSet.prod I G)

end PartitionPilot.Forcing

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Forcing_TaskTransportCodes
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PartitionPilot.Forcing

universe u

def TaskTransportCode (P R U Labels A g t t' : ZFSet.{u}) : Prop :=
  ∃ a ∈ P, ∃ c ∈ P, ∃ base ∈ R, ∃ s ∈ P, ∃ F ∈ U, ∃ label ∈ Labels,
    ∃ c' ∈ P, ∃ base' ∈ R, ∃ s' ∈ P, ∃ F' ∈ U,
      t = literalTaskCode a c base s F label ∧
      t' = literalTaskCode a c' base' s' F' label ∧
      ZFSet.pair (ZFSet.pair g c) c' ∈ A ∧ ZFSet.pair (ZFSet.pair g s) s' ∈ A ∧
      base' = actionPostcompose P A g base ∧ F' = actionImage P A g F

noncomputable def taskTransportGraph (G I P R U Labels A : ZFSet.{u}) : ZFSet.{u} :=
  ZFSet.sep (fun z => ∃ g ∈ G, ∃ t ∈ I, ∃ t' ∈ I,
    z = ZFSet.pair (ZFSet.pair g t) t' ∧ TaskTransportCode P R U Labels A g t t')
    (ZFSet.prod (ZFSet.prod G I) I)

end PartitionPilot.Forcing

end

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Forcing_CodedRecursiveTaskActions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PartitionPilot.Forcing

section

universe u

structure SetActionCode (G X m e A : ZFSet.{u}) : Prop where
  function : ZFSet.IsFunc (ZFSet.prod G X) X A
  one : ∀ p ∈ X, ZFSet.pair (ZFSet.pair e p) p ∈ A
  mul : ∀ g ∈ G, ∀ h ∈ G, ∀ k ∈ G, ∀ p ∈ X, ∀ q ∈ X, ∀ r ∈ X,
    ZFSet.pair (ZFSet.pair g h) k ∈ m → ZFSet.pair (ZFSet.pair h p) q ∈ A →
    ZFSet.pair (ZFSet.pair g q) r ∈ A → ZFSet.pair (ZFSet.pair k p) r ∈ A

theorem SetActionCode.entry_shape {G X m e A g x y : ZFSet.{u}}
    (action : SetActionCode G X m e A) (entry : ZFSet.pair (ZFSet.pair g x) y ∈ A) :
    g ∈ G ∧ x ∈ X ∧ y ∈ X := by
  have shape := ZFSet.pair_mem_prod.1 (action.function.1 entry)
  have domain := ZFSet.pair_mem_prod.1 shape.1
  exact ⟨domain.1, domain.2, shape.2⟩

theorem SetActionCode.entry_unique {G X m e A g x y z : ZFSet.{u}}
    (action : SetActionCode G X m e A)
    (first : ZFSet.pair (ZFSet.pair g x) y ∈ A)
    (second : ZFSet.pair (ZFSet.pair g x) z ∈ A) : y = z := by
  have shape := action.entry_shape first
  obtain ⟨w, _, unique⟩ := action.function.2 (ZFSet.pair g x)
    (ZFSet.pair_mem_prod.2 ⟨shape.1, shape.2.1⟩)
  exact (unique y first).trans (unique z second).symm

end

section

universe u

structure CodedAttachmentCovariance (G P N A B inside shadow upper : ZFSet.{u}) : Prop where
  inside : ∀ g ∈ G, ∀ q ∈ N, ∀ t ∈ N, ∀ q' ∈ N, ∀ t' ∈ N,
    ZFSet.pair (ZFSet.pair g q) q' ∈ B → ZFSet.pair (ZFSet.pair g t) t' ∈ B →
    ZFSet.pair q t ∈ inside → ZFSet.pair q' t' ∈ inside
  shadow : ∀ g ∈ G, ∀ q ∈ N, ∀ q' ∈ N, ∀ p ∈ P, ∀ p' ∈ P,
    ZFSet.pair (ZFSet.pair g q) q' ∈ B → ZFSet.pair (ZFSet.pair g p) p' ∈ A →
    ZFSet.pair q p ∈ shadow → ZFSet.pair q' p' ∈ shadow
  upper : ∀ g ∈ G, ∀ q ∈ N, ∀ q' ∈ N, ∀ p ∈ P, ∀ p' ∈ P,
    ZFSet.pair (ZFSet.pair g q) q' ∈ B → ZFSet.pair (ZFSet.pair g p) p' ∈ A →
    ZFSet.pair q p ∈ upper → ZFSet.pair q' p' ∈ upper

end

universe u

end PartitionPilot.Forcing

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Geometry_GroundCantorDiagonal
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

def injectionDiagonalFormula {n} (x p f : Fin n) : BoundedFormula n :=
  exMem p (.conj (pairMembershipFormula 0 x.succ f.succ) (.neg (.mem x.succ 0)))

end BoundedFormula

end PartitionPilot.Forcing

end

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Definability_SmallFunctionActionFormulas
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PartitionPilot.Forcing

open SetRealization SetFormula
universe u

def RenameActionRelation (X Y A g p q : ZFSet.{u}) : Prop :=
  ∀ x ∈ X, ∀ x' ∈ X, ∀ y ∈ Y,
    ZFSet.pair (ZFSet.pair g x) x' ∈ A → (ZFSet.pair x y ∈ p ↔ ZFSet.pair x' y ∈ q)

end PartitionPilot.Forcing

end

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Models_GroundChoiceEnumerationSteps
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PartitionPilot.Forcing
open SetFormula
universe u

noncomputable def enumerationRemainder (A a p : ZFSet.{u}) : ZFSet.{u} :=
  ZFSet.sep (fun x => ¬ ∃ b ∈ a, ZFSet.pair b x ∈ p) A

def ChoiceEnumerationStep (A F c a p y : ZFSet.{u}) : Prop :=
  (∃ R ∈ F, R = enumerationRemainder A a p ∧ ZFSet.pair R y ∈ c) ∨
    (¬ (enumerationRemainder A a p).Nonempty ∧ y = A)

end PartitionPilot.Forcing

end

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Geometry_GroundFamilyValueUnions
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

theorem familyCodeGraph_valueUnion_mem_iff (value : I → ZFSet.{u}) (x : ZFSet.{u}) :
    x ∈ ZFSet.sUnion (ZFSet.range value) ↔ ∃ i, x ∈ value i := by
  rw [ZFSet.mem_sUnion]
  exact ⟨fun ⟨_, hy, hx⟩ => by obtain ⟨i, rfl⟩ := ZFSet.mem_range.1 hy; exact ⟨i, hx⟩,
    fun ⟨i, hx⟩ => ⟨value i, ZFSet.mem_range.2 ⟨i, rfl⟩, hx⟩⟩

theorem familyCodeGraph_value_subset_union (key value : I → ZFSet.{u})
    {i X : ZFSet.{u}} (entry : ZFSet.pair i X ∈ familyCodeGraph key value) :
    X ⊆ ZFSet.sUnion (ZFSet.range value) := by
  obtain ⟨j, equal⟩ := (mem_familyCodeGraph key value _).1 entry
  have values := (ZFSet.pair_inj.1 equal).2
  intro x hx
  exact (familyCodeGraph_valueUnion_mem_iff value x).2 ⟨j, values.symm ▸ hx⟩

end PartitionPilot.Forcing

end

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Forcing_AllSupportFamilies
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PartitionPilot.Forcing
open SetRealization
universe u v

def allSupportBasis (G : Type u) [Group G] : ULift.{u} (Fin 1) → Subgroup G :=
  fun _ => ⊥

end PartitionPilot.Forcing

end

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Forcing_GroundNameSequenceValues
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace PartitionPilot.Forcing
universe u

noncomputable def decisionStepGraph (P r U D : ZFSet.{u}) : ZFSet.{u} :=
  ZFSet.sep (fun z => ∃ n ∈ ZFSet.omega, ∃ p ∈ P,
    ∃ m ∈ ZFSet.omega, ∃ q ∈ P, ∃ a ∈ U,
      z = ZFSet.pair (ZFSet.pair n p) (ZFSet.pair m q) ∧
      m = insert n n ∧ ZFSet.pair q p ∈ r ∧ ZFSet.pair (ZFSet.pair q n) a ∈ D)
    (ZFSet.prod (ZFSet.prod ZFSet.omega P) (ZFSet.prod ZFSet.omega P))

end PartitionPilot.Forcing



namespace PartitionPilot.Forcing
open SetFormula
universe u

noncomputable def decisionValues (U D p : ZFSet.{u}) : ZFSet.{u} :=
  ZFSet.sep (fun z => ∃ n ∈ ZFSet.omega, ∃ a ∈ U,
    z = ZFSet.pair n a ∧ ZFSet.pair (ZFSet.pair p n) a ∈ D)
    (ZFSet.prod ZFSet.omega U)

noncomputable def commonDecisionConditions (P U D : ZFSet.{u}) : ZFSet.{u} :=
  ZFSet.sep (fun p => ∀ n ∈ ZFSet.omega, ∃ a ∈ U,
    ZFSet.pair (ZFSet.pair p n) a ∈ D) P

noncomputable def decisionDenseCode (P r U D base : ZFSet.{u}) : ZFSet.{u} :=
  ZFSet.sep (fun p => (ZFSet.pair p base ∈ r ∧ p ∈ commonDecisionConditions P U D) ∨
    ¬ ∃ q ∈ P, ZFSet.pair q p ∈ r ∧ ZFSet.pair q base ∈ r) P

end PartitionPilot.Forcing



namespace PartitionPilot.Forcing
open SetFormula SetRealization
universe u

noncomputable def enumeratedFamilyDecisions (Q J B g f : ZFSet.{u}) : ZFSet.{u} :=
  ZFSet.sep (fun z => ∃ p ∈ Q, ∃ n ∈ ZFSet.omega, ∃ j ∈ J, ∃ E ∈ B,
    z = ZFSet.pair (ZFSet.pair p n) j ∧ ZFSet.pair n j ∈ g ∧
      ZFSet.pair j E ∈ f ∧ p ∈ E) (ZFSet.prod (ZFSet.prod Q ZFSet.omega) J)

end PartitionPilot.Forcing



end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Models_GroundRefinementQuotientNames
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace PartitionPilot.Forcing

universe u

noncomputable def refinementQuotientMap (U Rf Rc : ZFSet.{u}) : ZFSet.{u} :=
  relationCompose (equivalenceClasses U Rf) U (equivalenceClasses U Rc)
    (relationConverse U (equivalenceClasses U Rf) (equivalenceClassifier U Rf))
    (equivalenceClassifier U Rc)

end PartitionPilot.Forcing



end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Definability_GroundQuantifiedGraphFormulas
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

def allGraphFields {n} (graph : Fin n) (body : SetFormula (n + 2)) : SetFormula n :=
  .all (.all (imp (BoundedFormula.pairMembershipFormula 1 0 graph.succ.succ).toFormula body))

end SetFormula
end PartitionPilot.Forcing

end

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Definability_RefinementValidityCodes
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PartitionPilot.Forcing
universe u

def RefinementValidityCode (T U Rf Rc : ZFSet.{u}) : Prop :=
  U ⊆ T ∧ EquivalenceRelationCode U Rf ∧ EquivalenceRelationCode U Rc ∧ Rf ⊆ Rc

namespace BoundedFormula
open SetFormula

def equivalenceRelationFormula {n} (S R : Fin n) : BoundedFormula n :=
  .conj (relationBetweenFormula S S R)
    (.conj (.allMem S (pairMembershipFormula 0 0 R.succ))
      (.conj
        (.allMem S (.allMem S.succ
          (imp (pairMembershipFormula 1 0 R.succ.succ)
            (pairMembershipFormula 0 1 R.succ.succ))))
        (.allMem S (.allMem S.succ (.allMem S.succ.succ
          (imp (.conj (pairMembershipFormula 2 1 R.succ.succ.succ)
              (pairMembershipFormula 1 0 R.succ.succ.succ))
            (pairMembershipFormula 2 0 R.succ.succ.succ)))))))

end BoundedFormula

end PartitionPilot.Forcing

end

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Transfinite_GroundCountableProducts
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PartitionPilot.Forcing

universe u

noncomputable def relationProduct (A B C D f g : ZFSet.{u}) : ZFSet.{u} :=
  ZFSet.sep (fun z => ∃ a ∈ A, ∃ b ∈ B, ∃ c ∈ C, ∃ d ∈ D,
    z = ZFSet.pair (ZFSet.pair a b) (ZFSet.pair c d) ∧
      ZFSet.pair a c ∈ f ∧ ZFSet.pair b d ∈ g)
    (ZFSet.prod (ZFSet.prod A B) (ZFSet.prod C D))

theorem mem_relationProduct (A B C D f g z : ZFSet.{u}) :
    z ∈ relationProduct A B C D f g ↔
      ∃ a ∈ A, ∃ b ∈ B, ∃ c ∈ C, ∃ d ∈ D,
        z = ZFSet.pair (ZFSet.pair a b) (ZFSet.pair c d) ∧
          ZFSet.pair a c ∈ f ∧ ZFSet.pair b d ∈ g := by
  constructor
  · exact fun h => (ZFSet.mem_sep.1 h).2
  · rintro ⟨a, ha, b, hb, c, hc, d, hd, rfl, fac, gbd⟩
    exact ZFSet.mem_sep.2 ⟨ZFSet.pair_mem_prod.2
      ⟨ZFSet.pair_mem_prod.2 ⟨ha, hb⟩, ZFSet.pair_mem_prod.2 ⟨hc, hd⟩⟩,
      a, ha, b, hb, c, hc, d, hd, rfl, fac, gbd⟩

theorem pair_mem_relationProduct (A B C D f g a b c d : ZFSet.{u}) :
    ZFSet.pair (ZFSet.pair a b) (ZFSet.pair c d) ∈ relationProduct A B C D f g ↔
      a ∈ A ∧ b ∈ B ∧ c ∈ C ∧ d ∈ D ∧ ZFSet.pair a c ∈ f ∧ ZFSet.pair b d ∈ g := by
  rw [mem_relationProduct]
  constructor
  · rintro ⟨a', ha, b', hb, c', hc, d', hd, equal, fac, gbd⟩
    obtain ⟨left, right⟩ := ZFSet.pair_inj.1 equal
    obtain ⟨rfl, rfl⟩ := ZFSet.pair_inj.1 left
    obtain ⟨rfl, rfl⟩ := ZFSet.pair_inj.1 right
    exact ⟨ha, hb, hc, hd, fac, gbd⟩
  · rintro ⟨ha, hb, hc, hd, fac, gbd⟩
    exact ⟨a, ha, b, hb, c, hc, d, hd, rfl, fac, gbd⟩

theorem relationProduct_function {A B C D f g : ZFSet.{u}}
    (first : ZFSet.IsFunc A C f) (second : ZFSet.IsFunc B D g) :
    ZFSet.IsFunc (ZFSet.prod A B) (ZFSet.prod C D) (relationProduct A B C D f g) := by
  refine ⟨fun _ hz => (ZFSet.mem_sep.1 hz).1, ?_⟩
  intro x hx
  obtain ⟨a, ha, b, hb, rfl⟩ := ZFSet.mem_prod.1 hx
  obtain ⟨c, fac, uniqueC⟩ := first.2 a ha
  obtain ⟨d, gbd, uniqueD⟩ := second.2 b hb
  have hc := (ZFSet.pair_mem_prod.1 (first.1 fac)).2
  have hd := (ZFSet.pair_mem_prod.1 (second.1 gbd)).2
  refine ⟨ZFSet.pair c d, (pair_mem_relationProduct A B C D f g a b c d).2
    ⟨ha, hb, hc, hd, fac, gbd⟩, ?_⟩
  intro z hz
  obtain ⟨c', _, d', _, rfl⟩ := ZFSet.mem_prod.1 (ZFSet.pair_mem_prod.1 (ZFSet.mem_sep.1 hz).1).2
  obtain ⟨_, _, _, _, fac', gbd'⟩ := (pair_mem_relationProduct A B C D f g a b c' d').1 hz
  exact congrArg₂ ZFSet.pair (uniqueC c' fac') (uniqueD d' gbd')

theorem relationProduct_injection {A B C D f g : ZFSet.{u}}
    (first : InjectionCode A C f) (second : InjectionCode B D g) :
    InjectionCode (ZFSet.prod A B) (ZFSet.prod C D) (relationProduct A B C D f g) := by
  refine ⟨relationProduct_function first.function second.function, ?_⟩
  intro x y z hx hy
  have shapeX := ZFSet.pair_mem_prod.1 (ZFSet.mem_sep.1 hx).1
  have shapeY := ZFSet.pair_mem_prod.1 (ZFSet.mem_sep.1 hy).1
  obtain ⟨a, _, b, _, rfl⟩ := ZFSet.mem_prod.1 shapeX.1
  obtain ⟨a', _, b', _, rfl⟩ := ZFSet.mem_prod.1 shapeY.1
  obtain ⟨c, _, d, _, rfl⟩ := ZFSet.mem_prod.1 shapeX.2
  obtain ⟨_, _, _, _, fac, gbd⟩ := (pair_mem_relationProduct A B C D f g a b c d).1 hx
  obtain ⟨_, _, _, _, fa'c, gb'd⟩ := (pair_mem_relationProduct A B C D f g a' b' c d).1 hy
  exact congrArg₂ ZFSet.pair (first.injective a a' c fac fa'c) (second.injective b b' d gbd gb'd)

end PartitionPilot.Forcing

end

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Definability_GroundLiftedRowTupleProvenance
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open scoped ZFSet

namespace PartitionPilot.Forcing
open SetRealization SetFormula
universe u

noncomputable def pairedGraph (L H K f g : ZFSet.{u}) : ZFSet.{u} :=
  ZFSet.sep (fun z => ∃ x ∈ L, ∃ a ∈ H, ∃ b ∈ K,
    z = ZFSet.pair x (ZFSet.pair a b) ∧ ZFSet.pair x a ∈ f ∧ ZFSet.pair x b ∈ g)
    (ZFSet.prod L (ZFSet.prod H K))

theorem mem_pairedGraph (L H K f g z : ZFSet.{u}) : z ∈ pairedGraph L H K f g ↔
    ∃ x ∈ L, ∃ a ∈ H, ∃ b ∈ K,
      z = ZFSet.pair x (ZFSet.pair a b) ∧ ZFSet.pair x a ∈ f ∧ ZFSet.pair x b ∈ g := by
  constructor
  · exact fun hz => (ZFSet.mem_sep.1 hz).2
  · rintro ⟨x, hx, a, ha, b, hb, rfl, first, second⟩
    exact ZFSet.mem_sep.2 ⟨ZFSet.pair_mem_prod.2 ⟨hx, ZFSet.pair_mem_prod.2 ⟨ha, hb⟩⟩,
      x, hx, a, ha, b, hb, rfl, first, second⟩

theorem pair_mem_pairedGraph (L H K f g x a b : ZFSet.{u}) :
    ZFSet.pair x (ZFSet.pair a b) ∈ pairedGraph L H K f g ↔
      x ∈ L ∧ a ∈ H ∧ b ∈ K ∧ ZFSet.pair x a ∈ f ∧ ZFSet.pair x b ∈ g := by
  rw [mem_pairedGraph]
  constructor
  · rintro ⟨x', hx, a', ha, b', hb, equal, first, second⟩
    obtain ⟨left, right⟩ := ZFSet.pair_inj.1 equal
    obtain ⟨rfl, rfl⟩ := ZFSet.pair_inj.1 right
    subst x'
    exact ⟨hx, ha, hb, first, second⟩
  · rintro ⟨hx, ha, hb, first, second⟩
    exact ⟨x, hx, a, ha, b, hb, rfl, first, second⟩

end PartitionPilot.Forcing

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Forcing_RefinementCoarseImageNames
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PartitionPilot.Forcing
open SetRealization SetFormula
universe u v

noncomputable def coarseClassImage (U sigma Rc : ZFSet.{u}) : ZFSet.{u} :=
  ZFSet.sep (fun z => ∃ y ∈ sigma, y ∈ U ∧ ZFSet.pair z y ∈ Rc) U

end PartitionPilot.Forcing

end

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Geometry_GroundRowAssignmentCuts
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PartitionPilot.Forcing
open SetRealization SetFormula
universe u

noncomputable def rowAssignmentCutGraph (upper lower levels alpha : ZFSet.{u}) : ZFSet.{u} :=
  ZFSet.sep (fun z => ∃ row A,
    z = ZFSet.pair (ZFSet.pair row A) (ZFSet.pair row (assignmentCut levels alpha A)))
    (ZFSet.prod upper lower)

theorem mem_rowAssignmentCutGraph (upper lower levels alpha z : ZFSet.{u}) :
    z ∈ rowAssignmentCutGraph upper lower levels alpha ↔
      z ∈ ZFSet.prod upper lower ∧ ∃ row A,
        z = ZFSet.pair (ZFSet.pair row A) (ZFSet.pair row (assignmentCut levels alpha A)) :=
  ZFSet.mem_sep

theorem pair_mem_rowAssignmentCutGraph (upper lower levels alpha row A target : ZFSet.{u}) :
    ZFSet.pair (ZFSet.pair row A) target ∈ rowAssignmentCutGraph upper lower levels alpha ↔
      ZFSet.pair row A ∈ upper ∧ target ∈ lower ∧
        target = ZFSet.pair row (assignmentCut levels alpha A) := by
  rw [mem_rowAssignmentCutGraph, ZFSet.pair_mem_prod]
  constructor
  · rintro ⟨⟨hp, ht⟩, row', A', equal⟩
    obtain ⟨left, right⟩ := ZFSet.pair_inj.1 equal
    obtain ⟨rfl, rfl⟩ := ZFSet.pair_inj.1 left
    exact ⟨hp, ht, right⟩
  · rintro ⟨hp, ht, rfl⟩
    exact ⟨⟨hp, ht⟩, row, A, rfl⟩

end PartitionPilot.Forcing

end

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Transfinite_GroundStageOneAssignmentUnions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PartitionPilot.Forcing

section
universe u
namespace BoundedFormula

def refinementActivityFormula : BoundedFormula 3 :=
  .conj (.mem 0 2) (.mem 1 2)

def refinementCollisionFormula : BoundedFormula 4 :=
  .conj (imp (.equal 0 1) (.equal 2 3)) (imp (.equal 2 3) (.equal 0 1))

def refinementProfileFormula : BoundedFormula 3 :=
  .conj (imp (.mem 0 2) (.mem 1 2)) (imp (.mem 1 2) (.mem 0 2))

def refinementCompatibilityFormula : BoundedFormula 4 :=
  imp (.mem 0 1) (pairMembershipFormula 0 2 3)

end BoundedFormula
namespace SetFormula

def refinementActivityFormula : SetFormula 3 := BoundedFormula.refinementActivityFormula.toFormula

def refinementCollisionFormula : SetFormula 4 := BoundedFormula.refinementCollisionFormula.toFormula

def refinementProfileFormula : SetFormula 3 := BoundedFormula.refinementProfileFormula.toFormula

def refinementCompatibilityFormula : SetFormula 4 := BoundedFormula.refinementCompatibilityFormula.toFormula

end SetFormula
end

open SetRealization SetFormula
universe u

noncomputable def stageOneAssignmentUnion (family : Nat → ZFSet.{u}) : ZFSet.{u} :=
  (ZFSet.range family).sUnion

theorem mem_stageOneAssignmentUnion (family : Nat → ZFSet.{u}) (z : ZFSet.{u}) :
    z ∈ stageOneAssignmentUnion family ↔ ∃ n, z ∈ family n := by
  rw [stageOneAssignmentUnion, ZFSet.mem_sUnion]
  constructor
  · rintro ⟨A, hA, member⟩
    obtain ⟨n, rfl⟩ := ZFSet.mem_range.1 hA
    exact ⟨n, member⟩
  · rintro ⟨n, member⟩
    exact ⟨family n, ZFSet.mem_range.2 ⟨n, rfl⟩, member⟩

theorem stageOneAssignmentUnion_contains (family : Nat → ZFSet.{u}) (n : Nat) :
    family n ⊆ stageOneAssignmentUnion family :=
  fun z member => (mem_stageOneAssignmentUnion family z).2 ⟨n, member⟩

theorem stageOneAssignmentUnion_subset {family : Nat → ZFSet.{u}} {J : ZFSet.{u}}
    (subsets : ∀ n, family n ⊆ J) : stageOneAssignmentUnion family ⊆ J := by
  intro z member
  obtain ⟨n, hn⟩ := (mem_stageOneAssignmentUnion family z).1 member
  exact subsets n hn

end PartitionPilot.Forcing

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Definability_VisibilityProfileFormulas
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PartitionPilot.Forcing

section
open SetRealization SetFormula
universe u

theorem map_three_p1 {α β : Type*} (f : α → β) (a b c : α) :
    (fun j : Fin 3 => f ((extend a (extend b (extend c Fin.elim0))) j)) = ![f a, f b, f c] := by
  funext j
  exact Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (fun k => Fin.elim0 k))) j

theorem map_four_p1 {α β : Type*} (f : α → β) (a b c d : α) :
    (fun j : Fin 4 => f ((extend a (extend b (extend c (extend d Fin.elim0)))) j)) = ![f a, f b, f c, f d] := by
  funext j
  exact Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (fun k => Fin.elim0 k)))) j

end

open SetFormula
universe u

namespace SetFormula
def supportedEqualitySequenceFormula : SetFormula 6 :=
  .conj (BoundedFormula.functionFormula 0 1 2).toFormula
    (.all (imp (.mem 0 1) (.all (imp (.mem 0 3)
      (imp (BoundedFormula.pairMembershipFormula 1 0 4).toFormula
        (.conj (BoundedFormula.pairMembershipFormula 1 0 5).toFormula
          (BoundedFormula.pairMembershipFormula 0 7 6).toFormula))))))
end SetFormula

namespace SetFormula

def visibilityProfileFormula : SetFormula 4 :=
  .all (imp (.mem 0 3) (.all (imp (BoundedFormula.pairMembershipFormula 1 0 3).toFormula
    (.conj (imp (.mem 2 0) (.mem 1 5)) (imp (.mem 1 5) (.mem 2 0))))))
end SetFormula

end PartitionPilot.Forcing

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Definability_SupportedCertificateRelations
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PartitionPilot.Forcing
open SetRealization SetFormula
universe u

noncomputable def supportedEqualityRelation (B N R E value : ZFSet.{u}) : ZFSet.{u} :=
  ZFSet.sep (fun entry => ∃ v ∈ B, ∃ tau ∈ N, entry = ZFSet.pair v tau ∧
    ZFSet.pair v tau ∈ R ∧ ZFSet.pair tau value ∈ E) (ZFSet.prod B N)

namespace BoundedFormula
def supportedEqualityEntryFormula {n} (entry B N R E value : Fin n) : BoundedFormula n :=
  exMem B (exMem N.succ (.conj (orderedPairFormula entry.succ.succ 1 0)
    (.conj (pairMembershipFormula 1 0 R.succ.succ)
      (pairMembershipFormula 0 value.succ.succ E.succ.succ))))

end BoundedFormula

end PartitionPilot.Forcing



namespace PartitionPilot.Forcing
universe u

def SupportedEqualityCertificate
    (nodes N order R niceEval visibilityEval value F B f : ZFSet.{u}) : Prop :=
  F ⊆ nodes ∧ B ⊆ F ∧
    (∀ v ∈ F, ∃ w ∈ B, ZFSet.pair w v ∈ order) ∧
    ZFSet.IsFunc B N f ∧
    (∀ v V, ZFSet.pair v V ∈ visibilityEval → v ∈ nodes →
      (value ∈ V ↔ v ∈ F)) ∧
    ∀ v ∈ B, ∀ tau ∈ N, ZFSet.pair v tau ∈ f →
      ZFSet.pair v tau ∈ R ∧ ZFSet.pair tau value ∈ niceEval

noncomputable def supportedCertificateRelation
    (J PF PB WF nodes N order R inputEval niceEval visibilityEval : ZFSet.{u}) : ZFSet.{u} :=
  ZFSet.sep (fun entry => ∃ j ∈ J, ∃ F ∈ PF, ∃ B ∈ PB, ∃ f ∈ WF,
    entry = ZFSet.pair j (ZFSet.pair F (ZFSet.pair B f)) ∧
    ∃ value, ZFSet.pair j value ∈ inputEval ∧
      SupportedEqualityCertificate nodes N order R niceEval visibilityEval value F B f)
    (ZFSet.prod J (ZFSet.prod PF (ZFSet.prod PB WF)))

end PartitionPilot.Forcing

end

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Models_GroundSupportedEqualityChoices
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open scoped ZFSet

namespace PartitionPilot.Forcing
open SetFormula SetRealization
universe u

def OrdinalChoiceValue (T e x y : ZFSet.{u}) : Prop :=
  ∃ i ∈ T, ZFSet.pair i y ∈ e ∧ ∀ j ∈ i, ∀ z ∈ x, ZFSet.pair j z ∉ e

noncomputable def ordinalIndexedChoiceGraph (A T e : ZFSet.{u}) : ZFSet.{u} :=
  ZFSet.sep (fun z => ∃ x ∈ A, ∃ y ∈ x, z = ZFSet.pair x y ∧ OrdinalChoiceValue T e x y)
    (ZFSet.prod A (⋃₀ A))

namespace BoundedFormula

def ordinalChoiceValueFormula {n} (T e x y : Fin n) : BoundedFormula n :=
  exMem T (.conj (pairMembershipFormula 0 y.succ e.succ)
    (allMem 0 (allMem x.succ.succ (.neg (pairMembershipFormula 1 0 e.succ.succ.succ)))))

def ordinalIndexedChoiceEntryFormula {n} (z A T e : Fin n) : BoundedFormula n :=
  exMem A (exMem 0 (.conj (orderedPairFormula z.succ.succ 1 0)
    (ordinalChoiceValueFormula T.succ.succ e.succ.succ 1 0)))

end BoundedFormula

end PartitionPilot.Forcing

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Transfinite_GroundStandardInaccessible
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace PartitionPilot.Forcing
open SetFormula
universe u

theorem InjectionCode.retarget {A B C f : ZFSet.{u}} (code : InjectionCode A B f)
    (subset : B ⊆ C) : InjectionCode A C f := by
  refine ⟨⟨?_, code.function.2⟩, code.injective⟩
  intro z entry
  obtain ⟨x, hx, y, hy, rfl⟩ := ZFSet.mem_prod.1 (code.function.1 entry)
  exact ZFSet.pair_mem_prod.2 ⟨hx, subset hy⟩

theorem ordinalSetProperty_pair_bound {K α β : ZFSet.{u}}
    (ordinal : ordinalSetProperty K) (hα : α ∈ K) (hβ : β ∈ K) :
    ∃ γ ∈ K, α ⊆ γ ∧ β ⊆ γ := by
  rcases ordinalSetProperty_mem_compare ordinal hα hβ with lower | rfl | greater
  · exact ⟨β, hβ, fun x hx => ordinal.2 β hβ α lower x hx, fun _ hx => hx⟩
  · exact ⟨α, hα, fun _ hx => hx, fun _ hx => hx⟩
  · exact ⟨α, hα, fun _ hx => hx, fun x hx => ordinal.2 α hα β greater x hx⟩

end PartitionPilot.Forcing



end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Geometry_GroundMeetGeneratorSteps
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PartitionPilot.Forcing
open SetFormula SetRealization
universe u

noncomputable def meetGeneratorSteps (P μ A : ZFSet.{u}) : ZFSet.{u} :=
  ZFSet.sep (fun z => ∃ x ∈ P, ∃ y ∈ P, ∃ a ∈ A,
    z = ZFSet.pair x y ∧ ZFSet.pair (ZFSet.pair x a) y ∈ μ) (ZFSet.prod P P)

end PartitionPilot.Forcing

end

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Geometry_GroundEligibleCaps
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI



namespace PartitionPilot.Forcing

universe u

def eligibleTaskCap (P T i : ZFSet.{u}) : ZFSet.{u} :=
  ZFSet.pair P (ZFSet.pair i T)

end PartitionPilot.Forcing

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Geometry_GroundHeightPushforward
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PartitionPilot.Forcing
open SetFormula SetRealization
universe u

noncomputable def flatCopyEmbeddingGraph (U Q classifier w : ZFSet.{u}) : ZFSet.{u} :=
  ZFSet.sep (fun z => ∃ x ∈ U, ∃ y ∈ Q, z = ZFSet.pair x y ∧
    ZFSet.pair (ZFSet.pair w x) y ∈ classifier) (ZFSet.prod U Q)

theorem pair_mem_flatCopyEmbeddingGraph (U Q classifier w x y : ZFSet.{u}) :
    ZFSet.pair x y ∈ flatCopyEmbeddingGraph U Q classifier w ↔
      x ∈ U ∧ y ∈ Q ∧ ZFSet.pair (ZFSet.pair w x) y ∈ classifier := by
  rw [flatCopyEmbeddingGraph, ZFSet.mem_sep]
  constructor
  · rintro ⟨_, x', hx, y', hy, equal, entry⟩
    obtain ⟨rfl, rfl⟩ := ZFSet.pair_inj.1 equal
    exact ⟨hx, hy, entry⟩
  · rintro ⟨hx, hy, entry⟩
    exact ⟨ZFSet.pair_mem_prod.2 ⟨hx, hy⟩, x, hx, y, hy, rfl, entry⟩

end PartitionPilot.Forcing

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Forcing_GroundRecursiveActions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open scoped ZFSet



namespace PartitionPilot.Forcing

universe u

noncomputable def indexedTaskActionGraph (G I P N T : ZFSet.{u}) : ZFSet.{u} :=
  ZFSet.sep (fun z => ∃ g ∈ G, ∃ i ∈ I, ∃ j ∈ I, ∃ q ∈ P,
    z = ZFSet.pair (ZFSet.pair g (ZFSet.pair i q)) (ZFSet.pair j q) ∧
      ZFSet.pair (ZFSet.pair g i) j ∈ T)
    (ZFSet.prod (ZFSet.prod G N) N)

theorem indexedTaskActionGraph_subset (G I P N T : ZFSet.{u}) :
    indexedTaskActionGraph G I P N T ⊆ ZFSet.prod (ZFSet.prod G N) N :=
  fun _ hz => (ZFSet.mem_sep.1 hz).1

theorem mem_indexedTaskActionGraph (G I P N T z : ZFSet.{u}) :
    z ∈ indexedTaskActionGraph G I P N T ↔
      ∃ g ∈ G, ∃ i ∈ I, ∃ j ∈ I, ∃ q ∈ P,
        ZFSet.pair i q ∈ N ∧ ZFSet.pair j q ∈ N ∧
        z = ZFSet.pair (ZFSet.pair g (ZFSet.pair i q)) (ZFSet.pair j q) ∧
          ZFSet.pair (ZFSet.pair g i) j ∈ T := by
  constructor
  · intro hz
    obtain ⟨bound, g, hg, i, hi, j, hj, q, hq, rfl, entry⟩ := ZFSet.mem_sep.1 hz
    have outer := ZFSet.pair_mem_prod.1 bound
    exact ⟨g, hg, i, hi, j, hj, q, hq, (ZFSet.pair_mem_prod.1 outer.1).2,
      outer.2, rfl, entry⟩
  · rintro ⟨g, hg, i, hi, j, hj, q, hq, source, target, rfl, entry⟩
    exact ZFSet.mem_sep.2
      ⟨ZFSet.pair_mem_prod.2 ⟨ZFSet.pair_mem_prod.2 ⟨hg, source⟩, target⟩,
        g, hg, i, hi, j, hj, q, hq, rfl, entry⟩

theorem triple_mem_indexedTaskActionGraph (G I P N T g x y : ZFSet.{u}) :
    ZFSet.pair (ZFSet.pair g x) y ∈ indexedTaskActionGraph G I P N T ↔
      g ∈ G ∧ x ∈ N ∧ y ∈ N ∧ ∃ i ∈ I, ∃ j ∈ I, ∃ q ∈ P,
        x = ZFSet.pair i q ∧ y = ZFSet.pair j q ∧ ZFSet.pair (ZFSet.pair g i) j ∈ T := by
  rw [mem_indexedTaskActionGraph]
  constructor
  · rintro ⟨a, ha, i, hi, j, hj, q, hq, source, target, equal, entry⟩
    obtain ⟨first, last⟩ := ZFSet.pair_inj.1 equal
    obtain ⟨actor, middle⟩ := ZFSet.pair_inj.1 first
    subst a x y
    exact ⟨ha, source, target, i, hi, j, hj, q, hq, rfl, rfl, entry⟩
  · rintro ⟨hg, source, target, i, hi, j, hj, q, hq, rfl, rfl, entry⟩
    exact ⟨g, hg, i, hi, j, hj, q, hq, source, target, rfl, entry⟩

theorem indexedTaskActionGraph_entry_iff (G I P N T g i j q q' : ZFSet.{u}) :
    ZFSet.pair (ZFSet.pair g (ZFSet.pair i q)) (ZFSet.pair j q') ∈
      indexedTaskActionGraph G I P N T ↔
      g ∈ G ∧ i ∈ I ∧ j ∈ I ∧ q ∈ P ∧ q' = q ∧
        ZFSet.pair i q ∈ N ∧ ZFSet.pair j q ∈ N ∧ ZFSet.pair (ZFSet.pair g i) j ∈ T := by
  rw [triple_mem_indexedTaskActionGraph]
  constructor
  · rintro ⟨hg, source, target, a, ha, b, hb, t, ht, first, second, entry⟩
    obtain ⟨rfl, rfl⟩ := ZFSet.pair_inj.1 first
    obtain ⟨rfl, rfl⟩ := ZFSet.pair_inj.1 second
    exact ⟨hg, ha, hb, ht, rfl, source, target, entry⟩
  · rintro ⟨hg, hi, hj, hq, rfl, source, target, entry⟩
    exact ⟨hg, source, target, i, hi, j, hj, _, hq, rfl, rfl, entry⟩

theorem indexedTaskActionGraph_function {G I P N T : ZFSet.{u}}
    (task : ZFSet.IsFunc (ZFSet.prod G I) I T) (shape : N ⊆ ZFSet.prod I P)
    (closed : ∀ g ∈ G, ∀ i ∈ I, ∀ j ∈ I, ∀ q ∈ P,
      ZFSet.pair i q ∈ N → ZFSet.pair (ZFSet.pair g i) j ∈ T → ZFSet.pair j q ∈ N) :
    ZFSet.IsFunc (ZFSet.prod G N) N (indexedTaskActionGraph G I P N T) := by
  refine ⟨indexedTaskActionGraph_subset G I P N T, ?_⟩
  intro v hv
  obtain ⟨g, hg, x, hx, rfl⟩ := ZFSet.mem_prod.1 hv
  obtain ⟨i, hi, q, hq, rfl⟩ := ZFSet.mem_prod.1 (shape hx)
  obtain ⟨j, entry, unique⟩ := task.2 (ZFSet.pair g i) (ZFSet.pair_mem_prod.2 ⟨hg, hi⟩)
  have hj := (ZFSet.pair_mem_prod.1 (task.1 entry)).2
  refine ⟨ZFSet.pair j q, (indexedTaskActionGraph_entry_iff G I P N T g i j q q).2
    ⟨hg, hi, hj, hq, rfl, hx, closed g hg i hi j hj q hq hx entry, entry⟩, ?_⟩
  intro y hy
  obtain ⟨_, _, _, a, _, b, _, t, _, first, second, other⟩ :=
    (triple_mem_indexedTaskActionGraph G I P N T g (ZFSet.pair i q) y).1 hy
  obtain ⟨rfl, rfl⟩ := ZFSet.pair_inj.1 first
  exact second.trans (congrArg (fun k => ZFSet.pair k q) (unique b other))

theorem indexedTaskActionGraph_setAction {G I P N T m e : ZFSet.{u}}
    (task : SetActionCode G I m e T) (shape : N ⊆ ZFSet.prod I P)
    (closed : ∀ g ∈ G, ∀ i ∈ I, ∀ j ∈ I, ∀ q ∈ P,
      ZFSet.pair i q ∈ N → ZFSet.pair (ZFSet.pair g i) j ∈ T → ZFSet.pair j q ∈ N) :
    SetActionCode G N m e (indexedTaskActionGraph G I P N T) := by
  refine ⟨indexedTaskActionGraph_function task.function shape closed, ?_, ?_⟩
  · intro x hx
    obtain ⟨i, hi, q, hq, rfl⟩ := ZFSet.mem_prod.1 (shape hx)
    have identity := task.one i hi
    have he := (ZFSet.pair_mem_prod.1 (ZFSet.pair_mem_prod.1 (task.function.1 identity)).1).1
    exact (indexedTaskActionGraph_entry_iff G I P N T e i i q q).2
      ⟨he, hi, hi, hq, rfl, hx, hx, identity⟩
  · intro g hg h hh k hk x hx y hy z hz product first second
    obtain ⟨_, _, _, i, hi, j, hj, q, hq, xEq, yEq, firstTask⟩ :=
      (triple_mem_indexedTaskActionGraph G I P N T h x y).1 first
    obtain ⟨_, _, _, j', hj', l, hl, q', hq', yEq', zEq, secondTask⟩ :=
      (triple_mem_indexedTaskActionGraph G I P N T g y z).1 second
    have equal := ZFSet.pair_inj.1 (yEq.symm.trans yEq')
    obtain ⟨rfl, rfl⟩ := equal
    exact (triple_mem_indexedTaskActionGraph G I P N T k x z).2
      ⟨hk, hx, hz, i, hi, l, hl, _, hq, xEq, zEq,
        task.mul g hg h hh k hk i hi _ hj l hl product firstTask secondTask⟩

end PartitionPilot.Forcing



end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Definability_LiftedCompressionFormulas
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PartitionPilot.Forcing.BoundedFormula

open SetFormula
universe u

def rightTripleFormula {n} (z a b c : Fin n) : BoundedFormula n :=
  exMem z (exMem 0 (.conj (orderedPairFormula 0 b.succ.succ c.succ.succ)
    (orderedPairFormula z.succ.succ a.succ.succ 0)))

def liftOldEntryFormula {n} (d maps bound i x y : Fin n) : BoundedFormula n :=
  .conj (.mem x d) (exMem bound (.conj (pairMembershipFormula i.succ 0 maps.succ)
    (pairMembershipFormula x.succ y.succ 0)))

end PartitionPilot.Forcing.BoundedFormula

end

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Definability_RecursivePrimitiveFormulas
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
def recursiveIndicesSetFormula {n} (output i j p bound sources filters : Fin n) : SetFormula n :=
  exactSetFormula output (BoundedFormula.recursiveAttachmentIndexFormula 0 i.succ j.succ
    p.succ bound.succ sources.succ filters.succ).toFormula

def pairFieldSetFormula {n} (left : Bool) (output i j k bound family : Fin n) : SetFormula n :=
  exactSetFormula output (BoundedFormula.pairFieldEntryFormula left 0 k.succ i.succ j.succ
    bound.succ family.succ).toFormula

end SetFormula

end PartitionPilot.Forcing

end

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Transfinite_RecursiveStateFieldEnvironments
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open scoped ZFSet

namespace PartitionPilot.Forcing

universe u

structure RecursiveStateData where
  D : ZFSet.{u}
  rD : ZFSet.{u}
  μD : ZFSet.{u}
  J : ZFSet.{u}
  Qs : ZFSet.{u}
  rs : ZFSet.{u}
  μs : ZFSet.{u}
  As : ZFSet.{u}
  Es : ZFSet.{u}
  Fs : ZFSet.{u}
  Ss : ZFSet.{u}
  Maps : ZFSet.{u}
  A : ZFSet.{u}

namespace RecursiveStateData

def field (state : RecursiveStateData.{u}) : Fin 13 → ZFSet.{u} :=
  Fin.cases state.D (Fin.cases state.rD (Fin.cases state.μD (Fin.cases state.J (Fin.cases state.Qs (Fin.cases state.rs (Fin.cases state.μs (Fin.cases state.As (Fin.cases state.Es (Fin.cases state.Fs (Fin.cases state.Ss (Fin.cases state.Maps (Fin.cases state.A (Fin.elim0)))))))))))))

end RecursiveStateData

end PartitionPilot.Forcing

namespace PartitionPilot.Forcing.RecursiveStateData
universe u

def ofFields (fields : Fin 13 → ZFSet.{u}) : RecursiveStateData.{u} :=
  ⟨fields 0, fields 1, fields 2, fields 3, fields 4, fields 5, fields 6,
    fields 7, fields 8, fields 9, fields 10, fields 11, fields 12⟩

def successorEnvironment (state : RecursiveStateData.{u}) (I Sources Reps G T : ZFSet.{u}) :
    Fin 18 → ZFSet.{u} :=
  Fin.addCases (m := 13) (n := 5) state.field (SetFormula.extend I (SetFormula.extend Sources
    (SetFormula.extend Reps (SetFormula.extend G (SetFormula.extend T Fin.elim0)))))

end PartitionPilot.Forcing.RecursiveStateData

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Geometry_GroundTaskRepresentativeRecognition
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PartitionPilot.Forcing
open SetFormula
universe u
namespace SetFormula

def groundRelationsFormula {n} (output P Q : Fin n) : SetFormula n :=
  exactSetFormula output (BoundedFormula.relationBetweenFormula P.succ Q.succ 0).toFormula

end SetFormula

def TaskRepresentativesCode (Reps I P G r A R U Labels : ZFSet.{u}) : Prop :=
  ZFSet.IsFunc I G Reps ∧ ∀ i g, ZFSet.pair i g ∈ Reps →
    TaskRepresentative P r A R U Labels i g

end PartitionPilot.Forcing

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Transfinite_OwnerBirthLayers
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PartitionPilot.Forcing
universe u

noncomputable def ownerFresh (P B : ZFSet.{u}) : ZFSet.{u} :=
  ZFSet.sep (fun x => x ∉ P) B

theorem mem_ownerFresh (P B x : ZFSet.{u}) :
    x ∈ ownerFresh P B ↔ x ∈ B ∧ x ∉ P := ZFSet.mem_sep

noncomputable def ownerBirthGraph (P B T old levels stamps : ZFSet.{u}) : ZFSet.{u} :=
  old ∪ relationCompose (ownerFresh P B) ZFSet.omega T levels stamps

theorem pair_mem_ownerBirthGraph (P B T old levels stamps x t : ZFSet.{u}) :
    ZFSet.pair x t ∈ ownerBirthGraph P B T old levels stamps ↔
      ZFSet.pair x t ∈ old ∨
        x ∈ B ∧ x ∉ P ∧ t ∈ T ∧ ∃ n ∈ ZFSet.omega,
          ZFSet.pair x n ∈ levels ∧ ZFSet.pair n t ∈ stamps := by
  rw [ownerBirthGraph, ZFSet.mem_union, pair_mem_relationCompose, mem_ownerFresh]
  tauto

theorem ownerBirthGraph_old_iff {P B T old levels stamps x t : ZFSet.{u}}
    (hx : x ∈ P) :
    ZFSet.pair x t ∈ ownerBirthGraph P B T old levels stamps ↔ ZFSet.pair x t ∈ old := by
  rw [pair_mem_ownerBirthGraph]
  exact ⟨fun h => h.elim id (fun h => (h.2.1 hx).elim), Or.inl⟩

theorem ownerBirthGraph_fresh_iff {P B T T0 old levels stamps x t : ZFSet.{u}}
    (oldFunction : ZFSet.IsFunc P T0 old) (hx : x ∉ P) :
    ZFSet.pair x t ∈ ownerBirthGraph P B T old levels stamps ↔
      x ∈ B ∧ t ∈ T ∧ ∃ n ∈ ZFSet.omega,
        ZFSet.pair x n ∈ levels ∧ ZFSet.pair n t ∈ stamps := by
  rw [pair_mem_ownerBirthGraph]
  constructor
  · rintro (oldEntry | fresh)
    · exact (hx (ZFSet.pair_mem_prod.1 (oldFunction.1 oldEntry)).1).elim
    · exact ⟨fresh.1, fresh.2.2⟩
  · rintro ⟨hB, ht, n, hn, level, stamp⟩
    exact Or.inr ⟨hB, hx, ht, n, hn, level, stamp⟩

theorem ownerBirthGraph_function {P B T T0 old levels stamps : ZFSet.{u}}
    (oldFunction : ZFSet.IsFunc P T0 old) (oldSubset : P ⊆ B) (times : T0 ⊆ T)
    (levelFunction : ZFSet.IsFunc (ownerFresh P B) ZFSet.omega levels)
    (stampFunction : ZFSet.IsFunc ZFSet.omega T stamps) :
    ZFSet.IsFunc B T (ownerBirthGraph P B T old levels stamps) := by
  have freshFunction := relationCompose_function_of_subset levelFunction stampFunction (fun _ h => h)
  constructor
  · intro z hz
    rcases ZFSet.mem_union.1 hz with oldEntry | freshEntry
    · obtain ⟨x, hx, t, ht, rfl⟩ := ZFSet.mem_prod.1 (oldFunction.1 oldEntry)
      exact ZFSet.pair_mem_prod.2 ⟨oldSubset hx, times ht⟩
    · obtain ⟨x, hx, t, ht, rfl⟩ := ZFSet.mem_prod.1 (freshFunction.1 freshEntry)
      exact ZFSet.pair_mem_prod.2 ⟨(mem_ownerFresh P B x).1 hx |>.1, ht⟩
  · intro x hx
    by_cases oldPoint : x ∈ P
    · obtain ⟨t, entry, unique⟩ := oldFunction.2 x oldPoint
      exact ⟨t, (ownerBirthGraph_old_iff oldPoint).2 entry,
        fun y hy => unique y ((ownerBirthGraph_old_iff oldPoint).1 hy)⟩
    · have freshPoint := (mem_ownerFresh P B x).2 ⟨hx, oldPoint⟩
      obtain ⟨t, entry, unique⟩ := freshFunction.2 x freshPoint
      refine ⟨t, ZFSet.mem_union.2 (Or.inr entry), ?_⟩
      intro y hy
      rcases ZFSet.mem_union.1 hy with oldEntry | freshEntry
      · exact (oldPoint (ZFSet.pair_mem_prod.1 (oldFunction.1 oldEntry)).1).elim
      · exact unique y freshEntry

end PartitionPilot.Forcing

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Geometry_RectangleFulfillmentAtBound
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace PartitionPilot.Forcing
universe u

noncomputable def externalRectangleCode (c b d g h : ZFSet.{u}) : ZFSet.{u} :=
  ZFSet.pair c (ZFSet.pair b (ZFSet.pair d (ZFSet.pair g h)))

noncomputable def externalRectangleBound (P G : ZFSet.{u}) : ZFSet.{u} :=
  ZFSet.prod P (ZFSet.prod P (ZFSet.prod P (ZFSet.prod G G)))

theorem externalRectangleCode_inj {c b d g h c' b' d' g' h' : ZFSet.{u}} :
    externalRectangleCode c b d g h = externalRectangleCode c' b' d' g' h' ↔
      c = c' ∧ b = b' ∧ d = d' ∧ g = g' ∧ h = h' := by
  simp only [externalRectangleCode, ZFSet.pair_inj]

theorem externalRectangleCode_mem_bound (P G c b d g h : ZFSet.{u}) :
    externalRectangleCode c b d g h ∈ externalRectangleBound P G ↔
      c ∈ P ∧ b ∈ P ∧ d ∈ P ∧ g ∈ G ∧ h ∈ G := by
  simp only [externalRectangleCode, externalRectangleBound, ZFSet.pair_mem_prod]

end PartitionPilot.Forcing



namespace PartitionPilot.Forcing
universe u

def RectangleRootMeetCode (P μ A Q ν B e c d g k : ZFSet.{u}) : Prop :=
  ∀ x ∈ P, ∀ v ∈ P, ∀ w ∈ P, ∀ d' ∈ Q, ∀ x' ∈ Q, ∀ w' ∈ Q, ∀ y ∈ Q,
    ZFSet.pair (ZFSet.pair g c) v ∈ A → ZFSet.pair (ZFSet.pair v x) w ∈ μ →
    ZFSet.pair d d' ∈ e → ZFSet.pair x x' ∈ e → ZFSet.pair w w' ∈ e →
    ZFSet.pair (ZFSet.pair k d') y ∈ B → ZFSet.pair (ZFSet.pair y x') w' ∈ ν

def RectangleCrossMeetCode (Q ν B e b d k l : ZFSet.{u}) : Prop :=
  ∀ b' ∈ Q, ∀ d' ∈ Q, ∀ y ∈ Q, ∀ v ∈ Q, ∀ z ∈ Q,
    ZFSet.pair b b' ∈ e → ZFSet.pair d d' ∈ e →
    ZFSet.pair (ZFSet.pair k d') y ∈ B → ZFSet.pair (ZFSet.pair l d') v ∈ B →
    ZFSet.pair (ZFSet.pair k b') z ∈ B →
      ZFSet.pair (ZFSet.pair y v) z ∈ ν ∧ ZFSet.pair (ZFSet.pair l b') z ∈ B

end PartitionPilot.Forcing



end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Definability_GroundExternalRequestSetRecognition
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PartitionPilot.Forcing

section
universe u

noncomputable def externalRequestPayloadBound (I P Rectangles : ZFSet.{u}) : ZFSet.{u} :=
  (I ∪ P) ∪ Rectangles

def ExternalRequestOverlapForward
    (P G Rectangles Maps F r A zero first second q i x j y : ZFSet.{u}) : Prop :=
  (i = zero ∧ j = first ∧ ∃ f ∈ F, ZFSet.pair q f ∈ Maps ∧ ZFSet.pair y x ∈ f) ∨
  (i = zero ∧ j = first ∧ ∃ w ∈ P, q = ZFSet.pair first w ∧ x = y ∧ ZFSet.pair x w ∈ r) ∨
  (∃ t ∈ Rectangles, ∃ c ∈ P, ∃ b ∈ P, ∃ d ∈ P, ∃ g ∈ G, ∃ h ∈ G,
    q = ZFSet.pair second t ∧ t = externalRectangleCode c b d g h ∧
      ((i = zero ∧ j = first ∧ ZFSet.pair y c ∈ r ∧ ZFSet.pair (ZFSet.pair g y) x ∈ A) ∨
       (i = zero ∧ j = second ∧ ZFSet.pair y c ∈ r ∧ ZFSet.pair (ZFSet.pair h y) x ∈ A) ∨
       (i = first ∧ j = second ∧ x = y ∧ ZFSet.pair x b ∈ r)))

def ExternalRequestOverlapCode
    (P G Rectangles Maps F r A zero first second q i x j y : ZFSet.{u}) : Prop :=
  (i = j ∧ x = y) ∨
    ExternalRequestOverlapForward P G Rectangles Maps F r A zero first second q i x j y ∨
    ExternalRequestOverlapForward P G Rectangles Maps F r A zero first second q j y i x

namespace BoundedFormula
open SetFormula

def separationOverlapFormula {n} (P r zero first q i x j y : Fin n) : BoundedFormula n :=
  .conj (.equal i zero) (.conj (.equal j first)
    (exMem P (.conj (orderedPairFormula q.succ first.succ 0)
      (.conj (.equal x.succ y.succ) (pairMembershipFormula x.succ 0 r.succ)))))

end BoundedFormula

end

open SetFormula
universe u

end PartitionPilot.Forcing

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Transfinite_GroundBatchBirths
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PartitionPilot.Forcing

section

universe u

noncomputable def fixedTopBirth (P birth s : ZFSet.{u}) : ZFSet.{u} :=
  insert (ZFSet.pair P s) birth

theorem pair_mem_fixedTopBirth (P birth s x t : ZFSet.{u}) :
    ZFSet.pair x t ∈ fixedTopBirth P birth s ↔
      (x = P ∧ t = s) ∨ ZFSet.pair x t ∈ birth := by
  rw [fixedTopBirth, ZFSet.mem_insert_iff, ZFSet.pair_inj]

theorem fixedTopBirth_subset (P birth s : ZFSet.{u}) : birth ⊆ fixedTopBirth P birth s :=
  fun _ h => ZFSet.mem_insert_iff.2 (Or.inr h)

theorem fixedTopBirth_old_iff {P birth s x t : ZFSet.{u}} (hx : x ∈ P) :
    ZFSet.pair x t ∈ fixedTopBirth P birth s ↔ ZFSet.pair x t ∈ birth := by
  rw [pair_mem_fixedTopBirth]
  exact ⟨fun h => h.elim (fun equal => False.elim (ZFSet.mem_irrefl P (equal.1 ▸ hx))) id,
    Or.inr⟩

theorem fixedTopBirth_top_iff {P T birth s t : ZFSet.{u}} (born : ZFSet.IsFunc P T birth) :
    ZFSet.pair P t ∈ fixedTopBirth P birth s ↔ t = s := by
  rw [pair_mem_fixedTopBirth]
  exact ⟨fun h => h.elim And.right (fun entry =>
    False.elim (ZFSet.mem_irrefl P (ZFSet.pair_mem_prod.1 (born.1 entry)).1)),
    fun equal => Or.inl ⟨rfl, equal⟩⟩

theorem fixedTopBirth_bound {P birth s : ZFSet.{u}}
    (earlier : ∀ x t, ZFSet.pair x t ∈ birth → t ∈ s) :
    ∀ x t, ZFSet.pair x t ∈ fixedTopBirth P birth s → t = s ∨ t ∈ s := by
  intro x t entry
  exact ((pair_mem_fixedTopBirth P birth s x t).1 entry).elim
    (fun equal => Or.inl equal.2) (fun old => Or.inr (earlier x t old))

theorem fixedTopBirth_new_time_iff {P birth s x : ZFSet.{u}}
    (earlier : ∀ x t, ZFSet.pair x t ∈ birth → t ∈ s) :
    ZFSet.pair x s ∈ fixedTopBirth P birth s ↔ x = P := by
  rw [pair_mem_fixedTopBirth]
  exact ⟨fun h => h.elim And.left (fun old => False.elim (ZFSet.mem_irrefl s (earlier x s old))),
    fun equal => Or.inl ⟨equal, rfl⟩⟩

theorem fixedTopBirth_earlier_iff {P birth s x t : ZFSet.{u}} (before : t ∈ s) :
    ZFSet.pair x t ∈ fixedTopBirth P birth s ↔ ZFSet.pair x t ∈ birth := by
  rw [pair_mem_fixedTopBirth]
  exact ⟨fun h => h.elim (fun equal => False.elim (ZFSet.mem_irrefl s (equal.2 ▸ before))) id,
    Or.inr⟩

theorem fixedTopBirth_singleton_injection (P : ZFSet.{u}) :
    InjectionCode {P} ZFSet.omega {ZFSet.pair P ∅} := by
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · intro z hz
    have equal := ZFSet.mem_singleton.1 hz
    rw [equal]
    exact ZFSet.pair_mem_prod.2 ⟨ZFSet.mem_singleton.2 rfl, ZFSet.omega_zero⟩
  · intro x hx
    have equal := ZFSet.mem_singleton.1 hx
    subst x
    refine ⟨∅, ZFSet.mem_singleton.2 rfl, ?_⟩
    intro y entry
    exact (ZFSet.pair_inj.1 (ZFSet.mem_singleton.1 entry)).2
  · intro x y z first second
    exact (ZFSet.pair_inj.1 (ZFSet.mem_singleton.1 first)).1.trans
      (ZFSet.pair_inj.1 (ZFSet.mem_singleton.1 second)).1.symm

end

open SetRealization SetFormula
universe u

end PartitionPilot.Forcing

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Transfinite_GroundCompressionBirthData
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open scoped ZFSet


namespace PartitionPilot.Forcing
universe u

noncomputable def firstAppearanceBirth (U T Ps stamps oldBirth : ZFSet.{u}) : ZFSet.{u} :=
  ZFSet.sep (fun z => z ∈ oldBirth ∨ ∃ n ∈ ZFSet.omega, ∃ D E x t,
    z = ZFSet.pair x t ∧ ZFSet.pair n D ∈ Ps ∧ ZFSet.pair (insert n n) E ∈ Ps ∧
      ZFSet.pair n t ∈ stamps ∧ x ∈ E ∧ x ∉ D) (ZFSet.prod U T)

end PartitionPilot.Forcing



namespace PartitionPilot.Forcing
universe u

structure NatBirthExtensionCode (P stamp : Nat → ZFSet.{u}) (old birth : ZFSet.{u}) : Prop where
  shape : ∀ z ∈ birth, ∃ x t, z = ZFSet.pair x t
  entries : ∀ x t, ZFSet.pair x t ∈ birth ↔
    ZFSet.pair x t ∈ old ∨ ∃ n, x ∈ P (n + 1) ∧ x ∉ P n ∧ t = stamp n

namespace NatBirthExtensionCode
variable {P stamp : Nat → ZFSet.{u}} {old birth U T : ZFSet.{u}}

theorem first_appearance_unique (mono : ∀ n m, n ≤ m → P n ⊆ P m)
    {n m : Nat} {x : ZFSet.{u}} (hn : x ∈ P (n + 1)) (notN : x ∉ P n)
    (hm : x ∈ P (m + 1)) (notM : x ∉ P m) : n = m := by
  rcases lt_trichotomy n m with before | equal | after
  · exact False.elim (notM (mono (n + 1) m (Nat.succ_le_of_lt before) hn))
  · exact equal
  · exact False.elim (notN (mono (m + 1) n (Nat.succ_le_of_lt after) hm))

theorem first_appearance_exists (carrier : NatUnionCode P U) {x : ZFSet.{u}}
    (hx : x ∈ U) (outside : x ∉ P 0) : ∃ n, x ∈ P (n + 1) ∧ x ∉ P n := by
  obtain ⟨n, hn⟩ := (carrier x).1 hx
  induction n with
  | zero => exact False.elim (outside hn)
  | succ n ih =>
    by_cases before : x ∈ P n
    · exact ih before
    · exact ⟨n, hn, before⟩

variable (code : NatBirthExtensionCode P stamp old birth)
include code

theorem function (carrier : NatUnionCode P U)
    (mono : ∀ n m, n ≤ m → P n ⊆ P m)
    (born : ZFSet.IsFunc (P 0) T old) (stamps : ∀ n, stamp n ∈ T) :
    ZFSet.IsFunc U T birth := by
  constructor
  · intro z hz
    obtain ⟨x, t, rfl⟩ := code.shape z hz
    rcases (code.entries x t).1 hz with oldEntry | ⟨n, hn, _, rfl⟩
    · have bounds := ZFSet.pair_mem_prod.1 (born.1 oldEntry)
      exact ZFSet.pair_mem_prod.2 ⟨carrier.subset 0 bounds.1, bounds.2⟩
    · exact ZFSet.pair_mem_prod.2 ⟨carrier.subset (n + 1) hn, stamps n⟩
  · intro x hx
    by_cases original : x ∈ P 0
    · obtain ⟨t, oldEntry, unique⟩ := born.2 x original
      refine ⟨t, (code.entries x t).2 (Or.inl oldEntry), ?_⟩
      intro s entry
      rcases (code.entries x s).1 entry with before | ⟨n, _, outside, _⟩
      · exact unique s before
      · exact False.elim (outside (mono 0 n (Nat.zero_le n) original))
    · obtain ⟨n, hn, outside⟩ := first_appearance_exists carrier hx original
      refine ⟨stamp n, (code.entries x (stamp n)).2 (Or.inr ⟨n, hn, outside, rfl⟩), ?_⟩
      intro s entry
      rcases (code.entries x s).1 entry with before | ⟨m, hm, notM, equal⟩
      · exact False.elim (original (ZFSet.pair_mem_prod.1 (born.1 before)).1)
      · rw [first_appearance_unique mono hm notM hn outside] at equal
        exact equal

theorem old_entry_iff (mono : ∀ n m, n ≤ m → P n ⊆ P m)
    {x t : ZFSet.{u}} (hx : x ∈ P 0) :
    ZFSet.pair x t ∈ birth ↔ ZFSet.pair x t ∈ old := by
  rw [code.entries]
  constructor
  · rintro (entry | ⟨n, _, outside, _⟩)
    · exact entry
    · exact False.elim (outside (mono 0 n (Nat.zero_le n) hx))
  · exact Or.inl

end NatBirthExtensionCode

end PartitionPilot.Forcing



end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Geometry_GroundTileStarIncidence
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PartitionPilot.Forcing

open SetFormula
universe u

noncomputable def dartIncidenceGraph (source target : ZFSet.{u}) : ZFSet.{u} := source ∪ target
noncomputable def dartAdjacencyGraph (D V source target : ZFSet.{u}) : ZFSet.{u} :=
  relationCompose V D V (relationConverse D V source) target

namespace BoundedFormula

def tileStarReverseFormula {n} (Edges d v zero one : Fin n) : BoundedFormula n :=
  (exMem Edges (disj (.conj (orderedPairFormula d.succ 0 zero.succ) (orderedPairFormula v.succ 0 one.succ)) (.conj (orderedPairFormula d.succ 0 one.succ) (orderedPairFormula v.succ 0 zero.succ))))

def tileStarReverseEntryFormula {n} (z D V Edges zero one : Fin n) : BoundedFormula n :=
  exMem D (exMem V.succ (.conj (orderedPairFormula z.succ.succ 1 0)
    (tileStarReverseFormula Edges.succ.succ 1 0 zero.succ.succ one.succ.succ)))

end BoundedFormula

end PartitionPilot.Forcing

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Geometry_GroundCompressionHeightSteps
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace PartitionPilot.Forcing

universe u

noncomputable def lexHeightOrder (C D rD : ZFSet.{u}) : ZFSet.{u} :=
  ZFSet.sep (fun z => ∃ c ∈ C, ∃ q ∈ D, ∃ d ∈ C, ∃ v ∈ D,
    z = ZFSet.pair (ZFSet.pair c q) (ZFSet.pair d v) ∧
      (c ∈ d ∨ (c = d ∧ ZFSet.pair q v ∈ rD)))
    (ZFSet.prod (ZFSet.prod C D) (ZFSet.prod C D))

theorem mem_lexHeightOrder (C D rD z : ZFSet.{u}) :
    z ∈ lexHeightOrder C D rD ↔
      ∃ c ∈ C, ∃ q ∈ D, ∃ d ∈ C, ∃ v ∈ D,
        z = ZFSet.pair (ZFSet.pair c q) (ZFSet.pair d v) ∧
          (c ∈ d ∨ (c = d ∧ ZFSet.pair q v ∈ rD)) := by
  constructor
  · exact fun h => (ZFSet.mem_sep.1 h).2
  · rintro ⟨c, hc, q, hq, d, hd, v, hv, rfl, lower⟩
    exact ZFSet.mem_sep.2 ⟨ZFSet.pair_mem_prod.2
      ⟨ZFSet.pair_mem_prod.2 ⟨hc, hq⟩, ZFSet.pair_mem_prod.2 ⟨hd, hv⟩⟩,
      c, hc, q, hq, d, hd, v, hv, rfl, lower⟩

theorem pair_mem_lexHeightOrder (C D rD c q d v : ZFSet.{u}) :
    ZFSet.pair (ZFSet.pair c q) (ZFSet.pair d v) ∈ lexHeightOrder C D rD ↔
      c ∈ C ∧ q ∈ D ∧ d ∈ C ∧ v ∈ D ∧ (c ∈ d ∨ (c = d ∧ ZFSet.pair q v ∈ rD)) := by
  rw [mem_lexHeightOrder]
  constructor
  · rintro ⟨c', hc, q', hq, d', hd, v', hv, equal, lower⟩
    obtain ⟨left, right⟩ := ZFSet.pair_inj.1 equal
    obtain ⟨rfl, rfl⟩ := ZFSet.pair_inj.1 left
    obtain ⟨rfl, rfl⟩ := ZFSet.pair_inj.1 right
    exact ⟨hc, hq, hd, hv, lower⟩
  · rintro ⟨hc, hq, hd, hv, lower⟩
    exact ⟨c, hc, q, hq, d, hd, v, hv, rfl, lower⟩

end PartitionPilot.Forcing



namespace PartitionPilot.Forcing
universe u






noncomputable def fixedTopHeightGraph (P old b q : ZFSet.{u}) : ZFSet.{u} :=
  insert (ZFSet.pair P (ZFSet.pair b q)) old

theorem pair_mem_fixedTopHeightGraph (P old b q x y : ZFSet.{u}) :
    ZFSet.pair x y ∈ fixedTopHeightGraph P old b q ↔
      (x = P ∧ y = ZFSet.pair b q) ∨ ZFSet.pair x y ∈ old := by
  rw [fixedTopHeightGraph, ZFSet.mem_insert_iff, ZFSet.pair_inj]

theorem fixedTopHeightGraph_old_iff {P old b q x y : ZFSet.{u}} (hx : x ∈ P) :
    ZFSet.pair x y ∈ fixedTopHeightGraph P old b q ↔ ZFSet.pair x y ∈ old := by
  rw [pair_mem_fixedTopHeightGraph]
  exact ⟨fun h => h.elim (fun eq => False.elim (ZFSet.mem_irrefl P (eq.1 ▸ hx))) id,
    Or.inr⟩

end PartitionPilot.Forcing



end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Models_GroundCoherentHeightChoices
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PartitionPilot.Forcing
open SetFormula SetRealization
universe u

noncomputable def stagedGraphRelation (W : ZFSet.{u}) : ZFSet.{u} :=
  ZFSet.sep (fun z => ∃ n m h k,
    z = ZFSet.pair (ZFSet.pair n h) (ZFSet.pair m k) ∧ m = insert n n ∧ h ⊆ k)
    (ZFSet.prod W W)

end PartitionPilot.Forcing

end

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Transfinite_GroundCompressionPrefixGraphs
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PartitionPilot.Forcing

section
universe u

noncomputable def compressionPrefixValue (base limit : ZFSet.{u})
    (prior : ZFSet.{u} → ZFSet.{u}) (stages : Nat → ZFSet.{u}) (final s : ZFSet.{u}) : ZFSet.{u} := by
  classical
  exact if s ∈ base ∨ s = base then prior s else
    if s = limit then final else
      if witnessed : ∃ n, s = compressionStamp base n then stages witnessed.choose else ∅

variable {base limit : ZFSet.{u}}
variable (prior : ZFSet.{u} → ZFSet.{u}) (stages : Nat → ZFSet.{u}) (final : ZFSet.{u})

theorem compressionPrefixValue_old {s : ZFSet.{u}} (old : s ∈ base ∨ s = base) :
    compressionPrefixValue base limit prior stages final s = prior s := by
  classical
  simp only [compressionPrefixValue, ite_eq_left old]

end

open SetFormula
universe u

noncomputable def compressionPrefixGraph (base limit old stages stamps final : ZFSet.{u}) : ZFSet.{u} :=
  insert (ZFSet.pair limit final) (graphRestriction (insert base base) old ∪
    relationCompose limit ZFSet.omega (ZFSet.sUnion (ZFSet.sUnion stages))
      (relationConverse ZFSet.omega limit stamps) stages)

end PartitionPilot.Forcing

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Transfinite_GroundChronologyFieldAppend
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace PartitionPilot.Forcing
open SetFormula
universe u

theorem isFunc_retarget_of_entries {A B C f : ZFSet.{u}}
    (function : ZFSet.IsFunc A B f)
    (bound : ∀ x y, ZFSet.pair x y ∈ f → y ∈ C) : ZFSet.IsFunc A C f := by
  refine ⟨?_, function.2⟩
  intro z entry
  obtain ⟨x, hx, y, _, rfl⟩ := ZFSet.mem_prod.1 (function.1 entry)
  exact ZFSet.pair_mem_prod.2 ⟨hx, bound x y entry⟩

end PartitionPilot.Forcing



namespace PartitionPilot.Forcing
universe u

structure CompressionChronologyFields where
  space : ZFSet.{u} → ZFSet.{u}
  order : ZFSet.{u} → ZFSet.{u}
  meetGraph : ZFSet.{u} → ZFSet.{u}
  birth : ZFSet.{u} → ZFSet.{u}
  height : ZFSet.{u} → ZFSet.{u}

end PartitionPilot.Forcing



namespace PartitionPilot.Forcing
open SetFormula
universe u

noncomputable def appendHistoryValue (time : ZFSet.{u})
    (previous : ZFSet.{u} → ZFSet.{u}) (latest t : ZFSet.{u}) : ZFSet.{u} := by
  classical
  exact if t = time then latest else previous t

theorem appendHistoryValue_at (time : ZFSet.{u}) (previous : ZFSet.{u} → ZFSet.{u})
    (latest : ZFSet.{u}) : appendHistoryValue time previous latest time = latest := by
  simp [appendHistoryValue]

end PartitionPilot.Forcing



namespace PartitionPilot.Forcing
open SetFormula
universe u

noncomputable def terminalChronologyGraph (s f v : ZFSet.{u}) : ZFSet.{u} :=
  insert (ZFSet.pair s v) (graphRestriction s f)

end PartitionPilot.Forcing



end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Geometry_GroundCompressionStarIncidence
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace PartitionPilot.Forcing
open SetFormula
universe u

noncomputable def externalCosetRelation (E G inclusion multiplication : ZFSet.{u}) : ZFSet.{u} :=
  ZFSet.sep (fun z => ∃ w ∈ E, ∃ v ∈ E, z = ZFSet.pair w v ∧
    ∃ j ∈ G, ∃ k ∈ E, ZFSet.pair j k ∈ inclusion ∧
      ZFSet.pair (ZFSet.pair w k) v ∈ multiplication) (ZFSet.prod E E)

theorem externalCosetRelation_subset (E G inclusion multiplication : ZFSet.{u}) :
    externalCosetRelation E G inclusion multiplication ⊆ ZFSet.prod E E :=
  fun _ h => (ZFSet.mem_sep.1 h).1

theorem pair_mem_externalCosetRelation (E G inclusion multiplication w v : ZFSet.{u}) :
    ZFSet.pair w v ∈ externalCosetRelation E G inclusion multiplication ↔
      w ∈ E ∧ v ∈ E ∧ ∃ j ∈ G, ∃ k ∈ E, ZFSet.pair j k ∈ inclusion ∧
        ZFSet.pair (ZFSet.pair w k) v ∈ multiplication := by
  rw [externalCosetRelation, ZFSet.mem_sep]
  constructor
  · rintro ⟨_, w', hw, v', hv, equal, witnesses⟩
    obtain ⟨rfl, rfl⟩ := ZFSet.pair_inj.1 equal
    exact ⟨hw, hv, witnesses⟩
  · rintro ⟨hw, hv, witnesses⟩
    exact ⟨ZFSet.pair_mem_prod.2 ⟨hw, hv⟩, w, hw, v, hv, rfl, witnesses⟩

end PartitionPilot.Forcing



end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Definability_CompressionExternalStepRealization
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open scoped ZFSet


namespace PartitionPilot.Forcing
open SetFormula
universe u

def ExternalFlatVertexWordCode
    (E S generators m zero first second q i w v : ZFSet.{u}) : Prop :=
  (i = zero ∧ v = w) ∨ ∃ s ∈ S, ∃ k ∈ E,
    ((i = first ∧ s = ZFSet.pair q zero) ∨ (i = second ∧ s = ZFSet.pair q first)) ∧
      ZFSet.pair s k ∈ generators ∧ ZFSet.pair (ZFSet.pair w k) v ∈ m





def ExternalFlatCoordinateCode (E U G old m A a b : ZFSet.{u}) : Prop :=
  ∃ w ∈ E, ∃ k ∈ E, ∃ v ∈ E, ∃ j ∈ G, ∃ x ∈ U, ∃ y ∈ U,
    ZFSet.pair j k ∈ old ∧ ZFSet.pair (ZFSet.pair w k) v ∈ m ∧
      ZFSet.pair (ZFSet.pair j x) y ∈ A ∧ a = ZFSet.pair v x ∧ b = ZFSet.pair w y

def ExternalFlatTileStepCode (E V placements overlaps a b : ZFSet.{u}) : Prop :=
  ∃ w ∈ E, ∃ x ∈ V, ∃ y ∈ V,
    ZFSet.pair (ZFSet.pair w x) a ∈ placements ∧
      ZFSet.pair (ZFSet.pair w y) b ∈ placements ∧ ZFSet.pair x y ∈ overlaps

def ExternalFlatStepCode (E U G V old m A placements overlaps a b : ZFSet.{u}) : Prop :=
  (ExternalFlatCoordinateCode E U G old m A a b ∨ ExternalFlatTileStepCode E V placements overlaps a b) ∨
  (ExternalFlatCoordinateCode E U G old m A b a ∨ ExternalFlatTileStepCode E V placements overlaps b a)

theorem ExternalFlatStepCode.symm {E U G V old m A placements overlaps a b : ZFSet.{u}}
    (step : ExternalFlatStepCode E U G V old m A placements overlaps a b) :
    ExternalFlatStepCode E U G V old m A placements overlaps b a := Or.symm step

noncomputable def externalFlatStepGraph (E U G V old m A placements overlaps : ZFSet.{u}) : ZFSet.{u} :=
  ZFSet.sep (fun z => ∃ a ∈ ZFSet.prod E U, ∃ b ∈ ZFSet.prod E U, z = ZFSet.pair a b ∧
    ExternalFlatStepCode E U G V old m A placements overlaps a b)
    (ZFSet.prod (ZFSet.prod E U) (ZFSet.prod E U))

theorem pair_mem_externalFlatStepGraph (E U G V old m A placements overlaps a b : ZFSet.{u}) :
    ZFSet.pair a b ∈ externalFlatStepGraph E U G V old m A placements overlaps ↔
      a ∈ ZFSet.prod E U ∧ b ∈ ZFSet.prod E U ∧
        ExternalFlatStepCode E U G V old m A placements overlaps a b := by
  rw [externalFlatStepGraph, ZFSet.mem_sep]
  constructor
  · rintro ⟨_, a', ha, b', hb, equal, step⟩
    obtain ⟨rfl, rfl⟩ := ZFSet.pair_inj.1 equal
    exact ⟨ha, hb, step⟩
  · rintro ⟨ha, hb, step⟩
    exact ⟨ZFSet.pair_mem_prod.2 ⟨ha, hb⟩, a, ha, b, hb, rfl, step⟩

theorem externalFlatStepGraph_symmetric {E U G V old m A placements overlaps a b : ZFSet.{u}}
    (entry : ZFSet.pair a b ∈ externalFlatStepGraph E U G V old m A placements overlaps) :
    ZFSet.pair b a ∈ externalFlatStepGraph E U G V old m A placements overlaps := by
  obtain ⟨ha, hb, step⟩ := (pair_mem_externalFlatStepGraph _ _ _ _ _ _ _ _ _ _ _).1 entry
  exact (pair_mem_externalFlatStepGraph _ _ _ _ _ _ _ _ _ _ _).2 ⟨hb, ha, step.symm⟩

end PartitionPilot.Forcing



end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Definability_GroundPackedRefinementFormulaData
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace PartitionPilot.Forcing
open SetRealization SetFormula
universe u

theorem map_three_p0 {α β : Type*} (f : α → β) (a b c : α) :
    (fun j : Fin 3 => f ((extend a (extend b (extend c Fin.elim0))) j)) = ![f a, f b, f c] := by
  funext j
  exact Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (fun k => Fin.elim0 k))) j

theorem map_four_p0 {α β : Type*} (f : α → β) (a b c d : α) :
    (fun j : Fin 4 => f ((extend a (extend b (extend c (extend d Fin.elim0)))) j)) = ![f a, f b, f c, f d] := by
  funext j
  exact Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (fun k => Fin.elim0 k)))) j

end PartitionPilot.Forcing



end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Definability_GroundTaggedComponentGraphs
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

def taggedComponentFormula : BoundedFormula 6 :=
  exMem 1 (exMem 3 (exMem 5 (exMem 7
    (.conj (orderedPairFormula 4 3 2)
      (.conj (orderedPairFormula 3 9 1) (orderedPairFormula 1 2 0))))))

end BoundedFormula

end PartitionPilot.Forcing

end

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Definability_RowAssignmentCutGraphLaws
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PartitionPilot.Forcing
universe u

theorem rowAssignmentCutGraph_function (upper lower levels alpha : ZFSet.{u})
    (flat : ∀ p ∈ upper, ∃ row A, p = ZFSet.pair row A)
    (closed : ∀ row A, ZFSet.pair row A ∈ upper →
      ZFSet.pair row (assignmentCut levels alpha A) ∈ lower) :
    ZFSet.IsFunc upper lower (rowAssignmentCutGraph upper lower levels alpha) := by
  refine ⟨fun _ h => ((mem_rowAssignmentCutGraph _ _ _ _ _).1 h).1, ?_⟩
  intro p hp
  obtain ⟨row, A, rfl⟩ := flat p hp
  refine ⟨ZFSet.pair row (assignmentCut levels alpha A),
    (pair_mem_rowAssignmentCutGraph _ _ _ _ _ _ _).2 ⟨hp, closed row A hp, rfl⟩, ?_⟩
  intro q entry
  exact ((pair_mem_rowAssignmentCutGraph _ _ _ _ _ _ _).1 entry).2.2

end PartitionPilot.Forcing

end

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Definability_RowAssignmentTransitionFormulas
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PartitionPilot.Forcing
open SetFormula SetRealization
universe u

namespace BoundedFormula
def cutGraphProductMember {n : Nat} (z upper lower : Fin n) : BoundedFormula n :=
  exMem upper (exMem lower.succ (orderedPairFormula z.succ.succ 1 0))

end BoundedFormula

end PartitionPilot.Forcing

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Forcing_GreedyAntichainTraces
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PartitionPilot.Forcing
universe u

def OrderAntichainCode (Q order D : ZFSet.{u}) : Prop :=
  D ⊆ Q ∧ ∀ p ∈ D, ∀ q ∈ D, ∀ r ∈ Q,
    ZFSet.pair r p ∈ order → ZFSet.pair r q ∈ order → p = q

def RelativeMaximalAntichainCode (Q order D A : ZFSet.{u}) : Prop :=
  A ⊆ D ∧ OrderAntichainCode Q order A ∧
    ∀ q ∈ D, ∃ p ∈ A, ∃ r ∈ Q,
      ZFSet.pair r q ∈ order ∧ ZFSet.pair r p ∈ order

noncomputable def antichainEligible (Q order D alpha prior : ZFSet.{u}) : ZFSet.{u} :=
  ZFSet.sep (fun q => ¬ ∃ beta ∈ alpha, ∃ p ∈ D,
    ZFSet.pair beta p ∈ prior ∧ ∃ r ∈ Q,
      ZFSet.pair r q ∈ order ∧ ZFSet.pair r p ∈ order) D

def GreedyAntichainStep (Q order D F c alpha prior y : ZFSet.{u}) : Prop :=
  (∃ E ∈ F, E = antichainEligible Q order D alpha prior ∧ ZFSet.pair E y ∈ c) ∨
    (¬ (antichainEligible Q order D alpha prior).Nonempty ∧ y = D)

end PartitionPilot.Forcing

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Geometry_GroundCodedBinaryHeights
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open scoped ZFSet


namespace PartitionPilot.Forcing
open SetFormula
universe u

structure StrictHeightGraphCode (L H rL rH h : ZFSet.{u}) : Prop where
  function : ZFSet.IsFunc L H h
  strict : ∀ x ∈ L, ∀ y ∈ L, x ≠ y → ZFSet.pair x y ∈ rL →
    ∀ a b, ZFSet.pair x a ∈ h → ZFSet.pair y b ∈ h → ZFSet.pair a b ∈ rH

end PartitionPilot.Forcing



namespace PartitionPilot.Forcing
universe u

noncomputable def lexProductOrder (C D rC rD : ZFSet.{u}) : ZFSet.{u} :=
  ZFSet.sep (fun z => ∃ c ∈ C, ∃ q ∈ D, ∃ d ∈ C, ∃ v ∈ D,
    z = ZFSet.pair (ZFSet.pair c q) (ZFSet.pair d v) ∧
      (ZFSet.pair c d ∈ rC ∨ (c = d ∧ ZFSet.pair q v ∈ rD)))
    (ZFSet.prod (ZFSet.prod C D) (ZFSet.prod C D))

end PartitionPilot.Forcing



namespace PartitionPilot.Forcing
open SetRealization SetFormula
universe u

structure IntervalHeightCode (L r D rD lo hi height : ZFSet.{u}) : Prop
    extends StrictHeightGraphCode L D r rD height where
  inside : ∀ x z, ZFSet.pair x z ∈ height → ZFSet.pair lo z ∈ rD ∧ ZFSet.pair z hi ∈ rD

end PartitionPilot.Forcing



namespace PartitionPilot.Forcing
universe u

def intervalHeightCandidate (Ps rs D rD lo hi i f : ZFSet.{u}) : Prop :=
  ∃ P ∈ ⋃₀ ⋃₀ Ps, ∃ r ∈ ⋃₀ ⋃₀ rs,
    ZFSet.pair i P ∈ Ps ∧ ZFSet.pair i r ∈ rs ∧ IntervalHeightCode P r D rD lo hi f

noncomputable def intervalHeightRelation (I W Ps rs D rD lo hi : ZFSet.{u}) : ZFSet.{u} :=
  ZFSet.sep (fun z => ∃ i ∈ I, ∃ f ∈ W, z = ZFSet.pair i f ∧
    intervalHeightCandidate Ps rs D rD lo hi i f) (ZFSet.prod I W)

end PartitionPilot.Forcing



end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Definability_IntervalHeightFormulas
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PartitionPilot.Forcing.BoundedFormula
open SetFormula
universe u

def intervalHeightFormula {n} (L r D rD lo hi f : Fin n) : BoundedFormula n :=
  let lift (i : Fin n) : Fin (n + 4) := i.succ.succ.succ.succ
  let strict : BoundedFormula n :=
    .allMem L (.allMem L.succ (.allMem D.succ.succ (.allMem D.succ.succ.succ
      (imp (.neg (.equal 3 2)) (imp (pairMembershipFormula 3 2 (lift r))
        (imp (pairMembershipFormula 3 1 (lift f))
          (imp (pairMembershipFormula 2 0 (lift f)) (pairMembershipFormula 1 0 (lift rD)))))))))
  let inside : BoundedFormula n :=
    .allMem L (.allMem D.succ (imp (pairMembershipFormula 1 0 f.succ.succ)
      (.conj (pairMembershipFormula lo.succ.succ 0 rD.succ.succ)
        (pairMembershipFormula 0 hi.succ.succ rD.succ.succ))))
  .conj (functionFormula L D f) (.conj strict inside)

end PartitionPilot.Forcing.BoundedFormula

end

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Definability_IndexedSubstructureCodes
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PartitionPilot.Forcing
open SetFormula
universe u

def indexedSuborderGraph (I B R domains : ZFSet.{u}) : ZFSet.{u} :=
  ZFSet.sep (fun z => ∃ i ∈ I, ∃ v ∈ R, ∃ x ∈ B, ∃ y ∈ B,
    z = ZFSet.pair i v ∧ v = ZFSet.pair x y ∧
      ZFSet.pair i x ∈ domains ∧ ZFSet.pair i y ∈ domains) (ZFSet.prod I R)

def indexedSubmeetGraph (I B μ domains : ZFSet.{u}) : ZFSet.{u} :=
  ZFSet.sep (fun z => ∃ i ∈ I, ∃ v ∈ μ, ∃ x ∈ B, ∃ y ∈ B, ∃ w ∈ B,
    z = ZFSet.pair i v ∧ v = ZFSet.pair (ZFSet.pair x y) w ∧
      ZFSet.pair i x ∈ domains ∧ ZFSet.pair i y ∈ domains ∧ ZFSet.pair i w ∈ domains)
    (ZFSet.prod I μ)

namespace BoundedFormula
def indexedSuborderEntryFormula {n} (z I B R domains : Fin n) : BoundedFormula n :=
  exMem I (exMem R.succ (exMem B.succ.succ (exMem B.succ.succ.succ
    (.conj (orderedPairFormula z.succ.succ.succ.succ 3 2)
      (.conj (orderedPairFormula 2 1 0)
        (.conj (pairMembershipFormula 3 1 domains.succ.succ.succ.succ)
          (pairMembershipFormula 3 0 domains.succ.succ.succ.succ)))))))

end BoundedFormula

end PartitionPilot.Forcing

end

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Geometry_GroundExternalLocalHeightSelection
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

def intervalHeightCandidateFormula {n}
    (Ps rs D rD lo hi i f boundPs boundRs : Fin n) : BoundedFormula n :=
  let lift (j : Fin n) := j.succ.succ
  exMem boundPs (exMem boundRs.succ
    (.conj (pairMembershipFormula (lift i) 1 (lift Ps))
      (.conj (pairMembershipFormula (lift i) 0 (lift rs))
        (intervalHeightFormula 1 0 (lift D) (lift rD) (lift lo) (lift hi) (lift f)))))

def intervalHeightRelationEntryFormula {n}
    (z I W Ps rs D rD lo hi boundPs boundRs : Fin n) : BoundedFormula n :=
  exMem I (exMem W.succ
    (.conj (orderedPairFormula z.succ.succ 1 0)
      (intervalHeightCandidateFormula Ps.succ.succ rs.succ.succ D.succ.succ
        rD.succ.succ lo.succ.succ hi.succ.succ 1 0 boundPs.succ.succ boundRs.succ.succ)))

end BoundedFormula

end PartitionPilot.Forcing



namespace PartitionPilot.Forcing
open SetFormula
universe u

def vertexImageDomains (Requests N U Q V images : ZFSet.{u}) : ZFSet.{u} :=
  ZFSet.sep (fun z => ∃ r ∈ Requests, ∃ y ∈ Q, ∃ j ∈ N, ∃ x ∈ U, ∃ v ∈ V,
    z = ZFSet.pair r y ∧ v = ZFSet.pair (ZFSet.pair r j) x ∧ ZFSet.pair v y ∈ images)
    (ZFSet.prod Requests Q)

theorem pair_mem_vertexImageDomains (Requests N U Q V images r y : ZFSet.{u}) :
    ZFSet.pair r y ∈ vertexImageDomains Requests N U Q V images ↔
      r ∈ Requests ∧ y ∈ Q ∧ ∃ j ∈ N, ∃ x ∈ U,
        ZFSet.pair (ZFSet.pair r j) x ∈ V ∧
          ZFSet.pair (ZFSet.pair (ZFSet.pair r j) x) y ∈ images := by
  rw [vertexImageDomains, ZFSet.mem_sep]
  constructor
  · rintro ⟨_, r', hr, y', hy, j, hj, x, hx, v, hv, equal, rfl, entry⟩
    obtain ⟨rfl, rfl⟩ := ZFSet.pair_inj.1 equal
    exact ⟨hr, hy, j, hj, x, hx, hv, entry⟩
  · rintro ⟨hr, hy, j, hj, x, hx, hv, entry⟩
    exact ⟨ZFSet.pair_mem_prod.2 ⟨hr, hy⟩, r, hr, y, hy, j, hj, x, hx,
      ZFSet.pair (ZFSet.pair r j) x, hv, rfl, rfl, entry⟩

end PartitionPilot.Forcing



end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Geometry_GroundExternalTileSlotSupports
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PartitionPilot.Forcing

section
universe u

noncomputable def externalOwnerHeightGraph (P B V C D old owner depths columns coordinates : ZFSet.{u}) : ZFSet.{u} :=
  old ∪ ZFSet.sep (fun z => ∃ x ∈ B, ∃ v ∈ V, ∃ n ∈ ZFSet.omega, ∃ a ∈ C, ∃ q ∈ D,
    z = ZFSet.pair x (ZFSet.pair a q) ∧ x ∉ P ∧ ZFSet.pair x v ∈ owner ∧
      ZFSet.pair v n ∈ depths ∧ ZFSet.pair n a ∈ columns ∧
      ZFSet.pair (ZFSet.pair v x) q ∈ coordinates) (ZFSet.prod B (ZFSet.prod C D))

end

end PartitionPilot.Forcing

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Definability_LeastSlotOwnerCodes
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PartitionPilot.Forcing
open SetFormula SetRealization
universe u

def LeastSupportCode (V omega depths supports x v : ZFSet.{u}) : Prop :=
  ZFSet.pair v x ∈ supports ∧ ∃ n ∈ omega, ZFSet.pair v n ∈ depths ∧
    ∀ w ∈ V, ∀ m ∈ omega, ZFSet.pair w x ∈ supports → ZFSet.pair w m ∈ depths → m ∉ n

noncomputable def leastSupportGraph (V Q depths supports : ZFSet.{u}) : ZFSet.{u} :=
  ZFSet.sep (fun z => ∃ x ∈ Q, ∃ v ∈ V, z = ZFSet.pair x v ∧
    LeastSupportCode V ZFSet.omega depths supports x v) (ZFSet.prod Q V)

theorem pair_mem_leastSupportGraph (V Q depths supports x v : ZFSet.{u}) :
    ZFSet.pair x v ∈ leastSupportGraph V Q depths supports ↔
      x ∈ Q ∧ v ∈ V ∧ LeastSupportCode V ZFSet.omega depths supports x v := by
  rw [leastSupportGraph, ZFSet.mem_sep]
  constructor
  · rintro ⟨_, x', hx, v', hv, equal, body⟩
    obtain ⟨rfl, rfl⟩ := ZFSet.pair_inj.1 equal
    exact ⟨hx, hv, body⟩
  · rintro ⟨hx, hv, body⟩
    exact ⟨ZFSet.pair_mem_prod.2 ⟨hx, hv⟩, x, hx, v, hv, rfl, body⟩

namespace BoundedFormula
def leastSupportFormula {k} (V omega depths supports x v : Fin k) : BoundedFormula k :=
  .conj (pairMembershipFormula v x supports)
    (exMem omega (.conj (pairMembershipFormula v.succ 0 depths.succ)
      (allMem V.succ (allMem omega.succ.succ
        (.imp (pairMembershipFormula 1 x.succ.succ.succ supports.succ.succ.succ)
          (.imp (pairMembershipFormula 1 0 depths.succ.succ.succ) (.neg (.mem 0 2))))))))

def leastSupportEntryFormula {k} (z V Q omega depths supports : Fin k) : BoundedFormula k :=
  exMem Q (exMem V.succ (.conj (orderedPairFormula z.succ.succ 1 0)
    (leastSupportFormula V.succ.succ omega.succ.succ depths.succ.succ supports.succ.succ 1 0)))

end BoundedFormula

end PartitionPilot.Forcing



namespace PartitionPilot.Forcing
open SetFormula
universe u

def LeastSlotCode (supports v x j : ZFSet.{u}) : Prop :=
  ZFSet.pair (ZFSet.pair v j) x ∈ supports ∧
    ∀ k ∈ j, ZFSet.pair (ZFSet.pair v k) x ∉ supports

end PartitionPilot.Forcing

end

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Geometry_GroundPreparationFamilyImages
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PartitionPilot.Forcing
open SetFormula SetRealization
universe u

theorem pairedGraph_function_of_subset {A B H K f g : ZFSet.{u}}
    (first : ZFSet.IsFunc A H f) (second : ZFSet.IsFunc B K g) (subset : B ⊆ A) :
    ZFSet.IsFunc B (ZFSet.prod H K) (pairedGraph B H K f g) := by
  refine ⟨fun _ hz => (ZFSet.mem_sep.1 hz).1, ?_⟩
  intro x hx
  obtain ⟨a, firstEntry, firstUnique⟩ := first.2 x (subset hx)
  obtain ⟨b, secondEntry, secondUnique⟩ := second.2 x hx
  have ha := (ZFSet.pair_mem_prod.1 (first.1 firstEntry)).2
  have hb := (ZFSet.pair_mem_prod.1 (second.1 secondEntry)).2
  refine ⟨ZFSet.pair a b, (pair_mem_pairedGraph _ _ _ _ _ _ _ _).2
    ⟨hx, ha, hb, firstEntry, secondEntry⟩, ?_⟩
  intro y hy
  obtain ⟨x', _, a', _, b', _, equal, firstEntry', secondEntry'⟩ := (mem_pairedGraph _ _ _ _ _ _).1 hy
  obtain ⟨rfl, rfl⟩ := ZFSet.pair_inj.1 equal
  exact congrArg₂ ZFSet.pair (firstUnique a' firstEntry') (secondUnique b' secondEntry')

end PartitionPilot.Forcing

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Transfinite_GroundTwoStageMainDiagram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PartitionPilot.Forcing

section
universe u

def OldBirthFiberCoverageCode (P e born cutoff : ZFSet.{u}) : Prop :=
  ∀ y t, ZFSet.pair y t ∈ born → (t = cutoff ∨ t ∈ cutoff) →
    ∃ x ∈ P, ZFSet.pair x y ∈ e

end

section
open SetFormula
universe u

def ChronologyGraphPrefixCode (cutoff : ZFSet.{u}) (source target : Fin 5 → ZFSet.{u}) : Prop :=
  ∀ j s, s = cutoff ∨ s ∈ cutoff → ∀ x,
    ZFSet.pair s x ∈ source j ↔ ZFSet.pair s x ∈ target j

structure ChronologicalTransitionLaws (points sourceCutoff targetCutoff sourceBirth targetBirth : ZFSet.{u})
    (sourceGraphs targetGraphs : Fin 5 → ZFSet.{u}) : Prop where
  cutoff_le : sourceCutoff = targetCutoff ∨ sourceCutoff ∈ targetCutoff
  birth : ∀ x y t, ZFSet.pair x y ∈ points →
    (ZFSet.pair y t ∈ targetBirth ↔ ZFSet.pair x t ∈ sourceBirth)
  history_prefix : ChronologyGraphPrefixCode sourceCutoff sourceGraphs targetGraphs

end

namespace GroundChronologicalMainDiagram
open SetFormula
universe u
variable {M : TransitiveGround.{u}} {C D rD : ZFSet.{u}}
variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
variable (unions : Realize M.sets SetFormula.union Fin.elim0)
variable (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)

theorem twoStage_index_cases (i : Fin 2) : i = 0 ∨ i = 1 := by
  obtain ⟨n, bound⟩ := i
  cases n with
  | zero => exact Or.inl rfl
  | succ n =>
    have zero : n = 0 := Nat.eq_zero_of_le_zero (Nat.le_of_lt_succ (Nat.lt_of_succ_lt_succ bound))
    subst n
    exact Or.inr rfl

end GroundChronologicalMainDiagram

end PartitionPilot.Forcing

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Transfinite_ExternalChronologyStageLaws
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace PartitionPilot.Forcing
open SetFormula
universe u

noncomputable def ownerLevelPrefix (P B levels n : ZFSet.{u}) : ZFSet.{u} :=
  P ∪ ZFSet.sep (fun x => x ∉ P ∧ ∃ k ∈ ZFSet.omega,
    ZFSet.pair x k ∈ levels ∧ (k = n ∨ k ∈ n)) B

theorem mem_ownerLevelPrefix (P B levels n x : ZFSet.{u}) :
    x ∈ ownerLevelPrefix P B levels n ↔ x ∈ P ∨
      x ∈ B ∧ x ∉ P ∧ ∃ k ∈ ZFSet.omega, ZFSet.pair x k ∈ levels ∧ (k = n ∨ k ∈ n) := by
  rw [ownerLevelPrefix, ZFSet.mem_union, ZFSet.mem_sep]

theorem ownerLevelPrefix_old (P B levels n : ZFSet.{u}) : P ⊆ ownerLevelPrefix P B levels n :=
  fun _ hx => (mem_ownerLevelPrefix _ _ _ _ _).2 (Or.inl hx)

theorem ownerLevelPrefix_subset {P B : ZFSet.{u}} (subset : P ⊆ B) (levels n : ZFSet.{u}) :
    ownerLevelPrefix P B levels n ⊆ B := by
  intro x hx
  exact ((mem_ownerLevelPrefix _ _ _ _ _).1 hx).elim (fun h => subset h) And.left

theorem mem_ownerLevelPrefix_fresh {P B levels n x : ZFSet.{u}} (fresh : x ∉ P) :
    x ∈ ownerLevelPrefix P B levels n ↔
      x ∈ B ∧ ∃ k ∈ ZFSet.omega, ZFSet.pair x k ∈ levels ∧ (k = n ∨ k ∈ n) := by
  rw [mem_ownerLevelPrefix]
  exact ⟨fun h => h.elim (fun old => False.elim (fresh old)) (fun h => ⟨h.1, h.2.2⟩),
    fun h => Or.inr ⟨h.1, fresh, h.2⟩⟩





noncomputable def ownerLevelPrefixPoints (P B levels : ZFSet.{u}) : ZFSet.{u} :=
  ZFSet.sep (fun z => ∃ n ∈ ZFSet.omega, ∃ x ∈ B,
    z = ZFSet.pair n x ∧ x ∈ ownerLevelPrefix P B levels n) (ZFSet.prod ZFSet.omega B)

theorem pair_mem_ownerLevelPrefixPoints (P B levels n x : ZFSet.{u}) :
    ZFSet.pair n x ∈ ownerLevelPrefixPoints P B levels ↔
      n ∈ ZFSet.omega ∧ x ∈ B ∧ x ∈ ownerLevelPrefix P B levels n := by
  rw [ownerLevelPrefixPoints, ZFSet.mem_sep]
  constructor
  · rintro ⟨_, n', hn, x', hx, equal, member⟩
    obtain ⟨rfl, rfl⟩ := ZFSet.pair_inj.1 equal
    exact ⟨hn, hx, member⟩
  · rintro ⟨hn, hx, member⟩
    exact ⟨ZFSet.pair_mem_prod.2 ⟨hn, hx⟩, n, hn, x, hx, rfl, member⟩

theorem ownerLevelPrefixPoints_fiber {P B levels n : ZFSet.{u}}
    (subset : P ⊆ B) (hn : n ∈ ZFSet.omega) :
    relationFiber B (ownerLevelPrefixPoints P B levels) n = ownerLevelPrefix P B levels n := by
  apply ZFSet.ext
  intro x
  rw [mem_relationFiber, pair_mem_ownerLevelPrefixPoints]
  exact ⟨fun h => h.2.2.2, fun hx =>
    ⟨ownerLevelPrefix_subset subset levels n hx, hn, ownerLevelPrefix_subset subset levels n hx, hx⟩⟩

namespace BoundedFormula

def ownerLevelPrefixFormula {n} (x P B levels cutoff omega : Fin n) : BoundedFormula n :=
  disj (.mem x P) (.conj (.mem x B) (.conj (.neg (.mem x P))
    (exMem omega (.conj (pairMembershipFormula x.succ 0 levels.succ)
      (disj (.equal 0 cutoff.succ) (.mem 0 cutoff.succ))))))

def ownerLevelPrefixPointFormula {n} (z P B levels omega : Fin n) : BoundedFormula n :=
  exMem omega (exMem B.succ (.conj (orderedPairFormula z.succ.succ 1 0)
    (ownerLevelPrefixFormula 0 P.succ.succ B.succ.succ levels.succ.succ 1 omega.succ.succ)))

end BoundedFormula





noncomputable def chronologyRestriction (kind : Fin 3) (P f : ZFSet.{u}) : ZFSet.{u} :=
  Fin.cases (graphRestriction P f) (Fin.cases (heightOrderRestriction P f)
    (fun _ => graphRestriction (ZFSet.prod P P) f)) kind

end PartitionPilot.Forcing



end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Forcing_GroundUnionSizeWitnesses
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PartitionPilot.Forcing
open SetFormula
open scoped ZFSet
universe u

noncomputable def belowWitnessRelation (R K W : ZFSet.{u}) : ZFSet.{u} :=
  ZFSet.sep (fun z => ∃ A ∈ R, ∃ β ∈ K, ∃ f ∈ W,
    z = ZFSet.pair A (ZFSet.pair β f) ∧ InjectionCode A β f) (ZFSet.prod R (ZFSet.prod K W))

theorem pair_mem_belowWitnessRelation (R K W A β f : ZFSet.{u}) :
    ZFSet.pair A (ZFSet.pair β f) ∈ belowWitnessRelation R K W ↔
      A ∈ R ∧ β ∈ K ∧ f ∈ W ∧ InjectionCode A β f := by
  rw [belowWitnessRelation, ZFSet.mem_sep]
  constructor
  · rintro ⟨_, A', hA, β', hβ, f', hf, equal, code⟩
    obtain ⟨hAeq, inner⟩ := ZFSet.pair_inj.1 equal
    obtain ⟨hβeq, hfeq⟩ := ZFSet.pair_inj.1 inner
    subst A'
    subst β'
    subst f'
    exact ⟨hA, hβ, hf, code⟩
  · rintro ⟨hA, hβ, hf, code⟩
    exact ⟨ZFSet.pair_mem_prod.2 ⟨hA, ZFSet.pair_mem_prod.2 ⟨hβ, hf⟩⟩,
      A, hA, β, hβ, f, hf, rfl, code⟩

end PartitionPilot.Forcing

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Geometry_GroundRawLayerPushforward
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PartitionPilot.Forcing
open SetFormula
universe u

noncomputable def layerFiberEmbedding (F B e : ZFSet.{u}) : ZFSet.{u} :=
  ZFSet.sep (fun z => z ∈ ZFSet.prod F B) e

end PartitionPilot.Forcing

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Geometry_GroundTwoPointHeights
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PartitionPilot.Forcing
open SetFormula
universe u

noncomputable def twoPointHeight (a b c d0 d1 : ZFSet.{u}) : ZFSet.{u} :=
  {ZFSet.pair a (ZFSet.pair c d0), ZFSet.pair b (ZFSet.pair c d1)}

theorem twoPointHeight_entry (a b c d0 d1 x y : ZFSet.{u}) :
    ZFSet.pair x y ∈ twoPointHeight a b c d0 d1 ↔
      (x = a ∧ y = ZFSet.pair c d0) ∨ (x = b ∧ y = ZFSet.pair c d1) := by
  simp only [twoPointHeight, ZFSet.mem_pair, ZFSet.pair_inj]

theorem twoPointHeight_function {a b c d0 d1 C D : ZFSet.{u}}
    (different : a ≠ b) (hc : c ∈ C) (h0 : d0 ∈ D) (h1 : d1 ∈ D) :
    ZFSet.IsFunc {a, b} (ZFSet.prod C D) (twoPointHeight a b c d0 d1) := by
  constructor
  · intro z hz
    rcases ZFSet.mem_pair.1 hz with rfl | rfl
    · exact ZFSet.pair_mem_prod.2 ⟨ZFSet.mem_pair.2 (Or.inl rfl), ZFSet.pair_mem_prod.2 ⟨hc, h0⟩⟩
    · exact ZFSet.pair_mem_prod.2 ⟨ZFSet.mem_pair.2 (Or.inr rfl), ZFSet.pair_mem_prod.2 ⟨hc, h1⟩⟩
  · intro x hx
    rcases ZFSet.mem_pair.1 hx with hx | hx
    · subst x
      refine ⟨ZFSet.pair c d0, ZFSet.mem_pair.2 (Or.inl rfl), ?_⟩
      intro y hy
      rcases (twoPointHeight_entry a b c d0 d1 a y).1 hy with ⟨_, equal⟩ | ⟨bad, _⟩
      · exact equal
      · exact False.elim (different bad)
    · subst x
      refine ⟨ZFSet.pair c d1, ZFSet.mem_pair.2 (Or.inr rfl), ?_⟩
      intro y hy
      rcases (twoPointHeight_entry a b c d0 d1 b y).1 hy with ⟨bad, _⟩ | ⟨_, equal⟩
      · exact False.elim (different bad.symm)
      · exact equal

end PartitionPilot.Forcing

end

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Transfinite_CodedMainPrefixSystems
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace PartitionPilot.Forcing
open SetFormula
universe u

namespace CompressionChronologyFields
noncomputable def fieldValue (fields : CompressionChronologyFields.{u}) : Fin 5 → ZFSet.{u} → ZFSet.{u} :=
  Fin.cases fields.space (Fin.cases fields.order (Fin.cases fields.meetGraph
    (Fin.cases fields.birth (fun _ => fields.height))))

end CompressionChronologyFields

end PartitionPilot.Forcing



end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Transfinite_GroundMainPrefixConePreservation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open scoped ZFSet

namespace PartitionPilot.Forcing.GroundMainPrefix
open SetFormula
universe u v
variable {M : TransitiveGround.{u}} {K Labels C D rD : ZFSet.{u}}
variable {pairing : Realize M.sets SetFormula.pairing Fin.elim0}
variable {unions : Realize M.sets SetFormula.union Fin.elim0}
variable {powers : Realize M.sets powerSet Fin.elim0} {separation : SeparationSchema M.sets}
variable {I : Type v} [Small.{u} I] [Preorder I]
instance withTopSmall : Small.{u} (WithTop I) :=
  small_map (Equiv.optionEquivSumPUnit I)

end PartitionPilot.Forcing.GroundMainPrefix

namespace PartitionPilot.Forcing
open SetFormula
universe u v

theorem relationCompose_uniformSource_eq {A B C R f g : ZFSet.{u}}
    (member : f ∈ R) (shape : f ⊆ ZFSet.prod A B) :
    relationCompose (⋃₀ ⋃₀ ⋃₀ R) B C f g = relationCompose A B C f g := by
  apply ZFSet.ext
  intro z
  constructor
  · intro hz
    obtain ⟨x, _, y, hy, w, hw, rfl, xy, yw⟩ := (mem_relationCompose _ _ _ _ _ z).1 hz
    exact (pair_mem_relationCompose _ _ _ _ _ _ _).2
      ⟨(ZFSet.pair_mem_prod.1 (shape xy)).1, hw, y, hy, xy, yw⟩
  · intro hz
    obtain ⟨x, _, y, hy, w, hw, rfl, xy, yw⟩ := (mem_relationCompose _ _ _ _ _ z).1 hz
    exact (pair_mem_relationCompose _ _ _ _ _ _ _).2
      ⟨pair_first_mem_doubleUnion (ZFSet.mem_sUnion.2 ⟨f, member, xy⟩), hw, y, hy, xy, yw⟩

end PartitionPilot.Forcing

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

def ChronologyLayerLookup (T : ZFSet.{u}) (graphs : Fin 5 → ZFSet.{u})
    (layers s t L r μ birth z : ZFSet.{u}) : Prop :=
  s ∈ T ∧ t ∈ T ∧ (t = s ∨ t ∈ s) ∧
    ZFSet.pair s L ∈ graphs 0 ∧ ZFSet.pair s r ∈ graphs 1 ∧
    ZFSet.pair s μ ∈ graphs 2 ∧ ZFSet.pair s birth ∈ graphs 3 ∧
    ZFSet.pair (ZFSet.pair s t) z ∈ layers

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

def chronologyCandidateGraphs {A : Type v} (fields : Fin 10 → A) : Fin 5 → A :=
  Fin.cases (fields 2) (Fin.cases (fields 3) (Fin.cases (fields 4)
    (Fin.cases (fields 5) (fun _ => fields 6))))

def linkedChronologyGraphs {A : Type v} (f : Fin 24 → A) : Fin 5 → A :=
  Fin.cases (f 14) (Fin.cases (f 15) (Fin.cases (f 16) (Fin.cases (f 17) (fun _ => f 18))))

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
universe u v

def mainPrefixLimitTargetFields {A : Type v} (w : Fin 32 → A) : Fin 24 → A :=
  fun j => w (Fin.natAdd 8 j)

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

def orderAntichainFormula {n} (Q order A : Fin n) : BoundedFormula n :=
  .conj (.allMem A (.mem 0 Q.succ))
    (.allMem A (.allMem A.succ (.allMem Q.succ.succ
      (imp (.conj (pairMembershipFormula 0 2 order.succ.succ.succ)
        (pairMembershipFormula 0 1 order.succ.succ.succ)) (.equal 2 1)))))

def relativeMaximalAntichainFormula {n} (Q order D A : Fin n) : BoundedFormula n :=
  .conj (.allMem A (.mem 0 D.succ)) (.conj (orderAntichainFormula Q order A)
    (.allMem D (exMem A.succ (exMem Q.succ.succ
      (.conj (pairMembershipFormula 0 2 order.succ.succ.succ)
        (pairMembershipFormula 0 1 order.succ.succ.succ))))))

end PartitionPilot.Forcing.BoundedFormula

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

namespace PartitionPilot.Forcing
open SetFormula
universe u

noncomputable def visibilitySupportIncidence
    (nodes names visibility top : ZFSet.{u}) : ZFSet.{u} :=
  ZFSet.sep (fun z => ∃ v tau, z = ZFSet.pair v tau ∧
    ∃ V, ZFSet.pair v V ∈ visibility ∧ ZFSet.pair tau top ∈ V)
    (ZFSet.prod nodes names)

end PartitionPilot.Forcing



end

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
universe u

def SynchronizedEnumerationCode (omega N B f e names : ZFSet.{u}) : Prop :=
  ZFSet.IsFunc B N f ∧ ZFSet.IsFunc omega B e ∧ ZFSet.IsFunc omega N names ∧
    (∀ v ∈ B, ∃ n ∈ omega, ZFSet.pair n v ∈ e) ∧
    (∀ n ∈ omega, ∀ v tau, ZFSet.pair n v ∈ e →
      ZFSet.pair n tau ∈ names → ZFSet.pair v tau ∈ f) ∧
    (∀ n ∈ omega, ∀ v tau, ZFSet.pair n v ∈ e →
      ZFSet.pair v tau ∈ f → ZFSet.pair n tau ∈ names)

end PartitionPilot.Forcing



end

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

def imageProfilePositiveFormula {n} (F Q e R x : Fin n) : BoundedFormula n :=
  .exMem Q (.conj (.exMem F.succ (pairMembershipFormula 0 1 e.succ.succ))
    (pairMembershipFormula 0 x.succ R.succ))

end PartitionPilot.Forcing.BoundedFormula

namespace PartitionPilot.Forcing
universe u

def CommonTargetCapMeetCode (I P Q ν e Targets Caps : ZFSet.{u}) : Prop :=
  ∀ i ∈ I, ∀ j ∈ I, ∀ c ∈ P, ∀ K ∈ Q, ∀ L ∈ Q, ∀ c' ∈ Q,
    i ≠ j → ZFSet.pair i c ∈ Targets → ZFSet.pair j c ∈ Targets →
    ZFSet.pair i K ∈ Caps → ZFSet.pair j L ∈ Caps → ZFSet.pair c c' ∈ e →
      ZFSet.pair (ZFSet.pair K L) c' ∈ ν

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

noncomputable def indexedMixedBinaryLift (T UG UP G P A JG JP : ZFSet.{u}) : ZFSet.{u} :=
  ZFSet.sep (fun w => ∃ g ∈ G, ∃ p ∈ P, ∃ q ∈ P, ∃ i ∈ T,
    ∃ a ∈ ZFSet.sUnion (ZFSet.sUnion A),
      ∃ eG ∈ ZFSet.sUnion (ZFSet.sUnion JG), ∃ eP ∈ ZFSet.sUnion (ZFSet.sUnion JP),
      ∃ u ∈ UG, ∃ x ∈ UP, ∃ y ∈ UP,
        w = ZFSet.pair (ZFSet.pair g p) q ∧
          ZFSet.pair i a ∈ A ∧ ZFSet.pair i eG ∈ JG ∧ ZFSet.pair i eP ∈ JP ∧
          ZFSet.pair u g ∈ eG ∧ ZFSet.pair x p ∈ eP ∧ ZFSet.pair y q ∈ eP ∧
          ZFSet.pair (ZFSet.pair u x) y ∈ a) (ZFSet.prod (ZFSet.prod G P) P)

theorem indexedMixedBinaryLift_subset (T UG UP G P A JG JP : ZFSet.{u}) :
    indexedMixedBinaryLift T UG UP G P A JG JP ⊆ ZFSet.prod (ZFSet.prod G P) P :=
  fun _ hz => (ZFSet.mem_sep.1 hz).1

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

noncomputable def indexedRelationLift (T U Q R J : ZFSet.{u}) : ZFSet.{u} :=
  ZFSet.sep (fun z => ∃ p ∈ Q, ∃ q ∈ Q, ∃ i ∈ T,
    ∃ r ∈ ⋃₀ ⋃₀ R, ∃ e ∈ ⋃₀ ⋃₀ J, ∃ x ∈ U, ∃ y ∈ U,
      z = ZFSet.pair p q ∧ ZFSet.pair i r ∈ R ∧ ZFSet.pair i e ∈ J ∧
        ZFSet.pair x p ∈ e ∧ ZFSet.pair y q ∈ e ∧ ZFSet.pair x y ∈ r)
    (ZFSet.prod Q Q)

theorem indexedRelationLift_subset (T U Q R J : ZFSet.{u}) :
    indexedRelationLift T U Q R J ⊆ ZFSet.prod Q Q :=
  fun _ hz => (ZFSet.mem_sep.1 hz).1

noncomputable def indexedBinaryLift (T U Q B J : ZFSet.{u}) : ZFSet.{u} :=
  ZFSet.sep (fun w => ∃ p ∈ Q, ∃ q ∈ Q, ∃ v ∈ Q, ∃ i ∈ T,
    ∃ b ∈ ⋃₀ ⋃₀ B, ∃ e ∈ ⋃₀ ⋃₀ J, ∃ x ∈ U, ∃ y ∈ U, ∃ z ∈ U,
      w = ZFSet.pair (ZFSet.pair p q) v ∧ ZFSet.pair i b ∈ B ∧ ZFSet.pair i e ∈ J ∧
        ZFSet.pair x p ∈ e ∧ ZFSet.pair y q ∈ e ∧ ZFSet.pair z v ∈ e ∧
          ZFSet.pair (ZFSet.pair x y) z ∈ b) (ZFSet.prod (ZFSet.prod Q Q) Q)

theorem indexedBinaryLift_subset (T U Q B J : ZFSet.{u}) :
    indexedBinaryLift T U Q B J ⊆ ZFSet.prod (ZFSet.prod Q Q) Q :=
  fun _ hz => (ZFSet.mem_sep.1 hz).1

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
namespace BoundedFormula
open SetFormula

def indexedRelationLiftEntryFormula : BoundedFormula 8 :=
  exMem 3 (exMem 4 (exMem 3 (exMem 9 (exMem 11 (exMem 7 (exMem 8
    (.conj (orderedPairFormula 7 6 5)
      (.conj (pairMembershipFormula 4 3 11)
        (.conj (pairMembershipFormula 4 2 12)
          (.conj (pairMembershipFormula 1 6 2)
            (.conj (pairMembershipFormula 0 5 2)
              (pairMembershipFormula 1 0 3))))))))))))

end BoundedFormula

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

noncomputable def indexedValueLift (T U Q V F J : ZFSet.{u}) : ZFSet.{u} :=
  ZFSet.sep (fun z => ∃ i ∈ T, ∃ f ∈ ZFSet.sUnion (ZFSet.sUnion F),
    ∃ e ∈ ZFSet.sUnion (ZFSet.sUnion J),
    ∃ x ∈ U, ∃ q ∈ Q, ∃ v ∈ V,
      z = ZFSet.pair q v ∧ ZFSet.pair i f ∈ F ∧ ZFSet.pair i e ∈ J ∧
      ZFSet.pair x q ∈ e ∧ ZFSet.pair x v ∈ f) (ZFSet.prod Q V)

theorem indexedValueLift_subset (T U Q V F J : ZFSet.{u}) :
    indexedValueLift T U Q V F J ⊆ ZFSet.prod Q V := fun _ hz => (ZFSet.mem_sep.1 hz).1

namespace BoundedFormula
open SetFormula

def indexedValueLiftEntryFormula : BoundedFormula 9 :=
  exMem 1 (exMem 8 (exMem 10 (exMem 5 (exMem 7 (exMem 9
    (.conj (orderedPairFormula 6 1 0)
      (.conj (pairMembershipFormula 5 4 11)
        (.conj (pairMembershipFormula 5 3 12)
          (.conj (pairMembershipFormula 2 1 3) (pairMembershipFormula 2 0 4))))))))))

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

noncomputable def directLimitRelation (T U F L : ZFSet.{u}) : ZFSet.{u} :=
  ZFSet.sep (fun z => ∃ i ∈ T, ∃ x ∈ U, ∃ j ∈ T, ∃ y ∈ U,
    ∃ k ∈ T, ∃ w ∈ U, ∃ f ∈ ⋃₀ ⋃₀ F, ∃ g ∈ ⋃₀ ⋃₀ F,
      z = ZFSet.pair (ZFSet.pair i x) (ZFSet.pair j y) ∧
      ZFSet.pair (ZFSet.pair k i) f ∈ F ∧ ZFSet.pair (ZFSet.pair k j) g ∈ F ∧
      ZFSet.pair x w ∈ f ∧ ZFSet.pair y w ∈ g) (ZFSet.prod L L)

theorem directLimitRelation_subset (T U F L : ZFSet.{u}) :
    directLimitRelation T U F L ⊆ ZFSet.prod L L := fun _ hz => (ZFSet.mem_sep.1 hz).1

end PartitionPilot.Forcing

namespace PartitionPilot.Forcing
universe u v

noncomputable def directLimitCarrier (T U A F : ZFSet.{u}) : ZFSet.{u} :=
  equivalenceClasses (indexedCarrierLabels T U A)
    (directLimitRelation T U F (indexedCarrierLabels T U A))

end PartitionPilot.Forcing

namespace PartitionPilot.Forcing
open SetRealization
universe u

theorem indexedCarrierLabels_rank_lt {o : Ordinal.{u}} (limit : Order.IsSuccLimit o)
    {T U : ZFSet.{u}} (A : ZFSet.{u})
    (indices : ZFSet.rank T < o) (points : ZFSet.rank U < o) :
    ZFSet.rank (indexedCarrierLabels T U A) < o :=
  (ZFSet.rank_mono (indexedCarrierLabels_subset T U A)).trans_lt
    (rank_product_lt limit indices points)

theorem equivalenceClasses_rank_lt {o : Ordinal.{u}} (limit : Order.IsSuccLimit o)
    {L : ZFSet.{u}} (E : ZFSet.{u}) (labels : ZFSet.rank L < o) :
    ZFSet.rank (equivalenceClasses L E) < o := by
  have bound := ZFSet.rank_mono
    (show equivalenceClasses L E ⊆ ZFSet.powerset L from fun _ hz => (ZFSet.mem_sep.1 hz).1)
  rw [ZFSet.rank_powerset] at bound
  exact bound.trans_lt (limit.succ_lt labels)

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
open SetFormula
universe u

namespace BoundedFormula

def identityInsertionGraphEntryFormula {n} (z Labels I C base E F : Fin n) : BoundedFormula n :=
  .exMem Labels (.exMem I.succ (.conj (orderedPairFormula z.succ.succ 1 0)
    (literalTaskFormula 0 C.succ.succ C.succ.succ base.succ.succ E.succ.succ F.succ.succ 1)))

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

def StrictSuccessorTopCode (P Q R e top : ZFSet.{u}) : Prop :=
  ∀ x ∈ P, ∀ y ∈ Q, ZFSet.pair x y ∈ e →
    ZFSet.pair y top ∈ R ∧ ZFSet.pair top y ∉ R

namespace BoundedFormula

def strictSuccessorTopFormula {n} (P Q R e top : Fin n) : BoundedFormula n :=
  .allMem P (.allMem Q.succ (imp (pairMembershipFormula 1 0 e.succ.succ)
    (.conj (pairMembershipFormula 0 top.succ.succ R.succ.succ)
      (.neg (pairMembershipFormula top.succ.succ 0 R.succ.succ)))))

end BoundedFormula





end PartitionPilot.Forcing



namespace PartitionPilot.Forcing
open SetFormula
universe u v w

def linkedSuccessorOutputFields {A : Type v} (s t : Fin 24 → A)
    (points actors : A) (extra : Fin 8 → A) : Fin 30 → A :=
  Fin.cases (s 0) (Fin.cases (t 0) (Fin.cases (s 1) (Fin.cases (t 1) (Fin.cases (s 2) (Fin.cases (t 2) (Fin.cases (s 3) (Fin.cases (t 3) (Fin.cases (s 4) (Fin.cases (t 4) (Fin.cases (s 6) (Fin.cases (t 6) (Fin.cases (s 7) (Fin.cases (t 7) (Fin.cases (s 8) (Fin.cases (t 8) (Fin.cases (s 10) (Fin.cases (t 10) (Fin.cases (points) (Fin.cases (actors) (Fin.cases (s 9) (Fin.cases (extra 0) (Fin.cases (extra 1) (Fin.cases (extra 2) (Fin.cases (extra 3) (Fin.cases (extra 4) (Fin.cases (extra 5) (Fin.cases (extra 6) (Fin.cases (extra 7) ((fun _ => t 9))))))))))))))))))))))))))))))

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

namespace TransitiveGround
variable (M : TransitiveGround.{u})

def taskBearingSuccessorParams (S V K Labels C D rD : ZFSet.{u}) : Fin 8 → ZFSet.{u} :=
  extend K (extend Labels (extend C (extend D (extend rD (extend ZFSet.omega
    (extend S (extend V Fin.elim0)))))))

end TransitiveGround
end PartitionPilot.Forcing




end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Transfinite_GroundMainPrefixPreservedSeeds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace PartitionPilot.Forcing.GroundMainPrefix
open SetFormula SetRealization
universe u v
variable {M : TransitiveGround.{u}} {K Labels C D rD : ZFSet.{u}}
variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
variable (unions : Realize M.sets SetFormula.union Fin.elim0)
variable (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
variable {I : Type v} [Small.{u} I] [Preorder I] [Finite I]

local instance instFiniteMainTransitionIndex : Finite (MainTransitionIndex I) := by
  classical
  let := Fintype.ofFinite I
  infer_instance

end PartitionPilot.Forcing.GroundMainPrefix



end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Transfinite_GroundMainPrefixLimitCoverageConstruction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PartitionPilot.Forcing

section
open SetFormula
universe u v

theorem relationCompose_enlargeCodomain {A B C D f g : ZFSet.{u}}
    (bound : g ⊆ ZFSet.prod B C) (subset : C ⊆ D) :
    relationCompose A B D f g = relationCompose A B C f g := by
  apply ZFSet.ext
  intro z
  constructor
  · intro entry
    obtain ⟨x, hx, y, hy, w, _, rfl, first, second⟩ :=
      (mem_relationCompose _ _ _ _ _ z).1 entry
    exact (mem_relationCompose _ _ _ _ _ _).2
      ⟨x, hx, y, hy, w, (ZFSet.pair_mem_prod.1 (bound second)).2, rfl, first, second⟩
  · intro entry
    obtain ⟨x, hx, y, hy, w, hw, rfl, first, second⟩ :=
      (mem_relationCompose _ _ _ _ _ z).1 entry
    exact (mem_relationCompose _ _ _ _ _ _).2
      ⟨x, hx, y, hy, w, subset hw, rfl, first, second⟩

end

end PartitionPilot.Forcing

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Forcing_GroundMainConditionalTotality
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

def mainPrefixConditionalParams (K Labels C D rD N f : ZFSet.{u}) : Fin 7 → ZFSet.{u} :=
  extend K (extend Labels (extend C (extend D (extend rD (extend N (extend f Fin.elim0))))))

end TransitiveGround
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

def mainPrefixTraceParams (B seed g : ZFSet.{u}) : Fin 3 → ZFSet.{u} :=
  Fin.cases B (Fin.cases seed (fun _ => g))

end

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

noncomputable def tupleRelationBound : (k : Nat) → (Fin (k + 1) → ZFSet.{u}) → ZFSet.{u}
  | 0, f => ⋃₀ ⋃₀ f 0
  | k + 1, f => ZFSet.prod (⋃₀ ⋃₀ f 0) (tupleRelationBound k (fun j => f j.succ))

noncomputable def tupleRelationProduct : (k : Nat) → (Fin (k + 1) → ZFSet.{u}) → ZFSet.{u}
  | 0, f => f 0
  | k + 1, f => relationProduct (⋃₀ ⋃₀ f 0) (tupleRelationBound k (fun j => f j.succ))
      (⋃₀ ⋃₀ f 0) (tupleRelationBound k (fun j => f j.succ)) (f 0)
      (tupleRelationProduct k (fun j => f j.succ))

end PartitionPilot.Forcing

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

noncomputable def rowAssignmentOrder (Q C B r : ZFSet.{u}) : ZFSet.{u} :=
  ZFSet.sep (fun z => ∃ q ∈ C, ∃ A ∈ B, ∃ p ∈ C, ∃ D ∈ B,
    z = ZFSet.pair (ZFSet.pair q A) (ZFSet.pair p D) ∧ ZFSet.pair q p ∈ r ∧ D ⊆ A)
    (ZFSet.prod Q Q)

theorem mem_rowAssignmentOrder (Q C B r z : ZFSet.{u}) :
    z ∈ rowAssignmentOrder Q C B r ↔ z ∈ ZFSet.prod Q Q ∧
      ∃ q ∈ C, ∃ A ∈ B, ∃ p ∈ C, ∃ D ∈ B,
        z = ZFSet.pair (ZFSet.pair q A) (ZFSet.pair p D) ∧ ZFSet.pair q p ∈ r ∧ D ⊆ A :=
  ZFSet.mem_sep

theorem pair_mem_rowAssignmentOrder (Q C B r q A p D : ZFSet.{u}) :
    ZFSet.pair (ZFSet.pair q A) (ZFSet.pair p D) ∈ rowAssignmentOrder Q C B r ↔
      ZFSet.pair q A ∈ Q ∧ ZFSet.pair p D ∈ Q ∧
        q ∈ C ∧ A ∈ B ∧ p ∈ C ∧ D ∈ B ∧ ZFSet.pair q p ∈ r ∧ D ⊆ A := by
  rw [mem_rowAssignmentOrder, ZFSet.pair_mem_prod]
  constructor
  · rintro ⟨⟨hqQ,hpQ⟩,q',hq,A',hA,p',hp,D',hD,equal,rows,subset⟩
    obtain ⟨left,right⟩ := ZFSet.pair_injective equal
    obtain ⟨rfl,rfl⟩ := ZFSet.pair_injective left
    obtain ⟨rfl,rfl⟩ := ZFSet.pair_injective right
    exact ⟨hqQ,hpQ,hq,hA,hp,hD,rows,subset⟩
  · rintro ⟨hqQ,hpQ,hq,hA,hp,hD,rows,subset⟩
    exact ⟨⟨hqQ,hpQ⟩,q,hq,A,hA,p,hp,D,hD,rfl,rows,subset⟩

end PartitionPilot.Forcing

end

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

structure RelationActionLaws (G : Type u) [Group G] (X : ZFSet.{u})
    (graph : G → ZFSet.{u}) : Prop where
  function : ∀ g, ZFSet.IsFunc X X (graph g)
  injection : ∀ g, InjectionCode X X (graph g)
  one : ∀ x ∈ X, ∀ y, ZFSet.pair x y ∈ graph 1 ↔ y = x
  mul : ∀ g h, ∀ x ∈ X, ∀ z, ZFSet.pair x z ∈ graph (g * h) ↔
    ∃ y ∈ X, ZFSet.pair x y ∈ graph h ∧ ZFSet.pair y z ∈ graph g

end PartitionPilot.Forcing



namespace PartitionPilot.Forcing.RelationActionLaws
universe u v
variable {G : Type u} [Group G] {ι : Type v}

theorem of_disjoint_family (X : ι → ZFSet.{u}) (branch : ι → G → ZFSet.{u})
    (Y : ZFSet.{u}) (whole : G → ZFSet.{u})
    (cover : ∀ x, x ∈ Y ↔ ∃ i, x ∈ X i)
    (entries : ∀ g z, z ∈ whole g ↔ ∃ i, z ∈ branch i g)
    (apart : ∀ i j x, x ∈ X i → x ∈ X j → i = j)
    (laws : ∀ i, RelationActionLaws G (X i) (branch i)) :
    RelationActionLaws G Y whole := by
  have bounds (g : G) : whole g ⊆ ZFSet.prod Y Y := by
    intro z hz
    obtain ⟨i, hi⟩ := (entries g z).1 hz
    obtain ⟨x, hx, y, hy, rfl⟩ := ZFSet.mem_prod.1 (((laws i).function g).1 hi)
    exact ZFSet.pair_mem_prod.2 ⟨(cover x).2 ⟨i, hx⟩, (cover y).2 ⟨i, hy⟩⟩
  have functions (g : G) : ZFSet.IsFunc Y Y (whole g) := by
    refine ⟨bounds g, ?_⟩
    intro x hx
    obtain ⟨i, hi⟩ := (cover x).1 hx
    obtain ⟨y, edge, unique⟩ := ((laws i).function g).2 x hi
    refine ⟨y, (entries g _).2 ⟨i, edge⟩, ?_⟩
    intro z hz
    obtain ⟨j, other⟩ := (entries g _).1 hz
    have same := apart i j x hi (ZFSet.pair_mem_prod.1 (((laws j).function g).1 other)).1
    subst j
    exact unique z other
  refine ⟨functions, ?_, ?_, ?_⟩
  · intro g
    refine ⟨functions g, ?_⟩
    intro x y z hx hy
    obtain ⟨i, ei⟩ := (entries g _).1 hx
    obtain ⟨j, ej⟩ := (entries g _).1 hy
    have same := apart i j z (ZFSet.pair_mem_prod.1 (((laws i).function g).1 ei)).2
      (ZFSet.pair_mem_prod.1 (((laws j).function g).1 ej)).2
    subst j
    exact ((laws i).injection g).injective x y z ei ej
  · intro x hx y
    constructor
    · intro edge
      obtain ⟨i, hi⟩ := (entries 1 _).1 edge
      exact ((laws i).one x (ZFSet.pair_mem_prod.1 (((laws i).function 1).1 hi)).1 y).1 hi
    · intro equal
      obtain ⟨i, hi⟩ := (cover x).1 hx
      exact (entries 1 _).2 ⟨i, ((laws i).one x hi y).2 equal⟩
  · intro g h x _ z
    constructor
    · intro edge
      obtain ⟨i, hi⟩ := (entries (g * h) _).1 edge
      have source := (ZFSet.pair_mem_prod.1 (((laws i).function (g * h)).1 hi)).1
      obtain ⟨y, hy, eh, eg⟩ := ((laws i).mul g h x source z).1 hi
      exact ⟨y, (cover y).2 ⟨i, hy⟩, (entries h _).2 ⟨i, eh⟩, (entries g _).2 ⟨i, eg⟩⟩
    · rintro ⟨y, _, eh, eg⟩
      obtain ⟨i, ei⟩ := (entries h _).1 eh
      obtain ⟨j, ej⟩ := (entries g _).1 eg
      have fields := ZFSet.pair_mem_prod.1 (((laws i).function h).1 ei)
      have same := apart i j y fields.2 (ZFSet.pair_mem_prod.1 (((laws j).function g).1 ej)).1
      subst j
      exact (entries (g * h) _).2 ⟨i, ((laws i).mul g h x fields.1 z).2 ⟨y, fields.2, ei, ej⟩⟩

end PartitionPilot.Forcing.RelationActionLaws

end

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

def transitionShape {n} (p y upperOrder cutGraph : Fin n) : BoundedFormula (n + 8) :=
  let old := suffixIndex n 8
  let v := prefixIndex n 8
  .conj (BoundedFormula.orderedPairFormula (old p) (v 0) (v 1))
    (.conj (BoundedFormula.orderedPairFormula (old y) (v 2) (v 5))
      (.conj (BoundedFormula.orderedPairFormula (v 5) (v 3) (v 4))
        (.conj (BoundedFormula.pairMembershipFormula (v 2) (old p) (old upperOrder))
          (BoundedFormula.pairMembershipFormula (v 2) (v 6) (old cutGraph)))))

end PartitionPilot.Forcing.TransitiveGround




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

def FairPreparationStateCode (omega E0 enumSelector state : ZFSet.{u}) : Prop :=
  ∃ n p births last, state = ZFSet.pair n (ZFSet.pair p (ZFSet.pair births last)) ∧
    n ∈ omega ∧ insert n n ∈ omega ∧ ZFSet.IsFunc (insert n n) E0 births ∧
    ∃ e ∈ E0, ZFSet.pair p e ∈ enumSelector ∧ ZFSet.pair n e ∈ births






def FairPreparationStepCode
    (omega E0 stages U enumSelector prepSelector gridGraph state next : ZFSet.{u}) : Prop :=
  ∃ n p births last m q nextBirths event,
    state = ZFSet.pair n (ZFSet.pair p (ZFSet.pair births last)) ∧
    next = ZFSet.pair m (ZFSet.pair q (ZFSet.pair nextBirths event)) ∧
    m = insert n n ∧
    ∃ i ∈ omega, ∃ j ∈ omega, ∃ e ∈ E0, ∃ newE ∈ E0,
      ZFSet.pair n (ZFSet.pair i j) ∈ gridGraph ∧
      ZFSet.pair i e ∈ births ∧ ZFSet.pair q newE ∈ enumSelector ∧
      nextBirths = insert (ZFSet.pair m newE) births ∧
      ((e = ∅ ∧ q = p ∧ event = ∅) ∨
        (∃ alpha ∈ stages, ∃ y ∈ U, (∃ payload, y = ZFSet.pair q payload) ∧
          ZFSet.pair j alpha ∈ e ∧ ZFSet.pair (ZFSet.pair alpha p) y ∈ prepSelector ∧
          event = ZFSet.pair alpha y))

end PartitionPilot.Forcing




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

theorem rowAssignmentOrder_top {Q C B r top : ZFSet.{u}}
    (shape : Q ⊆ ZFSet.prod C B)
    (rowTop : ∀ q ∈ C, ZFSet.pair q top ∈ r)
    (member : ZFSet.pair top ∅ ∈ Q) :
    ∀ z ∈ Q, ZFSet.pair z (ZFSet.pair top ∅) ∈ rowAssignmentOrder Q C B r := by
  have topShape := ZFSet.pair_mem_prod.1 (shape member)
  intro z hz
  obtain ⟨q, hq, A, hA, rfl⟩ := ZFSet.mem_prod.1 (shape hz)
  exact (pair_mem_rowAssignmentOrder Q C B r q A top ∅).2
    ⟨hz, member, hq, hA, topShape.1, topShape.2, rowTop q hq,
      fun x impossible => False.elim (ZFSet.notMem_empty x impossible)⟩

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

noncomputable def rawRowAssignmentOrder (Q rowOrder : ZFSet.{u}) : ZFSet.{u} :=
  rowAssignmentOrder Q Q.sUnion.sUnion Q.sUnion.sUnion rowOrder

end PartitionPilot.Forcing



end

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Geometry_GroundAbsentLiftRangeCollisions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section


namespace PartitionPilot.Forcing.SetFormula

def refinementVisibleLiftFormula : SetFormula 4 :=
  ex (.conj (.mem 0 1) (.conj (.mem 0 2)
    (BoundedFormula.pairMembershipFormula 0 3 4).toFormula))

end PartitionPilot.Forcing.SetFormula

end



end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Forcing_GroundRecursiveRowNameActions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PartitionPilot.Forcing
universe u

theorem assignmentCut_empty_data (levels alpha : ZFSet.{u}) : assignmentCut levels alpha ∅ = ∅ :=
  assignmentCut_eq_of_lower (fun z member => False.elim (ZFSet.notMem_empty z member))

end PartitionPilot.Forcing

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Geometry_GroundRefinementAssignmentLabelEntries
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

def labelEntryFormula : SetFormula 7 :=
  exBlock 10 (.conj (.mem 0 11) (.conj (.mem 1 11) (.conj (.mem 2 14)
    (.conj (orderedPairFormula 2 3 4)
    (.conj (orderedPairFormula 8 0 1)
    (.conj (orderedPairFormula 9 15 8) (.conj (.mem 9 4)
    (.conj (pairMembershipFormula 0 5 12)
    (.conj (pairMembershipFormula 1 6 13)
    (.conj (orderedPairNameCodeFormula 7 5 6 16)
      (orderedPairFormula 10 7 2)))))))))))

end PartitionPilot.Forcing

end

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

noncomputable def certificateUsedSupports (nodes k : ZFSet.{u}) : ZFSet.{u} :=
  ZFSet.sep (fun v => ∃ z F B f,
    ZFSet.pair z (ZFSet.pair F (ZFSet.pair B f)) ∈ k ∧ v ∈ B) nodes

noncomputable def preparationEventUsedSupports (nodes event : ZFSet.{u}) : ZFSet.{u} :=
  ZFSet.sep (fun v => ∃ alpha r k enumerations,
    event = ZFSet.pair alpha (ZFSet.pair r (ZFSet.pair k enumerations)) ∧
      ∃ z F B f, ZFSet.pair z (ZFSet.pair F (ZFSet.pair B f)) ∈ k ∧ v ∈ B) nodes

end PartitionPilot.Forcing



end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Geometry_GroundRetainedPreparationSelections
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI



namespace PartitionPilot.Forcing.TransitiveGround
open SetFormula
universe u
variable (M : TransitiveGround.{u})

def selectionBody {n} (z A R p levels : Fin n) : BoundedFormula (n + 10) :=
  let old := suffixIndex n 10
  let v := prefixIndex n 10
  .conj (BoundedFormula.orderedPairFormula (old z) (v 0) (v 1))
    (.conj (BoundedFormula.orderedPairFormula (v 1) (v 2) (v 9))
      (.conj (BoundedFormula.orderedPairFormula (v 9) (v 3) (v 6))
        (.conj (BoundedFormula.orderedPairFormula (v 3) (v 4) (v 5))
          (.conj (BoundedFormula.orderedPairFormula (v 7) (v 2) (v 3))
            (.conj (BoundedFormula.orderedPairFormula (v 8) (old p) (v 6))
              (.conj (BoundedFormula.pairMembershipFormula (v 7) (v 8) (old R))
                (.conj (.allMem (v 5) (.mem 0 (old A).succ))
                  (.conj (.mem (v 0) (v 5))
                    (BoundedFormula.pairMembershipFormula (v 0) (v 2) (old levels))))))))))

def selectionFormula {n} (z A R p levels : Fin n) : SetFormula n :=
  exBlock 10 (selectionBody z A R p levels).toFormula

end PartitionPilot.Forcing.TransitiveGround

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

def localizedWitnessFormula : BoundedFormula 5 :=
  .disj (.mem 0 1) (.neg (exMem 2
    (.conj (pairMembershipFormula 0 1 4) (pairMembershipFormula 0 5 4))))

end PartitionPilot.Forcing.BoundedFormula

end


end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Transfinite_GroundOrdinalImagePartitions
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

noncomputable def ordinalFirstRelation (delta Y R : ZFSet.{u}) : ZFSet.{u} :=
  ZFSet.sep (fun z => ∃ i ∈ delta, ∃ y ∈ Y,
    z = ZFSet.pair i y ∧ ∀ k ∈ i, ZFSet.pair k y ∉ R) R

namespace BoundedFormula
def firstRelationEntryFormula {n} (z delta Y R : Fin n) : BoundedFormula n :=
  exMem delta (exMem Y.succ (.conj (orderedPairFormula z.succ.succ 1 0)
    (.allMem 1 (.neg (pairMembershipFormula 0 1 R.succ.succ.succ)))))

end BoundedFormula

end PartitionPilot.Forcing

end

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Geometry_GroundPartialCoverPartitions
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

noncomputable def partialCoverOccurrence (delta T X h : ZFSet.{u}) : ZFSet.{u} :=
  ZFSet.sep (fun z => ∃ i ∈ delta, ∃ x ∈ X, ∃ hi ∈ ⋃₀ ⋃₀ h,
    z = ZFSet.pair i x ∧ ZFSet.pair i hi ∈ h ∧ ∃ u ∈ T, ZFSet.pair u x ∈ hi)
    (ZFSet.prod delta X)

namespace BoundedFormula
def partialCoverOccurrenceFormula {n} (z delta T X H h : Fin n) : BoundedFormula n :=
  exMem delta (exMem X.succ (exMem H.succ.succ
    (.conj (orderedPairFormula z.succ.succ.succ 2 1)
      (.conj (pairMembershipFormula 2 0 h.succ.succ.succ)
        (exMem T.succ.succ.succ (pairMembershipFormula 0 2 1))))))

end BoundedFormula

end PartitionPilot.Forcing

end

end OAI
end


