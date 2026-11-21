-- Prove2me | Definitions.Def_OAIQ430Hc000
-- name    : OAIQ430Hc000
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-20T23:03:33.037774+00:00
-- url     : https://prove2.me/theorems/81cc338a-bf9c-4f90-83ab-3a8c7f2f6f5d
-- title:
--   Definitions bundle OAIQ430Hc000 of the split of OpenAI, A counterexample to Hadwiger's conjecture
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.HadwigerCounterexample.exists_graphs` and `OAI.HadwigerMatching.full_matching_minor_proposition`, carved from OpenAI's openai/math development (OpenAI, *A counterexample to Hadwiger's conjecture*, OpenAI Math Release, September 23, 2026, result family 157, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 1410 declarations of OpenAI's Lean: 1153 definitions, 69 inductive types or structures, 55 instances and 133 theorems. The definitions and types are `OAI.HadwigerCounterexample.AIdx`, `OAI.HadwigerCounterexample.Ambient`, `OAI.HadwigerCounterexample.Among`, `OAI.HadwigerCounterexample.AnalyticParameters`, `OAI.HadwigerCounterexample.Aside`, `OAI.HadwigerCounterexample.Atlas`, `OAI.HadwigerCounterexample.AtomKey`, `OAI.HadwigerCounterexample.Augur`, `OAI.HadwigerCounterexample.Avenue`, `OAI.HadwigerCounterexample.B1`, `OAI.HadwigerCounterexample.BMark`, `OAI.HadwigerCounterexample.Bag`, `OAI.HadwigerCounterexample.Base`, `OAI.HadwigerCounterexample.BaseIdx`, `OAI.HadwigerCounterexample.BaseMat`, `OAI.HadwigerCounterexample.Batch`, `OAI.HadwigerCounterexample.Bazaar`, `OAI.HadwigerCounterexample.Bazaar.Catalog`, `OAI.HadwigerCounterexample.Bazaar.Sales`, `OAI.HadwigerCounterexample.Bazaar.atList`, `OAI.HadwigerCounterexample.Bazaar.bids`, `OAI.HadwigerCounterexample.Bazaar.chart`, `OAI.HadwigerCounterexample.Bazaar.discard`, `OAI.HadwigerCounterexample.Bazaar.frequent`, `OAI.HadwigerCounterexample.Bazaar.opened`, `OAI.HadwigerCounterexample.Bazaar.pay`, `OAI.HadwigerCounterexample.Bazaar.probed`, `OAI.HadwigerCounterexample.Block`, `OAI.HadwigerCounterexample.Block.O`, `OAI.HadwigerCounterexample.Block.S`, `OAI.HadwigerCounterexample.Block.Z`, `OAI.HadwigerCounterexample.Block.sharp`, `OAI.HadwigerCounterexample.Bstep`, `OAI.HadwigerCounterexample.CTile`, `OAI.HadwigerCounterexample.Canopy`, `OAI.HadwigerCounterexample.Chan`, `OAI.HadwigerCounterexample.ChanOut`, `OAI.HadwigerCounterexample.CheckGram`, `OAI.HadwigerCounterexample.CheckOne`, `OAI.HadwigerCounterexample.Comp` and 1182 more.
--
--   **Sources.** They come from these modules of lean/OAI/Combinatorics, in whole or in part: `HadwigerCounterexample_AdaptiveRecordBounds`, `HadwigerCounterexample_AdditionalProbeBounds`, `HadwigerCounterexample_AffineFrames`, `HadwigerCounterexample_AggregateCostBounds`, `HadwigerCounterexample_AmbientBatchSlots`, `HadwigerCounterexample_AnalyticParameters`, `HadwigerCounterexample_AtomFlavors`, `HadwigerCounterexample_AttackCutDecomposition`, `HadwigerCounterexample_BaselineExtension`, `HadwigerCounterexample_BaselineForms`, `HadwigerCounterexample_BasisConditioning`, `HadwigerCounterexample_BatchCharacters`, `HadwigerCounterexample_BilinearBlockCorrelation`, `HadwigerCounterexample_BilinearCompression`, `HadwigerCounterexample_BinaryEvaluationForms`, `HadwigerCounterexample_BinaryMatrices`, `HadwigerCounterexample_BinaryMixingBounds`, `HadwigerCounterexample_BinaryPrescriptions`, `HadwigerCounterexample_BinaryStatusComparison`, `HadwigerCounterexample_BooleanLabels`, `HadwigerCounterexample_BoundedQueryTemplates`, `HadwigerCounterexample_CellPositivityScales`, `HadwigerCounterexample_CellPruning`, `HadwigerCounterexample_ChannelFrameLaws`, `HadwigerCounterexample_CollisionInequality`, `HadwigerCounterexample_CommonPartitionRefinement`, `HadwigerCounterexample_CommonPredictions`, `HadwigerCounterexample_CompatibleOptionRealization`, `HadwigerCounterexample_CompatibleTableEvents`, `HadwigerCounterexample_ComponentIndices`, `HadwigerCounterexample_ConcentrationScales`, `HadwigerCounterexample_ConditionalCellEntropy`, `HadwigerCounterexample_ConditionalFlags`, `HadwigerCounterexample_ConditionalLargeSetHits`, `HadwigerCounterexample_ConditionalProductLaws`, `HadwigerCounterexample_ConditionalProjection`, `HadwigerCounterexample_ConditionalSignaturePositivity`, `HadwigerCounterexample_ConditionedBatchLaws`, `HadwigerCounterexample_ConditionedCorrelations`, `HadwigerCounterexample_CoordinateBlocks`, `HadwigerCounterexample_CoordinateDuality`, `HadwigerCounterexample_CoordinateEmbeddings`, `HadwigerCounterexample_CoverSpaces`, `HadwigerCounterexample_CrossForms`, `HadwigerCounterexample_CrossPatternCorrelation`, `HadwigerCounterexample_CrossPatternCounting`, `HadwigerCounterexample_CutIntegralBounds`, `HadwigerCounterexample_DependentPairConcentration`, `HadwigerCounterexample_DerivativeCompression`, `HadwigerCounterexample_EmpiricalInformation`, `HadwigerCounterexample_EndpointEvaluations`, `HadwigerCounterexample_EndpointGramRanks`, `HadwigerCounterexample_EndpointTemplateConcentration`, `HadwigerCounterexample_ExplicitStatusEquations`, `HadwigerCounterexample_ExponentialGraphTransfer`, `HadwigerCounterexample_ExponentialRates`, `HadwigerCounterexample_FinalContradiction`, `HadwigerCounterexample_FiniteComparisonBounds`, `HadwigerCounterexample_FiniteConditioning`, `HadwigerCounterexample_FiniteDualSystems`, `HadwigerCounterexample_FiniteEntropy`, `HadwigerCounterexample_FiniteGraphTransfer`, `HadwigerCounterexample_FiniteLaws`, `HadwigerCounterexample_FiniteOptionLabels`, `HadwigerCounterexample_FinitePhaseAlternative`, `HadwigerCounterexample_FinitePredictions`, `HadwigerCounterexample_FiniteProjectionCenters`, `HadwigerCounterexample_FiniteTableEnumeration`, `HadwigerCounterexample_FixedPositionTests`, `HadwigerCounterexample_FlatRankLevels`, `HadwigerCounterexample_ForbiddenPredictions`, `HadwigerCounterexample_FourCornerMasks`, `HadwigerCounterexample_FourCornerTrials`, `HadwigerCounterexample_FourCornerViews`, `HadwigerCounterexample_FourEdgeFamilies`, `HadwigerCounterexample_FourPhaseBits`, `HadwigerCounterexample_FrameIntersectionBounds`, `HadwigerCounterexample_FrameIntersectionCosts`, `HadwigerCounterexample_FrameOrbitLaws`, `HadwigerCounterexample_FrameRotations`, `HadwigerCounterexample_FreeBlockFourier`, `HadwigerCounterexample_FreeBlockLinearAction`, `HadwigerCounterexample_FreshGeneratorCorrection`, `HadwigerCounterexample_FrozenProjections`, `HadwigerCounterexample_GradientRankBounds`, `HadwigerCounterexample_GradientRealization`, `HadwigerCounterexample_GramArrayConcentration`, `HadwigerCounterexample_GramCharacterExpansion`, `HadwigerCounterexample_GramCharacterQuotients`, `HadwigerCounterexample_GramConditionedLaws`, `HadwigerCounterexample_GramProbabilities`, `HadwigerCounterexample_GreedyExposures`, `HadwigerCounterexample_GroupedQueryIndependence`, `HadwigerCounterexample_HistogramBounds`, `HadwigerCounterexample_HistogramEnergyScales`, `HadwigerCounterexample_ImageCharacterBounds`, `HadwigerCounterexample_ImagePartitions`, `HadwigerCounterexample_IncompatibleMassBounds`, `HadwigerCounterexample_IndependentColumnBatches`, `HadwigerCounterexample_IndependentPhaseBounds`, `HadwigerCounterexample_IndependentWeightCorrelation`, `HadwigerCounterexample_InformationSmallSetBounds`, `HadwigerCounterexample_InitialPartitionExistence`, `HadwigerCounterexample_InjectionWitnesses`, `HadwigerCounterexample_KeyDirections`, `HadwigerCounterexample_KeyProjectionBounds`, `HadwigerCounterexample_KeyReferenceLaws`, `HadwigerCounterexample_KeyTestCorrespondence`, `HadwigerCounterexample_LabeledGenerators`, `HadwigerCounterexample_LargeSetHits`, `HadwigerCounterexample_LeafMixtures`, `HadwigerCounterexample_LeafSurrogateExperiments`, `HadwigerCounterexample_LinearExtension`, `HadwigerCounterexample_LinearResponse`, `HadwigerCounterexample_LowRankKernelAlternative`, `HadwigerCounterexample_Main`, `HadwigerCounterexample_MatrixQuotients`, `HadwigerCounterexample_MatrixRankCounting`, `HadwigerCounterexample_MatrixRanks`, `HadwigerCounterexample_MixedImageBounds`, `HadwigerCounterexample_MixerConditions`, `HadwigerCounterexample_MixerProductVariables`, `HadwigerCounterexample_MomentCoordinates`, `HadwigerCounterexample_MomentLabelSupport`, `HadwigerCounterexample_NominalPointArrays`, `HadwigerCounterexample_NominalSpaces`, `HadwigerCounterexample_NumericalGradientTests`, `HadwigerCounterexample_NumericalGramPrescriptions`, `HadwigerCounterexample_OffsetEnergy`, `HadwigerCounterexample_OffsetFourierBounds`, `HadwigerCounterexample_OffsetLifting`, `HadwigerCounterexample_OffsetRecords`, `HadwigerCounterexample_OppositeEndpointForms`, `HadwigerCounterexample_OppositePredictions`, `HadwigerCounterexample_OrientationRankBounds`, `HadwigerCounterexample_OrthogonalSpectrumBounds`, `HadwigerCounterexample_PairIndexedTests`, `HadwigerCounterexample_PairedCollisionBounds`, `HadwigerCounterexample_PairedMassIdentities`, `HadwigerCounterexample_PairedOptions`, `HadwigerCounterexample_PairedTemplateConcentration`, `HadwigerCounterexample_ParameterExistence`, `HadwigerCounterexample_PartitionSelection`, `HadwigerCounterexample_PhaseAlternativeSupport`, `HadwigerCounterexample_PhaseClassCompatibility`, `HadwigerCounterexample_PhaseMomentBounds`, `HadwigerCounterexample_PhaseParameters`, `HadwigerCounterexample_PhasePreparedOutcomes`, `HadwigerCounterexample_PinInjectionTests`, `HadwigerCounterexample_PolarRankBounds`, `HadwigerCounterexample_PolynomialCompatibility`, `HadwigerCounterexample_PolynomialRankBounds`, `HadwigerCounterexample_PolynomialZeroTests`, `HadwigerCounterexample_PositiveTestMass`, `HadwigerCounterexample_PredictedDualCoefficients`, `HadwigerCounterexample_PredictedDualEvaluation`, `HadwigerCounterexample_PredictionClassBounds`, `HadwigerCounterexample_PredictionClasses`, `HadwigerCounterexample_PredictionDichotomy`, `HadwigerCounterexample_PredictionExactification`, `HadwigerCounterexample_PredictionExtraction`, `HadwigerCounterexample_PreliminaryRestrictions`, `HadwigerCounterexample_PreparationConditions`, `HadwigerCounterexample_PreparedOutcomes`, `HadwigerCounterexample_PreparedPopulationTrimming`, `HadwigerCounterexample_PrimalChannelDecomposition`, `HadwigerCounterexample_PrimalChannelTests`, `HadwigerCounterexample_PrimalSpaceCompression`, `HadwigerCounterexample_ProbePointMasses`, `HadwigerCounterexample_ProductCharacterTests`, `HadwigerCounterexample_ProductComparisonScales`, `HadwigerCounterexample_ProductLaws`, `HadwigerCounterexample_ProjectedSurrogates`, `HadwigerCounterexample_ProjectionEnergy`, `HadwigerCounterexample_ProjectionError`, `HadwigerCounterexample_ProjectionNets`, `HadwigerCounterexample_QuadraticFourier`, `HadwigerCounterexample_QuadraticTesters`, `HadwigerCounterexample_QueryConcentration`, `HadwigerCounterexample_RandomBinaryMixing`, `HadwigerCounterexample_RandomLinearTransforms`, `HadwigerCounterexample_RankEfficientDecomposition`, `HadwigerCounterexample_RareLeafEvents`, `HadwigerCounterexample_RareTestEvents`, `HadwigerCounterexample_RawFrameLaws`, `HadwigerCounterexample_RealizationConditions`, `HadwigerCounterexample_RectangleComparisons`, `HadwigerCounterexample_RectangleRegularity`, `HadwigerCounterexample_RecursiveComparisonErrors`, `HadwigerCounterexample_RefinedPinImages`, `HadwigerCounterexample_ReindexedFourierSupport`, `HadwigerCounterexample_RelationMismatchBounds`, `HadwigerCounterexample_RelativeEntropy`, `HadwigerCounterexample_RelativeInjectionBounds`, `HadwigerCounterexample_RepeatedBatchLaws`, `HadwigerCounterexample_RepeatedQueryBounds`, `HadwigerCounterexample_ReservedLabels`, `HadwigerCounterexample_ResidualCutPairs`, `HadwigerCounterexample_ResidualRegularity`, `HadwigerCounterexample_ResponseAnnihilators`, `HadwigerCounterexample_ResponseSolvability`, `HadwigerCounterexample_RestrictedComparisonLaws`, `HadwigerCounterexample_SampledGraphs`, `HadwigerCounterexample_ScalarStatusAlgebra`, `HadwigerCounterexample_ScriptGramCorrespondence`, `HadwigerCounterexample_SimultaneousProjection`, `HadwigerCounterexample_SinglePositionExpansion`, `HadwigerCounterexample_SingletonPhaseTests`, `HadwigerCounterexample_SmallCoverBounds`, `HadwigerCounterexample_SpanDeficits`, `HadwigerCounterexample_SparseCutProfiles`, `HadwigerCounterexample_SparseLabelBounds`, `HadwigerCounterexample_StatusCharts`, `HadwigerCounterexample_StatusRecipes`, `HadwigerCounterexample_SumRankBounds`, `HadwigerCounterexample_SuperlevelBounds`, `HadwigerCounterexample_SupportedPhaseLaws`, `HadwigerCounterexample_SurrogateAggregation`, `HadwigerCounterexample_SurrogateProductBounds`, `HadwigerCounterexample_SurrogateQueryScores`, `HadwigerCounterexample_SurrogateStatusLaws`, `HadwigerCounterexample_SyntheticArraySlices`, `HadwigerCounterexample_SyntheticFailureBounds`, `HadwigerCounterexample_SyntheticParity`, `HadwigerCounterexample_SyntheticSliceComparison`, `HadwigerCounterexample_SyntheticSliceExperiments`, `HadwigerCounterexample_TableInjectionTransfer`, `HadwigerCounterexample_TemplateTypicality`, `HadwigerCounterexample_TensorIntersections`, `HadwigerCounterexample_TerminalCut`, `HadwigerCounterexample_TesterFourierSupport`, `HadwigerCounterexample_TesterSummaryMass`, `HadwigerCounterexample_UltrafilterRates`, `HadwigerCounterexample_UnaryCellComparisons`, `HadwigerCounterexample_UnaryPositivityBounds`, `HadwigerCounterexample_UnaryQueryComparison`, `HadwigerCounterexample_UnaryQueryFrequencies`, `HadwigerCounterexample_UnaryRecords`, `HadwigerCounterexample_UnfilteredHistogramEnergy`, `HadwigerCounterexample_UniformLeafComparisons`, `HadwigerCounterexample_UniformSideComparisons`, `HadwigerCounterexample_UnseenCrossingFactorization`, `HadwigerCounterexample_WalshBounds`, `HadwigerCounterexample_WeightedPartitions`, `HadwigerCounterexample_ZeroDiscrepancyPrediction`, `HadwigerMatching_BranchCounting`, `HadwigerMatching_SmallBranches`.
--
--   **Imports.** It imports no bundle or statement, only Mathlib.
--
--   **Imported by** (directly, in this split): the statements `OAI.HadwigerCounterexample.PreparationParameters.outlook_to_dose`, `OAI.HadwigerCounterexample.PreparationParameters.phaseAbsent`, `OAI.HadwigerCounterexample.PreparationParameters.phaseSplit`, `OAI.HadwigerCounterexample.PreparationParameters.veil.score_cost`, `OAI.HadwigerCounterexample.StatusAnalysis.Quill.sideRelease`, `OAI.HadwigerCounterexample.StatusAnalysis.Quill.soberCalendar`, `OAI.HadwigerCounterexample.StatusAnalysis.Station.eclipse_beam`, `OAI.HadwigerCounterexample.StatusAnalysis.dim_end`, `OAI.HadwigerCounterexample.StatusAnalysis.gauzeCalendar`, `OAI.HadwigerCounterexample.StatusAnalysis.invoke`, `OAI.HadwigerCounterexample.StatusAnalysis.lightmap`, `OAI.HadwigerCounterexample.StatusAnalysis.refuteVeil`, `OAI.HadwigerCounterexample.Template.controls`, `OAI.HadwigerCounterexample.Template.crane_mean`, `OAI.HadwigerCounterexample.Template.shade_calendar`, `OAI.HadwigerCounterexample.eventual_conflict_lower_bound`, `OAI.HadwigerCounterexample.exists_parameters`, `OAI.HadwigerCounterexample.law_peekR`, `OAI.HadwigerCounterexample.litFire_calendar`, `OAI.HadwigerCounterexample.poUse` and `OAI.HadwigerCounterexample.pooled_batch`; the proofs of `OAI.HadwigerCounterexample.PreparationParameters.outlook_to_dose`, `OAI.HadwigerCounterexample.PreparationParameters.phaseAbsent`, `OAI.HadwigerCounterexample.PreparationParameters.phaseSplit`, `OAI.HadwigerCounterexample.PreparationParameters.veil.score_cost`, `OAI.HadwigerCounterexample.StatusAnalysis.Quill.sideRelease`, `OAI.HadwigerCounterexample.StatusAnalysis.Quill.soberCalendar`, `OAI.HadwigerCounterexample.StatusAnalysis.Station.eclipse_beam`, `OAI.HadwigerCounterexample.StatusAnalysis.dim_end`, `OAI.HadwigerCounterexample.StatusAnalysis.gauzeCalendar`, `OAI.HadwigerCounterexample.StatusAnalysis.invoke`, `OAI.HadwigerCounterexample.StatusAnalysis.lightmap`, `OAI.HadwigerCounterexample.StatusAnalysis.refuteVeil`, `OAI.HadwigerCounterexample.Template.controls`, `OAI.HadwigerCounterexample.Template.crane_mean`, `OAI.HadwigerCounterexample.Template.shade_calendar`, `OAI.HadwigerCounterexample.eventual_conflict_lower_bound`, `OAI.HadwigerCounterexample.exists_graphs`, `OAI.HadwigerCounterexample.exists_parameters`, `OAI.HadwigerCounterexample.law_peekR`, `OAI.HadwigerCounterexample.litFire_calendar`, `OAI.HadwigerCounterexample.poUse`, `OAI.HadwigerCounterexample.pooled_batch` and `OAI.HadwigerMatching.full_matching_minor_proposition`.
-- source:
--   OpenAI, A counterexample to Hadwiger's conjecture, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 157; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/A-counterexample-to-Hadwigers-conjecture-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Combinatorics at commit 7ef5c0c

import Lean.Elab.Tactic.Omega
import Mathlib
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.GroupWithZero.Finset
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Field.ZMod
import Mathlib.Algebra.Group.Fin.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Combinatorics.SimpleGraph.Clique
import Mathlib.Combinatorics.SimpleGraph.Coloring.Vertex
import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Fintype.Option
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Matrix.ColumnRowPartitioned
import Mathlib.FieldTheory.Finiteness
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.LinearAlgebra.Projection
import Mathlib.Order.Filter.Ultrafilter.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Tactic.SplitIfs

section
-- module Solutions.OAIQ430_HC.Compat
namespace OAI

/-! Compatibility with the newer Lean core OpenAI's code was written against: lemmas it uses by
names this environment (Lean 4.33.1, Mathlib 0df444a) does not have yet. Each is the
corresponding `if_pos` / `if_neg` / `dif_pos` / `dif_neg`. The `dite` forms are stated as
`dite p a b`, not with the `if hp : p then …` notation: its eta-expanded lambdas form is a higher-order pattern
that `rw` cannot find (DepthThree, PeriodicTiling 2026-10-25). -/
section OAICompat434
theorem ite_eq_left {α : Sort _} {c : Prop} {_ : Decidable c} {a b : α} (h : c) :
    (if c then a else b) = a := if_pos h
theorem ite_eq_right {α : Sort _} {c : Prop} {_ : Decidable c} {a b : α} (h : ¬c) :
    (if c then a else b) = b := if_neg h

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
/-- Mathlib's newer case names for `FreeGroup.induction_on` (`one`, where ours says `C1`). -/
@[elab_as_elim]
theorem freeGroupInductionOn {α : Type*} {C : FreeGroup α → Prop} (z : FreeGroup α) (one : C 1)
    (of : ∀ x, C (FreeGroup.of x)) (inv_of : ∀ x, C (FreeGroup.of x) → C (FreeGroup.of x)⁻¹)
    (mul : ∀ x y, C x → C y → C (x * y)) : C z :=
  FreeGroup.induction_on z one of inv_of mul
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
/-- A closed non-unital ⋆-subalgebra of a C⋆-algebra is star ordered (d13f23b's `Subtype.starOrderedRing` is an
instance for every closed non-unital ⋆-subalgebra class; OpenAI's projection corners rely on it, q360). -/
instance nonUnitalStarSubalgebraStarOrderedRing {A : Type*} [CStarAlgebra A] [PartialOrder A]
    [StarOrderedRing A] (S : NonUnitalStarSubalgebra ℂ A) [IsClosed (S : Set A)] : StarOrderedRing S := by
  refine StarOrderedRing.of_nonneg_iff' (fun {a b} h c => ?_) (fun {s} => ?_)
  · show ((c : A) + (a : A)) ≤ (c : A) + (b : A)
    exact add_le_add le_rfl (show (a : A) ≤ (b : A) from h)
  · constructor
    · intro hs
      have hs' : (0 : A) ≤ (s : A) := hs
      have hmem : CFC.sqrt (s : A) ∈ S := by
        rw [CFC.sqrt_eq_real_sqrt _ hs']
        exact cfcₙ_mem (𝕜 := ℝ) (𝕜' := ℂ) (s := S) _ s.property
      refine ⟨⟨CFC.sqrt (s : A), hmem⟩, Subtype.ext ?_⟩
      show (s : A) = star (CFC.sqrt (s : A)) * CFC.sqrt (s : A)
      rw [CFC.sqrt_nonneg _ |>.isSelfAdjoint.star_eq, CFC.sqrt_mul_sqrt_self _ hs']
    · rintro ⟨t, rfl⟩
      show (0 : A) ≤ star (t : A) * (t : A)
      exact star_mul_self_nonneg _
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
/-- Mathlib d13f23b's `MeasurableSpace (Matrix m n α)` (Mathlib/Analysis/Matrix/MeasurableSpace.lean): the product structure
(InvariantIsing, q251). Explicitly named: the platform's `Def_InvariantIsing` declares an anonymous copy of the same
instance. -/
instance _root_.Matrix.compatMeasurableSpace {m n α : Type*} [MeasurableSpace α] :
    MeasurableSpace (Matrix m n α) :=
  inferInstanceAs <| MeasurableSpace (m → n → α)
/-- Mathlib d13f23b's `BorelSpace (Matrix m n α)` (Mathlib/Analysis/Matrix/MeasurableSpace.lean; InvariantIsing, q258). -/
instance _root_.Matrix.compatBorelSpace {m n α : Type*} [Countable m] [Countable n] [MeasurableSpace α]
    [TopologicalSpace α] [SecondCountableTopology α] [BorelSpace α] : BorelSpace (Matrix m n α) :=
  inferInstanceAs <| BorelSpace (m → n → α)
end OAICompat434

end OAI
end

section
-- module Solutions.OAIQ430_HC.HadwigerCounterexample_FiniteLaws
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Finite Laws -/

noncomputable section
open scoped BigOperators

namespace HadwigerCounterexample

abbrev Wgt (α : Type*) := α → ℝ

variable {α β : Type*}

/-- Real indicator. -/
def ind (p : Prop) : ℝ := @ite ℝ p (Classical.propDecidable _) 1 0

/-- Total weight. -/
def tot [Fintype α] (w : Wgt α) : ℝ := ∑ x, w x
/-- Weighted average (not normalized if the weights are not a probability law). -/
def avg [Fintype α] (w f : Wgt α) : ℝ := ∑ x, w x * f x
/-- Weight of an event. -/
def pr [Fintype α] (w : Wgt α) (p : α → Prop) := avg w (fun x => ind (p x))

structure SubLaw [Fintype α] (w : Wgt α) : Prop where
  nz (x : α) : 0 ≤ w x
  total : tot w ≤ 1
structure IsLaw [Fintype α] (w : Wgt α) : Prop where
  nz (x : α) : 0 ≤ w x
  total : tot w = 1

/-- All positive mass is supported on `p`. We use the equivalent contrapositive with
zero mass (and supply nonnegativity wherever we speak of a law). -/
def carried (w : Wgt α) (p : α → Prop) := ∀ x : α, ¬ p x → w x = 0

section Basic
variable [Fintype α] {w v f g : Wgt α} {p q : α → Prop}

@[simp] theorem avg_zero (w : Wgt α) : avg w (fun _ => 0) = 0 := by simp [avg]

@[simp] theorem pr_point (w : Wgt α) (x : α) : pr w (fun y => x = y) = w x := by
  classical simp [pr, avg, ind]

@[simp] theorem pr_point' (w : Wgt α) (x : α) : pr w (fun y => y = x) = w x := by
  classical simp [pr, avg, ind]

end Basic

/-- Restrict weights; *not* renormalized. -/
def subW (w : Wgt α) (p : α → Prop) := fun x => w x * ind (p x)

/-- Divide a finite weight function by its total, giving zero if total is zero. -/
def normW [Fintype α] (w : Wgt α) := fun x => w x / tot w

def unif [Fintype α] : Wgt α := normW fun _ => 1
def unifOn [Fintype α] (p : α → Prop) : Wgt α := normW (fun x => ind (p x))

section Restrict
variable [Fintype α] {w : Wgt α} {p : α → Prop}

@[simp] theorem subW_tot (w : Wgt α) (p : α → Prop) : tot (subW w p) = pr w p := rfl

end Restrict

def pairW (w : Wgt α) (v : Wgt β) : Wgt (α × β) := fun p => w p.1 * v p.2
def mixW [Fintype α] (w : Wgt α) (F : α → Wgt β) : Wgt β := fun y => avg w (fun x => F x y)
def mapW [Fintype α] (w : Wgt α) (f : α → β) : Wgt β := fun y => pr w (fun x => f x = y)

end HadwigerCounterexample

end

end OAI
end

section
-- module Solutions.OAIQ430_HC.HadwigerCounterexample_ProductLaws
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Product Laws -/

noncomputable section
open scoped BigOperators
namespace HadwigerCounterexample

variable {ι κ α : Type*}
variable {β : ι → Type*}

def prodW [Fintype ι] (w : ∀ i, Wgt (β i)) : Wgt (∀ i, β i) := fun x => ∏ i, w i (x i)

end HadwigerCounterexample

end

end OAI
end

section
-- module Solutions.OAIQ430_HC.HadwigerCounterexample_FiniteConditioning
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


/-! # Finite Conditioning -/

noncomputable section
namespace HadwigerCounterexample
open scoped BigOperators

variable {A B : Type*} [Fintype A]

/-- Number of solutions as a real. -/
def nbr (p : A → Prop) := tot (fun x => ind (p x))

def onW (w : Wgt A) (p : A → Prop) := normW (subW w p)

end HadwigerCounterexample

end

end OAI
end

section
-- module Solutions.OAIQ430_HC.HadwigerCounterexample_ConditionalProductLaws
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Conditional Product Laws -/

noncomputable section
namespace HadwigerCounterexample
open scoped BigOperators

variable {A B I : Type} [Fintype A] [Fintype B]

def semi (w : Wgt A) (k : A → Wgt B) : Wgt (A × B) := fun x => w x.1 * k x.1 x.2

end HadwigerCounterexample

end

end OAI
end

section
-- module Solutions.OAIQ430_HC.HadwigerCounterexample_CellPruning
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Cell Pruning -/

noncomputable section
namespace HadwigerCounterexample
open scoped BigOperators
open Finset
variable {A B I J : Type} [Fintype A] [Fintype B] [Fintype I] [Fintype J]

def memberC (p : A→Prop) (f : A→I) (i : I) (x : A) := p x ∧ f x=i

end HadwigerCounterexample

end

end OAI
end

section
-- module Solutions.OAIQ430_HC.HadwigerCounterexample_BinaryMatrices
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Binary Matrices -/

noncomputable section
namespace HadwigerCounterexample

open scoped BigOperators
open Matrix

abbrev F := ZMod 2
abbrev Vec (I : Type) := I → F
abbrev Mat (I J : Type) := Matrix I J F
abbrev Space (V : Type) [AddCommGroup V] [Module F V] := Submodule F V

theorem char_two {V : Type*} [AddCommGroup V] [Module F V] (x : V) : x+x=0 :=
  ZModModule.add_self x

section Linear

variable {I J K L R S : Type} [Fintype I] [Fintype J]

def evmat (M : Mat I J) (x : Vec I) (y : Vec J) := dotProduct x (M *ᵥ y)

def mpair (M : Mat I J) : Mat I J →ₗ[F] F where
  toFun A := ∑ i, ∑ j, M i j * A i j
  map_add' A B := by simp only [Matrix.add_apply,mul_add,Finset.sum_add_distrib]
  map_smul' b A := by
    simp only [Matrix.smul_apply, smul_eq_mul,RingHom.id_apply,Finset.mul_sum,mul_left_comm b]

theorem mpair_comm (M A : Mat I J) : mpair M A = mpair A M := by
  dsimp [mpair]
  simp only [mul_comm]

/-- Apply frame maps to the two factors of every tensor. -/
def liftM (P : Mat K I) (Q : Mat L J) : Mat I J →ₗ[F] Mat K L where
  toFun A := P*A*Qᵀ
  map_add' A B := by rw [Matrix.mul_add,Matrix.add_mul]
  map_smul' b A := by simp only [Matrix.mul_smul, Matrix.smul_mul,RingHom.id_apply]

theorem liftM_def (P : Mat K I) (Q : Mat L J) (A : Mat I J) :
    liftM P Q A = P*A*Qᵀ := rfl

variable [Fintype K] [Fintype L]

theorem liftM_comp (P : Mat K I) (Q : Mat L J) (P' : Mat R K) (Q' : Mat S L)
    (A : Mat I J) :
    liftM P' Q' (liftM P Q A) = liftM (P'*P) (Q'*Q) A := by
  simp only [liftM_def, Matrix.transpose_mul,Matrix.mul_assoc]

theorem mat_left_inv [DecidableEq I] {P : Mat K I} (hp : Function.Injective P.mulVec) :
    ∃ Q : Mat I K, Q*P = 1 := by
  classical
  have hp' : Function.Injective (P.mulVecLin) := hp
  obtain ⟨f,hf⟩ := P.mulVecLin.exists_leftInverse_of_injective (LinearMap.ker_eq_bot.mpr hp')
  refine ⟨LinearMap.toMatrix' f, ?_⟩
  apply Matrix.toLin'.injective
  rw [Matrix.toLin'_mul]
  simp only [Matrix.toLin'_one]
  change ((LinearMap.toMatrix').symm _) ∘ₗ _ = _
  rw [LinearEquiv.symm_apply_apply]
  exact hf

theorem liftM_inj {P : Mat K I} {Q : Mat L J} (hp : Function.Injective P.mulVec)
    (hq : Function.Injective Q.mulVec) : Function.Injective (liftM P Q) := by
  classical
  obtain ⟨P', hP⟩ := mat_left_inv hp
  obtain ⟨Q', hQ⟩ := mat_left_inv hq
  intro A B hab
  have hh := congrArg (liftM P' Q') hab
  rw [liftM_comp,liftM_comp,hP,hQ] at hh
  simpa only [liftM_def, Matrix.one_mul, Matrix.transpose_one,
    Matrix.mul_one] using hh

end Linear
end HadwigerCounterexample

end

end OAI
end

section
-- module Solutions.OAIQ430_HC.HadwigerCounterexample_LinearExtension
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Linear Extension -/

noncomputable section
namespace HadwigerCounterexample

open Matrix Module Submodule LinearMap Function

abbrev dim (V : Type) [AddCommGroup V] [Module F V] := finrank F V
abbrev rk {V W : Type} [AddCommGroup V] [Module F V]
    [AddCommGroup W] [Module F W] (f : V →ₗ[F] W) := dim (LinearMap.range f)

end HadwigerCounterexample

end

end OAI
end

section
-- module Solutions.OAIQ430_HC.HadwigerCounterexample_MatrixRanks
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


/-! # Matrix Ranks -/

noncomputable section
namespace HadwigerCounterexample
open Matrix Module LinearMap Function

variable {I J K : Type}
variable [Fintype I] [Fintype J]

abbrev colSp (P : Mat I J) := range P.mulVecLin

/-- A coordinate set of basis vectors of a subspace arranged as columns. -/
def pack (S : Space (Vec I)) : Mat I (Fin (dim S)) :=
  let E : Vec (Fin (dim S)) ≃ₗ[F] S := LinearEquiv.ofFinrankEq (Vec (Fin (dim S))) S (by
    rw [finrank_pi]; simp)
  LinearMap.toMatrix' (S.subtype ∘ₗ E.toLinearMap)

theorem pack_eq {S : Space (Vec I)} :
    ∃ E : Vec (Fin (dim S)) ≃ₗ[F] S, (pack S).mulVecLin = S.subtype ∘ₗ E.toLinearMap := by
  unfold pack
  refine ⟨LinearEquiv.ofFinrankEq _ _ (by rw [finrank_pi]; simp),?_⟩
  rw [← toLin'_apply']
  exact LinearEquiv.symm_apply_apply _ _

theorem pack_inj (S : Space (Vec I)) : Function.Injective (pack S).mulVec := by
  rw [← Matrix.coe_mulVecLin]
  obtain ⟨E,he⟩ := pack_eq (S:=S)
  rw [he]
  exact Subtype.val_injective.comp E.injective

theorem colSp_pack (S : Space (Vec I)) : colSp (pack S) = S := by
  obtain ⟨E,he⟩ := pack_eq (S:=S)
  rw [colSp,he,LinearMap.range_comp]
  simp

omit [Fintype I] in
theorem coe_mv_inj : Function.Injective (fun P : Mat I J => P.mulVecLin) := by
  classical
  rw [show (fun P : Mat I J => P.mulVecLin) = toLin' by rfl]
  exact LinearEquiv.injective _

end HadwigerCounterexample

end

end OAI
end

section
-- module Solutions.OAIQ430_HC.HadwigerCounterexample_ComponentIndices
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Component Indices -/

noncomputable section
namespace HadwigerCounterexample

abbrev Tag := Fin
abbrev Comp (g : ℕ) := { p : Tag g × Tag g // p.1 < p.2 }

variable {g : ℕ}

def edge (l d : Tag g) (h : l ≠ d) : Comp g :=
  if hl : l < d then ⟨(l,d),hl⟩ else ⟨(d,l),lt_of_le_of_ne (le_of_not_gt hl) h.symm⟩

theorem edge_eq {l d : Tag g} (h : l < d) : edge l d (ne_of_lt h) = ⟨(l,d),h⟩ := by
  simp [edge,h]

theorem edge_symm {l d : Tag g} (h : l ≠ d) : edge l d h = edge d l h.symm := by
  rcases lt_or_gt_of_ne h with e|e
  · simp [edge,e,not_lt.mpr e.le]
  · simp [edge,e,not_lt.mpr e.le]

def inc (e : Comp g) (l : Tag g) : Prop := e.val.1 = l ∨ e.val.2 = l
instance instDecidableInc (e : Comp g) (l : Tag g) : Decidable (inc e l) := inferInstanceAs (Decidable (_ ∨ _))

theorem inc_edge_fst {l d : Tag g} (h : l ≠ d) : inc (edge l d h) l := by
  by_cases e : l < d <;> simp [inc,edge,e]

theorem inc_edge_iff {l d x : Tag g} (h : l ≠ d) : inc (edge l d h) x ↔ (l=x ∨ d=x) := by
  by_cases e : l < d <;> simp [inc,edge,e,or_comm]

abbrev TagStar (l : Tag g) := {e : Comp g // inc e l}

def starEquiv (l : Tag g) : {d : Tag g // l ≠ d} ≃ TagStar l := by
  let f (d : {d : Tag g // l ≠ d}) : TagStar l := ⟨edge l d d.property,inc_edge_fst _⟩
  apply Equiv.ofBijective f
  constructor
  · intro i j h
    have hi : inc (edge l i i.property) i := (inc_edge_iff _).mpr (Or.inr rfl)
    change inc (f i).val i at hi
    rw [h] at hi
    exact Subtype.ext (((inc_edge_iff j.property).mp hi).resolve_left i.property).symm
  · rintro ⟨⟨⟨i,j⟩,hij⟩,he⟩
    rcases he with g|g
    · change i = l at g
      subst l
      refine ⟨⟨j,hij.ne⟩,Subtype.ext ?_⟩
      exact edge_eq hij
    · change j = l at g
      subst l
      refine ⟨⟨i,hij.ne.symm⟩,Subtype.ext ?_⟩
      dsimp only [f]
      rw [edge_symm,edge_eq hij]

theorem card_star (l : Tag g) : Fintype.card (TagStar l) = g - 1 := by
  rw [← Fintype.card_congr (starEquiv l)]
  exact (Fintype.card_subtype_compl (fun d => l=d)).trans (by simp)

/-- l in I_d. -/
def allowed (d l : Tag g) :=
  0 < (l-d).val ∧ (l-d).val ≤ (g-1)/2

instance instDecidableAllowed (d l : Tag g) : Decidable (allowed d l) :=
  inferInstanceAs (Decidable (_ ∧ _))

end HadwigerCounterexample

end

end OAI
end

section
-- module Solutions.OAIQ430_HC.HadwigerCounterexample_MomentCoordinates
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Moment Coordinates -/

noncomputable section
namespace HadwigerCounterexample
open scoped BigOperators
open Matrix Finset

/-- Construction parameters that affect dimensions (except n,N). j = selector degree;
r = number of ordered tester pairs in a tester. J, h mix and channel indices. -/
structure Shape where
  g : ℕ
  b : ℕ
  j : ℕ
  J : ℕ
  r : ℕ
  h : ℕ

abbrev Block (g : ℕ) := (Tag g × Tag g) ⊕ Fin 3
namespace Block
variable {g : ℕ}
abbrev O (d t : Tag g) : Block g := .inl (d,t)
abbrev S : Block g := .inr 0
abbrev sharp : Block g := .inr 1
abbrev Z : Block g := .inr 2
end Block

abbrev BaseIdx (g n : ℕ) := Block g × Fin n
abbrev Base (g n : ℕ) := Vec (BaseIdx g n)
abbrev AIdx (g n : ℕ) := Option (BaseIdx g n)
abbrev Label (b : ℕ) := Vec (Fin b)
abbrev SelIdx (b j : ℕ) := { m : Finset (Fin b) // m.card ≤ j }
abbrev Row (p : Shape) (n : ℕ) := SelIdx p.b p.j × AIdx p.g n
abbrev Ray (p : Shape) (n : ℕ) := Vec (Row p n)
abbrev Moment (p : Shape) (n : ℕ) := Mat (Row p n) (Row p n)

def psize (p : Shape) := Fintype.card (SelIdx p.b p.j)

def emptySel {b j} : SelIdx b j := ⟨∅,by simp⟩
def selV {b} (j) (s : Label b) : Vec (SelIdx b j) := fun x => ∏ i ∈ x.val, s i
def baseV {g n} (z : Base g n) : Vec (AIdx g n) := Option.elim' 1 z

variable (p : Shape)
variable {n : ℕ}

/-- Embedding of the affine coordinate space at a fixed label. -/
def putLab (n : ℕ) (s : Label p.b) : Vec (AIdx p.g n) →ₗ[F] Ray p n where
  toFun z r := selV p.j s r.1 * z r.2
  map_add' z w := by ext; simp only [Pi.add_apply,mul_add]
  map_smul' b z := by ext; simp only [Pi.smul_apply,RingHom.id_apply,smul_eq_mul] <;> ring

def point (s : Label p.b) (z : Base p.g n) : Ray p n := putLab p n s (baseV z)
def mom (s : Label p.b) (z : Base p.g n) : Moment p n := vecMulVec (point p s z) (point p s z)

def Wspace (n : ℕ) : Space (Moment p n) :=
  Submodule.span F {m | ∃ s z, m = mom p s z}

/-- O-blocks disallowed at l are set to zero. -/
def allows {g n} (l : Tag g) (z : Base g n) :=
  ∀ d t : Tag g, ¬ allowed d l → ∀ i : Fin n, z (Block.O d t,i) = 0

def shared {g n} (z : Base g n) :=
  ∀ d t : Tag g, ∀ i : Fin n, z (Block.O d t,i) = 0

def Wtag (n : ℕ) (l : Tag p.g) : Space (Moment p n) :=
  Submodule.span F {m | ∃ s z, allows l z ∧ m = mom p s z}

def Wstar (n : ℕ) : Space (Moment p n) :=
  Submodule.span F {m | ∃ s z, shared z ∧ m = mom p s z}

variable {p}

/-- Cut profiles in the direct sum over unordered components. -/
abbrev Profile (p : Shape) (n : ℕ) := Comp p.g → Moment p n
def cut (p : Shape) (n : ℕ) : (Tag p.g → Moment p n) →ₗ[F] Profile p n where
  toFun w e := w e.val.1 + w e.val.2
  map_add' w w' := by
    funext e
    simp only [Pi.add_apply]
    ac_rfl
  map_smul' b w := by funext; simp only [Pi.smul_apply, RingHom.id_apply, smul_add]

def Xspace (p : Shape) (n : ℕ) : Space (Profile p n) :=
  (Submodule.pi Set.univ (fun l => Wtag p n l)).map (cut p n)

theorem mem_X {x : Profile p n} :
    x ∈ Xspace p n ↔ ∃ w : Tag p.g → Moment p n, (∀ l, w l ∈ Wtag p n l) ∧ cut p n w = x :=
  Submodule.mem_map.trans (by simp [Submodule.mem_pi])

/-- For complete generality this returns zero on pairs with equal tags. -/
def getPair (p : Shape) (n : ℕ) (l d : Tag p.g) : Profile p n →ₗ[F] Moment p n :=
  if h : l ≠ d then LinearMap.proj (edge l d h) else 0

/-- Single star atoms as profiles in ambient coordinates. -/
def atom (p : Shape) (l : Tag p.g) (s : Label p.b) (z : Base p.g n) : Profile p n :=
  cut p n (Pi.single l (mom p s z))

theorem atom_mem {l} {z : Base p.g n} (s : Label p.b) (h : allows l z) :
    atom p l s z ∈ Xspace p n := by
  rw [mem_X]
  refine ⟨Pi.single l (mom p s z),fun i => ?_,rfl⟩
  by_cases e : l = i
  · subst i
    rw [Pi.single_eq_same]
    exact Submodule.subset_span ⟨s,z,h,rfl⟩
  · simp [Pi.single_eq_of_ne (Ne.symm e)]

end HadwigerCounterexample

end

end OAI
end

section
-- module Solutions.OAIQ430_HC.HadwigerCounterexample_BooleanLabels
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Boolean Labels -/

noncomputable section
namespace HadwigerCounterexample
open scoped BigOperators
open Matrix Finset
variable {b : ℕ}

def monoBit (s : Label b) (S : Finset (Fin b)) := ∏ i ∈ S, s i

variable {p : Shape} {n : ℕ}

def hankel (M : Moment p n) :=
  ∀ (i k : AIdx p.g n) (a b c d : SelIdx p.b p.j),
    a.val ∪ b.val = c.val ∪ d.val → M (a,i) (b,k) = M (c,i) (d,k)

def diagBase (M : Moment p n) :=
  ∀ (i : AIdx p.g n) (a b : SelIdx p.b p.j), M (a,i) (b,i) = M (a,none) (b,i)

abbrev BaseMat (p : Shape) (n : ℕ) := Mat (AIdx p.g n) (AIdx p.g n)

def labMat (p : Shape) (n) (s : Label p.b) :
    Mat (Row p n) (AIdx p.g n) :=
  Matrix.of (fun v i => if v.2=i then monoBit s v.1.val else 0)

def mput (p : Shape) (s : Label p.b) {n} :
    BaseMat p n →ₗ[F] Moment p n := liftM (labMat p n s) (labMat p n s)

end HadwigerCounterexample

end

end OAI
end

section
-- module Solutions.OAIQ430_HC.HadwigerCounterexample_FlatRankLevels
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Flat Rank Levels -/

noncomputable section
namespace HadwigerCounterexample
open Matrix
open scoped BigOperators
variable {p : Shape} {n k : ℕ}

abbrev Layer (p : Shape) (n k : ℕ) := SelIdx p.b k × AIdx p.g n

def rise (p : Shape) {n k m} (h : k ≤ m) (i : Layer p n k) : Layer p n m :=
  (⟨i.1.val,i.1.property.trans h⟩,i.2)

def bump (p : Shape) {n k} (a : Fin p.b) (i : Layer p n k) : Layer p n (k+1) :=
  (⟨insert a i.1.val,(Finset.card_insert_le ..).trans (Nat.add_le_add_right i.1.property 1)⟩,i.2)

def atLayer (M : Moment p n) {k : ℕ} (h : k≤p.j) := M.submatrix (rise p h) (rise p h)

end HadwigerCounterexample

end

end OAI
end

section
-- module Solutions.OAIQ430_HC.HadwigerCounterexample_MomentLabelSupport
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Moment Label Support -/

noncomputable section
namespace HadwigerCounterexample
open Matrix Finset
open scoped BigOperators
variable {p : Shape} {n k : ℕ}

def labelSum (p : Shape) (L : Finset (Label p.b)) (Z : Label p.b → BaseMat p n) :=
  ∑ s∈L, mput p s (Z s)

end HadwigerCounterexample

end

end OAI
end

section
-- module Solutions.OAIQ430_HC.HadwigerCounterexample_CoordinateEmbeddings
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Coordinate Embeddings -/

noncomputable section
namespace HadwigerCounterexample
open Matrix Module Function
open scoped BigOperators
variable {U V I J K T : Type} [Fintype U] [Fintype V] [Fintype I] [Fintype J]
    [Fintype K] [Fintype T]

def embedMat [DecidableEq U] (f : I → U) : Mat U I := Matrix.of (fun i j => if i=f j then 1 else 0)

omit [Fintype U] in
theorem inj_fromCols {A : Mat U I} {B : Mat U J} (hA : Injective A.mulVec)
    (hB : Injective B.mulVec) (h : Disjoint (colSp A) (colSp B)) :
    Injective (fromCols A B).mulVec := by
  rw [← Matrix.coe_mulVecLin,← LinearMap.ker_eq_bot, Matrix.ker_mulVecLin_eq_bot_iff]
  intro x hx
  let a := fun i => x (Sum.inl i)
  let b := fun j => x (Sum.inr j)
  rw [fromCols_mulVec] at hx
  have he : A*ᵥa=B*ᵥb := add_right_cancel (hx.trans (char_two (B*ᵥb)).symm)
  have hi : A*ᵥa ∈ colSp A ⊓ colSp B :=
    ⟨⟨a,rfl⟩, he.symm ▸ (show B*ᵥb∈colSp B from ⟨b,rfl⟩)⟩
  rw [h.eq_bot] at hi
  have hg : A*ᵥa=0 := by simpa using hi
  have ha : a=0 := hA (hg.trans (Matrix.mulVec_zero A).symm)
  rw [he] at hg
  have hb : b=0 := hB (hg.trans (Matrix.mulVec_zero B).symm)
  funext i
  cases i
  · exact congr_fun ha _
  · exact congr_fun hb _

end HadwigerCounterexample

end

end OAI
end

section
-- module Solutions.OAIQ430_HC.HadwigerCounterexample_QuadraticTesters
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Quadratic Testers -/

noncomputable section
namespace HadwigerCounterexample
open Matrix
open scoped BigOperators

theorem mpair_add {I J : Type} [Fintype I] [Fintype J] (A B M : Mat I J) :
    mpair (A+B) M = mpair A M + mpair B M := by rw [mpair_comm,map_add,mpair_comm M,mpair_comm M]

theorem mpair_smul {I J : Type} [Fintype I] [Fintype J] (b : F) (A M : Mat I J) :
    mpair (b • A) M = b * mpair A M := by rw [mpair_comm,map_smul,mpair_comm M, smul_eq_mul]

variable (p : Shape)

def pick (n : ℕ) (u : SelIdx p.b p.j) (d : Block p.g) (i : ℕ) : Ray p n :=
  if h : i < n then Pi.single (u,some (d,⟨i,h⟩)) 1 else 0

def readBit {n g} (z : Base g n) (d : Block g) (i : ℕ) : F :=
  if h : i < n then z (d,⟨i,h⟩) else 0

def testM (n : ℕ) (d : Block p.g) : Moment p n :=
  ∑ i : Fin p.r, vecMulVec (pick p n emptySel d (2*i.val))
    (pick p n emptySel d (2*i.val+1))

def etab (n) (d : Block p.g) : Moment p n →ₗ[F] F := mpair (testM p n d)

def test (n : ℕ) (d : Block p.g) (z z' : Base p.g n) : F :=
  ∑ i : Fin p.r, readBit z d (2*i.val) * readBit z' d (2*i.val+1)

/-- all O testers. -/
def etaO (n) : Moment p n →ₗ[F] F :=
  ∑ (d : Tag p.g), ∑ (t : Tag p.g), etab p n (Block.O d t)

def eta (n) : Moment p n →ₗ[F] F := etaO p n + etab p n Block.S

/-- a_t read on full ambient profile using allowed tags with partner d. -/
def roleT (n : ℕ) (t : Tag p.g) : Profile p n →ₗ[F] F :=
  ∑ (l : Tag p.g), ∑ d ∈ Finset.univ.filter (fun d => allowed d l),
    etab p n (Block.O d t) ∘ₗ getPair p n l d

def role (n : ℕ) := ∑ t : Tag p.g, roleT p n t

/-- b_t read on the full ambient profile. -/
def sharedT (n : ℕ) (t : Tag p.g) : Profile p n →ₗ[F] F :=
  ∑ (l : Tag p.g), etab p n Block.S ∘ₗ getPair p n l t

def sharpPick (n : ℕ) (a : Fin p.b) (i : Fin n) : Ray p n :=
  if h : 1 ≤ p.j then pick p n ⟨{a},by simp [h]⟩ Block.sharp i.val else 0

def sharpM (n : ℕ) (Y : Fin p.b → Mat (Fin n) (Fin n)) : Moment p n :=
  ∑ a : Fin p.b, ∑ i : Fin n, ∑ j : Fin n,
    Y a i j • (vecMulVec (sharpPick p n a i) (pick p n emptySel Block.sharp j.val) +
      vecMulVec (pick p n emptySel Block.sharp i.val) (sharpPick p n a j))

def selfM (n) (Y : Fin p.b → Mat (Fin n) (Fin n)) : Moment p n :=
  ((∑ d : Tag p.g, ∑ t : Tag p.g, testM p n (Block.O d t)) +
    testM p n Block.S) + sharpM p n Y

end HadwigerCounterexample

end

end OAI
end

section
-- module Solutions.OAIQ430_HC.HadwigerCounterexample_CoordinateBlocks
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Coordinate Blocks -/

noncomputable section
namespace HadwigerCounterexample
open Matrix
open scoped BigOperators
variable {p : Shape} {n : ℕ}

def blockA (p : Shape) (n : ℕ) (B : Block p.g) : Mat (AIdx p.g n) (Fin n) :=
  embedMat (fun i => some (B,i))

def blockRay (p : Shape) (n : ℕ) (s : Label p.b) (B : Block p.g) : Mat (Row p n) (Fin n) :=
  labMat p n s * blockA p n B

def pullM {I J V U : Type} [Fintype V] [Fintype U] (P : Mat V I) (Q : Mat U J) :
    Mat V U →ₗ[F] Mat I J := liftM Pᵀ Qᵀ
end HadwigerCounterexample

end

end OAI
end

section
-- module Solutions.OAIQ430_HC.HadwigerCounterexample_SampledGraphs
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Sampled Graphs -/

noncomputable section
namespace HadwigerCounterexample
open Finset
variable {A V : Type*}

structure Holes (A : Type*) where
  rel : A → A → Prop
  sym {x y : A} : rel x y → rel y x
  irr (x : A) : ¬ rel x x
  ntri {x y z : A} : rel x y → rel y z → ¬ rel x z

namespace Holes

variable (H : Holes A)
def unit (p : A × A) := ¬H.rel p.1 p.2
def conflict (p q : A × A) := H.rel p.1 q.1 ∧ H.rel p.1 q.2 ∧ H.rel p.2 q.1 ∧ H.rel p.2 q.2

def graph (x : V → A) : SimpleGraph V where
  Adj i j := i ≠ j ∧ ¬H.rel (x i) (x j)
  symm := ⟨fun _ _ ⟨hne,h⟩ => ⟨hne.symm,fun h' => h (H.sym h')⟩⟩
  loopless := ⟨fun _ h => h.1 rfl⟩

end Holes
end HadwigerCounterexample

end

end OAI
end

section
-- module Solutions.OAIQ430_HC.HadwigerCounterexample_AffineFrames
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Affine Frames -/

noncomputable section
namespace HadwigerCounterexample

open Matrix
open scoped BigOperators

structure Mixer (p : Shape) (n : ℕ) where
  mixL : Fin p.J → Comp p.g → Comp p.g → Moment p n
  mixR : Fin p.J → Comp p.g → Comp p.g → Moment p n
  mixM : Fin p.b → Mat (Fin n) (Fin n)

abbrev Pdual (p : Shape) (n : ℕ) := Profile p n →ₗ[F] F

def linTensor {V : Type} [AddCommGroup V] [Module F V] (a b : V →ₗ[F] F) : V →ₗ[F] V →ₗ[F] F :=
  a.smulRight b

theorem linTensor_val {V : Type} [AddCommGroup V] [Module F V] (a b : V →ₗ[F] F)
    (x y : V) : linTensor a b x y = a x * b y := rfl

variable {p : Shape} {n N : ℕ}

def T0 (p : Shape) (n : ℕ) : Profile p n →ₗ[F] Pdual p n :=
  linTensor (role p n) (role p n) +
    ∑ i : Tag p.g, (linTensor (roleT p n i) (sharedT p n i) +
      linTensor (sharedT p n i) (roleT p n i))

theorem T0_val (x y : Profile p n) : T0 p n x y =
    role p n x * role p n y +
      ∑ i : Tag p.g, (roleT p n i x * sharedT p n i y + sharedT p n i x * roleT p n i y) := by
  simp only [T0,LinearMap.add_apply,LinearMap.sum_apply,linTensor_val]

def B1 (m : Mixer p n) : Profile p n →ₗ[F] Pdual p n where
  toFun x := {
    toFun := fun y => ∑ j, ∑ e, ∑ f,
      mpair (x e) (liftM (m.mixL j e f) (m.mixR j e f) (y f))
    map_add' y z := by simp only [Pi.add_apply,map_add, Finset.sum_add_distrib]
    map_smul' b y := by simp only [Pi.smul_apply,map_smul,RingHom.id_apply,smul_eq_mul,
      Finset.mul_sum] }
  map_add' x y := LinearMap.ext fun z => by
    simp only [LinearMap.coe_mk,AddHom.coe_mk,LinearMap.add_apply,
      Pi.add_apply,mpair_add, Finset.sum_add_distrib]
  map_smul' b x := LinearMap.ext fun z => by
    simp only [LinearMap.coe_mk,AddHom.coe_mk,LinearMap.smul_apply,RingHom.id_apply,
      Pi.smul_apply,mpair_smul,smul_eq_mul, Finset.mul_sum]

def Tmix (m : Mixer p n) := B1 m + LinearMap.flip (B1 m)
def Tsym (m : Mixer p n) := T0 p n + Tmix m

theorem Tsym_val (m : Mixer p n) (x y : Profile p n) :
    Tsym m x y = T0 p n x y + (B1 m x y + B1 m y x) := by
  change (T0 p n + (B1 m + _)) x y = _
  simp

theorem T_swap (m : Mixer p n) (x y : Profile p n) : Tsym m x y = Tsym m y x := by
  simp only [Tsym_val,T0_val]
  refine congrArg₂ (· + ·) (congrArg₂ (· + ·) (mul_comm _ _)
    (Finset.sum_congr rfl fun i _ => ?_)) (add_comm _ _)
  rw [mul_comm (roleT p n i x),mul_comm (sharedT p n i x),add_comm]

def grad (m : Mixer p n) (x : Profile p n) := role p n + Tsym m x
theorem grad_val (m : Mixer p n) (x y : Profile p n) :
    grad m x y = role p n y + Tsym m x y := rfl

abbrev Full (p : Shape) (n : ℕ) := Row p n ⊕ Fin p.h
abbrev RawFrame (I J : Type) := Mat J I × Mat J I
abbrev Oframe (p : Shape) (n N : ℕ) := RawFrame (Full p n) (Fin N)
abbrev Orient (p : Shape) (n N : ℕ) := Comp p.g → Oframe p n N

def primary {I J E : Type} (M : Mat E (I ⊕ J)) : Mat E I := M.submatrix id Sum.inl
def channel {I J E : Type} (M : Mat E (I ⊕ J)) : Mat E J := M.submatrix id Sum.inr

theorem fromCols_frame {I J E : Type} (M : Mat E (I ⊕ J)) :
    fromCols (primary M) (channel M) = M := by ext i j; rcases j with i|j <;> rfl

theorem primary_inj {I J E : Type} [Fintype I] [Fintype J]
    {M : Mat E (I ⊕ J)} (h : Function.Injective M.mulVec) :
    Function.Injective (primary M).mulVec := by
  intro a b hab
  let v (x : Vec I) := Sum.elim x (fun _ : J => (0:F))
  have he (x : Vec I) : M *ᵥ v x = primary M *ᵥ x := by
    conv_lhs => rw [← fromCols_frame M]
    unfold v; rw [fromCols_mulVec_sumElim]
    change _ + (channel M *ᵥ 0) = _
    rw [Matrix.mulVec_zero,add_zero]
  have hh : v a = v b := h (by rw [he,he]; exact hab)
  exact funext fun i => congr_fun hh (.inl i)

def valid (M : Moment p n) (o : Oframe p n N) : Prop :=
  Function.Injective o.1.mulVec ∧ Function.Injective o.2.mulVec ∧
  (primary o.1)ᵀ * primary o.2 = M ∧ (channel o.1)ᵀ * primary o.2 = 0 ∧
  (primary o.1)ᵀ * channel o.2 = 0

def frameLaw (m : Mixer p n) (o : Orient p n N) :=
  ∀ e, valid (selfM p n m.mixM) (o e)

abbrev Ambient (p : Shape) (N : ℕ) := Comp p.g → Mat (Fin N) (Fin N)

def Uembed (o : Orient p n N) : Profile p n →ₗ[F] Ambient p N where
  toFun x e := liftM (primary (o e).1) (primary (o e).2) (x e)
  map_add' x y := by funext e; simp only [Pi.add_apply,map_add]
  map_smul' a x := by funext e; simp only [Pi.smul_apply,map_smul,RingHom.id_apply]

def ufun (o : Orient p n N) : Ambient p N →ₗ[F] F where
  toFun x := ∑ e, mpair (channel (o e).2 * (channel (o e).1)ᵀ) (x e)
  map_add' x y := by simp only [Pi.add_apply,map_add, Finset.sum_add_distrib]
  map_smul' a x := by simp only [Pi.smul_apply,map_smul,RingHom.id_apply,
    smul_eq_mul,Finset.mul_sum]

theorem Uembed_inj {m : Mixer p n} {o : Orient p n N} (h : frameLaw m o) :
    Function.Injective (Uembed o) := by
  intro x y e
  exact funext fun i =>
    liftM_inj (primary_inj (h i).1) (primary_inj (h i).2.1) (congr_fun e i)

/-- Witnesses v,w are in the cut-profile space. The gradients agree over that
*whole* space. -/
def hole (m : Mixer p n) (x y : Orient p n N) :=
  frameLaw m x ∧ frameLaw m y ∧ ∃ v w : Profile p n,
    v ∈ Xspace p n ∧ w ∈ Xspace p n ∧
    Uembed x v = Uembed y w ∧
    (∀ i ∈ Xspace p n, ufun y (Uembed x i) = grad m v i) ∧
    (∀ i ∈ Xspace p n, ufun x (Uembed y i) = grad m w i) ∧
    role p n v + role p n w = 1

theorem hole_sym {m : Mixer p n} {x y : Orient p n N} (h : hole m x y) : hole m y x := by
  obtain ⟨hx,hy,v,w,hv,hw,e,h,g,p⟩ := h
  exact ⟨hy,hx,w,v,hw,hv,e.symm,g,h,(add_comm _ _).trans p⟩

theorem not_hole_self (m : Mixer p n) (x : Orient p n N) : ¬hole m x x := by
  rintro ⟨hx,_,v,w,_,_,e,_,_,hp⟩
  rw [Uembed_inj hx e,char_two] at hp
  exact zero_ne_one hp

theorem hole_triangle {m : Mixer p n} {x y z : Orient p n N}
    (h1 : hole m x y) (h2 : hole m y z) : ¬ hole m x z := by
  intro h3
  obtain ⟨_,_,a,b,ha,hb,hab,u1,u2,p1⟩ := h1
  obtain ⟨_,_,c,d,hc,hd,hcd,u3,u4,p2⟩ := h2
  obtain ⟨_,_,e,f,he,hf,hef,u5,u6,p3⟩ := h3
  have hx : grad m b c = grad m f d := by rw [←u2 _ hc, ←u6 _ hd,hcd]
  have hy : grad m a e = grad m d f := by rw [←u1 _ he, ←u4 _ hf,hef]
  have hz : grad m e a = grad m c b := by rw [←u5 _ ha, ←u3 _ hb,hab]
  simp only [grad_val] at hx hy hz
  let A := role p n
  have hw (x y : F) (h : x=y) : x+y=0 := by rw [h,char_two]
  have hp : (A a+A b)+(A c+A d)+(A e+A f)=0 := by
    let H := Tsym m
    change A _ + H _ _ = A _ + H _ _ at hx hy hz
    calc (A a+A b)+(A c+A d)+(A e+A f)
      _ = ((A c+H b c)+(A d+H f d)) +
        ((A e+H a e)+(A f+H d f)) +
        ((A a+H e a)+(A b+H c b)) := by
          have h (x y) : H x y+H y x=0 := hw _ _ (T_swap m _ _)
          symm
          calc ((A c+H b c)+(A d+H f d)) +
            ((A e+H a e)+(A f+H d f)) +
            ((A a+H e a)+(A b+H c b))
            _ = ((A a+A b)+(A c+A d)+(A e+A f)) + (H b c+H c b) +
              (H f d+H d f)+(H a e+H e a) := by ac_rfl
            _ = _ := by simp only [h,add_zero]
      _ = 0 := by rw [hw _ _ hx, hw _ _ hy, hw _ _ hz]; simp
  unfold A at hp
  rw [p1,p2,p3,char_two,zero_add] at hp
  exact one_ne_zero hp

def rawHoles (m : Mixer p n) : Holes (Orient p n N) where
  rel := hole m
  sym := hole_sym
  irr := not_hole_self m
  ntri := hole_triangle

end HadwigerCounterexample

end

end OAI
end

section
-- module Solutions.OAIQ430_HC.HadwigerCounterexample_ExponentialRates
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Exponential Rates -/

noncomputable section
namespace HadwigerCounterexample

open Filter Real
open scoped Topology

def bp (x : ℝ) := (2:ℝ)^x
@[simp] theorem bp_zero : bp 0 = 1 := by simp [bp]
@[simp] theorem bp_one : bp 1 = 2 := by simp [bp]
@[gcongr] theorem bp_le {x y : ℝ} (h : x ≤ y) : bp x ≤ bp y :=
  Real.rpow_le_rpow_of_exponent_le (by norm_num) h
@[gcongr] theorem bp_lt {x y : ℝ} (h : x < y) : bp x < bp y :=
  Real.rpow_lt_rpow_of_exponent_lt (by norm_num) h

variable {ι : Type*} {l : Filter ι} {n f g : ι → ℝ}

/-- Exponentially small at scale n. -/
def ExpSmall (l : Filter ι) (n f : ι → ℝ) :=
  ∃ c : ℝ, 0 < c ∧ ∀ᶠ i in l, |f i| ≤ bp (-c * n i)

/-- Subexponential upper bound at scale n. -/
def ExpO (l : Filter ι) (n f : ι → ℝ) :=
  ∀ c : ℝ, 0 < c → ∀ᶠ i in l, |f i| ≤ bp (c * n i)

end HadwigerCounterexample

end

end OAI
end

section
-- module Solutions.OAIQ430_HC.HadwigerCounterexample_GramProbabilities
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Gram Probabilities -/

noncomputable section
namespace HadwigerCounterexample
open scoped BigOperators
open Matrix Function LinearMap

abbrev num (I : Type) [Fintype I] : ℝ := (Fintype.card I:ℝ)

variable {I J U : Type} [Fintype I] [Fintype J] [Fintype U]

def columnInv {w : Wgt (Mat U I)} (T : Space (Vec U)) :=
  ∀ M A : Mat U I, colSp A ≤ T → w (M+A) = w M

variable [DecidableEq U] [DecidableEq I] [DecidableEq J]

def gramGood (G : Mat I J) (q : Mat U I × Mat U J) :=
  q.1ᵀ*q.2 = G ∧ Injective q.1.mulVec ∧ Injective q.2.mulVec

def GramL (J : Type) (P : Mat U I) : Mat U J →ₗ[F] Mat I J where
  toFun M := Pᵀ * M
  map_add' _ _ := Matrix.mul_add _ _ _
  map_smul' _ _ := Matrix.mul_smul _ _ _

end HadwigerCounterexample

end

end OAI
end

section
-- module Solutions.OAIQ430_HC.HadwigerCounterexample_FrameOrbitLaws
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Frame Orbit Laws -/

noncomputable section
namespace HadwigerCounterexample
open Matrix Function

variable {U I J R S : Type} [Fintype U] [Fintype I] [Fintype J] [Fintype R] [Fintype S]
    [DecidableEq U]

def FramesAt (C : Mat I J → Prop) (x : Mat U I × Mat U J) :=
  C (x.1ᵀ * x.2) ∧ Injective x.1.mulVec ∧ Injective x.2.mulVec

structure Move (U : Type) [Fintype U] [DecidableEq U] where
  L : Mat U U
  R : Mat U U
  LR : L*R=1
  RL : R*L=1

namespace Move
variable (c : Move U)
def sym : Move U := ⟨c.R,c.L,c.RL,c.LR⟩
def dual : Move U := ⟨c.Rᵀ,c.Lᵀ,by rw [← transpose_mul,c.LR, Matrix.transpose_one],
  by rw [← transpose_mul,c.RL,Matrix.transpose_one]⟩
def permMat (I : Type) : Mat U I ≃ Mat U I where
  toFun A := c.L*A
  invFun A := c.R*A
  left_inv A := by simp only [← Matrix.mul_assoc, c.RL, Matrix.one_mul]
  right_inv A := by simp only [← Matrix.mul_assoc, c.LR, Matrix.one_mul]
def perm (I J : Type) : Mat U I × Mat U J ≃ Mat U I × Mat U J :=
  (c.permMat I).prodCongr (c.dual.permMat J)

end Move

variable [DecidableEq I] [DecidableEq J] [DecidableEq R] [DecidableEq S]

def observe (P : Mat I R) (Q : Mat J S) (x : Mat U I × Mat U J) : Mat U R × Mat U S :=
  (x.1 * P, x.2 * Q)

end HadwigerCounterexample

end

end OAI
end

section
-- module Solutions.OAIQ430_HC.HadwigerCounterexample_MixedImageBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

set_option backward.isDefEq.respectTransparency false

namespace OAI

/-! # Mixed Image Bounds -/

noncomputable section

namespace HadwigerCounterexample
open Matrix Function LinearMap
open scoped BigOperators

variable {I J U S : Type} [Fintype I] [Fintype J] [Fintype U] [Fintype S]
  [DecidableEq I] [DecidableEq J] [DecidableEq U] [DecidableEq S]

def mixImage (D : Mat (I ⊕ I) J) (x : Mat U I × Mat U I) := fromCols x.1 x.2 * D

def mixImageLin (D : Mat (I ⊕ I) J) :
    (Mat U I × Mat U I) →ₗ[F] Mat U J where
  toFun := mixImage D
  map_add' a b := by
    have e : fromCols (a+b).1 (a+b).2 = fromCols a.1 a.2 + fromCols b.1 b.2 := by
      ext i j; cases j <;> rfl
    unfold mixImage
    rw [e,Matrix.add_mul]
  map_smul' b x := by
    have e : fromCols (b•x).1 (b•x).2 = b • fromCols x.1 x.2 := by
      ext i j; cases j <;> rfl
    unfold mixImage
    rw [e,Matrix.smul_mul]; rfl

def weakMinus (C : Mat I I → Prop) (P : Mat U I) := unifOn (fun Q : Mat U I => C (Pᵀ*Q))

end HadwigerCounterexample

end

end OAI
end

section
-- module Solutions.OAIQ430_HC.HadwigerCounterexample_RawFrameLaws
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Raw Frame Laws -/

noncomputable section
namespace HadwigerCounterexample
open Matrix
open scoped BigOperators

variable {p : Shape} {n N : ℕ}

instance rowDecidableEq (p : Shape) (n : ℕ) : DecidableEq (Row p n) := inferInstance
instance fullDecidableEq (p : Shape) (n : ℕ) : DecidableEq (Full p n) := inferInstance
instance fullFintype (p : Shape) (n : ℕ) : Fintype (Full p n) := inferInstance
instance oframeFintype (p : Shape) (n N : ℕ) : Fintype (Oframe p n N) := inferInstance
instance orientFintype (p : Shape) (n N : ℕ) : Fintype (Orient p n N) := inferInstance

def gramCond (m : Mixer p n) (G : Mat (Full p n) (Full p n)) : Prop :=
  G.toBlocks₁₁ = selfM p n m.mixM ∧ G.toBlocks₂₁ = 0 ∧ G.toBlocks₁₂ = 0

def raw (m : Mixer p n) (N : ℕ) : Wgt (Orient p n N) :=
  prodW (fun (_ : Comp p.g) => unifOn (FramesAt (U := Fin N) (gramCond m)))

abbrev UnitType (p : Shape) (n N : ℕ) := Orient p n N × Orient p n N
abbrev Place (p : Shape) := Comp p.g × Bool
abbrev JointIdx (p : Shape) (n : ℕ) := Full p n ⊕ Full p n

def takeSign (w : Oframe p n N) (b : Bool) := if b then w.1 else w.2

def images (x : UnitType p n N) (z : Place p) : Mat (Fin N) (JointIdx p n) :=
  fromCols (takeSign (x.1 z.1) z.2) (takeSign (x.2 z.1) z.2)

abbrev Dir (p : Shape) (n : ℕ) := Vec (JointIdx p n)
abbrev Plan (p : Shape) (n : ℕ) := Place p → Submodule F (Dir p n)
def planRank (s : Plan p n) := ∑ i, dim (s i)

/-- Pin data: stored subspaces of directions with assigned images. We store a
full linear map for convenience; only its restriction to the pin directions
at each place is used. Counts charge only for the restrictions. -/
structure Pin (p : Shape) (n N : ℕ) where
  sp : Plan p n
  target : Place p → Mat (Fin N) (JointIdx p n)

def Pin.agree (a : Pin p n N) (x : UnitType p n N) :=
  ∀ i, ∀ v ∈ a.sp i, images x i *ᵥ v = a.target i *ᵥ v

end HadwigerCounterexample

end

end OAI
end

section
-- module Solutions.OAIQ430_HC.HadwigerCounterexample_SparseCutProfiles
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Sparse Cut Profiles -/

noncomputable section
namespace HadwigerCounterexample
open Matrix
open scoped BigOperators

variable {p : Shape} {n : ℕ}

def totalRank (x : Profile p n) : ℕ := ∑ i, (x i).rank
def nonzeroTags (w : Tag p.g → Moment p n) : Finset (Tag p.g) :=
  by classical exact Finset.univ.filter (fun i => w i ≠ 0)

end HadwigerCounterexample

end

end OAI
end

section
-- module Solutions.OAIQ430_HC.HadwigerCounterexample_TensorIntersections
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Tensor Intersections -/

noncomputable section
namespace HadwigerCounterexample
open Matrix LinearMap Submodule
open scoped BigOperators

variable {p : Shape} {n N : ℕ}

/-- Sum of dimensions of the kernel of the combined plus maps at each component.
This bounds (in fact equals) the sum of intersection dimensions of full plus
frames when the frames are valid. -/
def joins (x : UnitType p n N) : ℕ :=
  ∑ i : Comp p.g, dim (ker (images x (i,true)).mulVecLin)

def parityW (w : Tag p.g → Moment p n) := ∑ i, eta p n (w i)

end HadwigerCounterexample

end

end OAI
end

section
-- module Solutions.OAIQ430_HC.HadwigerCounterexample_MatrixQuotients
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Matrix Quotients -/

noncomputable section
namespace HadwigerCounterexample
open Matrix LinearMap Submodule Module
open scoped BigOperators
variable {I J K L : Type} [Fintype I] [Fintype J] [Fintype K] [Fintype L]

def box (S : Space (Vec I)) (T : Space (Vec J)) :=
  LinearMap.range (liftM (pack S) (pack T))

theorem pack_mem_iff (v : Vec I) (S : Space (Vec I)) :
    v∈S ↔ ∃ x, pack S *ᵥ x=v := by
  change _ ↔ v∈colSp (pack S)
  rw [colSp_pack]

def annih (S : Space (Vec I)) := ker ((pack S)ᵀ.mulVecLin)

def vanish (S : Space (Vec I)) (T : Space (Vec J)) (M : Mat I J) :=
  ∀ x ∈ annih S, ∀ y∈ annih T, evmat M x y=0

end HadwigerCounterexample

end

end OAI
end

section
-- module Solutions.OAIQ430_HC.HadwigerCounterexample_SparseLabelBounds
attribute [-instance] _root_.OAI.HadwigerCounterexample.fullDecidableEq _root_.OAI.HadwigerCounterexample.fullFintype _root_.OAI.HadwigerCounterexample.oframeFintype _root_.OAI.HadwigerCounterexample.orientFintype _root_.OAI.HadwigerCounterexample.rowDecidableEq
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Sparse Label Bounds -/

noncomputable section
namespace HadwigerCounterexample
open scoped BigOperators
open Matrix Finset Submodule
variable {p : Shape} {n : ℕ}

abbrev LabVals (p : Shape) (n : ℕ) := Label p.b → Vec (AIdx p.g n)

def labcomb (p : Shape) (n : ℕ) (L : Finset (Label p.b)) :
    LabVals p n →ₗ[F] Ray p n :=
  ∑ i∈L, putLab p n i ∘ₗ LinearMap.proj i

def labV (p : Shape) (n : ℕ) (L : Finset (Label p.b)) : Space (Ray p n) :=
  LinearMap.range (labcomb p n L)

def withinL (p : Shape) (L : Finset (Label p.b)) (z : LabVals p n) : LabVals p n :=
  fun i => if i ∈ L then z i else 0

/-- L is the set excluded at this projected space. -/
def protectedBy (p : Shape) {n} (S : Space (Ray p n)) (q : ℕ) (L : Finset (Label p.b)) :=
  ∀ (B : Finset (Label p.b)) (z : LabVals p n),
    labcomb p n B z∈S → B.card≤q → ∀ i∈B,i∉L → z i=0

end HadwigerCounterexample

end

end OAI
end

section
-- module Solutions.OAIQ430_HC.HadwigerCounterexample_NominalSpaces
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Nominal Spaces -/

noncomputable section
namespace HadwigerCounterexample
open Matrix Module
open scoped BigOperators

variable {p : Shape} {n N : ℕ}

def onSide {A : Type} (x : A × A) (b : Bool) := if b then x.1 else x.2
def putFull (p : Shape) (n : ℕ) : Bool → Full p n → JointIdx p n
| true => Sum.inl
| false => Sum.inr

instance jointDecidableEq (p : Shape) (n : ℕ) : DecidableEq (JointIdx p n) := inferInstance

abbrev Chan (p : Shape) := Fin p.h
def IP (p : Shape) (n : ℕ) (b : Bool) : Mat (JointIdx p n) (Row p n) :=
  embedMat (fun i => putFull p n b (.inl i))
def IH (p : Shape) (n : ℕ) (b : Bool) : Mat (JointIdx p n) (Chan p) :=
  embedMat (fun i => putFull p n b (.inr i))

def sPin (s : Plan p n) (z : Place p) (i : Bool) : Space (Ray p n) :=
  (s z).map (IP p n i)ᵀ.mulVecLin

def hPin (s : Plan p n) (z : Place p) (i : Bool) : Space (Vec (Chan p)) :=
  (s z).map (IH p n i)ᵀ.mulVecLin

/-- small table-coordinate space J. -/
def halfTable (s : Plan p n) (z : Place p) (i : Bool) :=
  (sPin s z i).map (IP p n i).mulVecLin ⊔ colSp (IH p n i)
def tabSpace (s : Plan p n) : Plan p n :=
  fun z => halfTable s z true ⊔ halfTable s z false

/-- effective test space on endpoint i. -/
def effective (s : Plan p n) (i : Bool) : Space (Profile p n) :=
  Xspace p n ⊓ Submodule.pi Set.univ (fun e => box (sPin s (e,true) i) (sPin s (e,false) i))

end HadwigerCounterexample

end

end OAI
end

section
-- module Solutions.OAIQ430_HC.HadwigerCounterexample_CrossForms
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Cross Forms -/

noncomputable section
namespace HadwigerCounterexample
open Matrix
open scoped BigOperators
variable {p : Shape} {n N : ℕ}

def flipZ (p : Shape) (z : Place p) : Place p := (z.1,!z.2)
@[simp] theorem flipZ_flip (z : Place p) : flipZ p (flipZ p z)=z := by cases z; simp [flipZ]

abbrev Cross (p : Shape) (n : ℕ) := Place p → Mat (JointIdx p n) (JointIdx p n)
def reciprocal (p : Shape) {n} (M : Cross p n) : Cross p n := fun z => (M (flipZ p z))ᵀ
@[simp] theorem reciprocal_twice (M : Cross p n) : reciprocal p (reciprocal p M)=M := by
  funext i; simp [reciprocal]

def actual (p : Shape) {n N} (x y : UnitType p n N) : Cross p n :=
  fun z => (images x z)ᵀ * images y (flipZ p z)

@[simp] theorem reciprocal_actual (x y : UnitType p n N) :
    reciprocal p (actual p x y)=actual p y x := by
  funext z; simp only [reciprocal,actual,transpose_mul,flipZ_flip,transpose_transpose]

/-- two abstract cross sets agree at every row coming from these frozen
directions. Also apply this notion reciprocally to check columns. -/
def rowAgree (q : Plan p n) (A B : Cross p n) :=
  ∀ z, ∀ x∈ q z,∀ y, evmat (A z) x y=evmat (B z) x y

/-- The flag on an orientation of A. Test all entries on the table spaces
with column in the B pins. Test the other entries by the reciprocal flag.
Together these are §5 admissibility (when units are in the pin leaves). -/
def tableFlag (a b : Pin p n N) (M : Cross p n) (x : UnitType p n N) :=
  ∀ z,∀ v∈tabSpace a.sp z,∀ w∈b.sp (flipZ p z),
    evmat (M z) v w=dotProduct (images x z *ᵥ v) (b.target (flipZ p z) *ᵥ w)

def channelOut (p : Shape) {n} (M : Cross p n) (j : Bool) (z : Place p) :
    Mat (Chan p) (JointIdx p n) := (M z * IH p n j)ᵀ

/-- small table injecting condition, at this role. Row directions are in
a.sp and wholly in the indicated primal block; output is viewed modulo
*hPin at the same sign*, not the sign of the tested columns. -/
def tableInj (a b : Plan p n) (M : Cross p n) :=
  ∀ (z : Place p) (i j : Bool) (v : Ray p n), (IP p n i)*ᵥv ∈ a z →
    channelOut p M j z *ᵥ (IP p n i *ᵥ v) ∈ hPin b z j → v=0

/-- Contraction on x, computed in full table coordinates; at the small
table only its restriction to C_i is initially meaningful. -/
def contract (p : Shape) {n} (M : Cross p n) (i j : Bool) :
    Profile p n →ₗ[F] F where
  toFun x := ∑ e : Comp p.g, mpair
    ((channelOut p M j (e,true))ᵀ * channelOut p M j (e,false))
    (liftM (IP p n i) (IP p n i) (x e))
  map_add' x y := by simp only [Pi.add_apply,map_add,Finset.sum_add_distrib]
  map_smul' a x := by simp only [Pi.smul_apply,map_smul,RingHom.id_apply,
    smul_eq_mul, Finset.mul_sum]

def innerP (p : Shape) {n N} (x : UnitType p n N) (i : Bool) :=
  ufun (onSide x (!i)) ∘ₗ Uembed (onSide x i)

end HadwigerCounterexample

end

end OAI
end

section
-- module Solutions.OAIQ430_HC.HadwigerCounterexample_ImagePartitions
attribute [-instance] _root_.OAI.HadwigerCounterexample.jointDecidableEq
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Image Partitions -/

noncomputable section
namespace HadwigerCounterexample
open Matrix
open scoped BigOperators
variable {p : Shape} {n N : ℕ}

/-- Joint nominal rank modulo pins. -/
def planNew (a b : Plan p n) := planRank (a⊔b) - planRank a

def Pin.make (a : Plan p n) (x : UnitType p n N) : Pin p n N := ⟨a,images x⟩

def fee (N : ℕ) (ζ : ℝ) (t : ℕ) := bp (-(1-ζ)*t*N)
def Pin.clear (a : Pin p n N) (ζ : ℝ) (w : Wgt (UnitType p n N)) :=
  ∀ b : Pin p n N, pr w b.agree ≤ fee N ζ (planNew a.sp b.sp)

structure PeelCell (w r : Wgt (UnitType p n N)) (D ζ : ℝ) (K : ℕ)
    (S : Finset (UnitType p n N)) (a b : Pin p n N) : Prop where
  pos : 0 < pr w (fun x => x ∈ S)
  fixpin : ∀ x ∈ S, b.agree x
  extendsSp : a.sp ≤ b.sp
  bound : planRank b.sp ≤ planRank a.sp + K
  clear : b.clear ζ (onW w (fun x => x ∈ S))
  density x : onW w (fun x => x ∈ S) x ≤ bp ((D+K+1)*N) * r x

end HadwigerCounterexample

end

end OAI
end

section
-- module Solutions.OAIQ430_HC.HadwigerCounterexample_KeyDirections
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Key Directions -/

noncomputable section
namespace HadwigerCounterexample
open scoped BigOperators
open Matrix Finset

variable {I : Type} [Fintype I]
variable {p : Shape} {n N : ℕ}

/-- One side of the lists, with actual point inputs, indexed by the
simultaneous (both units') list positions. Tags passed separately
because matched across the two sides. -/
structure Volley (p : Shape) (n : ℕ) (I : Type) where
  obj : I → Bool
  sel : I → Label p.b
  par : I → Base p.g n

abbrev Tagging (p : Shape) (I : Type) := I → Tag p.g
abbrev AtomKey {p : Shape} (l : Tag p.g) (N : ℕ) := TagStar l → Bool → Vec (Fin N)

def keyOne (p : Shape) (l : Tag p.g) (s : Label p.b) (z : Base p.g n)
    (o : Orient p n N) : AtomKey (p:=p) l N :=
  fun e b => primary (takeSign (p:=p) (o e.val) b) *ᵥ point p s z

abbrev Keys {p : Shape} {I : Type} (t : Tagging p I) (N : ℕ) := ∀ i, AtomKey (p:=p) (t i) N

namespace Volley
variable (v : Volley p n I)
def atomAt (t : Tagging p I) (i) := atom p (t i) (v.sel i) (v.par i)
def rayAt (i) := point p (v.sel i) (v.par i)
def rayLoc (i) := IP p n (v.obj i) *ᵥ v.rayAt i

/-- List from endpoint j to endpoint k of the other unit. -/
def shoots (w : I → Bool) (j k : Bool) := univ.filter (fun i => v.obj i=j ∧ w i=k)
def here (j : Bool) := Finset.univ.filter (fun i => v.obj i=j)
def sumAt (t : Tagging p I) (w : I→Bool) (j k : Bool) :=
  ∑ i∈shoots v w j k, v.atomAt t i

def keys (t : Tagging p I) (x : UnitType p n N) : Keys (p:=p) t N :=
  fun i => keyOne p (t i) (v.sel i) (v.par i) (onSide x (v.obj i))

abbrev visits (p : Shape) (t : Tagging p I) (e : Comp p.g) := {i:I//inc e (t i)}
instance instFintypeVisits (t : Tagging p I) (e) : Fintype (visits p t e) := inferInstance

def keyM (t : Tagging p I) (e : Comp p.g) : Mat (JointIdx p n) (visits p t e) :=
  Matrix.of fun i j => v.rayLoc j.val i
def keyPlan (t : Tagging p I) : Plan p n := fun e => colSp (v.keyM t e.1)

/-- At each endpoint at most q calls, with distinct labels and no
label interacting with a short vector in the pinned projections. -/
def avoids (a : Plan p n) (q : ℕ) :=
  ∀ i, ∃ B : Finset (Label p.b),
    (∀ z : Place p, protectedBy p (sPin a z i) q B) ∧
    (∀ j∈v.here i,v.sel j∉ B) ∧
    (v.here i).card ≤ q ∧
    Set.InjOn v.sel (v.here i : Set I)
end Volley

end HadwigerCounterexample

end

end OAI
end

section
-- module Solutions.OAIQ430_HC.HadwigerCounterexample_RealizationConditions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Realization Conditions -/

noncomputable section
namespace HadwigerCounterexample
open Matrix
open scoped BigOperators
variable {p : Shape} {n N : ℕ} {I : Type} [Fintype I]

namespace Volley
variable (v w : Volley p n I)

def legal (t : Tagging p I) := ∀ i : I, allows (t i) (v.par i)
def diagonalAt (i : I) := eta p n (mom p (v.sel i) (v.par i))
def bounded (w' : I→Bool) := ∀ (i j : Bool), 1≤ (v.shoots w' i j).card ∧
    (v.shoots w' i j).card ≤7

/-- Conditions for one orientation of roles, §5 (scalar recipe). -/
structure scalarRecipe (t : Tagging p I) (m : Mixer p n) (x : UnitType p n N) (S : Plan p n)
    (M : Cross p n) : Prop where
  summ (i j : Bool) : ∑ a ∈ v.shoots w.obj i j,v.diagonalAt a=1
  coupled (j : Bool) : ((innerP p x true)+role p n) (v.sumAt t w.obj true j) =
    ((innerP p x false)+role p n) (v.sumAt t w.obj false j)
  gradient (i j : Bool) (y : Profile p n) : y∈effective S i →
    grad m (v.sumAt t w.obj i j) y= contract p M i j y

def roleMatch (t : Tagging p I) :=
  ∀ i j, role p n (v.sumAt t w.obj i j)+ role p n (w.sumAt t v.obj j i)=1

def attackGrad (t : Tagging p I) (m : Mixer p n) (y : UnitType p n N) :=
  ∀ (a : I) (j : Bool),
    grad m (v.sumAt t w.obj (v.obj a) j) (v.atomAt t a) =
      if j=w.obj a then 0 else innerP p y (w.obj a) (w.atomAt t a)

def realized (t : Tagging p I) (m : Mixer p n) (M : Cross p n) :=
  ∀ i j, ∀ y ∈ Xspace p n, grad m (v.sumAt t w.obj i j) y=contract p M i j y

end Volley

def scalarBlocks (p : Shape) {n} (M : Cross p n) (e : Place p) (i j : Bool) :=
  channelOut p M j e * IP p n i

end HadwigerCounterexample

end

end OAI
end

section
-- module Solutions.OAIQ430_HC.HadwigerCounterexample_GradientRankBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Gradient Rank Bounds -/

noncomputable section
namespace HadwigerCounterexample
open Matrix
open scoped BigOperators
variable {p : Shape} {n : ℕ}

def routed (p : Shape) (n : ℕ) (t a d : Tag p.g) :=
  if allowed d a then testM p n (Block.O d t) else 0

def Represents (m : Profile p n →ₗ[F] F) (A : Profile p n) :=
  ∀ x, m x=∑ i,mpair (A i) (x i)

end HadwigerCounterexample

end

end OAI
end

section
-- module Solutions.OAIQ430_HC.HadwigerCounterexample_PrimalChannelDecomposition
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Primal Channel Decomposition -/

noncomputable section
namespace HadwigerCounterexample
open scoped BigOperators
open Matrix Submodule
variable {I : Type} [Fintype I]

/-- Onto projection in coordinates, killing a specified disjoint subspace. -/
structure ProjData (S T : Space (Vec I)) (A : Mat I I) : Prop where
  onto (x) : A *ᵥ x ∈ S
  fixes x : x ∈ S → A *ᵥ x=x
  kills x : x∈T → A *ᵥ x=0

theorem proj_exists (S T : Space (Vec I)) (h : Disjoint S T) :
    ∃ A, ProjData S T A := by
  classical
  obtain ⟨A,hA⟩ := mat_left_inv (inj_fromCols (pack_inj S) (pack_inj T)
    (by rw [colSp_pack, colSp_pack]; exact h))
  let B := A.toRows₁
  let C := A.toRows₂
  have he : fromRows B C * fromCols (pack S) (pack T)=1 := by
    rw [show fromRows B C=A from Matrix.fromRows_toRows A,hA]
  rw [Matrix.fromRows_mul_fromCols, ← Matrix.fromBlocks_one] at he
  have hb : B*pack S=1 := congrArg Matrix.toBlocks₁₁ he
  have hg : B*pack T=0 := congrArg Matrix.toBlocks₁₂ he
  refine ⟨pack S*B,fun x => ?_,fun x hx => ?_,fun x hx => ?_⟩
  · rw [←mulVec_mulVec]
    exact (pack_mem_iff ..).mpr ⟨_,rfl⟩
  · obtain ⟨x,rfl⟩ := (pack_mem_iff ..).mp hx
    rw [←mulVec_mulVec, mulVec_mulVec _ B, hb,one_mulVec]
  · obtain ⟨x,rfl⟩ := (pack_mem_iff ..).mp hx
    rw [←mulVec_mulVec,mulVec_mulVec _ B,hg,zero_mulVec,mulVec_zero]

variable {p : Shape} {n : ℕ}

/-- aggregate primal (resp. channel) directions in a unit. -/
def primal (p : Shape) (n : ℕ) := colSp (IP p n true) ⊔ colSp (IP p n false)
def channels (p : Shape) (n : ℕ) := colSp (IH p n true) ⊔ colSp (IH p n false)

/-- prSmall a z consists of the pure-primal coordinates kept by the small
table. -/
def prSmall (a : Plan p n) (z : Place p) :=
  (sPin a z true).map (IP p n true).mulVecLin ⊔
    (sPin a z false).map (IP p n false).mulVecLin

end HadwigerCounterexample

end

end OAI
end

section
-- module Solutions.OAIQ430_HC.HadwigerCounterexample_BaselineExtension
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Baseline Extension -/

noncomputable section
namespace HadwigerCounterexample
open Matrix Submodule

variable {p : Shape} {n : ℕ}

abbrev CrossM (p : Shape) (n : ℕ) := Mat (JointIdx p n) (JointIdx p n)

end HadwigerCounterexample

end

end OAI
end

section
-- module Solutions.OAIQ430_HC.HadwigerCounterexample_BaselineForms
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Baseline Forms -/

noncomputable section
namespace HadwigerCounterexample

open scoped BigOperators
open Matrix
variable {p : Shape} {n N : ℕ}

def lowCross (K : ℕ) (B : Cross p n) :=
  ∀ z i,( (B z)ᵀ * IP p n i).rank ≤ K

def fitsTable (a b : Plan p n) (B T : Cross p n) :=
  ∀ z, ∀ x∈tabSpace a z,∀ y∈tabSpace b (flipZ p z), evmat (B z) x y=evmat (T z) x y

def blin (K : ℕ) := 4*K+56

end HadwigerCounterexample

end

end OAI
end

section
-- module Solutions.OAIQ430_HC.HadwigerCounterexample_LinearResponse
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Linear Response -/

noncomputable section
namespace HadwigerCounterexample
open Matrix LinearMap Submodule Module
open scoped BigOperators
variable {p : Shape} {n : ℕ}

abbrev PureForms (p : Shape) (n : ℕ) := Comp p.g → Mat (JointIdx p n) (JointIdx p n)
abbrev ChanOut (p : Shape) (n : ℕ) := Place p → Mat (Chan p) (JointIdx p n)
abbrev Xpair (p : Shape) (n : ℕ) := Bool → Xspace p n

def pureSpace (p : Shape) {n} (f : Plan p n) : Space (PureForms p n) :=
  Submodule.pi Set.univ (fun e => box (annih (f (e,true))) (annih (f (e,false))))
def deltaSpace (p : Shape) {n} (f b : Plan p n) (j : Bool) : Space (ChanOut p n) :=
  Submodule.pi Set.univ (fun e => box (annih (hPin b (flipZ p e) j)) (annih (f e)))

def chanInner (p : Shape) {n} (C D : ChanOut p n) : PureForms p n :=
  fun e => (C (e,true))ᵀ * D (e,false)
def chanDeriv (p : Shape) {n} (C D : ChanOut p n) : PureForms p n :=
  chanInner p C D+chanInner p D C

def purePair (p : Shape) (n) (x : Xpair p n) : PureForms p n :=
  ∑ i : Bool,(fun e => liftM (IP p n i) (IP p n i) ((x i).val e))

def react (p : Shape) {n : ℕ} (C : ChanOut p n) :
    ChanOut p n × PureForms p n →ₗ[F] Module.Dual F (Xpair p n) where
  toFun A := {
    toFun x := ∑ e : Comp p.g,
      mpair ((chanDeriv p C A.1+A.2) e) (purePair p n x e)
    map_add' x y := by
      have hh (e) : purePair p n (x+y) e=purePair p n x e+purePair p n y e := by
        simp only [purePair,Finset.sum_apply,Pi.add_apply,Submodule.coe_add,map_add,
          Finset.sum_add_distrib]
      simp only [hh,map_add,Finset.sum_add_distrib]
    map_smul' b x := by
      have hh (e) : purePair p n (b•x) e=b • purePair p n x e := by
        simp only [purePair,Finset.sum_apply,Pi.smul_apply,Submodule.coe_smul,map_smul,
          Finset.smul_sum]
      simp only [hh,map_smul,RingHom.id_apply,Finset.smul_sum] }
  map_add' A B := LinearMap.ext fun x => by
    have h (e) : (chanDeriv p C (A+B).1 + (A+B).2) e =
        (chanDeriv p C A.1 + A.2) e + (chanDeriv p C B.1 + B.2) e := by
      simp only [chanDeriv,chanInner,Pi.add_apply,Prod.fst_add,Prod.snd_add,
        transpose_add,Matrix.add_mul,Matrix.mul_add]; abel
    simp only [LinearMap.coe_mk,AddHom.coe_mk,h,mpair_add,LinearMap.add_apply,
      Finset.sum_add_distrib]
  map_smul' b A := LinearMap.ext fun x => by
    have h (e) : (chanDeriv p C (b•A).1 + (b•A).2) e =
        b • (chanDeriv p C A.1 + A.2) e := by
      simp only [chanDeriv,chanInner,Pi.add_apply,Pi.smul_apply,Prod.smul_fst,Prod.smul_snd,
        transpose_smul, Matrix.smul_mul, Matrix.mul_smul,smul_add]
    simp only [LinearMap.coe_mk,AddHom.coe_mk,h,mpair_smul,LinearMap.smul_apply,RingHom.id_apply,
      smul_eq_mul,Finset.mul_sum]

def orth (p : Shape) {n : ℕ} (C : ChanOut p n) (f b : Plan p n) (j) (x : Xpair p n) :=
  ∀ D∈deltaSpace p f b j,∀ A∈pureSpace p f, react p C (D,A) x=0

end HadwigerCounterexample

end

end OAI
end

section
-- module Solutions.OAIQ430_HC.HadwigerCounterexample_FrozenProjections
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Frozen Projections -/

noncomputable section
namespace HadwigerCounterexample
open Matrix LinearMap Submodule Module Finset
open scoped BigOperators
variable {p : Shape} {n : ℕ}

variable {I : Type} [Fintype I]
namespace Volley
variable (v : Volley p n I)

/-- D + attack directions. -/
def frozen (a : Plan p n) (t : Tagging p I) : Plan p n := a⊔v.keyPlan t

/-- All labels at one endpoint. -/
def marked (i : Bool) := (v.here i).image v.sel

/-- project matrix of active key rays to one endpoint under attack -/
def visitH (t : Tagging p I) (i : Bool) (e : Comp p.g) : Finset (visits p t e) :=
  Finset.univ.filter (fun j => v.obj j.val=i)

end Volley

end HadwigerCounterexample

end

end OAI
end

section
-- module Solutions.OAIQ430_HC.HadwigerCounterexample_ResponseAnnihilators
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Response Annihilators -/

noncomputable section
namespace HadwigerCounterexample
open Matrix Finset LinearMap Submodule Module
open scoped BigOperators
variable {p : Shape} {n : ℕ}
variable {I : Type} [Fintype I]

def dotL (x : Vec I) : Vec I →ₗ[F] F where
  toFun y := dotProduct x y
  map_add' u v := dotProduct_add x _ _
  map_smul' b u := by
    simp only [dotProduct,Pi.smul_apply,RingHom.id_apply,smul_eq_mul,mul_sum,mul_left_comm]

end HadwigerCounterexample

end

end OAI
end

section
-- module Solutions.OAIQ430_HC.HadwigerCounterexample_AttackCutDecomposition
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Attack Cut Decomposition -/

noncomputable section
namespace HadwigerCounterexample
open Matrix Submodule LinearMap Module Finset
open scoped BigOperators
variable {p : Shape} {n : ℕ}
variable {I J : Type} [Fintype I] [Fintype J]

namespace Volley
variable (v : Volley p n I)

def strike (t : Tagging p I) (ht : v.legal t) (j : I) : Xpair p n :=
  Pi.single (v.obj j) (⟨v.atomAt t j,atom_mem _ (ht j)⟩ : Xspace p n)

end Volley

def labStruct (p : Shape) (n : ℕ) (M : Moment p n) (R : ℕ)
    (L : Finset (Label p.b)) (Z : Label p.b→BaseMat p n) :=
  M=labelSum p L Z ∧ L.card ≤ R ∧ (∀ s,s∉L → Z s=0) ∧
    ∀ s∈L,(Z s)ᵀ=Z s ∧ ∀ i,Z s i i=Z s none i

namespace Volley
variable {v : Volley p n I}

/-- a component uses at most R nonattack labels. -/
def clean (v : Volley p n I) (i : Bool) (R : ℕ) (M : Moment p n) :=
  ∃ (L : Finset (Label p.b)) (Z : Label p.b → BaseMat p n),
    M=labelSum p L Z ∧ L.card≤R ∧ Disjoint L (v.marked i)

end Volley
end HadwigerCounterexample

end

end OAI
end

section
-- module Solutions.OAIQ430_HC.HadwigerCounterexample_CoverSpaces
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Cover Spaces -/

noncomputable section
namespace HadwigerCounterexample
open Matrix LinearMap Submodule Module
open scoped BigOperators
variable {p : Shape} {N : ℕ}
variable {I J : Type} [Fintype I] [Fintype J]

noncomputable def prj (S : Space (Vec I)) : Mat I I :=
  (proj_exists S ⊥ disjoint_bot_right).choose

variable [DecidableEq I] [DecidableEq J]
def chop (S : Space (Vec I)) := 1-prj S

def chopSpace (S T : Space (Vec I)) := T.map (chop S).mulVecLin

abbrev Cov (p : Shape) (N : ℕ) := Place p → Space (Vec (Fin N))
def cdSign (p : Shape) {N} (S : Cov p N) (i : Bool) :=
  ∑ e : Comp p.g,dim (S (e,i))
def cdim (p : Shape) {N} (S : Cov p N) := ∑ i : Place p,dim (S i)

def epoch (p : Shape) {N} (x : Ambient p N) := ∑ e : Comp p.g,(x e).rank

def matter (p : Shape) {N} (x : Ambient p N) : Cov p N :=
  fun z => colSp (if z.2 then x z.1 else (x z.1)ᵀ)

def erased (p : Shape) {N} (S : Cov p N) : Ambient p N →ₗ[F] Ambient p N :=
  LinearMap.pi (fun i => liftM (chop (S (i,true))) (chop (S (i,false))) ∘ₗ LinearMap.proj i)

def covered (p : Shape) {N} (S : Cov p N) (x : Ambient p N) :=
  erased p S x=0

/-- Cover as a tensor space; used to count tiny-cover span. -/
def coverX (p : Shape) {N} (S : Cov p N) := ker (erased p S)

end HadwigerCounterexample

end

end OAI
end

section
-- module Solutions.OAIQ430_HC.HadwigerCounterexample_SpanDeficits
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Span Deficits -/

noncomputable section
namespace HadwigerCounterexample
open Matrix LinearMap Submodule Module Finset
open scoped BigOperators
variable {p : Shape} {N : ℕ} {I J K : Type} [Fintype I] [Fintype J] [Fintype K]

@[simp] theorem cdim_bot {p N} : cdim p (N:=N) ⊥=0 := by
  unfold cdim
  refine Finset.sum_eq_zero fun i _ => ?_
  exact finrank_bot _ _

def tax (p : Shape) {N} (a b : Cov p N) := cdim p (a⊔b)-cdim p a

def chopped (p : Shape) {N} (a b : Cov p N) : Cov p N :=
  fun z => chopSpace (a z) (b z)

def arrange (p : Shape) {N J} (f : J→ Ambient p N) (r : Finset J) := r.sup (matter p ∘ f)

end HadwigerCounterexample

end

end OAI
end

section
-- module Solutions.OAIQ430_HC.HadwigerCounterexample_GreedyExposures
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Greedy Exposures -/

noncomputable section
namespace HadwigerCounterexample
open Matrix LinearMap Submodule Module Finset
open scoped BigOperators
variable {p : Shape} {N : ℕ} {I : Type} [DecidableEq I]

def price (f : I → Ambient p N) (S : Cov p N) (W : Finset I) :=
  W.sup (fun i => tax p S (matter p (f i)))

end HadwigerCounterexample

end

end OAI
end

section
-- module Solutions.OAIQ430_HC.HadwigerCounterexample_SumRankBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Sum Rank Bounds -/

noncomputable section
namespace HadwigerCounterexample
open scoped BigOperators
open Finset
variable {A I : Type} [Fintype A] [Fintype I] [DecidableEq I]

def draws (I : Type) [Fintype I] (w : Wgt A) : Wgt (I→A) := prodW (fun _ : I => w)

def refresh (J : Finset I) (x y : I → A) : I → A :=
  fun i => if i∈J then y i else x i

end HadwigerCounterexample

end

end OAI
end

section
-- module Solutions.OAIQ430_HC.HadwigerCounterexample_ChannelFrameLaws
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Channel Frame Laws -/

noncomputable section
namespace HadwigerCounterexample
open Matrix LinearMap Module Submodule Finset Function
open scoped BigOperators

variable {A B : Type} [Fintype A] [Fintype B]

variable {I J U : Type} [Fintype I] [Fintype J] [Fintype U]
variable [DecidableEq I] [DecidableEq J] [DecidableEq U]

variable {p : Shape} {n N : ℕ}
abbrev HMat (p : Shape) (N : ℕ) := Mat (Fin N) (Chan p)
abbrev HFrame (p : Shape) (N : ℕ) := HMat p N × HMat p N
abbrev HCube (p : Shape) (N : ℕ) := Comp p.g → HFrame p N

def hchan (p : Shape) {n N} (x : Oframe p n N) : HFrame p N :=
  (channel x.1,channel x.2)
def hcube (p : Shape) {n N} (x : Orient p n N) : HCube p N := fun z => hchan p (x z)
def lawH (p : Shape) (N : ℕ) : Wgt (HCube p N) :=
  prodW (fun (_ : Comp p.g) => pairW unif unif)

def intoChan (p : Shape) (n) : Mat (Full p n) (Chan p) := embedMat (.inr ·)

def chanPrice (p : Shape) : ℝ :=
  (4*bp ((p.h:ℝ)*p.h))^(Fintype.card (Comp p.g))

end HadwigerCounterexample

end

end OAI
end

section
-- module Solutions.OAIQ430_HC.HadwigerCounterexample_FrameIntersectionBounds
attribute [-instance] _root_.OAI.HadwigerCounterexample.Volley.instFintypeVisits _root_.OAI.HadwigerCounterexample.jointDecidableEq
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Frame Intersection Bounds -/

noncomputable section
namespace HadwigerCounterexample
open Matrix LinearMap
open scoped BigOperators

variable {p : Shape} {n N : ℕ}

abbrev KCand (p : Shape) (n t : ℕ) := Comp p.g → Mat (JointIdx p n) (Fin t)

def zeroPin {t : ℕ} (f : KCand p n t) : Pin p n N :=
  ⟨fun z => if z.2 then colSp (f z.1) else ⊥,0⟩

open Filter

end HadwigerCounterexample

end

end OAI
end

section
-- module Solutions.OAIQ430_HC.HadwigerCounterexample_MatrixRankCounting
attribute [-instance] _root_.OAI.HadwigerCounterexample.Volley.instFintypeVisits _root_.OAI.HadwigerCounterexample.jointDecidableEq
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Matrix Rank Counting -/

noncomputable section
namespace HadwigerCounterexample
open Matrix LinearMap
open scoped BigOperators

variable {I J K : Type} [Fintype I] [Fintype J] [Fintype K]
    [DecidableEq I] [DecidableEq J] [DecidableEq K]

def rmult (I : Type) (A : Mat J K) : Mat I J →ₗ[F] Mat I K where
  toFun M := M*A
  map_add' _ _ := Matrix.add_mul _ _ _
  map_smul' _ _ := Matrix.smul_mul _ _ _

variable (p : Shape)
def profileA (K : ℕ) := 10*(K+1)*psize p*(p.g*p.g+5)

open Filter

end HadwigerCounterexample

end

end OAI
end

section
-- module Solutions.OAIQ430_HC.HadwigerCounterexample_ResidualCutPairs
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Residual Cut Pairs -/

noncomputable section
namespace HadwigerCounterexample
open scoped BigOperators
open Matrix LinearMap Submodule Module Finset
variable {p : Shape} {n : ℕ} {I : Type} [Fintype I]
namespace Volley

def CleanRay (v : Volley p n I) (i : Bool) (R : ℕ) (x : Ray p n) :=
  ∃ (L : Finset (Label p.b)) (u : LabVals p n), x=labcomb p n L u ∧ L.card≤R ∧
    Disjoint L (v.marked i)

end Volley

end HadwigerCounterexample

end

end OAI
end

section
-- module Solutions.OAIQ430_HC.HadwigerCounterexample_ResponseSolvability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Response Solvability -/

noncomputable section
namespace HadwigerCounterexample
open Matrix LinearMap Module Finset Submodule
open scoped BigOperators
variable {p : Shape} {n N : ℕ} {I : Type} [Fintype I]

abbrev Individual (p : Shape) (n : ℕ) := Bool → Profile p n
abbrev OnForms (p : Shape) (n : ℕ) := Bool → (Profile p n →ₗ[F] F)
abbrev ReqF (p : Shape) (n : ℕ) := Module.Dual F (Xpair p n)

def combineF (p : Shape) {n} : OnForms p n →ₗ[F] ReqF p n where
  toFun f := ∑ i : Bool, f i ∘ₗ (Xspace p n).subtype ∘ₗ LinearMap.proj i
  map_add' f g := LinearMap.ext fun x => by
    simp only [LinearMap.sum_apply,LinearMap.comp_apply,Pi.add_apply,LinearMap.add_apply,
      Finset.sum_add_distrib]
  map_smul' a f := LinearMap.ext fun x => by
    simp only [LinearMap.sum_apply,LinearMap.comp_apply,Pi.smul_apply,LinearMap.smul_apply,
      RingHom.id_apply,smul_eq_mul,mul_sum]

def obsPair (p : Shape) {n} : PureForms p n →ₗ[F] ReqF p n :=
  react p 0 ∘ₗ LinearMap.inr F (ChanOut p n) (PureForms p n)

/-- Restrict pure form to individual diagonal blocks. -/
def eachF (p : Shape) {n} :
    PureForms p n →ₗ[F] Individual p n where
  toFun P i e := pullM (IP p n i) (IP p n i) (P e)
  map_add' P Q := by ext; simp only [Pi.add_apply,map_add]
  map_smul' a P := by ext; simp only [Pi.smul_apply,map_smul,RingHom.id_apply]

/-- Extend the individual forms by zero outside respective blocks, then add. -/
def sumF (p : Shape) {n} : Individual p n → PureForms p n :=
  fun A e => ∑ i,liftM (IP p n i) (IP p n i) (A i e)

def repF (p : Shape) {n} (A : Individual p n) : OnForms p n :=
  fun i => ∑ e : Comp p.g, mpair (A i e) ∘ₗ LinearMap.proj e

theorem repF_rep (A : Individual p n) (i) :
    Represents (repF p A i) (A i) := by
  intro x
  simp only [repF,LinearMap.sum_apply]; rfl

namespace Volley
variable (v w : Volley p n I)

def demand (t : Tagging p I) (m : Mixer p n) (j : Bool) : OnForms p n :=
  fun i => grad m (v.sumAt t w.obj i j)

end Volley

end HadwigerCounterexample

end

end OAI
end

section
-- module Solutions.OAIQ430_HC.HadwigerCounterexample_DerivativeCompression
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Derivative Compression -/

noncomputable section
namespace HadwigerCounterexample
open Matrix LinearMap Module Submodule
open scoped BigOperators
variable {I J : Type} [Fintype I] [Fintype J]

variable {p : Shape} {n : ℕ}
def priOut (p : Shape) {n} (C : ChanOut p n) (z : Place p) : Space (Vec (Chan p)) :=
  colSp (C z * IP p n true) ⊔ colSp (C z * IP p n false)
def outSmall (H : ℕ) {p : Shape} {n} (C : ChanOut p n) :=
  ∀ (z : Place p) i,(C z * IP p n i).rank≤H

end HadwigerCounterexample

end

end OAI
end

section
-- module Solutions.OAIQ430_HC.HadwigerCounterexample_RankEfficientDecomposition
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Rank Efficient Decomposition -/

noncomputable section
namespace HadwigerCounterexample
open Matrix LinearMap Module Submodule Finset
open scoped BigOperators
variable {p : Shape} {n : ℕ} {I : Type} [Fintype I]

/-- Evaluation of individual matrices on Xpair -/
def obsI (p : Shape) {n} : Individual p n →ₗ[F] ReqF p n where
  toFun A := combineF p (repF p A)
  map_add' A B := by
    rw [←map_add]; apply congrArg
    funext i; refine LinearMap.ext fun x => ?_
    change repF p (A+B) i x= repF p A i x+ repF p B i x
    rw [repF_rep, repF_rep,repF_rep]
    simp only [Pi.add_apply,mpair_add,Finset.sum_add_distrib]
  map_smul' a A := by
    change combineF p (repF p (a•A))=a • _
    rw [←map_smul]; apply congrArg
    funext i; refine LinearMap.ext fun x => ?_
    change repF p (a•A) i x= a • (repF p A i x)
    rw [repF_rep,repF_rep]
    simp only [Pi.smul_apply,mpair_smul,smul_eq_mul,Finset.mul_sum]

end HadwigerCounterexample

end

end OAI
end

section
-- module Solutions.OAIQ430_HC.HadwigerCounterexample_PrimalSpaceCompression
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Primal Space Compression -/

noncomputable section
namespace HadwigerCounterexample
open Matrix LinearMap Module Submodule Finset
open scoped BigOperators
variable {p : Shape} {n : ℕ} {I J : Type} [Fintype I] [Fintype J]

abbrev Sel (p : Shape) := SelIdx p.b p.j
abbrev Nendo (p : Shape) (n : ℕ) := Block p.g→ Mat (Fin n) (Fin n)
def iFix (p : Shape) (n : ℕ) : Mat (Row p n) (Sel p) := embedMat (fun s => (s,none))
def iCoeff (p : Shape) (n : ℕ) (s : Sel p) (d : Block p.g) :
    Mat (Row p n) (Fin n) := embedMat (fun i => (s,some (d,i)))

/-- induced row vector transform. -/
def rowShrink (p : Shape) {n} (A : Nendo p n) : Mat (Row p n) (Row p n) :=
  iFix p n*(iFix p n)ᵀ +
  ∑ i : Sel p,∑ d : Block p.g,iCoeff p n i d*A d*(iCoeff p n i d)ᵀ

def readCoeff (p : Shape) {n} (s : Sel p) (d : Block p.g) (v : Ray p n) :=
  fun i => v (s,some (d,i))

def nbBlock (p : Shape) := Fintype.card (Block p.g)
def ncComp (p : Shape) := Fintype.card (Comp p.g)

def dbits (p : Shape) (T R : ℕ) := ncComp p*2* psize p*(T+R)
def drow (p : Shape) (T R : ℕ) := psize p+psize p*(nbBlock p*dbits p T R)

def shrinkBase (A : Nendo p n) (v : Base p.g n) : Base p.g n :=
  fun x => (A x.1 *ᵥ (fun j => v (x.1,j))) x.2

end HadwigerCounterexample

end

end OAI
end

section
-- module Solutions.OAIQ430_HC.HadwigerCounterexample_BilinearCompression
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Bilinear Compression -/

noncomputable section
namespace HadwigerCounterexample
open Matrix LinearMap Submodule Module Finset
open scoped BigOperators

variable {p : Shape} {n : ℕ} {I J : Type} [Fintype I] [Fintype J]

def dqBound (p : Shape) (T H R : ℕ) := 2*(drow p T R+H)

def dualSpace (M : Profile p n) (z : Place p) :=
  colSp (if z.2 then M z.1 else (M z.1)ᵀ)

def jointShrink (A : Bool → Nendo p n) (B : Place p → Bool → Mat (Chan p) (Chan p))
    (z : Place p) :=
  ∑ i : Bool,(liftM (IP p n i) (IP p n i) (rowShrink p (A i))+
    liftM (IH p n i) (IH p n i) (B z i))

end HadwigerCounterexample

end

end OAI
end

section
-- module Solutions.OAIQ430_HC.HadwigerCounterexample_GradientRealization
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Gradient Realization -/

noncomputable section
namespace HadwigerCounterexample
open Matrix LinearMap Submodule Module Finset
open scoped BigOperators
variable {p : Shape} {n N : ℕ}
def Rorth (K : ℕ) := 2*(K+20)
def qorth (K : ℕ) := Rorth K+14
def rankInit (p : Shape) := 15*p.r+14*p.J*ncComp p
def rankRes (K : ℕ) := 2*(K+14)+3*blin K
def rankAll (p : Shape) (K : ℕ) :=
  2*rankInit p+dqBound p (K+14) K (rankRes K)

structure realizeAssum (p : Shape) (K : ℕ) : Prop where
  odd : Odd p.g
  sel : 6*Rorth K+4≤p.j
  cap : rankAll p K+2*(K+2*(3*blin K))≤p.h

variable {I : Type} [Fintype I]

/-- Lift the derivative changes into one actual abstract cross Gram
(on column channel arguments only). -/
def addChan (p : Shape) {n} (D : Bool → ChanOut p n) : Cross p n :=
  fun z => ∑ j : Bool,(D j z)ᵀ * (IH p n j)ᵀ

def zeroRow (p : Shape) {n} (f : Plan p n) (M : Cross p n) :=
  ∀ z,∀ v∈f z, (M z)ᵀ *ᵥ v=0

end HadwigerCounterexample

end

end OAI
end

section
-- module Solutions.OAIQ430_HC.HadwigerCounterexample_WalshBounds
attribute [-instance] _root_.OAI.HadwigerCounterexample.fullDecidableEq _root_.OAI.HadwigerCounterexample.jointDecidableEq _root_.OAI.HadwigerCounterexample.rowDecidableEq
attribute [-simp] _root_.OAI.HadwigerCounterexample.cdim_bot
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Walsh Bounds -/

noncomputable section
namespace HadwigerCounterexample
open scoped BigOperators

def wsign (x : F) : ℝ := if x = 0 then 1 else -1

@[simp] theorem wsign_zero : wsign 0=1 := by simp [wsign]
@[simp] theorem wsign_one : wsign 1=-1 := by simp [wsign]

end HadwigerCounterexample

end

end OAI
end

section
-- module Solutions.OAIQ430_HC.HadwigerCounterexample_ConditionalCellEntropy
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Conditional Cell Entropy -/

noncomputable section
namespace HadwigerCounterexample
open Matrix LinearMap Submodule Module Finset
open scoped BigOperators
variable {p : Shape} {n N : ℕ}

variable {I : Type} [Fintype I]

def kslots (p : Shape) (I : Type) [Fintype I] :=
  Fintype.card I*(p.g-1)*2
def kmax (p : Shape) := 56*(p.g-1)

instance instFKeys (t : Tagging p I) (N : ℕ) : Fintype (Keys (p:=p) t N) :=
  by classical exact inferInstance

def tau (N k : ℕ) := bp (-((k:ℝ)+0.01)*N)
def hit (N : ℕ) := bp (-0.02*N)

end HadwigerCounterexample

end

end OAI
end

section
-- module Solutions.OAIQ430_HC.HadwigerCounterexample_ImageCharacterBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Image Character Bounds -/

noncomputable section
namespace HadwigerCounterexample
open Matrix LinearMap Module Submodule Finset
open scoped BigOperators
variable {p : Shape} {n N : ℕ}
abbrev DTuple {p : Shape} (r : Place p → ℕ) (N : ℕ) :=
  ∀ z, Mat (Fin N) (Fin (r z))
abbrev WTuple {p : Shape} (r : Place p → ℕ) (n : ℕ) :=
  ∀ z, Mat (JointIdx p n) (Fin (r z))

def flipEquiv (p : Shape) : Place p ≃ Place p :=
  ⟨flipZ p,flipZ p,fun i => flipZ_flip i,fun i => flipZ_flip i⟩

variable {r : Place p→ℕ}

def projTuple (p : Shape) {n N} (r : Place p→ℕ) (A : WTuple (p:=p) r n)
    (x : Place p ≃ Place p) (w : UnitType p n N) : DTuple (p:=p) r N :=
  fun z => images w (x z) * A z

variable {I J : Type} [Fintype I] [Fintype J]

def tupleB (p : Shape) (r : Place p → ℕ) (N : ℕ) :
    DTuple (p:=p) r N →ₗ[F] DTuple (p:=p) r N →ₗ[F] F where
  toFun x := ∑ z : Place p, mpair (x z) ∘ₗ LinearMap.proj z
  map_add' x y := LinearMap.ext fun v => by
    simp only [LinearMap.sum_apply,LinearMap.comp_apply,Pi.add_apply,LinearMap.add_apply,
      mpair_add,Finset.sum_add_distrib]
  map_smul' a x := LinearMap.ext fun v => by
    simp only [LinearMap.sum_apply,LinearMap.comp_apply,Pi.smul_apply,RingHom.id_apply,
      LinearMap.smul_apply,mpair_smul,Finset.mul_sum,smul_eq_mul]

end HadwigerCounterexample

end

end OAI
end

section
-- module Solutions.OAIQ430_HC.HadwigerCounterexample_GramCharacterQuotients
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Gram Character Quotients -/

noncomputable section
namespace HadwigerCounterexample
open Matrix LinearMap Module Submodule Finset
open scoped BigOperators
variable {p : Shape} {n N : ℕ}

def cpDual (p : Shape) {n} (A : Cross p n) :
    Cross p n →ₗ[F] F :=
  ∑ z : Place p, mpair (A z) ∘ₗ LinearMap.proj z

end HadwigerCounterexample

end

end OAI
end

section
-- module Solutions.OAIQ430_HC.HadwigerCounterexample_PrimalChannelTests
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Primal Channel Tests -/

noncomputable section
namespace HadwigerCounterexample
open Matrix LinearMap Module Submodule Finset
open scoped BigOperators
variable {p : Shape} {n N : ℕ}

abbrev CheckOne (p : Shape) (n : ℕ) :=
  Place p → Bool → Bool → Mat (Chan p) (Row p n)
abbrev CheckGram (p : Shape) (n : ℕ) :=
  CheckOne p n × CheckOne p n
instance cgOneFin (p : Shape) (n : ℕ) : Fintype (CheckOne p n) := by
  classical
  letI : Fintype (Mat (Chan p) (Row p n)) := inferInstance
  letI : Fintype (Bool → Bool → Mat (Chan p) (Row p n)) := inferInstance
  exact inferInstance
instance cgFin (p : Shape) (n : ℕ) : Fintype (CheckGram p n) := inferInstance

def testgram (p : Shape) {n} : Cross p n →ₗ[F] CheckGram p n where
  toFun A := (scalarBlocks p A, scalarBlocks p (reciprocal p A))
  map_add' A B := by
    apply Prod.ext <;>
    · ext; simp only [Pi.add_apply,Prod.fst_add,Prod.snd_add,
        scalarBlocks,channelOut,reciprocal,Matrix.add_apply,Matrix.add_mul,Matrix.transpose_add]
  map_smul' a A := by
    apply Prod.ext <;>
    · ext; simp only [Pi.smul_apply,Prod.smul_fst,Prod.smul_snd,
        scalarBlocks,channelOut,reciprocal,Matrix.smul_apply,Matrix.smul_mul,Matrix.transpose_smul,
        RingHom.id_apply]

end HadwigerCounterexample

end

end OAI
end

section
-- module Solutions.OAIQ430_HC.HadwigerCounterexample_IndependentPhaseBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Independent Phase Bounds -/

noncomputable section
namespace HadwigerCounterexample
open Matrix LinearMap Module Submodule Finset
open scoped BigOperators
variable {p : Shape} {n N : ℕ} {J K : Type} [Fintype J] [Fintype K]

abbrev PhasePair (p : Shape) (N : ℕ) := HCube p N × HCube p N
abbrev Party := Vec Bool

def uPhase (p : Shape) {N} (v : HCube p N) : Ambient p N →ₗ[F] F :=
  ∑ e : Comp p.g, mpair ((v e).2*(v e).1ᵀ) ∘ₗ LinearMap.proj e

def joinPhase (p : Shape) {N} (v : PhasePair p N) (o : Party) :=
  ∑ b : Bool, o b • uPhase p (onSide v b)

/-- Read the whole channel frames of a unit. -/
def listens (p : Shape) {n N} (x : UnitType p n N) : PhasePair p N :=
  Prod.map (hcube p) (hcube p) x

def tone (p : Shape) {n N} (x : UnitType p n N) (S : Party) (T : Ambient p N) :=
  joinPhase p (listens p x) S T

def pitch (p : Shape) {n N} (Δ : UnitType p n N → Ambient p N)
    (w : Wgt (UnitType p n N)) (S R : Party) :=
  avg (pairW w w) (fun x =>
    wsign (tone p x.1 R (Δ x.2)+tone p x.2 S (Δ x.1)))

variable [DecidableEq J] [DecidableEq K]

def freeH (p : Shape) (N : ℕ) := pairW (lawH p N) (lawH p N)

end HadwigerCounterexample

end

end OAI
end

section
-- module Solutions.OAIQ430_HC.HadwigerCounterexample_OffsetLifting
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Offset Lifting -/

noncomputable section
namespace HadwigerCounterexample
open scoped BigOperators
open Matrix LinearMap Submodule Module Finset Function
variable {I J K L : Type} [Fintype I] [Fintype J] [Fintype K] [Fintype L]

variable [DecidableEq I]

structure FrameProduct (M : Mat I I) (S T : Space (Vec I)) (X Y : Mat I J) : Prop where
  xin : Injective X.mulVec
  yin : Injective Y.mulVec
  xcol : colSp X ≤ S
  ycol : colSp Y ≤ T
  prod : X*Yᵀ=M

end HadwigerCounterexample

end

end OAI
end

section
-- module Solutions.OAIQ430_HC.HadwigerCounterexample_OffsetRecords
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Offset Records -/

noncomputable section
namespace HadwigerCounterexample
open Matrix LinearMap Module Submodule Finset Function
open scoped BigOperators
variable {p : Shape} {r n N : ℕ}

def fpAt (p : Shape) {n N} (w : Orient p n N) (z : Place p) :=
  primary (takeSign (w z.1) z.2)
def fyAt (p : Shape) {n N} (w : Orient p n N) (z : Place p) :=
  channel (takeSign (w z.1) z.2)
def imageP (p : Shape) {n N} (w : UnitType p n N) (i : Bool) : Cov p N :=
  fun z => colSp (fpAt p (onSide w i) z)

abbrev BMark (p : Shape) (n N : ℕ) := UnitType p n N → Bool → Profile p n
def mrAmbient {p : Shape} {n N} (m : BMark p n N) (x : UnitType p n N) (i : Bool) :=
  Uembed (onSide x i) (m x i)
def delta {p : Shape} {n N} (m : BMark p n N) (x : UnitType p n N) :=
  mrAmbient m x true+mrAmbient m x false

abbrev Wide (p : Shape) (r : ℕ) := Place p → Fin (r+1)
abbrev OffBasis (p : Shape) (r : ℕ) {N} (S : Cov p N) (q : Wide p r) :=
  ∀ z, Mat (Fin (dim (S z))) (Fin (q z).val)
abbrev OffAux (p : Shape) (r : ℕ) (q : Wide p r) :=
  ∀ e : Comp p.g,Mat (Fin (q (e,true)).val) (Fin (q (e,false)).val)
abbrev Atlas (p : Shape) (r : ℕ) {N} (S : Cov p N) :=
  Σ q : Wide p r, OffBasis p r S q × OffAux p r q

instance aFintype (S : Cov p N) : Fintype (Atlas p r S) := by
  classical
  letI : (q : Wide p r) → Fintype (OffBasis p r S q) := fun q => inferInstance
  letI : (q : Wide p r) → Fintype (OffAux p r q) := fun q => inferInstance
  exact inferInstanceAs (Fintype (Atlas p r S))
instance aDefault (S : Cov p N) : Inhabited (Atlas p r S) :=
  ⟨⟨fun _ => (0:Fin (r+1)),0,0⟩⟩

variable {S : Cov p N}

abbrev breadth {p : Shape} {N r} {S : Cov p N} (X : Atlas p r S) := fun z : Place p => (X.1 z).val
def cells {p : Shape} {N r} {S : Cov p N} (X : Atlas p r S) := ∑ z : Place p,breadth X z

abbrev Batch {p : Shape} {N r} {S : Cov p N} (X : Atlas p r S) (n) :=
  DTuple (p:=p) (breadth X) n

def src (X : Atlas p r S) : Batch X N :=
  fun z => pack (S z) * X.2.1 z

def edgeCost (X : Atlas p r S) : Ambient p N :=
  fun e => liftM (src X (e,true)) (src X (e,false)) (X.2.2 e)
def spelled (X : Atlas p r S) (A : Batch X N) : Ambient p N := fun e =>
  src X (e,true)*(A (e,true))ᵀ + A (e,false) * (src X (e,false))ᵀ + edgeCost X e

/-- comp for A play Zplus paired offset+, Zminus paired offset-.
Companion columns at each compared sign in **opposite** sign primal frame.
-/
def compFor (X : Atlas p r S) (A : Batch X N) (C : Cov p N)
    (D : Ambient p N) :=
  (∀ z, Injective (A z).mulVec ∧ colSp (A z) ≤ C (flipZ p z)) ∧ D=spelled X A

def locIndep (X : Atlas p r S) := ∀ z, Injective (src X z).mulVec

def standard (X : Atlas p r S) := cells X ≠ 0 ∧ cells X≤2*r ∧ locIndep X

def offsetCov (X : Atlas p r S) : Cov p N := fun z => colSp (src X z)

end HadwigerCounterexample

end

end OAI
end

section
-- module Solutions.OAIQ430_HC.HadwigerCounterexample_OffsetEnergy
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Offset Energy -/

noncomputable section
namespace HadwigerCounterexample
open Matrix LinearMap Module Submodule Finset Function
open scoped BigOperators
variable {p : Shape} {r n N : ℕ}
variable {q t : Place p→ℕ} {S : Cov p N}

def unary (i : Bool) : Party := Pi.single i 1

def heat (p : Shape) {n N} (x : UnitType p n N) (v : Party) (z : Place p) :
    Mat (Fin N) (Fin N) :=
  ∑ i : Bool,v i • (fyAt p (onSide x i) z * (fyAt p (onSide x i) (flipZ p z))ᵀ)
def thermal (p : Shape) {n N} (x : UnitType p n N) (v : Party) {q : Place p→ℕ}
    (A : DTuple (p:=p) q N) : DTuple (p:=p) q N :=
  fun z => heat p x v z * A z

def sparks (p : Shape) {n N} (x : UnitType p n N) (v : Party) {q : Place p→ℕ}
    (A : DTuple (p:=p) q N) (i : Bool) : DTuple (p:=p) q p.h :=
  fun z => v i • ((fyAt p (onSide x i) (flipZ p z))ᵀ * A z)

def glimpse (p : Shape) {n N} (x : UnitType p n N) (i : Bool) {q : Place p→ℕ}
    (A : DTuple (p:=p) q N) :=
  ∀ z,Injective ((fyAt p (onSide x i) (flipZ p z))ᵀ * A z).mulVec

def hfused (p : Shape) (n : ℕ) (r : Place p→ℕ) (A : Bool→DTuple (p:=p) r p.h) :
    WTuple (p:=p) r n :=
  fun z => ∑ i : Bool, IH p n i * A i z

end HadwigerCounterexample

end

end OAI
end

section
-- module Solutions.OAIQ430_HC.HadwigerCounterexample_ProbePointMasses
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Probe Point Masses -/

noncomputable section
namespace HadwigerCounterexample
open scoped BigOperators
open Matrix Module Submodule LinearMap Finset Function
variable {p : Shape} {n N : ℕ} {q t : Place p→ℕ}

def initCap (p : Shape) {n} (N : ℕ) (m : Mixer p n) (ε : ℝ) :=
  ∀ a : Pin p n N,pr (pairW (raw m N) (raw m N)) a.agree ≤ fee N ε (planRank a.sp)

def bySide (p : Shape) {n N} (w : Wgt (UnitType p n N))
    (m : Mixer p n) (c : ℝ) :=
  ∀ i x, mapW w (fun y => onSide y i) x ≤ c*raw m N x

def basisFrom (p : Shape) {n N} (x : UnitType p n N) (i : Bool)
    {q : Place p→ℕ} (Z : DTuple (p:=p) q N) :=
  ∀ z,Injective (Z z).mulVec ∧ colSp (Z z) ≤ imageP p x i (flipZ p z)

def ctot (p : Shape) (r : Place p→ℕ) := ∑ i,r i
abbrev Among (p : Shape) (n : ℕ) (q : Place p→ℕ) :=
  ∀ z, Mat (Row p n) (Fin (q z))
def csignal (p : Shape) {n} (i : Bool) {q : Place p → ℕ}
    (S : Among p n q) : WTuple (p:=p) q n :=
  fun z => IP p n i * S z

def poke (p : Shape) {n N} {q t : Place p → ℕ}
    (B : WTuple (p:=p) q n) (C : WTuple (p:=p) t n)
    (Z : DTuple (p:=p) q N) (A : DTuple (p:=p) t N)
    (x : UnitType p n N) :=
  ∀ z, images x (flipZ p z) * B z=Z z ∧ images x z * C z = A z

def heatRate (p : Shape) (n N : ℕ) (ε : ℝ) (x y : ℕ) :=
  bp (num (Row p n)* x+ 2*p.h*y)*fee N ε (x+y)

instance amongFintype (p : Shape) (n : ℕ) (r : Place p→ℕ) : Fintype (Among p n r) := by
  classical exact inferInstanceAs (Fintype (Among p n r))

end HadwigerCounterexample

end

end OAI
end

section
-- module Solutions.OAIQ430_HC.HadwigerCounterexample_FrameIntersectionCosts
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Frame Intersection Costs -/

noncomputable section
namespace HadwigerCounterexample
open Matrix LinearMap Module Submodule Finset Function
open scoped BigOperators
variable {p : Shape} {n N : ℕ} {I J K : Type} [Fintype I] [Fintype J] [Fintype K]

def ipPart (p : Shape) (n : ℕ) : Mat (Full p n) (Row p n) :=
  embedMat (.inl ·)

variable [DecidableEq I] [DecidableEq J] [DecidableEq K]

def expand (P : Mat I J) (K : Type) : Mat I K →ₗ[F] Mat K J where
  toFun X := Xᵀ*P
  map_add' a b := by rw [Matrix.transpose_add,Matrix.add_mul]
  map_smul' a b := by rw [Matrix.transpose_smul,Matrix.smul_mul]; rfl

def glimpsesBill (p : Shape) (k : ℕ) (H : ℝ) :=
  num (Place p)*(H*2*bp ((k:ℝ)-p.h))

end HadwigerCounterexample

end

end OAI
end

section
-- module Solutions.OAIQ430_HC.HadwigerCounterexample_SupportedPhaseLaws
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Supported Phase Laws -/

noncomputable section
namespace HadwigerCounterexample
open Matrix LinearMap Module Submodule Function Finset
open scoped BigOperators
variable {p : Shape} {n N r : ℕ} {T : Cov p N}

/-- Tables already fixed on population. bag M is total for convenience
but hypotheses on positive mass only apply on the indicated chart. -/
structure Bazaar (p : Shape) {N} (n r : ℕ) (T : Cov p N) where
  ix : UnitType p n N → Atlas p r T
  bag : (M : Atlas p r T) → Bool → UnitType p n N → Batch M N

namespace Bazaar

variable (s : Bazaar p n r T)

def opened (Δ : UnitType p n N → Ambient p N) (w : Wgt (UnitType p n N)) :=
  ∀ x,w x≠0 → standard (s.ix x) ∧ ∀ i,compFor (s.ix x)
    (s.bag (s.ix x) i x) (imageP p x i) (Δ x)

def chart (w : Wgt (UnitType p n N)) (M : Atlas p r T) :=
  subW w (fun x => s.ix x=M)

def pay (M G : Atlas p r T) (j : Bool) (S : Party)
    (y : UnitType p n N) : Batch M N × Batch G N :=
  (thermal p y S (src M),s.bag G j y)

end Bazaar

def loseA (_ : Shape) (N x y : ℕ) := bp (-((x:ℝ)+y)*N+0.01*N)
def prize (_ : Shape) (N x : ℕ) := bp (- ((x:ℝ)+0.5)*N)
def beat (N : ℕ) := bp (-0.245*N)
def selPrice (p : Shape) (r n N : ℕ) (H ε : ℝ) :=
  ∀ x y : ℕ,x≤2*r → y≤2*r → H*heatRate p n N ε x y≤loseA p N x y

end HadwigerCounterexample

end

end OAI
end

section
-- module Solutions.OAIQ430_HC.HadwigerCounterexample_OffsetFourierBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Offset Fourier Bounds -/

noncomputable section
namespace HadwigerCounterexample
open scoped BigOperators
open Matrix LinearMap Module Submodule Function Finset
variable {p : Shape} {n N r : ℕ} {T : Cov p N}

def chant (p : Shape) {n N} (Δ : UnitType p n N → Ambient p N) (S R : Party) :
    Wgt (UnitType p n N × UnitType p n N) :=
  fun x => wsign (tone p x.1 R (Δ x.2)+tone p x.2 S (Δ x.1))

variable {U V : Type} [AddCommGroup U] [AddCommGroup V] [Module F U] [Module F V]

def coupledB (A : U →ₗ[F] U →ₗ[F] F) (B : V →ₗ[F] V →ₗ[F] F) :
    U × V→ₗ[F] U × V→ₗ[F] F where
  toFun x := (A x.1).coprod (B x.2)
  map_add' x y := LinearMap.ext fun z => by
    simp only [Prod.fst_add,Prod.snd_add,map_add,LinearMap.add_apply,LinearMap.coprod_apply]
    abel
  map_smul' a x := LinearMap.ext fun z => by
    simp only [Prod.smul_fst,Prod.smul_snd,map_smul,RingHom.id_apply,LinearMap.smul_apply,
      LinearMap.coprod_apply,smul_add]

namespace Bazaar
variable (s : Bazaar p n r T)

abbrev Sales (p : Shape) {N} (n r : ℕ) (T : Cov p N) :=
  Atlas p r T → Atlas p r T → UnitType p n N → Prop

def discard {s : Bazaar p n r T} (w : Wgt (UnitType p n N)) (C : Sales p n r T) :=
  pr (pairW w w) (fun x => ¬ C (s.ix x.1) (s.ix x.2) x.2)

end Bazaar
end HadwigerCounterexample

end

end OAI
end

section
-- module Solutions.OAIQ430_HC.HadwigerCounterexample_SingletonPhaseTests
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Singleton Phase Tests -/

noncomputable section
namespace HadwigerCounterexample
open Matrix LinearMap Module Submodule Function Finset
open scoped BigOperators
variable {p : Shape} {n N r : ℕ} {T : Cov p N} {A : Type} [Fintype A]

namespace Bazaar
variable (s : Bazaar p n r T)

def frequent (w : Wgt (UnitType p n N)) (S : Party) (j : Bool)
    (M G : Atlas p r T) (y : UnitType p n N) :=
  prize p N (cells G) < mapW (s.chart w G) (s.pay M G j S) (s.pay M G j S y)

/-- fixed companion Z restrict frequent pair to this list of small Φ values -/
def bids (w : Wgt (UnitType p n N)) (S : Party) (i : Bool)
    (M G : Atlas p r T) (Z : Batch G N) : Finset (Batch M N) :=
  open scoped Classical in
  Finset.univ.filter (fun x => prize p N (cells G) < mapW (s.chart w G) (s.pay M G i S) (x,Z))

end Bazaar
end HadwigerCounterexample

end

end OAI
end

section
-- module Solutions.OAIQ430_HC.HadwigerCounterexample_AdditionalProbeBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Additional Probe Bounds -/

noncomputable section
namespace HadwigerCounterexample
open Matrix Module Submodule Function Finset
open scoped BigOperators
variable {I J K : Type} [Fintype I] [Fintype J] [Fintype K]

def moreMatrix_p0 {r : ℕ} (A : Mat I (Fin r)) (v : Vec I) : Mat I (Fin (r+1)) :=
  Matrix.of (fun i => Fin.cons (v i) (A i))

variable {p : Shape} {n N r : ℕ} {T : Cov p N}
variable {q : Place p → ℕ}

def growFmt (q : Place p→ℕ) (z : Place p) := fun i =>
  q i+(if i=z then 1 else 0)

def growing (A : DTuple (p:=p) q N) (z : Place p) (v : Vec (Fin N)) :
    DTuple (p:=p) (growFmt (p:=p) q z) N := fun i => by
  change Mat (Fin N) (Fin (q i+ if i=z then 1 else 0))
  by_cases h : i=z
  · rw [ite_eq_left h]; exact moreMatrix_p0 (A i) v
  rw [ite_eq_right h]; exact A i

namespace Bazaar
variable (s : Bazaar p n r T)

abbrev Catalog (p : Shape) {N} (T : Cov p N) (r : ℕ) (q : Place p→ℕ) :=
  (M : Atlas p r T) → Batch M N → Finset (DTuple (p:=p) q N)

def atList (s : Bazaar p n r T) (S : Party) (j : Bool)
    (A : DTuple (p:=p) q N) (F : Catalog p T r q) (x : UnitType p n N) :=
  let M := s.ix x
  thermal p x S A∈ F M (s.bag M j x)

def probed (p : Shape) {N} {q : Place p→ℕ} (A : DTuple (p:=p) q N) : Cov p N :=
  fun z => colSp (A z)

end Bazaar
end HadwigerCounterexample

end

end OAI
end

section
-- module Solutions.OAIQ430_HC.HadwigerCounterexample_AdaptiveRecordBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Adaptive Record Bounds -/

noncomputable section
namespace HadwigerCounterexample
open Matrix LinearMap Module Submodule Function Finset
open scoped BigOperators
variable {p : Shape} {n N r : ℕ} {T : Cov p N}

def quest (p : Shape) (r k n N : ℕ) (H ε : ℝ) :=
  ∀ x : ℕ,x≤2*r →
    bp ((x:ℝ)*N)*bp (0.51*k*N)*(H*heatRate p n N ε x k)≤bp (-0.2*N)

end HadwigerCounterexample

end

end OAI
end

section
-- module Solutions.OAIQ430_HC.HadwigerCounterexample_FiniteEntropy
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Finite Entropy -/

noncomputable section
namespace HadwigerCounterexample

open scoped BigOperators
open Real

variable {α : Type*} [Fintype α]

def negEnt (w : Wgt α) : ℝ := ∑ x, w x * Real.log (w x)
def midLaw (w v : Wgt α) : Wgt α := fun x => (w x + v x) * 2⁻¹

@[fun_prop] theorem tot_continuous : Continuous (tot : Wgt α → ℝ) := by
  unfold tot; fun_prop
@[fun_prop] theorem pr_continuous (p : α → Prop) : Continuous (pr (α := α) · p) := by
  unfold pr avg; fun_prop
@[fun_prop] theorem negEnt_continuous : Continuous (negEnt : Wgt α → ℝ) := by
  unfold negEnt
  exact continuous_finsetSum _ fun x _ => Real.continuous_mul_log.comp (continuous_apply x)

end HadwigerCounterexample

end

end OAI
end

section
-- module Solutions.OAIQ430_HC.HadwigerCounterexample_RelativeEntropy
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Relative Entropy -/

noncomputable section
namespace HadwigerCounterexample
open Finset Real
open scoped BigOperators
variable {A B C : Type} [Fintype A] [Fintype B] [Fintype C]

def lsupp (p q : Wgt A) := ∀ x,p x ≠ 0 → q x≠0

def tension (p q : Wgt A) := avg p (fun x => log (p x)-log (q x))
def varOne (p q : Wgt A) := ∑ x, |p x-q x|

end HadwigerCounterexample

end

end OAI
end

section
-- module Solutions.OAIQ430_HC.HadwigerCounterexample_ProjectionEnergy
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Projection Energy -/

noncomputable section
namespace HadwigerCounterexample
open Finset Real
open scoped BigOperators
variable {A B C : Type} [Fintype A] [Fintype B] [Fintype C]

def pour (q : Wgt A) (f : A→B) (w : Wgt B) :=
  fun i => q i * (w (f i) / mapW q f (f i))

def bucket (q : Wgt A) (f : A→B) (p : Wgt A) := pour q f (mapW p f)

end HadwigerCounterexample

end

end OAI
end

section
-- module Solutions.OAIQ430_HC.HadwigerCounterexample_EmpiricalInformation
attribute [-instance] _root_.OAI.HadwigerCounterexample.aFintype _root_.OAI.HadwigerCounterexample.amongFintype _root_.OAI.HadwigerCounterexample.cgFin _root_.OAI.HadwigerCounterexample.cgOneFin _root_.OAI.HadwigerCounterexample.instFKeys
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Empirical Information -/

noncomputable section
namespace HadwigerCounterexample
open Finset Real
open scoped BigOperators
variable {A B C J : Type} [Fintype A] [Fintype B] [Fintype C] [Fintype J]
variable [DecidableEq J] {l : ℕ}

abbrev Track (B : Type) (l : ℕ) := B→ Fin (l+1)
def traceTraj [DecidableEq B] (x : Fin l → B) :
    Track B l :=
  fun i => ⟨(univ.filter (fun j => x j=i)).card,
    Nat.lt_succ_of_le ((card_le_card (filter_subset ..)).trans_eq (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top))⟩

end HadwigerCounterexample

end

end OAI
end

section
-- module Solutions.OAIQ430_HC.HadwigerCounterexample_UnaryRecords
attribute [-instance] _root_.OAI.HadwigerCounterexample.aDefault _root_.OAI.HadwigerCounterexample.aFintype _root_.OAI.HadwigerCounterexample.amongFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Unary Records -/

noncomputable section
namespace HadwigerCounterexample
open Matrix LinearMap Module Submodule Finset
open scoped BigOperators
variable {p : Shape} {n N : ℕ}

/-- records of x indexed by opposite pin plan signs -/
abbrev Ledger {p : Shape} {n} (f : Plan p n) :=
  ∀ z, Mat (Fin (dim (f z))) (JointIdx p n)

instance fintypeLedger (f : Plan p n) : Fintype (Ledger f) := by
  classical
  letI (z : Place p) : Fintype (Mat (Fin (dim (f z))) (JointIdx p n)) := inferInstance
  exact inferInstance

def entries (f : Pin p n N) (x : UnitType p n N) : Ledger f.sp :=
  fun z => (pack (f.sp z))ᵀ * (f.target z)ᵀ * images x (flipZ p z)

variable {I : Type} [Fintype I]
namespace Volley
variable (v w : Volley p n I)

/-- Deterministic realization promise at two orientations. Can be required
only if both accept the specific parameter pair and their keys agree. -/
def promised (t : Tagging p I) (m : Mixer p n)
    (a b : Plan p n) (x y : UnitType p n N) :=
  v.legal t ∧ w.legal t ∧ v.roleMatch w t ∧
    ∃ Q : Cross p n, v.realized w t m Q ∧ w.realized v t m (reciprocal p Q) ∧
    rowAgree (v.frozen a t) Q (actual p x y) ∧
    rowAgree (w.frozen b t) (reciprocal p Q) (actual p y x)

end Volley
end HadwigerCounterexample

end

end OAI
end

section
-- module Solutions.OAIQ430_HC.HadwigerCounterexample_CollisionInequality
attribute [-instance] _root_.OAI.HadwigerCounterexample.aDefault _root_.OAI.HadwigerCounterexample.aFintype _root_.OAI.HadwigerCounterexample.amongFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Collision Inequality -/

noncomputable section
namespace HadwigerCounterexample
open Matrix Module Finset Filter
open scoped BigOperators
variable {p : Shape} {n N : ℕ}
variable {I A B : Type} [Fintype I] [Fintype A] [Fintype B]

def density (v w : Wgt I) := fun x => w x/v x
def overlap (v a b : Wgt I) :=
  avg v (fun x => density v a x*density v b x)

namespace Volley

/-- law of accepted keys as an unnormalized histogram -/
def hist (v : A → Volley p n I) (t : Tagging p I)
    (μ : Wgt (UnitType p n N)) (rho' : Wgt A) (U : A → UnitType p n N → Prop) :
    Wgt (Keys (p:=p) t N) :=
  fun u => avg rho' (fun a => pr μ (fun x => U a x ∧ (v a).keys t x=u))

end Volley

end HadwigerCounterexample

end

end OAI
end

section
-- module Solutions.OAIQ430_HC.HadwigerCounterexample_AtomFlavors
attribute [-instance] _root_.OAI.HadwigerCounterexample.aDefault _root_.OAI.HadwigerCounterexample.aFintype _root_.OAI.HadwigerCounterexample.amongFintype _root_.OAI.HadwigerCounterexample.cgFin _root_.OAI.HadwigerCounterexample.cgOneFin _root_.OAI.HadwigerCounterexample.fintypeLedger _root_.OAI.HadwigerCounterexample.instFKeys
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Atom Flavors -/

noncomputable section
namespace HadwigerCounterexample
open Matrix LinearMap Finset Function
open scoped BigOperators
variable {g r n b : ℕ} {p : Shape}

abbrev Flavor (g : ℕ) := Option (Option (Finset (Tag g × Tag g)))
namespace Flavor
abbrev full {g : ℕ} : Flavor g := none
abbrev sharedOnly {g : ℕ} : Flavor g := some none
abbrev pure {g : ℕ} (s : Finset (Tag g × Tag g)) : Flavor g := some (some s)

def keeps (f : Flavor g) (x : Tag g) (y : Block g) : Prop :=
  match f,y with
  | none, .inl (i,_) => allowed i x
  | some none,.inl _ => False
  | some (some s),.inl (i,j) => allowed i x ∧ (i,j) ∈ s
  | some (some _), .inr v => v≠0
  | _, .inr _ => True
instance instDecidableKeeps (f : Flavor g) (x : Tag g) (y : Block g) : Decidable (keeps f x y) :=
  Classical.propDecidable _

end Flavor

abbrev Knobs (g n : ℕ) := Block g → Vec (Fin n)

def lit (f : Flavor g) (x : Tag g) (y : Knobs g n) : Base g n :=
  fun i => if f.keeps x i.1 then y i.1 i.2 else 0

def useAtom (p : Shape) {n : ℕ} (x : Tag p.g) (s : Label p.b) (f : Flavor p.g)
    (y : Knobs p.g n) := atom p x s (lit f x y)

abbrev ProbeIdx (g : ℕ) := (Tag g × Tag g)⊕Unit
abbrev Digest (g : ℕ) := Vec (ProbeIdx g)

def asBlock (i : ProbeIdx g) : Block g := i.elim (fun q => Block.O q.1 q.2) (fun _ => Block.S)

def zget (y : Vec (Fin n)) (i : ℕ) := if h:i<n then y ⟨i,h⟩ else 0
def tested (r : ℕ) (y : Vec (Fin n)) :=
  ∑ i : Fin r,zget y (2*i.val)*zget y (2*i.val+1)

def scan (p : Shape) {n} (l : Tag p.g) (f : Flavor p.g) (x : Knobs p.g n) :
    Digest p.g :=
  fun i => if Flavor.keeps f l (asBlock i) then tested p.r (x (asBlock i)) else 0

namespace Digest
variable (q : Digest g)

def feasible (l : Tag g) (f : Flavor g) := ∀ i,¬ Flavor.keeps f l (asBlock i) → q i=0

def diagO := ∑ d : Tag g, ∑ t,q (.inl (d,t))
def sumBit := q.diagO+q (.inr ())

end Digest

def dialed (p : Shape) {n} (l : Tag p.g) (f : Flavor p.g) (x : Knobs p.g n) :=
  (scan p l f x).sumBit

def spins (p : Shape) (n : ℕ) : Wgt (Knobs p.g n) := draws (Block p.g) unif

/-- Projection notation for conditioning on a specified (possible)
diagnostic or diagonal only. -/
def scopedBit (p : Shape) (n : ℕ) (l : Tag p.g) (f : Flavor p.g) (q : F) :
    Wgt (Knobs p.g n) := onW (spins p n) (fun x => dialed p l f x=q)
def scopedScan (p : Shape) (n : ℕ) (l : Tag p.g) (f : Flavor p.g) (z : Digest p.g) :
    Wgt (Knobs p.g n) := onW (spins p n) (fun x => scan p l f x=z)

end HadwigerCounterexample

end

end OAI
end

section
-- module Solutions.OAIQ430_HC.HadwigerCounterexample_PhaseMomentBounds
attribute [-instance] _root_.OAI.HadwigerCounterexample.Flavor.instDecidableKeeps _root_.OAI.HadwigerCounterexample.aDefault _root_.OAI.HadwigerCounterexample.aFintype _root_.OAI.HadwigerCounterexample.amongFintype _root_.OAI.HadwigerCounterexample.fintypeLedger
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Phase Moment Bounds -/

noncomputable section
namespace HadwigerCounterexample
open Matrix LinearMap Module Finset
open scoped BigOperators
variable {p : Shape} {n N : ℕ} {A : Type} [Fintype A]

def sweep (p : Shape) {N} (f : A→Ambient p N) (w g : Wgt A) (S : Party)
    (q : PhasePair p N) := avg w (fun x => g x*wsign (joinPhase p q S (f x)))

def exponentErr (p : Shape) (m b : ℕ) (c : ℝ) :=
  let s := 2^m*(2*b)
  ((2:ℝ)^s*(2:ℝ)^s)*c^b + bp (- (p.h:ℝ)*b/2)

def noSweepBudget (p : Shape) (N m b r : ℕ) (c ψ H : ℝ) :=
  bp (2*(r:ℝ)*num (Comp p.g)*N) * (H*chanPrice p^2 *(exponentErr p m b c/ψ^(2^m*(2*b))))

end HadwigerCounterexample

end

end OAI
end

section
-- module Solutions.OAIQ430_HC.HadwigerCounterexample_PhaseAlternativeSupport
attribute [-instance] _root_.OAI.HadwigerCounterexample.Flavor.instDecidableKeeps _root_.OAI.HadwigerCounterexample.fintypeLedger
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Phase Alternative Support -/

noncomputable section
namespace HadwigerCounterexample
open Matrix LinearMap Module Submodule Function Finset
open scoped BigOperators
variable {p : Shape} {n N r : ℕ}
variable {A : Type} [Fintype A]

def rhUp (H c : ℝ) := (c/2)⁻¹ * H

def scaleBill (p : Shape) (n N k : ℕ) (H : ℝ) :=
  (num (Place p)*2)*(H*2 * bp (num (Row p n)+k-N))

def tonalMix (p : Shape) {n N} (Δ : UnitType p n N → Ambient p N) (w) :=
  ∀ S R,S ≠ 0 ∨ R ≠ 0 → |pitch p Δ w S R|< 0.005
def tonalTiny (p : Shape) {n N} (Δ : UnitType p n N → Ambient p N) (w : Wgt (UnitType p n N)) (d : ℕ) :=
  ∃ S : Cov p N, cdim p S≤d ∧ (∀ x,w x≠0 → covered p S (Δ x)) ∧
    ∀ i : Bool,∀ R : Party, |pitch p Δ w (unary i) R|≤bp (-0.24*N)

def preGlimpse (x : UnitType p n N) (C : Cov p N) :=
  ∀ i,glimpse p x i (q:=fun z => dim (C z)) (fun z => pack (C z))

end HadwigerCounterexample

end

end OAI
end

section
-- module Solutions.OAIQ430_HC.HadwigerCounterexample_TesterSummaryMass
attribute [-instance] _root_.OAI.HadwigerCounterexample.fintypeLedger
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Tester Summary Mass -/

noncomputable section
namespace HadwigerCounterexample
open Matrix LinearMap Module Finset Function
open scoped BigOperators
variable {p : Shape} {r n : ℕ} {A I : Type} [Fintype A] [Fintype I]
variable [DecidableEq I]

def scanPrice (p : Shape) : ℝ := (1/4)^Fintype.card (ProbeIdx p.g)

def canDial (p : Shape) (l : Tag p.g) (f : Flavor p.g) (q : F) :=
  ∃ v : Digest p.g, v.feasible l f ∧ v.sumBit=q

end HadwigerCounterexample

end

end OAI
end

section
-- module Solutions.OAIQ430_HC.HadwigerCounterexample_AmbientBatchSlots
attribute [-instance] _root_.OAI.HadwigerCounterexample.fintypeLedger
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Ambient Batch Slots -/

noncomputable section
namespace HadwigerCounterexample
open Matrix Module LinearMap Finset Function
open scoped BigOperators
variable {I J G A B : Type} [Fintype I] [Fintype J] [Fintype A] [Fintype B]
variable {p : Shape} {n N : ℕ}

abbrev PlusRack (I : Type) (N : ℕ) := Mat (Fin N) I
abbrev Rack (I : Type) (N : ℕ) := PlusRack I N × PlusRack I N
def sectionR {I J : Type} (f : J→I) (x : Rack I N) : Rack J N :=
  ((x.1).submatrix _root_.id f, (x.2).submatrix _root_.id f)
abbrev Route (I G : Type) := I → G
abbrev Port {I G : Type} (f : Route I G) (g : G) := {i:I//f i=g}
abbrev Network {I G : Type} (f : Route I G) (N : ℕ) := ∀ i,Rack (Port f i) N

variable [Fintype G]
variable [DecidableEq I] [DecidableEq J] [DecidableEq G]
variable {f : Route I G}

def rackEquiv (f : Route I G) (N : ℕ) : Rack I N ≃ Network f N where
  toFun x i := sectionR Subtype.val x
  invFun x := (Matrix.of (fun j i => (x (f i)).1 j ⟨i,rfl⟩),
    Matrix.of (fun j i => (x (f i)).2 j ⟨i,rfl⟩))
  left_inv x := by apply Prod.ext <;> rfl
  right_inv x := by
    funext i; apply Prod.ext <;>
      · ext j ⟨y,rfl⟩; rfl

abbrev GeoM (f : Route I G) := ∀ i,Mat (Port f i) (Port f i)

def gramPart {N} (A : GeoM f) (x : Rack I N) :=
  ∀ i,let P:=rackEquiv f N x i;
    P.1ᵀ*P.2=A i
def injPart (f : Route I G) {N} (x : Rack I N) :=
  ∀ i,let P:=rackEquiv f N x i;
    Injective P.1.mulVec ∧ Injective P.2.mulVec

def bothPart {N} (A : GeoM f) (x : Rack I N) := ∀ i, gramGood (A i) (rackEquiv f N x i)

def scoreR {I : Type} (x : Rack I N) (i j : I) : F := (x.1ᵀ*x.2) i j

def rackStation (A : GeoM f) (N : ℕ) : Wgt (Rack I N) := unifOn (bothPart A)
def rackWave (A : GeoM f) (N : ℕ) : Wgt (Rack I N) := unifOn (gramPart A)

def netSize (f : Route I G) := ∑ i : G,num (Port f i)*num (Port f i)
def netFact (f : Route I G) :=
  (4:ℝ)^(Fintype.card G)*bp (netSize f)

end HadwigerCounterexample

end

end OAI
end

section
-- module Solutions.OAIQ430_HC.HadwigerCounterexample_IndependentColumnBatches
attribute [-instance] _root_.OAI.HadwigerCounterexample.fintypeLedger
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Independent Column Batches -/

noncomputable section
namespace HadwigerCounterexample
open scoped BigOperators
open Matrix LinearMap Module Finset Function
variable {I G J A B : Type} [Fintype I] [Fintype G] [Fintype J] [Fintype A] [Fintype B]
variable [DecidableEq I] [DecidableEq J] [DecidableEq G]
variable {p : Shape} {n N : ℕ}

def rawC (m : Mixer p n) (N : ℕ) : Wgt (Oframe p n N) := unifOn (FramesAt (gramCond m))
def peer (p : Shape) {n} (A B : Mat (Row p n) I) {N} (x : Oframe p n N) :
    Rack I N := (primary x.1*A,primary x.2*B)

abbrev Forum (p : Shape) (n N : ℕ) (G : Type) := G → Oframe p n N
def forumLaw (m : Mixer p n) (N : ℕ) : Wgt (Forum p n N G) :=
  prodW (fun (_ : G) => rawC m N)

abbrev NomQuery (p : Shape) (n : ℕ) {I G : Type} (g : Route I G) :=
  ∀ i, Mat (Row p n) (Port g i)
variable {g : Route I G}
def peekR (p : Shape) {n} (g : Route I G) (A B : NomQuery p n g)
    {N} (x : Forum p n N G) :=
  (rackEquiv g N).symm (fun i => peer p (A i) (B i) (x i))
def database (m : Mixer p n) (A B : NomQuery p n g) : GeoM g :=
  fun i => pullM (A i) (B i) (selfM p n m.mixM)

/-- Merge two endpoints of raw frame. Assign ports according
to their endpoint. -/
abbrev Ports (p : Shape) := Bool × Comp p.g
def mergeR (p : Shape) {n N} :
    UnitType p n N ≃ Forum p n N (Ports p) where
  toFun x i := onSide x i.1 i.2
  invFun x := (fun i => x (true,i),fun i => x (false,i))
  left_inv _ := rfl
  right_inv x := funext fun i => by rcases i with ⟨c|c,z⟩ <;> rfl

end HadwigerCounterexample

end

end OAI
end

section
-- module Solutions.OAIQ430_HC.HadwigerCounterexample_BoundedQueryTemplates
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Bounded Query Templates -/

noncomputable section
namespace HadwigerCounterexample
open scoped BigOperators
open Matrix Module LinearMap Function
variable {p : Shape} {n N : ℕ} {I : Type} [Fintype I] [DecidableEq I]

structure Template (p : Shape) (I : Type) where
  aim : I→Bool
  t : Tagging p I
  s : I→Label p.b
  f : I→Flavor p.g

abbrev Inputs (p : Shape) (n : ℕ) (I : Type) := I → Knobs p.g n

namespace Template
variable (v : Template p I)

def draw (y : Inputs p n I) : Volley p n I where
  obj := v.aim
  sel := v.s
  par i := lit (v.f i) (v.t i) (y i)

def state (q : I→F) (n : ℕ) : Wgt (Inputs p n I) :=
  prodW (fun i : I => scopedBit p n (v.t i) (v.f i) (q i))
end Template

abbrev KeySlots (p : Shape) (t : Tagging p I) := Σ i, TagStar (t i)

def scatter (t : Tagging p I) (N : ℕ) : Keys (p:=p) t N ≃ Rack (KeySlots p t) N where
  toFun x := (Matrix.of (fun j i => x i.1 i.2 true j),Matrix.of (fun j i => x i.1 i.2 false j))
  invFun x := fun i j b => if b then x.1.col ⟨i,j⟩ else x.2.col ⟨i,j⟩
  left_inv x := by funext i j b; cases b <;> rfl
  right_inv x := by apply Prod.ext <;> rfl

def globPort (p : Shape) (t : Tagging p I) (q : I→Bool) :
    Route (KeySlots p t) (Ports p) :=
  fun x => (q x.1,x.2.val)

def nomAsk (t : Tagging p I) (v : Volley p n I) :
    NomQuery p n (globPort p t v.obj) :=
  fun _ => Matrix.of (fun i j => v.rayAt j.val.1 i)

def ownPort (t : Tagging p I) : Route (KeySlots p t) (Comp p.g) := fun x => x.2.val
def ownMap (t : Tagging p I) (q : I→F) : GeoM (ownPort (p:=p) t) :=
  fun _ => Matrix.diagonal (fun i => q i.val.1)
def ownPart (t : Tagging p I) (q : I→F) {N : ℕ}
    (x : Keys (p:=p) t N) :=
  gramPart (ownMap (p:=p) t q) (scatter t N x)
def lawNu (p : Shape) (N : ℕ) (t : Tagging p I) (q : I→F) :
    Wgt (Keys (p:=p) t N) := unifOn (ownPart (p:=p) t q)

def ownOne (p : Shape) {N : ℕ} (l : Tag p.g) (q : F) (x : AtomKey (p:=p) l N) :=
  ∀ i,dotProduct (x i true) (x i false) = q
def lawOmega (p : Shape) (N : ℕ) (l : Tag p.g) (q : F) :
    Wgt (AtomKey (p:=p) l N) := unifOn (ownOne p l q)

end HadwigerCounterexample

end

end OAI
end

section
-- module Solutions.OAIQ430_HC.HadwigerCounterexample_CrossPatternCorrelation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Cross Pattern Correlation -/

noncomputable section
namespace HadwigerCounterexample
open scoped BigOperators
open Matrix Module LinearMap Submodule Finset Function
variable {p : Shape} {n N : ℕ}
variable {I J K A B : Type} [Fintype I] [Fintype J] [Fintype K]
variable [DecidableEq I] [DecidableEq J] [DecidableEq K]

def layerPhase (M : Mat I J) (N : ℕ) :
    PlusRack I N →ₗ[F] (PlusRack J N →ₗ[F] F) where
  toFun X := mpair (X*M)
  map_add' X Y := LinearMap.ext fun Z => by rw [Matrix.add_mul,mpair_add,LinearMap.add_apply]
  map_smul' a X := LinearMap.ext fun Z => by rw [Matrix.smul_mul,mpair_smul,LinearMap.smul_apply]; rfl

def phasedBy (M : Mat I I) (x : Rack I N) : ℝ := wsign (layerPhase M N x.1 x.2)
def upliftR (f : J→I) (x : PlusRack J N) : PlusRack I N := x * (embedMat f)ᵀ

def pairedShift {I J K : Type} [Fintype J] [Fintype K] [DecidableEq I] (f : J→I) (g : K→I)
    (P : PlusRack J N) (Q : PlusRack K N) := (upliftR f P,upliftR g Q)

end HadwigerCounterexample

end

end OAI
end

section
-- module Solutions.OAIQ430_HC.HadwigerCounterexample_GramCharacterExpansion
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Gram Character Expansion -/

noncomputable section
namespace HadwigerCounterexample
open Matrix Module LinearMap Function Finset
open scoped BigOperators
variable {I J : Type} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
  {N : ℕ}

def vectorPhase (x y : Vec I) := wsign (dotProduct x y)

abbrev Rail (I : Type) := Finset (I × I)
variable {E : Rail I}

def ledgerM (E : Rail I) (v : Vec E) : Mat I I :=
  Matrix.of (fun x y => if h:(x,y)∈E then v ⟨(x,y),h⟩ else 0)
def railsM (E : Rail I) (M : Mat I I) : Vec E := fun i => M i.val.1 i.val.2

def traced (x : Rack I N) (E : Rail I) (Z : Vec E) :=
  railsM E (x.1ᵀ*x.2)=Z

def withinRail (M : Mat I I) (E : Rail I) :=
  ∀ i j, (i,j)∉ E→M i j=0

def crowded (g : Route I J) : Rail I := Finset.univ.filter (fun x => g x.1=g x.2)

def directions (g : Route I J) (A : GeoM g) : Vec (crowded g) := fun x =>
  A (g x.val.1) ⟨x.val.1,rfl⟩ ⟨x.val.2,(mem_filter.mp x.property).2.symm⟩

end HadwigerCounterexample

end

end OAI
end

section
-- module Solutions.OAIQ430_HC.HadwigerCounterexample_CrossPatternCounting
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Cross Pattern Counting -/

noncomputable section
namespace HadwigerCounterexample
open Matrix Module LinearMap Submodule Function Finset
open scoped BigOperators

variable {I J T L : Type} [Fintype I] [Fintype J] [Fintype T] [Fintype L]
  [DecidableEq I] [DecidableEq J] [DecidableEq T] [DecidableEq L]

abbrev Avenue (I J : Type) := Mat (I×J) (I×J)
def interDraw (M : Avenue I J) :=
  ∀ i u v,M (i,u) (i,v)=0

def disperses (f : T → I × J) (g : L → I × J) :=
  ∀ i j,(f i).1≠(g j).1
def arcPeak (M : Avenue I J) (t : ℕ) :=
  ∃ (f g : Fin t→ I × J), disperses f g ∧ Injective (M.submatrix f g).mulVec

def peak (M : Avenue I J) : ℕ := sSup {t | arcPeak M t}

abbrev Incident (I J : Type) := Mat J (I×J)
def took (M : Avenue I J) (i : I) : Incident I J × Incident I J :=
  (M.submatrix (fun j => (i,j)) _root_.id, (Mᵀ.submatrix (fun j => (i,j)) _root_.id))

abbrev Bag (I J : Type) := (I × J) × Incident I J × Incident I J
def peakExpense (I J : Type) [Fintype I] [Fintype J] (t : ℕ) :=
  2*t * ((1+2*num J)* num I*num J)

end HadwigerCounterexample

end

end OAI
end

section
-- module Solutions.OAIQ430_HC.HadwigerCounterexample_BatchCharacters
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Batch Characters -/

noncomputable section
namespace HadwigerCounterexample
open scoped BigOperators
open Matrix Module LinearMap Function Finset
variable {I J A B : Type} [Fintype I] [Fintype J] [Fintype A] [Fintype B]
variable [DecidableEq I] [DecidableEq J] [DecidableEq A] [DecidableEq B]
variable {n N t : ℕ}

def led (i : I) (x : Rack (I×J) N) := sectionR (fun j => (i,j)) x
def relay (I J : Type) [Fintype I] [Fintype J] (N) :
    Rack (I×J) N ≃ (I → Rack J N) where
  toFun x i := led i x
  invFun x := (Matrix.of (fun i j => (x j.1).1 i j.2), Matrix.of (fun i j => (x j.1).2 i j.2))
  left_inv x := by apply Prod.ext <;> rfl
  right_inv x := funext fun _ => Prod.ext rfl rfl

def heard (T : A → I×J) := Finset.univ.image (Prod.fst ∘ T)

def phot (P : I→Rack J N→Prop) (x : Rack (I×J) N) :=
  ∏ i:I,ind (P i (led i x))

end HadwigerCounterexample

end

end OAI
end

section
-- module Solutions.OAIQ430_HC.HadwigerCounterexample_RepeatedQueryBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Repeated Query Bounds -/

noncomputable section
namespace HadwigerCounterexample
open Matrix Module LinearMap Submodule Function Finset
open scoped BigOperators
variable {I J G : Type} [Fintype I] [Fintype J] [Fintype G]
variable [DecidableEq I] [DecidableEq J] [DecidableEq G]
variable {N : ℕ}

def cInside (g : Route (I×J) G) :=
  (crowded g).filter (fun i => i.1.1=i.2.1)

end HadwigerCounterexample

end

end OAI
end

section
-- module Solutions.OAIQ430_HC.HadwigerCounterexample_IndependentWeightCorrelation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Independent Weight Correlation -/

noncomputable section
namespace HadwigerCounterexample
open Matrix Module LinearMap Submodule Function Finset
open scoped BigOperators
variable {I J T : Type} [Fintype I] [Fintype J] [Fintype T]
variable [DecidableEq I] [DecidableEq J] [DecidableEq T]
variable {N : ℕ}

def brightProd (f : I→ Wgt (Rack J N)) (x : Rack (I × J) N) :=
  ∏ i:I,f i (led i x)

end HadwigerCounterexample

end

end OAI
end

section
-- module Solutions.OAIQ430_HC.HadwigerCounterexample_ConditionedBatchLaws
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Conditioned Batch Laws -/

noncomputable section
namespace HadwigerCounterexample
open scoped BigOperators
open Matrix Module LinearMap Submodule Function Finset
variable {I J G H : Type} [Fintype I] [Fintype J] [Fintype G] [Fintype H]
variable [DecidableEq I] [DecidableEq J] [DecidableEq G]
variable {N : ℕ}

def street (g : Route (I×J) G) (i : I) : Route J G := fun j => g (i,j)
def condLane (g : Route (I×J) G) (i : I) (z : G) (k : Port (street g i) z) :
    Port g z := ⟨(i,k.val),k.property⟩
def laneM {g : Route (I×J) G} (Z : GeoM g) (i : I) :
    GeoM (street g i) :=
  fun z => (Z z).submatrix (condLane g i z) (condLane g i z)

variable {g : Route (I×J) G}

def crossroads (g : Route (I×J) G) :=
  (crowded g)\(cInside g)
def outsideZ (Z : GeoM g) : Vec (crossroads g) :=
  fun x => directions g Z ⟨x.val,Finset.sdiff_subset x.property⟩

def condMean (p : H→Prop) (f : Wgt H) :=
  avg unif (fun x => ind (p x)*f x)

def twinkle (_ : Route (I×J) G) (k : ℝ) (N : ℕ) :=
  num G * (2*bp (k-N))+bp (-(N:ℝ)/2)

end HadwigerCounterexample

end

end OAI
end

section
-- module Solutions.OAIQ430_HC.HadwigerCounterexample_RepeatedBatchLaws
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Repeated Batch Laws -/

noncomputable section
namespace HadwigerCounterexample
open Matrix Module LinearMap Submodule Finset Function
open scoped BigOperators
variable {I J G : Type} [Fintype I] [Fintype J] [Fintype G] [DecidableEq I]
variable [DecidableEq J] [DecidableEq G] {p : Shape} {n N : ℕ}

def tied (f : Route I G) (J : Type) : Route (J×I) G := f ∘ Prod.snd
variable {f : Route I G}

def pooled (A : J → NomQuery p n f) : NomQuery p n (tied f J) :=
  fun g => Matrix.of (fun i j => A j.val.1 g i (⟨j.val.2,j.property⟩))

end HadwigerCounterexample

end

end OAI
end

section
-- module Solutions.OAIQ430_HC.HadwigerCounterexample_GroupedQueryIndependence
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Grouped Query Independence -/

noncomputable section
namespace HadwigerCounterexample
open scoped BigOperators
open Matrix LinearMap Module Submodule Function Finset
variable {p : Shape} {n N : ℕ}
variable {I J G : Type} [Fintype I] [Fintype J] [Fintype G]
variable [DecidableEq I] [DecidableEq J] [DecidableEq G]

instance knFin (g n : ℕ) : Fintype (Knobs g n) := inferInstanceAs (Fintype (Knobs g n))
def freePart (p : Shape) {n} (x : Knobs p.g n) := x Block.Z

def frozenZ (p : Shape) {n} (P : Knobs p.g n → Prop) :=
  ∀ x y, (P x ↔ P (x+Pi.single Block.Z y))

def freeNet (p : Shape) {n} (x : J→ Inputs p n I) :
    PlusRack (J × I) n :=
  Matrix.of (fun i j => freePart p (x j.1 j.2) i)

def bloom (p : Shape) {n} (x : J→Inputs p n I) :=
  Injective (freeNet p x).mulVec

variable {g : Route I G}

namespace Template

variable (v : Template p I)

def queryLaw (x : Inputs p n I)
    {g : Route (KeySlots p v.t) G} : NomQuery p n g :=
  fun _ => Matrix.of (fun j k => (v.draw x).rayAt k.val.1 j)

end Template

end HadwigerCounterexample

end

end OAI
end

section
-- module Solutions.OAIQ430_HC.HadwigerCounterexample_QueryConcentration
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Query Concentration -/

noncomputable section
namespace HadwigerCounterexample
open Module Matrix Finset Function
open scoped BigOperators
variable {p : Shape} {n N : ℕ} {I G A K D : Type} [Fintype I] [Fintype G] [Fintype A]
variable [Fintype K] [Fintype D] [DecidableEq I] [DecidableEq G] [DecidableEq K]

structure Program (p : Shape) (n : ℕ) {I G : Type} (g : Route I G) (A : Type) where
  left : A→NomQuery p n g
  right : A→NomQuery p n g

variable {g : Route I G}

namespace Program
variable (s : Program p n g A)

def free (x : K→ A) :=
  (∀ i,Injective (pooled (s.left ∘ x) i).mulVec)∧
  (∀ i,Injective (pooled (s.right ∘ x) i).mulVec)

def showKey (x : A) (o : Forum p n N G) :=
  peekR p g (s.left x) (s.right x) o

def oexpect (w : Wgt A) (F : A → Rack I N → ℝ) (o : Forum p n N G) :=
  avg w (fun x => F x (s.showKey x o))
end Program

namespace Program
variable {s : Program p n g A}

def oFreq (w : Wgt A) (F : A → Rack I N→Prop) (o : Forum p n N G)
    (s : Program p n g A) :=
  pr w (fun i => F i (s.showKey i o))

end Program
end HadwigerCounterexample

end

end OAI
end

section
-- module Solutions.OAIQ430_HC.HadwigerCounterexample_DependentPairConcentration
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Dependent Pair Concentration -/

noncomputable section
namespace HadwigerCounterexample
open Matrix LinearMap Module Submodule Finset Function
open scoped BigOperators
variable {X Y A B : Type} [Fintype X] [Fintype Y] [Fintype A] [Fintype B]

def approxData (μ : Wgt X) (f : X→ Wgt A) (c d : ℝ) :=
  ∀ h : Wgt A,(∀ x,|h x|≤1) →
    pr μ (fun x => c ≤ |avg (f x) h-avg (mixW μ f) h|)≤d

def thinData (μ : Wgt X) (f : X→ Wgt A) (τ c d : ℝ) :=
  ∀ P : A → Prop,pr (mixW μ f) P≤τ → pr μ (fun x => c≤pr (f x) P)≤d

end HadwigerCounterexample

end

end OAI
end

section
-- module Solutions.OAIQ430_HC.HadwigerCounterexample_ConcentrationScales
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Concentration Scales -/

noncomputable section
namespace HadwigerCounterexample

open Matrix LinearMap Module Finset Filter Real Function
open scoped BigOperators Topology
variable {X : Type*}

variable {p : Shape} {M n N : ℕ}
variable {I J K G A B : Type} [Fintype I] [Fintype J] [Fintype K] [Fintype G]
variable [DecidableEq I] [DecidableEq J] [DecidableEq K] [DecidableEq G]
variable [Fintype A] [Fintype B]
variable {g : Route J G}

namespace Program
variable {s : Program p n g A}

/-- empirical input-and-image law -/
def makeData (s : Program p n g A) (w : Wgt A) (o : Forum p n N G) :
    Wgt (A×Rack J N) :=
  mapW w (fun x => (x,s.showKey x o))
end Program
end HadwigerCounterexample

end

end OAI
end

section
-- module Solutions.OAIQ430_HC.HadwigerCounterexample_EndpointTemplateConcentration
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Endpoint Template Concentration -/

noncomputable section
namespace HadwigerCounterexample
open Filter Real Finset Matrix Function
open scoped BigOperators
variable {p : Shape} {M n N : ℕ}
variable {I J K G : Type} [Fintype I] [Fintype J] [Fintype K] [Fintype G]
variable [DecidableEq I] [DecidableEq J] [DecidableEq K] [DecidableEq G]

namespace Template

variable (v : Template p I)

def callP (n : ℕ) (g : Route (KeySlots p v.t) G) : Program p n g (Inputs p n I) :=
  ⟨fun x => queryLaw v x,fun x => queryLaw v x⟩
def singleP (n : ℕ) := callP v n (ownPort (p:=p) v.t)
def doubleP (n : ℕ) := callP v n (globPort p v.t v.aim)

def callOne (i) (x : Knobs p.g n) (o : Orient p n N) :=
  keyOne p (v.t i) (v.s i) (lit (v.f i) (v.t i) x) o

end Template
end HadwigerCounterexample

end

end OAI
end

section
-- module Solutions.OAIQ430_HC.HadwigerCounterexample_PairedTemplateConcentration
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Paired Template Concentration -/

noncomputable section
namespace HadwigerCounterexample
open Filter Real Finset Matrix Function
open scoped BigOperators
variable {p : Shape} {M n N : ℕ}
variable {I J K G : Type} [Fintype I] [Fintype J] [Fintype K] [Fintype G]
variable [DecidableEq I] [DecidableEq J] [DecidableEq K] [DecidableEq G]

namespace Template

variable (v : Template p I) (z : Template p J)

abbrev Datum (v : Template p I) (n N : ℕ) :=
  Inputs p n I×Rack (KeySlots p v.t) N

instance inpFinite (p : Shape) (I : Type) [Fintype I] [DecidableEq I] (n : ℕ) :
    Fintype (Inputs p n I) := inferInstanceAs (Fintype (I→Knobs p.g n))
instance keySlotFinite (v : Template p I) : Fintype (KeySlots p v.t) := inferInstance
instance datumFinite (v : Template p I) (n N : ℕ) : Fintype (v.Datum n N) := inferInstance

end Template
end HadwigerCounterexample

end

end OAI
end

section
-- module Solutions.OAIQ430_HC.HadwigerCounterexample_TemplateTypicality
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Template Typicality -/

noncomputable section
namespace HadwigerCounterexample
open Filter Real Finset Matrix Function
open scoped BigOperators
variable {p : Shape} {M n N : ℕ}
variable {I J G : Type} [Fintype I] [DecidableEq I]

namespace Template
variable (v : Template p I)

def collect (p : Shape) (v : Template p I) (f : J→I) : Template p J :=
  ⟨v.aim ∘ f, v.t ∘ f, v.s ∘ f,v.f ∘ f⟩

abbrev PosA (v : Template p I) := {i:I//v.aim i}
abbrev PosB (v : Template p I) := {i:I//¬v.aim i}
def atA := collect p v (Subtype.val : v.PosA→I)
def atB := collect p v (Subtype.val : v.PosB→I)

def forkI (n : ℕ) : Inputs p n I ≃ Inputs p n v.PosA × Inputs p n v.PosB :=
  Equiv.piEquivPiSubtypeProd (fun i:I => v.aim i) (fun _ => _)
def forkK (N : ℕ) : Keys (p:=p) v.t N ≃ Keys (p:=p) v.atA.t N × Keys (p:=p) v.atB.t N :=
  Equiv.piEquivPiSubtypeProd (fun i:I => v.aim i) (fun i => AtomKey (p:=p) (v.t i) N)

def sampleAll (u : I→Wgt (Knobs p.g n))
    (T : Inputs p n I → Keys (p:=p) v.t N → ℝ)
    (x : UnitType p n N) :=
  avg (prodW u) (fun i => T i ((v.draw i).keys v.t x))

def connectT (T : Inputs p n I → Keys (p:=p) v.t N → ℝ)
    (x : v.atA.Datum n N × v.atB.Datum n N) :=
  T ((v.forkI n).symm (x.1.1,x.2.1))
    ((v.forkK N).symm ((scatter v.atA.t N).symm x.1.2,(scatter v.atB.t N).symm x.2.2))

end Template
end HadwigerCounterexample

end

end OAI
end

section
-- module Solutions.OAIQ430_HC.HadwigerCounterexample_HistogramEnergyScales
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Histogram Energy Scales -/

noncomputable section
namespace HadwigerCounterexample
open Finset Real Filter
open scoped BigOperators Topology
variable {I J G : Type} [Fintype I] [Fintype J] [Fintype G]
variable [DecidableEq I] [DecidableEq J] [DecidableEq G]

structure TollBar (M : ℕ) (C : ℝ) (I J G : Type) [Fintype I] [Fintype J]
    [Fintype G] [DecidableEq G] (g : Route J G) (n l : ℕ)
    (r u E V : ℝ) : Prop where
  pos : 0<l
  frame : ∀ i : G, 2*num (Port (tied g (Fin l)) i)-↑(M*n) ≤ -1
  peak : peakExpense (Fin l) J 1+ (-(↑(M*n):ℝ)/2+2*u) ≤0
  cap :
    bp (C*(M*n:ℕ))*( (4:ℝ)^Fintype.card G *bp (num (Fin l)*num J*num J) *
      (num (Fin l × J)+1)) ≤ bp (E*l)
  charge :
    r*log ((l:ℝ)+1)+(E*l + bp (num (Fin l)*num I - n)*u*l+1)*log 2 ≤
      l*V

end HadwigerCounterexample

end

end OAI
end

section
-- module Solutions.OAIQ430_HC.HadwigerCounterexample_UnfilteredHistogramEnergy
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Unfiltered Histogram Energy -/

noncomputable section
namespace HadwigerCounterexample
open Finset Real Filter Matrix Function
open scoped BigOperators
variable {I J G : Type} [Fintype I] [Fintype J] [Fintype G]
variable [DecidableEq I] [DecidableEq J] [DecidableEq G]
variable {p : Shape} {n N M : ℕ}
instance rackFintype {I : Type} [Fintype I] [DecidableEq I] (N : ℕ) : Fintype (Rack I N) := inferInstance

def stamina {B : Type} [Fintype B]
    (q : Wgt B) (δ : ℝ) := ∀ i,q i≠0→δ ≤ q i

namespace Template
variable (v : Template p I)

/-- full query data key function -/
def resultKey (o : UnitType p n N) (x : Inputs p n I) :=
  (v.draw x).keys v.t o
def heatMap (o : UnitType p n N) (w : I→Wgt (Knobs p.g n)) :=
  mapW (prodW w) (v.resultKey o)

end Template
end HadwigerCounterexample

end

end OAI
end

section
-- module Solutions.OAIQ430_HC.HadwigerCounterexample_InformationSmallSetBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Information Small Set Bounds -/

noncomputable section
namespace HadwigerCounterexample
open Finset Filter Matrix Real
open scoped BigOperators
variable {A B C X : Type} [Fintype A] [Fintype B] [Fintype C] [Fintype X]

/-- Family of orientation/flag-conditional laws (μ already
realizes joint flag law). -/
structure Ultra (μ : Wgt A) (p : A→Wgt B) : Prop where
  law : IsLaw μ
  labs : ∀ i,IsLaw (p i)

variable {μ : Wgt A} {p : A→Wgt B}

def budget (μ : Wgt A) (p : A→Wgt B) (f : B→ C) :=
  avg μ (fun i => tension (mapW (p i) f) (mapW unif f))
def tariffs (μ : Wgt A) (p : A→ Wgt B) (r : ℕ) (δ V : ℝ) :=
  ∀ (C : Type) [Fintype C],Fintype.card C≤ r →
    ∀ (f : B→ C), stamina (mapW unif f) δ → budget μ p f ≤ V

def catalog (μ : Wgt A) (p : A→Wgt B) (w : Wgt B) :=
  ∃ t : Wgt A,(∀ i,0 ≤ t i) ∧ (∀ i,t i≤ μ i) ∧ w=mixW t p
end HadwigerCounterexample

end

end OAI
end

section
-- module Solutions.OAIQ430_HC.HadwigerCounterexample_ProjectionNets
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Projection Nets -/

noncomputable section
namespace HadwigerCounterexample
open Finset Filter Matrix Real Function
open scoped BigOperators
variable {A B C D : Type} [Fintype A] [Fintype B] [Fintype C] [Fintype D]

def ample (μ : Wgt A) (p : A→Wgt B) (r : ℕ) (ε : ℝ) :=
  ∃ t : ℕ,t ≤ r ∧ ∃ f : B → Fin t,∀ w,catalog μ p w →
    varOne w (bucket unif f w) ≤ ε

end HadwigerCounterexample

end

end OAI
end

section
-- module Solutions.OAIQ430_HC.HadwigerCounterexample_FiniteProjectionCenters
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Finite Projection Centers -/

noncomputable section
namespace HadwigerCounterexample
open Finset Filter Matrix Real Function
open scoped BigOperators
variable {A B C D : Type} [Fintype A] [Fintype B] [Fintype C] [Fintype D]

def roster (P : Wgt A→ Prop) (r : ℕ) (ε : ℝ) :=
  ∃ (t : ℕ), t ≤ r ∧ ∃ w : Fin t→ Wgt A, ∀ p,P p→ ∃ i,varOne p (w i)≤ ε

end HadwigerCounterexample

end

end OAI
end

section
-- module Solutions.OAIQ430_HC.HadwigerCounterexample_ConditionalFlags
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Conditional Flags -/

noncomputable section
namespace HadwigerCounterexample
open Finset Real
open scoped BigOperators
variable {A B C X Y : Type} [Fintype A] [Fintype B] [Fintype C] [Fintype X] [Fintype Y]
variable {w : Wgt X}

def stained (w : Wgt X) (f : X→Y) (i : Y) : Wgt X := by
  classical exact if mapW w f i≠0 then onW w (fun x => f x=i) else w

variable {μ : Wgt A}

def colored (μ : Wgt A) (w : Wgt X) (v : A→ X→ Y) :=
  semi μ (fun i => mapW w (v i))
def coloredP (w : Wgt X) (v : A→ X→Y) (K : A→X→B) :=
  fun i : A×Y => mapW (stained w (v i.1) i.2) (K i.1)
def flaggedW (μ : Wgt A) (w : Wgt X) (v : A→X→Y) (K : A→X→B) (P : A→Y→Prop) :=
  mixW μ (fun i => mapW (subW w (P i ∘ v i)) (K i))

end HadwigerCounterexample

end

end OAI
end

section
-- module Solutions.OAIQ430_HC.HadwigerCounterexample_RestrictedComparisonLaws
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Restricted Comparison Laws -/

noncomputable section
namespace HadwigerCounterexample
open Finset Real
open scoped BigOperators
variable {A B C : Type} [Fintype A] [Fintype B] [Fintype C]

def hung (Q : Wgt B→Prop) (P : B→Prop) (w : Wgt B) :=
  ∃ v : Wgt B, Q v ∧ w=subW v P
def smallSet (Q : Wgt B→Prop) (q : Wgt B) (δ η : ℝ) :=
  ∀ p,Q p → ∀ P : B→ Prop, pr q P ≤ δ → pr p P ≤ η
def rosterTail (Q : Wgt B→Prop) (q : Wgt B) (R η : ℝ) :=
  ∀ p,Q p → pr p (fun x => R≤density q p x)≤η

end HadwigerCounterexample

end

end OAI
end

section
-- module Solutions.OAIQ430_HC.HadwigerCounterexample_HistogramBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Histogram Bounds -/

noncomputable section
namespace HadwigerCounterexample
open Finset Real Filter
open scoped BigOperators
variable {A X B C Y : Type} [Fintype A] [Fintype B] [Fintype C] [Fintype X] [Fintype Y]

def fromFlags (μ : Wgt A) (w : Wgt X) (v : A→X→Y) (K : A→X→B) :=
  fun z => ∃ P:A→ Y→ Prop,z=flaggedW μ w v K P

def Haberdash (Q : Wgt B→ Prop) (r : ℕ) (δ R η ε : ℝ) :=
  (∀ p,Q p→SubLaw p) ∧ roster Q r ε ∧ smallSet Q unif δ η ∧
  ∀ P : B→Prop,
    let v := unifOn P
    let H := hung Q P
    roster H r ε ∧ smallSet H v δ η ∧ rosterTail H v R η

end HadwigerCounterexample

end

end OAI
end

section
-- module Solutions.OAIQ430_HC.HadwigerCounterexample_ConditionalProjection
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Conditional Projection -/

noncomputable section
namespace HadwigerCounterexample
open Finset Real Function
open scoped BigOperators
variable {A B C K : Type} [Fintype A] [Fintype B] [Fintype C]

def dip (μ f g : Wgt A) := avg μ (fun i => f i*g i)
def ode (μ f : Wgt A) := dip μ f f
def cashbook (μ : Wgt A) (f : A→B) (g : Wgt A) :=
  fun i => mapW (fun x => μ x*g x) f i / mapW μ f i
def banner (μ : Wgt A) (f : A→B) (g : Wgt A) := cashbook μ f g ∘ f

end HadwigerCounterexample

end

end OAI
end

section
-- module Solutions.OAIQ430_HC.HadwigerCounterexample_RectangleRegularity
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Rectangle Regularity -/

noncomputable section
namespace HadwigerCounterexample
open Finset Real Function
open scoped BigOperators
variable {A B C K : Type} [Fintype A] [Fintype B] [Fintype C]

def thinCut (μ f : Wgt A) (x : A→B) (y : A→C) (ε : ℝ) :=
  ∀ u : Wgt B,(∀ i,|u i|≤1) → ∀ v : Wgt C,(∀ i,|v i|≤1) →
    |avg μ (fun i=> f i*(u (x i)*v (y i)))|≤ ε
def doubleBook {L R : Type} (x : A→B) (y : A→C) (a : B→L) (b : C→R) :=
  fun i => (a (x i),b (y i))
def swab (x : Bool) : ℝ := if x then 1 else -1

def weakRank (μ f : Wgt A) (x : A→B) (y : A→C) (δ : ℝ) (R : ℕ) :=
  ∃ l : ℕ,l≤R ∧ ∃ (a:B→Fin l) (b:C→ Fin l),
    thinCut μ (fun i=> f i-banner μ (doubleBook x y a b) f i) x y δ

end HadwigerCounterexample

end

end OAI
end

section
-- module Solutions.OAIQ430_HC.HadwigerCounterexample_ResidualRegularity
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Residual Regularity -/

noncomputable section
namespace HadwigerCounterexample
open Finset Matrix LinearMap Function Filter Real
open scoped BigOperators
variable {A B I : Type} [Fintype A] [Fintype B] [Fintype I]

def wanes (u : Wgt I) (w : Wgt A) (f : I→Wgt A) (p : A→B) (ε : ℝ) :=
  ∀ h : Wgt A,(∀ x,|h x| ≤ 1) →
    avg u (fun i => |dip w (fun x=> f i x - banner w p (f i) x) h|) ≤ ε
def hits (u : Wgt I) (w : Wgt A) (f : I→ Wgt A) (p : A→ B) :=
  avg u (fun i => ode w (banner w p (f i)))

def twistSign (b : ℝ) := decide (0≤ b)
end HadwigerCounterexample

end

end OAI
end

section
-- module Solutions.OAIQ430_HC.HadwigerCounterexample_ProjectionError
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Projection Error -/

noncomputable section
namespace HadwigerCounterexample
open Finset Matrix LinearMap Module Filter Function
open scoped BigOperators
variable {A B I : Type} [Fintype A] [Fintype B] [Fintype I]

def rebate (u f g : Wgt A) (p : A→B) :=
  dip u f g - dip u (banner u p f) (banner u p g)
def lcost (u f g : Wgt A) := avg u (fun i=>|f i-g i|)

def syrup (r : ℝ) (x : ℝ) := min (max x 0) r
def mcut (r : ℝ) (u : Wgt A) (f : Wgt A) := syrup r ∘ density u f
end HadwigerCounterexample

end

end OAI
end

section
-- module Solutions.OAIQ430_HC.HadwigerCounterexample_ProjectedSurrogates
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Projected Surrogates -/

noncomputable section
namespace HadwigerCounterexample
open Finset Real Function
open scoped BigOperators
variable {A B I J : Type} [Fintype A] [Fintype B] [Fintype I] [Fintype J]

def bower (f : Wgt A) := (∀ i,0≤ f i)∧ (∀ i,f i≤1)

def trayLoss (R : ℝ) (u f : Wgt A) := pr f (fun i => R≤density u f i)
end HadwigerCounterexample

end

end OAI
end

section
-- module Solutions.OAIQ430_HC.HadwigerCounterexample_MixerConditions
attribute [-instance] _root_.OAI.HadwigerCounterexample.Flavor.instDecidableKeeps _root_.OAI.HadwigerCounterexample.Template.datumFinite _root_.OAI.HadwigerCounterexample.Template.inpFinite _root_.OAI.HadwigerCounterexample.Template.keySlotFinite _root_.OAI.HadwigerCounterexample.Volley.instFintypeVisits _root_.OAI.HadwigerCounterexample.aDefault _root_.OAI.HadwigerCounterexample.aFintype _root_.OAI.HadwigerCounterexample.amongFintype _root_.OAI.HadwigerCounterexample.cgFin _root_.OAI.HadwigerCounterexample.cgOneFin _root_.OAI.HadwigerCounterexample.fintypeLedger _root_.OAI.HadwigerCounterexample.instFKeys _root_.OAI.HadwigerCounterexample.jointDecidableEq _root_.OAI.HadwigerCounterexample.knFin _root_.OAI.HadwigerCounterexample.rackFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Mixer Conditions -/

noncomputable section
namespace HadwigerCounterexample
open Matrix
open scoped BigOperators
variable {p : Shape} {n : ℕ}

abbrev MIdx (p : Shape) := Fin p.J × Comp p.g × Comp p.g
abbrev MArr (p : Shape) (n : ℕ) := MIdx p → Moment p n
abbrev Draw (p : Shape) (n : ℕ) :=
  MArr p n × MArr p n × (Fin p.b → Mat (Fin n) (Fin n))

def drawn (d : Draw p n) : Mixer p n where
  mixL i j k := d.1 (i,j,k)
  mixR i j k := d.2.1 (i,j,k)
  mixM := d.2.2

abbrev MOne (p : Shape) := (MIdx p × Bool)
abbrev MBits (p : Shape) := MOne p × Bool
def orderedM (m : Mixer p n) (i : MOne p) : Moment p n :=
  if i.2 then m.mixL i.1.1 i.1.2.1 i.1.2.2 else m.mixR i.1.1 i.1.2.1 i.1.2.2
def eitherM (b : Bool) {I : Type} (A : Mat I I) := if b then A else Aᵀ

def indexedSum (m : Mixer p n) (c : Vec (MBits p)) :=
  ∑ i : MBits p,c i • eitherM i.2 (orderedM m i.1)
def selfSum (m : Mixer p n) (f : Vec Bool) :=
  ∑ i : Bool,f i • eitherM i (selfM p n m.mixM)

def blockRank (d : Block p.g) (s t : Label p.b) (A : Moment p n) :=
  (pullM (blockRay p n s d) (blockRay p n t d) A).rank

def binaryGood (m : Mixer p n) :=
  ∀ s t : Label p.b,s≠t →
    (∀ (c : Vec (MBits p)) (b : Vec Bool),c ≠ 0 →
      n ≤ 5*blockRank Block.Z s t (indexedSum m c + selfSum m b)) ∧
    (∀ b : Vec Bool, b≠0 → n ≤ 5*blockRank Block.sharp s t (selfSum m b))

/-- Matrix on a point's v coordinates for Tmix(x,atom_l). -/
def qmix (m : Mixer p n) (x : Profile p n) (l : Tag p.g) : Moment p n :=
  ∑ j : Fin p.J, ∑ f : TagStar l, ∑ e : Comp p.g,
    (liftM (m.mixL j e f.val)ᵀ (m.mixR j e f.val)ᵀ (x e) +
      liftM (m.mixL j f.val e) (m.mixR j f.val e) (x e))

def unaryGood (m : Mixer p n) (K s0 : ℕ) :=
  ∀ (x : Profile p n) (l : Tag p.g) (s : Label p.b), totalRank x ≤ K → totalRank x > 0 →
    2*(p.J-s0) ≤ blockRank Block.Z s s (qmix m x l + (qmix m x l)ᵀ)

end HadwigerCounterexample

end

end OAI
end

section
-- module Solutions.OAIQ430_HC.HadwigerCounterexample_BinaryPrescriptions
attribute [-instance] _root_.OAI.HadwigerCounterexample.Flavor.instDecidableKeeps _root_.OAI.HadwigerCounterexample.Template.datumFinite _root_.OAI.HadwigerCounterexample.Template.inpFinite _root_.OAI.HadwigerCounterexample.Template.keySlotFinite _root_.OAI.HadwigerCounterexample.aDefault _root_.OAI.HadwigerCounterexample.aFintype _root_.OAI.HadwigerCounterexample.amongFintype _root_.OAI.HadwigerCounterexample.cgFin _root_.OAI.HadwigerCounterexample.cgOneFin _root_.OAI.HadwigerCounterexample.fintypeLedger _root_.OAI.HadwigerCounterexample.instFKeys _root_.OAI.HadwigerCounterexample.knFin _root_.OAI.HadwigerCounterexample.rackFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Binary Prescriptions -/

noncomputable section
namespace HadwigerCounterexample

open scoped BigOperators
open Matrix Finset
variable {p : Shape} {n N : ℕ} {I : Type} [Fintype I]

/-- list for a cross edge -/
def aiming (a b : I → Bool) (i j : Bool) :=
  Finset.univ.filter (fun x => a x=i ∧ b x=j)

/-- within-endpoint L/R bit tests. Read only a x=a y, x≠y.
(tests between ordered points; no double counting since L,R and
both orientations are in the mixer hypothesis). -/
abbrev Script (p : Shape) (I : Type) := I → I → Vec (MOne p)

namespace Volley
variable (v : Volley p n I)
def reads (s : Script p I) (m : Mixer p n) :=
  ∀ x y : I,x≠y → v.obj x=v.obj y →
    ∀ i : MOne p, s x y i = evmat (orderedM m i) (v.rayAt x) (v.rayAt y)
end Volley

def prescribedB (p : Shape) (t : Tagging p I) (s : Script p I) (x y : I) :=
  ∑ i : Fin p.J,∑ e : Comp p.g, ∑ f : Comp p.g, if inc e (t x) ∧ inc f (t y) then
    s x y ((i,e,f),true)*s x y ((i,e,f),false) else 0

noncomputable def prescribedT (p : Shape) (t : Tagging p I) (d : Vec I)
    (h : Mat I I) (s : Script p I) (x y : I) : F :=
  @ite _ (x=y) (Classical.propDecidable _) (d x)
    (h x y+(prescribedB p t s x y+prescribedB p t s y x))

def fulfills (p : Shape) (t : Tagging p I) (d f : Vec I) (u : Mat I I)
    (s : Script p I) (a b : I → Bool) :=
  ∀ (x : I) (j : Bool),
    d x+ (∑ i∈aiming a b (a x) j, prescribedT p t d u s i x) =
      if j=b x then 0 else f x

end HadwigerCounterexample

end

end OAI
end

section
-- module Solutions.OAIQ430_HC.HadwigerCounterexample_GramConditionedLaws
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Gram Conditioned Laws -/

noncomputable section
namespace HadwigerCounterexample
open scoped BigOperators
open Matrix Module LinearMap Submodule Function Finset
variable {I J G H : Type} [Fintype I] [Fintype J] [Fintype G] [Fintype H]
variable [DecidableEq I] [DecidableEq J] [DecidableEq G]
variable {g : Route (I×J) G} {N : ℕ}

def partMean (p : H→Prop) (f : Wgt H) :=
  avg unif (fun x => ind (p x)*f x)
end HadwigerCounterexample

end

end OAI
end

section
-- module Solutions.OAIQ430_HC.HadwigerCounterexample_KeyReferenceLaws
attribute [-instance] _root_.OAI.HadwigerCounterexample.Template.datumFinite _root_.OAI.HadwigerCounterexample.Template.inpFinite _root_.OAI.HadwigerCounterexample.Template.keySlotFinite _root_.OAI.HadwigerCounterexample.knFin _root_.OAI.HadwigerCounterexample.rackFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Key Reference Laws -/

noncomputable section
namespace HadwigerCounterexample
open Matrix Module Function
open scoped BigOperators
variable {I : Type} [Fintype I] [DecidableEq I] {p : Shape} {n N : ℕ}

abbrev Toast (p : Shape) := Fin (p.g-1)
def outlet (p : Shape) (l : Tag p.g) : Toast p ≃ TagStar l :=
  (Fintype.equivFinOfCardEq (card_star l)).symm
def channelTag (p : Shape) (l : Tag p.g) (i : Toast p) := (outlet p l i).val

def mug (p : Shape) (l : Tag p.g) (N : ℕ) : AtomKey (p:=p) l N ≃ Rack (Toast p) N where
  toFun x := (Matrix.of (fun i j => x (outlet p l j) true i),Matrix.of (fun i j =>
    x (outlet p l j) false i))
  invFun x := fun i b j => if b then x.1 j ((outlet p l).symm i) else x.2 j ((outlet p l).symm i)
  left_inv x := by
    funext i b j
    cases b <;> simp
  right_inv x := by apply Prod.ext <;> ext <;> simp

def tray (p : Shape) (t : Tagging p I) (N : ℕ) : Keys (p:=p) t N ≃ Rack (I×Toast p) N :=
  (Equiv.piCongrRight (fun i => mug p (t i) N)).trans (relay I (Toast p) N).symm

def handles (p : Shape) (t : Tagging p I) : I×Toast p ≃ KeySlots p t where
  toFun x := ⟨x.1,outlet p (t x.1) x.2⟩
  invFun x := (x.1,(outlet p (t x.1)).symm x.2)
  left_inv x := by simp
  right_inv x := by simp
def trayPort (p : Shape) (t : Tagging p I) : Route (I×Toast p) (Comp p.g) :=
  fun x => channelTag p (t x.1) x.2
def trayJoin (p : Shape) (t : Tagging p I) (e : Comp p.g) :
    Port (trayPort p t) e ≃ Port (ownPort (p:=p) t) e where
  toFun x := ⟨handles p t x.val,x.property⟩
  invFun x :=
    ⟨(handles p t).symm x.val,by
      have h : (ownPort t) ∘ (handles p t)=trayPort p t := rfl
      rw [←h]; simp only [Function.comp_apply,Equiv.apply_symm_apply]; exact x.property⟩
  left_inv x := Subtype.ext (Equiv.symm_apply_apply ..)
  right_inv x := Subtype.ext (Equiv.apply_symm_apply ..)

def trayMap (p : Shape) (t : Tagging p I) (q : I → F) : GeoM (trayPort p t) :=
  fun e => (ownMap (p:=p) t q e).submatrix (trayJoin p t e) (trayJoin p t e)

end HadwigerCounterexample

end

end OAI
end

section
-- module Solutions.OAIQ430_HC.HadwigerCounterexample_EndpointGramRanks
attribute [-instance] _root_.OAI.HadwigerCounterexample.Template.datumFinite _root_.OAI.HadwigerCounterexample.Template.inpFinite _root_.OAI.HadwigerCounterexample.Template.keySlotFinite _root_.OAI.HadwigerCounterexample.rackFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Endpoint Gram Ranks -/

noncomputable section
namespace HadwigerCounterexample
open Matrix Module Finset Function
open scoped BigOperators
variable {I J U : Type} [Fintype I] [Fintype J] [Fintype U]
variable [DecidableEq I] [DecidableEq J] [DecidableEq U]
variable {n N : ℕ}

def crossSquare (n N : ℕ) (W : Mat (Fin n) (Fin n)) (v : F)
    (x : Rack (Fin n) N × Rack (Fin n) N) :=
  x.1.1ᵀ*x.2.2+(v • (x.1.2ᵀ * x.2.1) + W)

def rankJump (X Y : PlusRack (Fin n) N) (d : ℕ) :=
  (fromCols X Y).rank + d≤2*n

end HadwigerCounterexample

end

end OAI
end

section
-- module Solutions.OAIQ430_HC.HadwigerCounterexample_OppositeEndpointForms
attribute [-instance] _root_.OAI.HadwigerCounterexample.Template.datumFinite _root_.OAI.HadwigerCounterexample.Template.inpFinite _root_.OAI.HadwigerCounterexample.Template.keySlotFinite _root_.OAI.HadwigerCounterexample.rackFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Opposite Endpoint Forms -/

noncomputable section
namespace HadwigerCounterexample
open scoped BigOperators
open Matrix Module Finset Function Filter
variable {p : Shape} {n N : ℕ}

abbrev Notches (p : Shape) := Comp p.g × Bool

def duel (p : Shape) {n N : ℕ} (s t : Oframe p n N) (b : Bool) : Moment p n :=
  (primary (takeSign (p:=p) s b))ᵀ * primary (takeSign (p:=p) t (!b))

def duelPart (p : Shape) (c : Vec Bool) (x y : Oframe p n N) :=
  ∑ b:Bool,c b • duel p x y b
def issue (p : Shape) (c : Vec (Notches p)) (x : UnitType p n N) :=
  ∑ i:Comp p.g,duelPart p (fun b=>c (i,b)) (x.1 i) (x.2 i)

end HadwigerCounterexample

end

end OAI
end

section
-- module Solutions.OAIQ430_HC.HadwigerCounterexample_BilinearBlockCorrelation
attribute [-instance] _root_.OAI.HadwigerCounterexample.Template.datumFinite _root_.OAI.HadwigerCounterexample.Template.inpFinite _root_.OAI.HadwigerCounterexample.Template.keySlotFinite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Bilinear Block Correlation -/

noncomputable section
namespace HadwigerCounterexample
open Finset LinearMap Module Matrix Function
open scoped BigOperators
variable {p : Shape} {I J A : Type} [Fintype I] [Fintype J] [Fintype A]
variable {n : ℕ}

def spring (p : Shape) (l : Tag p.g) (s : Label p.b) (f : Flavor p.g)
    (y : Knobs p.g n) := point p s (lit f l y)

def dotLB (I : Type) [Fintype I] : Vec I →ₗ[F] Vec I→ₗ[F] F where
  toFun := dotL
  map_add' p q := LinearMap.ext fun i => add_dotProduct p q i
  map_smul' a p := LinearMap.ext fun i => by
    change dotProduct (a • p) i=a*dotProduct p i
    rw [smul_dotProduct]; rfl

end HadwigerCounterexample

end

end OAI
end

section
-- module Solutions.OAIQ430_HC.HadwigerCounterexample_ConditionedCorrelations
attribute [-instance] _root_.OAI.HadwigerCounterexample.Template.datumFinite _root_.OAI.HadwigerCounterexample.Template.inpFinite _root_.OAI.HadwigerCounterexample.Template.keySlotFinite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Conditioned Correlations -/

noncomputable section
namespace HadwigerCounterexample
open Finset Real Filter Matrix LinearMap Function
open scoped BigOperators
variable {p : Shape} {I A : Type} [Fintype I] [Fintype A]
variable {n : ℕ}

def litFire (p : Shape) {n N : ℕ} (x : UnitType p n N) :=
  ∀ (s t : Label p.b) (c : Vec (Notches p)), c≠0 →
    n≤5*blockRank Block.Z s t (issue p c x)

end HadwigerCounterexample

end

end OAI
end

section
-- module Solutions.OAIQ430_HC.HadwigerCounterexample_ProductCharacterTests
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Product Character Tests -/

noncomputable section
namespace HadwigerCounterexample
open Finset Matrix Filter Function
open scoped BigOperators
variable {I J A Z D : Type} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
variable [Fintype A]

def Pipe (P : A→Z→ ℝ) :=
  ∃ (f : A→ℝ) (g : Z→ℝ),(∀ i, |f i|≤1) ∧ (∀ i, |g i|≤1) ∧ ∀ x y,P x y=f x*g y

structure Stage (I J : Type) where
  first : J→I
  nextP : J→I
  diff k : first k ≠ nextP k
  once k j : first k=first j → nextP k=nextP j → k=j
  anti k j : first k=nextP j → nextP k≠first j

variable (s : Stage I J)

def moveInputs (i j : I) (x : I→A) (p q : A) := update (update x i p) j q

end HadwigerCounterexample

end

end OAI
end

section
-- module Solutions.OAIQ430_HC.HadwigerCounterexample_PairIndexedTests
attribute [-instance] _root_.OAI.HadwigerCounterexample.Template.datumFinite _root_.OAI.HadwigerCounterexample.Template.inpFinite _root_.OAI.HadwigerCounterexample.Template.keySlotFinite _root_.OAI.HadwigerCounterexample.rackFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Pair Indexed Tests -/

noncomputable section
namespace HadwigerCounterexample
open Finset Matrix Module Function
open scoped BigOperators
variable {I J A : Type} [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J] [Fintype A]
variable {s : Stage I J} {B : J→ Type}
variable [∀ i,Fintype (B i)] [∀ i,DecidableEq (B i)]

def listen (s : Stage I J) (f : ∀ i,A→A→Vec (B i)) (x : I→ A) := fun i =>
  f i (x (s.first i)) (x (s.nextP i))

def prism (B : J →Type) [∀ i,Fintype (B i)] [∀ i,DecidableEq (B i)] :
    Wgt (∀ i,Vec (B i)) := prodW (fun _ : J => unif)
def wavelength (B : J →Type) [∀ i,Fintype (B i)] [∀ i,DecidableEq (B i)] :=
  prism B 0

end HadwigerCounterexample

end

end OAI
end

section
-- module Solutions.OAIQ430_HC.HadwigerCounterexample_EndpointEvaluations
attribute [-instance] _root_.OAI.HadwigerCounterexample.Template.datumFinite _root_.OAI.HadwigerCounterexample.Template.inpFinite _root_.OAI.HadwigerCounterexample.Template.keySlotFinite _root_.OAI.HadwigerCounterexample.rackFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Endpoint Evaluations -/

noncomputable section
namespace HadwigerCounterexample
open Finset Matrix Function LinearMap
open scoped BigOperators
variable {p : Shape} {n N : ℕ} {I : Type} [Fintype I] [DecidableEq I]

namespace Template
variable (v : Template p I)

abbrev SameDuet (v : Template p I) :=
  {i : I×I//v.aim i.1=v.aim i.2 ∧ Fintype.equivFin I i.1<Fintype.equivFin I i.2}
abbrev OppDuet (v : Template p I) := {i:I×I//v.aim i.1=true∧v.aim i.2=false}
abbrev Chorus (v : Template p I) := v.SameDuet ⊕ v.OppDuet
instance instFintypeSameDuet : Fintype v.SameDuet := inferInstance
instance instFintypeOppDuet : Fintype v.OppDuet := inferInstance

def verses (v : Template p I) (x : v.Chorus) := x.elim Subtype.val Subtype.val
def choral (v : Template p I) : Stage I v.Chorus := {
  first := fun i => (v.verses i).1
  nextP := fun i => (v.verses i).2
  diff i := by
    rcases i with i|i
    · intro h; exact i.property.2.ne (congrArg (Fintype.equivFin I) h)
    intro h
    exact Bool.noConfusion (i.property.1.symm.trans ((congrArg v.aim h).trans i.property.2))
  once i j := by
    intro hi hj
    have he : v.verses i=v.verses j := Prod.ext hi hj
    rcases i with i|i <;> rcases j with j|j
    · exact congrArg _ (Subtype.ext (show i.val=j.val from he))
    · have hf : v.aim j.val.1=v.aim j.val.2 := (show i.val=j.val from he) ▸ i.property.1
      simp only [j.property] at hf; cases hf
    · have hf : v.aim i.val.1=v.aim i.val.2 := (show j.val=i.val from he.symm) ▸ j.property.1
      simp only [i.property] at hf; cases hf
    exact congrArg _ (Subtype.ext (show i.val=j.val from he))
  anti i j h h' := by
    rcases i with i|i <;> rcases j with j|j <;>
      change i.val.1=j.val.2 at h <;> change i.val.2=j.val.1 at h'
    · have hh := i.property.2; rw [h,h'] at hh; exact (not_lt_of_gt hh) j.property.2
    · have hh := i.property.1; rw [h,h',j.property.2,j.property.1] at hh; cases hh
    · have hh := j.property.1; rw [←h,←h',i.property.1,i.property.2] at hh; cases hh
    have hh := i.property.1; rw [h,j.property.2] at hh; cases hh }

abbrev Crossing (p : Shape) (i j : Tag p.g) :=
  {x : Notches p//inc x.1 i ∧ inc x.1 j}
abbrev Harm (p : Shape) := MBits p ⊕ Bool
def Abbey (v : Template p I) : v.Chorus → Type
  | .inl _ => Harm p
  | .inr x => Crossing p (v.t x.val.1) (v.t x.val.2)
instance instFintypeAbbey (i : v.Chorus) : Fintype (v.Abbey i) :=
  i.rec (fun _ => inferInstanceAs (Fintype (Harm p))) (fun x => inferInstanceAs (Fintype
    (Crossing p (v.t x.val.1) (v.t x.val.2))))
instance instDecidableEqAbbey (i : v.Chorus) : DecidableEq (v.Abbey i) := Classical.typeDecidableEq _

def monks (v : Template p I) (m : Mixer p n) (x : UnitType p n N) (i : v.Chorus) :
    v.Abbey i → Moment p n :=
  match i with
  | .inl _ => Sum.elim (fun l => eitherM l.2 (orderedM m l.1))
    (fun l => eitherM l (selfM p n m.mixM))
  | .inr _ => fun ⟨j,_⟩ => duel p (x.1 j.1) (x.2 j.1) j.2

def croon (v : Template p I) (i : I) := spring p (n:=n) (v.t i) (v.s i) (v.f i)

def chime (m : Mixer p n) (x : UnitType p n N)
    (i : v.Chorus) (y z : Knobs p.g n) : Vec (v.Abbey i) :=
  fun j => evmat (v.monks m x i j) (v.croon (v.choral.first i) y) (v.croon (v.choral.nextP i) z)

def chorusM (m : Mixer p n) (x : UnitType p n N)
    (i : v.Chorus) (y : Vec (v.Abbey i)) := ∑ j:v.Abbey i,y j • monks v m x i j

end Template
end HadwigerCounterexample

end

end OAI
end

section
-- module Solutions.OAIQ430_HC.HadwigerCounterexample_ScriptGramCorrespondence
attribute [-instance] _root_.OAI.HadwigerCounterexample.Template.datumFinite _root_.OAI.HadwigerCounterexample.Template.inpFinite _root_.OAI.HadwigerCounterexample.Template.keySlotFinite _root_.OAI.HadwigerCounterexample.rackFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Script Gram Correspondence -/

noncomputable section
namespace HadwigerCounterexample
open Finset Matrix LinearMap Function
open scoped BigOperators
variable {p : Shape} {n N : ℕ} {I : Type} [Fintype I] [DecidableEq I]

namespace Template
variable (v : Template p I)

def lyrics (s : Script p I) (i : v.Chorus) : Vec (v.Abbey i) :=
  match i with
  | .inl z => Sum.elim (fun j => if j.2 then s z.val.1 z.val.2 j.1 else s z.val.2 z.val.1 j.1)
    (fun _ => 0)
  | .inr _ => 0
def performs (s : Script p I) (m : Mixer p n) (x : UnitType p n N) (z : Inputs p n I) :=
  listen v.choral (v.chime m x) z=v.lyrics s

def voices (v : Template p I) (x : Keys (p:=p) v.t N) (i j) (e : Comp p.g) (a : inc e (v.t i))
    (b : inc e (v.t j)) (q : Bool) :=
  dotProduct (x i ⟨e,a⟩ q) (x j ⟨e,b⟩ (!q))

def verges (v : Template p I) (x : Keys (p:=p) v.t N) (i j) :=
  ∀ e a b q,v.voices x i j e a b q=0

end Template
end HadwigerCounterexample

end

end OAI
end

section
-- module Solutions.OAIQ430_HC.HadwigerCounterexample_KeyTestCorrespondence
attribute [-instance] _root_.OAI.HadwigerCounterexample.Template.datumFinite _root_.OAI.HadwigerCounterexample.Template.inpFinite _root_.OAI.HadwigerCounterexample.Template.keySlotFinite _root_.OAI.HadwigerCounterexample.rackFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Key Test Correspondence -/

noncomputable section
namespace HadwigerCounterexample
open Finset Matrix LinearMap
open scoped BigOperators
variable {p : Shape} {n N : ℕ} {I : Type} [Fintype I] [DecidableEq I]

namespace Template
variable (v : Template p I)

def pairedRead (s : Script p I) (m : Mixer p n) (z : Inputs p n I) (i j : I) :=
  ∀ a:MOne p, s i j a=evmat (orderedM m a) (v.croon i (z i)) (v.croon j (z j))

def knows (s : Script p I) (m : Mixer p n) (z : Inputs p n I) (i j : I) :=
  v.aim i=v.aim j→ v.pairedRead s m z i j∧v.pairedRead s m z j i

def neigh (v : Template p I) (s : Script p I) (m : Mixer p n) (x : UnitType p n N)
    (z : Inputs p n I) := (v.draw z).reads s m ∧ ∀ i j, i≠j →
      v.verges ((v.draw z).keys v.t x) i j

end Template
end HadwigerCounterexample

end

end OAI
end

section
-- module Solutions.OAIQ430_HC.HadwigerCounterexample_BinaryMixingBounds
attribute [-instance] _root_.OAI.HadwigerCounterexample.Template.datumFinite _root_.OAI.HadwigerCounterexample.Template.inpFinite _root_.OAI.HadwigerCounterexample.Template.keySlotFinite _root_.OAI.HadwigerCounterexample.rackFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Binary Mixing Bounds -/

noncomputable section
namespace HadwigerCounterexample
open Finset Filter Matrix Function
open scoped BigOperators
variable {p : Shape} {n N : ℕ} {I : Type} [Fintype I] [DecidableEq I]
namespace Template
variable (v : Template p I)

def kappa := wavelength v.Abbey

def diffsel (v : Template p I) := ∀ i j, i≠j → v.aim i=v.aim j → v.s i≠ v.s j

end Template

end HadwigerCounterexample

end

end OAI
end

section
-- module Solutions.OAIQ430_HC.HadwigerCounterexample_BinaryEvaluationForms
attribute [-instance] _root_.OAI.HadwigerCounterexample.Flavor.instDecidableKeeps _root_.OAI.HadwigerCounterexample.Template.datumFinite _root_.OAI.HadwigerCounterexample.Template.inpFinite _root_.OAI.HadwigerCounterexample.Template.instDecidableEqAbbey _root_.OAI.HadwigerCounterexample.Template.instFintypeAbbey _root_.OAI.HadwigerCounterexample.Template.instFintypeOppDuet _root_.OAI.HadwigerCounterexample.Template.instFintypeSameDuet _root_.OAI.HadwigerCounterexample.Template.keySlotFinite _root_.OAI.HadwigerCounterexample.Volley.instFintypeVisits _root_.OAI.HadwigerCounterexample.aDefault _root_.OAI.HadwigerCounterexample.aFintype _root_.OAI.HadwigerCounterexample.amongFintype _root_.OAI.HadwigerCounterexample.cgFin _root_.OAI.HadwigerCounterexample.cgOneFin _root_.OAI.HadwigerCounterexample.fintypeLedger _root_.OAI.HadwigerCounterexample.instFKeys _root_.OAI.HadwigerCounterexample.jointDecidableEq _root_.OAI.HadwigerCounterexample.knFin _root_.OAI.HadwigerCounterexample.rackFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Binary Evaluation Forms -/

noncomputable section
namespace HadwigerCounterexample
open scoped BigOperators
open Matrix
variable {p : Shape} {n : ℕ}

theorem indexed_linear {c : Vec (MBits p)} {D D' : Draw p n} :
    indexedSum (drawn (p:=p) (D+D')) c =
      indexedSum (drawn D) c + indexedSum (drawn D') c := by
  have h (i : MBits p) :
      eitherM i.2 (orderedM (drawn (p:=p) (D+D')) i.1) =
        eitherM i.2 (orderedM (drawn D) i.1) + eitherM i.2 (orderedM (drawn D') i.1) := by
    rcases i with ⟨⟨⟨a,b,d⟩,_|_⟩,_|_⟩ <;> rfl
  unfold indexedSum
  simp_rw [h,smul_add,Finset.sum_add_distrib]

def obsZ (p : Shape) (n : ℕ) (s t : Label p.b) (c : Vec (MBits p)) :
    Draw p n →ₗ[F] Mat (Fin n) (Fin n) where
  toFun D := pullM (blockRay p n s Block.Z) (blockRay p n t Block.Z) (indexedSum (drawn D) c)
  map_add' _ _ := by rw [indexed_linear,map_add]
  map_smul' a x := by
    have h (i : MBits p) :
        eitherM i.2 (orderedM (drawn (p:=p) (a•x)) i.1)=
          a • eitherM i.2 (orderedM (drawn x) i.1) := by
      rcases i with ⟨⟨⟨a,b,d⟩,_|_⟩,_|_⟩ <;> rfl
    simp only [indexedSum,h,map_sum,map_smul,RingHom.id_apply,Finset.smul_sum]
    exact Finset.sum_congr rfl fun i _ => smul_comm _ _ _

def selfPartial (s t : Label p.b) (f : Vec Bool) (D : Draw p n) : Mat (Fin n) (Fin n) :=
  let A := ∑ a, (s a+t a) • D.2.2 a
  f true • A+f false • Aᵀ

def obsHalf (p : Shape) (s t : Label p.b) (f : Vec Bool) (n : ℕ)
    (l r : Fin (n/2)→Fin n) : Draw p n →ₗ[F] Mat (Fin (n/2)) (Fin (n/2)) where
  toFun D := (selfPartial (p:=p) s t f D).submatrix l r
  map_add' _ _ := by
    simp only [selfPartial, Prod.snd_add, Pi.add_apply, smul_add, Finset.sum_add_distrib,
      transpose_add, Matrix.submatrix_add]
    abel
  map_smul' a D := by
    simp only [selfPartial,Prod.smul_snd,Pi.smul_apply,RingHom.id_apply]
    let F (D : Draw p n) := ∑ i, (s i+t i) • D.2.2 i
    have h :
        ∑ i, (s i+t i) • (a • D.2.2 i) = a • F D := by
      unfold F; rw [Finset.smul_sum]; exact Finset.sum_congr rfl fun _ _ => smul_comm _ _ _
    rw [h,Matrix.transpose_smul]
    rw [smul_comm (f true),smul_comm (f false) a, ← smul_add]
    rfl

end HadwigerCounterexample

end

end OAI
end

section
-- module Solutions.OAIQ430_HC.HadwigerCounterexample_RandomBinaryMixing
attribute [-instance] _root_.OAI.HadwigerCounterexample.Flavor.instDecidableKeeps _root_.OAI.HadwigerCounterexample.Template.datumFinite _root_.OAI.HadwigerCounterexample.Template.inpFinite _root_.OAI.HadwigerCounterexample.Template.instDecidableEqAbbey _root_.OAI.HadwigerCounterexample.Template.instFintypeAbbey _root_.OAI.HadwigerCounterexample.Template.instFintypeOppDuet _root_.OAI.HadwigerCounterexample.Template.instFintypeSameDuet _root_.OAI.HadwigerCounterexample.Template.keySlotFinite _root_.OAI.HadwigerCounterexample.Volley.instFintypeVisits _root_.OAI.HadwigerCounterexample.aDefault _root_.OAI.HadwigerCounterexample.aFintype _root_.OAI.HadwigerCounterexample.amongFintype _root_.OAI.HadwigerCounterexample.cgFin _root_.OAI.HadwigerCounterexample.cgOneFin _root_.OAI.HadwigerCounterexample.fintypeLedger _root_.OAI.HadwigerCounterexample.instFKeys _root_.OAI.HadwigerCounterexample.jointDecidableEq _root_.OAI.HadwigerCounterexample.knFin _root_.OAI.HadwigerCounterexample.rackFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Random Binary Mixing -/

noncomputable section
namespace HadwigerCounterexample

instance momFintype (p : Shape) (n : ℕ) : Fintype (Moment p n) := inferInstance
instance idxDec (p : Shape) : DecidableEq (MIdx p) := inferInstance
instance arrFintype (p : Shape) (n : ℕ) : Fintype (MArr p n) := inferInstance
instance drawFintype (p : Shape) (n : ℕ) : Fintype (Draw p n) := inferInstance

open Filter Matrix Function
open scoped BigOperators Topology

end HadwigerCounterexample

end

end OAI
end

section
-- module Solutions.OAIQ430_HC.HadwigerCounterexample_MixerProductVariables
attribute [-instance] _root_.OAI.HadwigerCounterexample.Flavor.instDecidableKeeps _root_.OAI.HadwigerCounterexample.Template.datumFinite _root_.OAI.HadwigerCounterexample.Template.inpFinite _root_.OAI.HadwigerCounterexample.Template.instDecidableEqAbbey _root_.OAI.HadwigerCounterexample.Template.instFintypeAbbey _root_.OAI.HadwigerCounterexample.Template.instFintypeOppDuet _root_.OAI.HadwigerCounterexample.Template.instFintypeSameDuet _root_.OAI.HadwigerCounterexample.Template.keySlotFinite _root_.OAI.HadwigerCounterexample.Volley.instFintypeVisits _root_.OAI.HadwigerCounterexample.aDefault _root_.OAI.HadwigerCounterexample.aFintype _root_.OAI.HadwigerCounterexample.amongFintype _root_.OAI.HadwigerCounterexample.cgFin _root_.OAI.HadwigerCounterexample.cgOneFin _root_.OAI.HadwigerCounterexample.fintypeLedger _root_.OAI.HadwigerCounterexample.instFKeys _root_.OAI.HadwigerCounterexample.jointDecidableEq _root_.OAI.HadwigerCounterexample.knFin _root_.OAI.HadwigerCounterexample.rackFintype
attribute [-simp] _root_.OAI.HadwigerCounterexample.cdim_bot _root_.OAI.HadwigerCounterexample.flipZ_flip _root_.OAI.HadwigerCounterexample.reciprocal_actual _root_.OAI.HadwigerCounterexample.reciprocal_twice _root_.OAI.HadwigerCounterexample.wsign_one _root_.OAI.HadwigerCounterexample.wsign_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Mixer Product Variables -/

noncomputable section
namespace HadwigerCounterexample
open scoped BigOperators
open Matrix
variable {p : Shape} {n : ℕ} {r : Comp p.g → ℕ}

abbrev Terms (p : Shape) (l : Tag p.g) (r : Comp p.g → ℕ) :=
  Fin p.J × TagStar l × ((Σ e, Fin (r e)) × Bool)
abbrev Parts (p : Shape) (n : ℕ) (r : Comp p.g → ℕ) :=
  ∀ e, Mat (Row p n) (Fin (r e))

def formCol (P : Parts p n r) (l : Tag p.g) (d : MArr p n) :
    Mat (Row p n) (Terms p l r) :=
  Matrix.of (fun i =>
    fun ⟨j,f,⟨e,k⟩,b⟩ =>
      (if b then (d (j,e,f.val))ᵀ * P e else d (j,f.val,e) * P e) i k)

theorem formCol_true (P : Parts p n r) (l : Tag p.g) (d : MArr p n)
    (i j f e k) :
    formCol P l d i (j,f,⟨e,k⟩,true)=((d (j,e,f.val))ᵀ * P e) i k := by simp [formCol]
theorem formCol_false (P : Parts p n r) (l : Tag p.g) (d : MArr p n)
    (i j f e k) :
    formCol P l d i (j,f,⟨e,k⟩,false)=(d (j,f.val,e) * P e) i k := by simp [formCol]

theorem formCol_add (P : Parts p n r) (l : Tag p.g) (d d' : MArr p n) :
    formCol P l (d+d') = formCol P l d + formCol P l d' := by
  ext i j; rcases j with ⟨j,f,⟨e,k⟩,_|_⟩
  · simp only [Matrix.add_apply, formCol_false,Pi.add_apply,Matrix.add_mul]
  · simp only [Matrix.add_apply, formCol_true,Pi.add_apply,Matrix.add_mul, Matrix.transpose_add]
theorem formCol_smul (P : Parts p n r) (l : Tag p.g) (a : F) (d : MArr p n) :
    formCol P l (a•d) = a • formCol P l d := by
  ext i j; rcases j with ⟨j,f,⟨e,k⟩,_|_⟩
  · simp only [Matrix.smul_apply, formCol_false,Pi.smul_apply,Matrix.smul_mul]
  · simp only [Matrix.smul_apply, formCol_true,Pi.smul_apply,Matrix.smul_mul,
      Matrix.transpose_smul]

variable {U : Type}

/-- Stacked evaluation of all columns on a batch of free directions. -/
def stackL (P Q : Parts p n r) (l : Tag p.g) (W : Mat (Row p n) U) :
    Draw p n →ₗ[F] Mat U (Terms p l r ⊕ Terms p l r) where
  toFun d := Wᵀ * fromCols (formCol P l d.1) (formCol Q l d.2.1)
  map_add' d d' := by
    simp only [Prod.fst_add,Prod.snd_add,formCol_add,mul_fromCols, Matrix.mul_add]
    ext i j; cases j <;> rfl
  map_smul' v d := by
    simp only [Prod.smul_fst,Prod.smul_snd,formCol_smul,mul_fromCols,RingHom.id_apply,
      Matrix.mul_smul]
    ext i j; cases j <;> rfl

end HadwigerCounterexample

end

end OAI
end

section
-- module Solutions.OAIQ430_HC.HadwigerCounterexample_PolarRankBounds
attribute [-instance] _root_.OAI.HadwigerCounterexample.Flavor.instDecidableKeeps _root_.OAI.HadwigerCounterexample.Template.datumFinite _root_.OAI.HadwigerCounterexample.Template.inpFinite _root_.OAI.HadwigerCounterexample.Template.instDecidableEqAbbey _root_.OAI.HadwigerCounterexample.Template.instFintypeAbbey _root_.OAI.HadwigerCounterexample.Template.instFintypeOppDuet _root_.OAI.HadwigerCounterexample.Template.instFintypeSameDuet _root_.OAI.HadwigerCounterexample.Template.keySlotFinite _root_.OAI.HadwigerCounterexample.Volley.instFintypeVisits _root_.OAI.HadwigerCounterexample.aDefault _root_.OAI.HadwigerCounterexample.aFintype _root_.OAI.HadwigerCounterexample.amongFintype _root_.OAI.HadwigerCounterexample.cgFin _root_.OAI.HadwigerCounterexample.cgOneFin _root_.OAI.HadwigerCounterexample.fintypeLedger _root_.OAI.HadwigerCounterexample.instFKeys _root_.OAI.HadwigerCounterexample.jointDecidableEq
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Polar Rank Bounds -/

noncomputable section
namespace HadwigerCounterexample
open Matrix
open scoped BigOperators

variable {I J U : Type} [Fintype I] [Fintype J]

def swapM (I : Type) [DecidableEq I] : Mat (I⊕I) (I⊕I) :=
  fromBlocks (0:Mat I I) (1:Mat I I) (1:Mat I I) 0

variable {p : Shape} {n : ℕ}

def urBad (K s0 : ℕ) (x : Profile p n) (l : Tag p.g) (s : Label p.b) (d : Draw p n) :=
  totalRank x ≤ K ∧ totalRank x>0 ∧ blockRank Block.Z s s
    (qmix (drawn d) x l+(qmix (drawn d) x l)ᵀ)<2*(p.J-s0)

def prodBound (p : Shape) (K : ℕ) := 4*p.J*(p.g-1)*K

end HadwigerCounterexample

end

end OAI
end

section
-- module Solutions.OAIQ430_HC.HadwigerCounterexample_UnaryQueryComparison
attribute [-instance] _root_.OAI.HadwigerCounterexample.Template.datumFinite _root_.OAI.HadwigerCounterexample.Template.inpFinite _root_.OAI.HadwigerCounterexample.Template.keySlotFinite _root_.OAI.HadwigerCounterexample.arrFintype _root_.OAI.HadwigerCounterexample.drawFintype _root_.OAI.HadwigerCounterexample.idxDec _root_.OAI.HadwigerCounterexample.momFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Unary Query Comparison -/

noncomputable section
namespace HadwigerCounterexample
open scoped BigOperators
open Matrix Finset Filter Function LinearMap
variable {p : Shape} {n N : ℕ}

namespace Template

def solo (p : Shape) (t : Tag p.g) (s : Label p.b) (f : Flavor p.g) :
    Template p Unit := ⟨fun _ => true,fun _=>t,fun _ =>s,fun _=>f⟩

abbrev Solo (p : Shape) := Template p Unit
variable (v : Solo p)

def soloeq (N : ℕ) : Keys (p:=p) v.t N ≃ AtomKey (p:=p) (v.t ()) N where
  toFun x := x ()
  invFun x i := i.rec x
  left_inv x := by funext i; cases i; rfl
  right_inv x := rfl

def desc (v : Solo p) (x : Knobs p.g n) (o : Orient p n N) := callOne v () x o
end Template
end HadwigerCounterexample

end

end OAI
end

section
-- module Solutions.OAIQ430_HC.HadwigerCounterexample_UnaryQueryFrequencies
attribute [-instance] _root_.OAI.HadwigerCounterexample.Template.datumFinite _root_.OAI.HadwigerCounterexample.Template.inpFinite _root_.OAI.HadwigerCounterexample.Template.keySlotFinite _root_.OAI.HadwigerCounterexample.arrFintype _root_.OAI.HadwigerCounterexample.drawFintype _root_.OAI.HadwigerCounterexample.idxDec _root_.OAI.HadwigerCounterexample.momFintype _root_.OAI.HadwigerCounterexample.rackFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Unary Query Frequencies -/

noncomputable section
namespace HadwigerCounterexample
open Matrix Module Finset Filter Real Function
open scoped BigOperators
variable {p : Shape} {n N : ℕ}
namespace Template

def minorCall (v : Solo p) (w : Wgt (Knobs p.g n))
    (T : Wgt (AtomKey (p:=p) (v.t ()) N)) (o : Orient p n N) :=
  avg w (fun i => T (v.desc i o))

end Template

end HadwigerCounterexample

end

end OAI
end

section
-- module Solutions.OAIQ430_HC.HadwigerCounterexample_FreeBlockLinearAction
attribute [-instance] _root_.OAI.HadwigerCounterexample.Template.datumFinite _root_.OAI.HadwigerCounterexample.Template.inpFinite _root_.OAI.HadwigerCounterexample.Template.keySlotFinite _root_.OAI.HadwigerCounterexample.arrFintype _root_.OAI.HadwigerCounterexample.drawFintype _root_.OAI.HadwigerCounterexample.idxDec _root_.OAI.HadwigerCounterexample.momFintype _root_.OAI.HadwigerCounterexample.rackFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Free Block Linear Action -/

noncomputable section
namespace HadwigerCounterexample
open Matrix Module Submodule Function Finset LinearMap
open scoped BigOperators
variable {p : Shape} {n N : ℕ}
abbrev Flit (n : ℕ) := Move (Fin n)

def breeze (p : Shape) (M : Mat (Fin n) (Fin n)) (x : Ray p n) : Ray p n :=
  fun i =>
    match i.2 with
    | none => x i
    | some (B,j) => if B=Block.Z then (M *ᵥ (fun j => x (i.1,some (Block.Z,j)))) j else x i

def blitzL (p : Shape) (M : Mat (Fin n) (Fin n)) : Ray p n →ₗ[F] Ray p n where
  toFun := breeze p M
  map_add' x y := by
    have he (i : SelIdx p.b p.j) :
        (fun j : Fin n => (x+y) (i,some (Block.Z,j)))=
        ((fun j => x (i,some (Block.Z,j)))+ (fun j => y (i,some (Block.Z,j)))) := rfl
    funext i; rcases i with ⟨i, _|⟨B,j⟩⟩
    · rfl
    by_cases h : B=Block.Z
    · simp only [breeze,h,ite_true, if_true,he,mulVec_add]
      rfl
    simp [breeze,h]
  map_smul' a x := by
    have he (i : SelIdx p.b p.j) :
        (fun j : Fin n => (a•x) (i,some (Block.Z,j)))=
        a • (fun j => x (i,some (Block.Z,j))) := rfl
    funext i; rcases i with ⟨i, _|⟨B,j⟩⟩
    · rfl
    by_cases h : B=Block.Z
    · simp only [breeze,h,ite_true, if_true,he,mulVec_smul]; rfl
    simp [breeze,h]

def blitz (p : Shape) (M : Mat (Fin n) (Fin n)) := LinearMap.toMatrix' (blitzL p M)

theorem blitz_val (p : Shape) (M : Mat (Fin n) (Fin n)) (x) :
    blitz p M *ᵥ x=breeze p M x := by
  change LinearMap.toMatrix' (blitzL p M)*ᵥ x=blitzL p M x
  simp

theorem blitz_mul (p : Shape) (M L : Mat (Fin n) (Fin n)) :
    blitz p (M*L)=blitz p M*blitz p L := by
  classical
  apply coe_mv_inj
  apply LinearMap.ext
  intro x; simp_rw [mulVecLin_apply,← mulVec_mulVec,blitz_val]
  funext i; rcases i with ⟨i, _|⟨B,j⟩⟩
  · rfl
  by_cases h : B=Block.Z
  · simp only [breeze,h,ite_true, if_true,←mulVec_mulVec]
  simp [breeze,h]

theorem blitz_one (p : Shape) (n : ℕ) : blitz p (1:Mat (Fin n) (Fin n))=1 := by
  apply coe_mv_inj; apply LinearMap.ext; intro x
  rw [mulVecLin_apply,mulVecLin_apply,Matrix.one_mulVec,blitz_val]
  funext i; rcases i with ⟨i, _|⟨B,j⟩⟩
  · rfl
  by_cases h : B=Block.Z <;> simp [breeze,h]

/-- knobs player. -/
def doZ (p : Shape) (M : Mat (Fin n) (Fin n)) (x : Knobs p.g n) :=
  Function.update x Block.Z (M *ᵥ (x Block.Z))

end HadwigerCounterexample

end

end OAI
end

section
-- module Solutions.OAIQ430_HC.HadwigerCounterexample_FrameRotations
attribute [-instance] _root_.OAI.HadwigerCounterexample.Template.datumFinite _root_.OAI.HadwigerCounterexample.Template.inpFinite _root_.OAI.HadwigerCounterexample.Template.keySlotFinite _root_.OAI.HadwigerCounterexample.arrFintype _root_.OAI.HadwigerCounterexample.drawFintype _root_.OAI.HadwigerCounterexample.idxDec _root_.OAI.HadwigerCounterexample.momFintype _root_.OAI.HadwigerCounterexample.rackFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Frame Rotations -/

noncomputable section
namespace HadwigerCounterexample
open Matrix Module LinearMap Function Finset
open scoped BigOperators
variable {p : Shape} {n N : ℕ}
namespace Move

def vault (p : Shape) (c : Flit n) :
    Knobs p.g n ≃ Knobs p.g n where
  toFun x := doZ p c.L x
  invFun x := doZ p c.R x
  left_inv x := by simp only [doZ,update_self,mulVec_mulVec,c.RL,Matrix.one_mulVec] <;> simp
  right_inv x := by simp only [doZ,update_self,mulVec_mulVec,c.LR,Matrix.one_mulVec] <;> simp
variable (c : Flit n)

def boom (p : Shape) (c : Flit n) : Move (Full p n) where
  L := Matrix.fromBlocks (blitz p c.L) 0 0 1
  R := Matrix.fromBlocks (blitz p c.R) 0 0 1
  LR := by simp [fromBlocks_multiply,←blitz_mul,c.LR,blitz_one]
  RL := by simp [fromBlocks_multiply,←blitz_mul,c.RL,blitz_one]

def fuse (p : Shape) (c : Flit n) (N : ℕ) :
    Mat (Fin N) (Full p n) ≃ Mat (Fin N) (Full p n) where
  toFun y := y*(boom p c).L
  invFun y := y*(boom p c).R
  left_inv y := by simp only [Matrix.mul_assoc,(boom p c).LR]; exact Matrix.mul_one _
  right_inv y := by simp only [Matrix.mul_assoc,(boom p c).RL]; exact Matrix.mul_one _

def kite (p : Shape) (c : Flit n) (N) : Orient p n N ≃ Orient p n N :=
  Equiv.piCongrRight (fun _ => (fuse p c N).prodCongr (fuse p c N))

end Move

def flowZ (p : Shape) (w : Wgt (Knobs p.g n)) :=
  ∀ i j,w (update i Block.Z j) = w i

end HadwigerCounterexample

end

end OAI
end

section
-- module Solutions.OAIQ430_HC.HadwigerCounterexample_RandomLinearTransforms
attribute [-instance] _root_.OAI.HadwigerCounterexample.Template.datumFinite _root_.OAI.HadwigerCounterexample.Template.inpFinite _root_.OAI.HadwigerCounterexample.Template.keySlotFinite _root_.OAI.HadwigerCounterexample.arrFintype _root_.OAI.HadwigerCounterexample.drawFintype _root_.OAI.HadwigerCounterexample.idxDec _root_.OAI.HadwigerCounterexample.momFintype _root_.OAI.HadwigerCounterexample.rackFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Random Linear Transforms -/

noncomputable section
namespace HadwigerCounterexample
open Matrix Module LinearMap Submodule Finset Function
open scoped BigOperators
variable {I J K : Type} [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]
    [Fintype K] [DecidableEq K]

namespace Move

instance finiteMove (I : Type) [Fintype I] [DecidableEq I] : Fintype (Move I) := by
  classical
  let S := { z : Mat I I × Mat I I // z.1*z.2 = 1 ∧ z.2*z.1=1}
  let e : S ≃ Move I := {
    toFun z := ⟨z.val.1,z.val.2,z.property.1,z.property.2⟩
    invFun z := ⟨(z.L,z.R),z.LR,z.RL⟩
    left_inv _ := rfl
    right_inv _ := rfl }
  exact Fintype.ofEquiv S e

instance identity_move (I : Type) [Fintype I] [DecidableEq I] : Nonempty (Move I) :=
  ⟨1,1, Matrix.one_mul _,Matrix.mul_one _⟩
def combine (c d : Move I) : Move I :=
  ⟨c.L*d.L,d.R*c.R,by rw [Matrix.mul_assoc,←Matrix.mul_assoc d.L,d.LR,Matrix.one_mul,c.LR],
    by rw [Matrix.mul_assoc,←Matrix.mul_assoc c.R,c.RL,Matrix.one_mul,d.RL]⟩

@[ext] theorem extn (p q : Move I) (h : p.L=q.L) (h' : p.R=q.R) : p=q := by
  cases p; cases q; cases h; cases h'; rfl
def circShift (c : Move I) : Move I≃ Move I where
  toFun := combine c
  invFun := combine c.sym
  left_inv d := extn _ _ (by simp only [combine,sym,←Matrix.mul_assoc,c.RL, Matrix.one_mul])
    (by simp only [combine,sym,Matrix.mul_assoc,c.RL, Matrix.mul_one])
  right_inv d := extn _ _ (by simp only [combine,sym,←Matrix.mul_assoc,c.LR, Matrix.one_mul])
    (by simp only [combine,sym,Matrix.mul_assoc,c.LR, Matrix.mul_one])
def flipLines (I : Type) [Fintype I] [DecidableEq I] : Move I≃ Move I where
  toFun := Move.dual
  invFun := Move.dual
  left_inv _ := rfl
  right_inv _ := rfl

variable {n : ℕ}
def plume {n : ℕ} (c : Flit n) (S : Space (Vec (Fin n))) :=
  colSp (c.Rᵀ*pack S)

end Move
end HadwigerCounterexample

end

end OAI
end

section
-- module Solutions.OAIQ430_HC.HadwigerCounterexample_FreeBlockFourier
attribute [-instance] _root_.OAI.HadwigerCounterexample.Template.datumFinite _root_.OAI.HadwigerCounterexample.Template.inpFinite _root_.OAI.HadwigerCounterexample.Template.keySlotFinite _root_.OAI.HadwigerCounterexample.arrFintype _root_.OAI.HadwigerCounterexample.drawFintype _root_.OAI.HadwigerCounterexample.idxDec _root_.OAI.HadwigerCounterexample.momFintype _root_.OAI.HadwigerCounterexample.rackFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Free Block Fourier -/

noncomputable section
namespace HadwigerCounterexample
open Finset Matrix Module LinearMap Filter Function
open scoped BigOperators
variable {p : Shape} {n : ℕ} {I A : Type} [Fintype I] [DecidableEq I]
variable [Fintype A]

def zhat (p : Shape) (f : Wgt (Knobs p.g n)) (x : Knobs p.g n) (i : Vec (Fin n)) :=
  avg unif (fun y => vectorPhase i y * f (update x Block.Z y))
def zchar (p : Shape) (f : Wgt (Knobs p.g n)) (i : Vec (Fin n)) (x : Knobs p.g n) :=
  zhat p f x i * vectorPhase i (x Block.Z)
def zim (p : Shape) (f : Wgt (Knobs p.g n)) (s : Finset (Vec (Fin n))) (x) :=
  ∑ i∈s,zchar p f i x

end HadwigerCounterexample

end

end OAI
end

section
-- module Solutions.OAIQ430_HC.HadwigerCounterexample_QuadraticFourier
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Quadratic Fourier -/

noncomputable section
namespace HadwigerCounterexample
open scoped BigOperators
open Matrix Module LinearMap Submodule Function Finset
variable {I J : Type} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]

def polarize (f : Vec I→F) (M : Mat I I) :=
  ∀ x y,f (x+y)+f x=f y+f 0+dotProduct y (M *ᵥ x)

end HadwigerCounterexample

end

end OAI
end

section
-- module Solutions.OAIQ430_HC.HadwigerCounterexample_TesterFourierSupport
attribute [-instance] _root_.OAI.HadwigerCounterexample.Template.datumFinite _root_.OAI.HadwigerCounterexample.Template.inpFinite _root_.OAI.HadwigerCounterexample.Template.keySlotFinite _root_.OAI.HadwigerCounterexample.arrFintype _root_.OAI.HadwigerCounterexample.drawFintype _root_.OAI.HadwigerCounterexample.idxDec _root_.OAI.HadwigerCounterexample.momFintype _root_.OAI.HadwigerCounterexample.rackFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Tester Fourier Support -/

noncomputable section
namespace HadwigerCounterexample
open Matrix Module Submodule Function LinearMap Finset
open scoped BigOperators
variable {p : Shape} {n : ℕ}

namespace Template

variable (v : Solo p)
def shanty (v : Solo p) (m : Mixer p n) (x : Profile p n) (t : Knobs p.g n) :=
  wsign (Tsym m x (useAtom p (v.t ()) (v.s ()) (v.f ()) t))
def stave (v : Solo p) (n : ℕ) := blockRay p n (v.s ()) Block.Z
def slash (v : Solo p) (m : Mixer p n) (x : Profile p n) := qmix m x (v.t ())

def scroll (v : Solo p) (m : Mixer p n) (x : Profile p n) :=
  let P:=stave v n; let M := slash v m x
  colSp (Pᵀ*M) ⊔ colSp (Pᵀ*Mᵀ)

end Template
end HadwigerCounterexample

end

end OAI
end

section
-- module Solutions.OAIQ430_HC.HadwigerCounterexample_ReindexedFourierSupport
attribute [-instance] _root_.OAI.HadwigerCounterexample.Template.datumFinite _root_.OAI.HadwigerCounterexample.Template.inpFinite _root_.OAI.HadwigerCounterexample.Template.keySlotFinite _root_.OAI.HadwigerCounterexample.arrFintype _root_.OAI.HadwigerCounterexample.drawFintype _root_.OAI.HadwigerCounterexample.idxDec _root_.OAI.HadwigerCounterexample.momFintype _root_.OAI.HadwigerCounterexample.rackFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Reindexed Fourier Support -/

noncomputable section
namespace HadwigerCounterexample
open Finset Matrix Module LinearMap Submodule Function
open scoped BigOperators
variable {p : Shape} {n : ℕ} {I : Type} [Fintype I]

namespace Move
variable (c : Flit n) {j k : Vec (Fin n)}
def jumpV : Vec (Fin n) ≃ Vec (Fin n) where
  toFun := c.L.mulVec
  invFun := c.R.mulVec
  left_inv x := by change c.R*ᵥ(c.L *ᵥ x) = x; rw [mulVec_mulVec,c.RL,Matrix.one_mulVec]
  right_inv x := by change c.L*ᵥ(c.R *ᵥ x) = x; rw [mulVec_mulVec,c.LR,Matrix.one_mulVec]
def zreroute (p : Shape) (c : Flit n) (f : Wgt (Knobs p.g n)) :=
  fun y => f ((vault p c).symm y)

end Move

namespace Template
variable (v : Solo p)

def rotor (v : Solo p) (c : Flit n) (m : Mixer p n) (x : Profile p n) :=
  Move.zreroute p c (v.shanty m x)
end Template
end HadwigerCounterexample

end

end OAI
end

section
-- module Solutions.OAIQ430_HC.HadwigerCounterexample_OrthogonalSpectrumBounds
attribute [-instance] _root_.OAI.HadwigerCounterexample.Template.datumFinite _root_.OAI.HadwigerCounterexample.Template.inpFinite _root_.OAI.HadwigerCounterexample.Template.keySlotFinite _root_.OAI.HadwigerCounterexample.arrFintype _root_.OAI.HadwigerCounterexample.drawFintype _root_.OAI.HadwigerCounterexample.idxDec _root_.OAI.HadwigerCounterexample.momFintype _root_.OAI.HadwigerCounterexample.rackFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Orthogonal Spectrum Bounds -/

noncomputable section
namespace HadwigerCounterexample
open Finset Matrix Module LinearMap Submodule Function
open scoped BigOperators
variable {p : Shape} {n : ℕ}

def fieldRad (S : Space (Vec (Fin n))) : Finset (Vec (Fin n)) :=
  open Classical in univ.filter (fun i => i∈S)
@[simp] theorem mem_fieldRad (S : Space (Vec (Fin n))) (i) :
    i∈fieldRad S↔i∈S := by simp [fieldRad]

def zsafe (p : Shape) (w f : Wgt (Knobs p.g n)) (S : Space (Vec (Fin n))) :=
  ∀ (g : Wgt (Knobs p.g n)) (t : Finset (Vec (Fin n))),
    (∀ i∈t,i∉S) → avg w (fun i => f i * zim p g t i)=0
def zsumPeak (p : Shape) (w f : Wgt (Knobs p.g n)) (P : Knobs p.g n → Prop) :=
  avg w (fun i => ind (P i)*f i)

end HadwigerCounterexample

end

end OAI
end

section
-- module Solutions.OAIQ430_HC.HadwigerCounterexample_OrientationRankBounds
attribute [-instance] _root_.OAI.HadwigerCounterexample.Template.datumFinite _root_.OAI.HadwigerCounterexample.Template.inpFinite _root_.OAI.HadwigerCounterexample.Template.keySlotFinite _root_.OAI.HadwigerCounterexample.arrFintype _root_.OAI.HadwigerCounterexample.drawFintype _root_.OAI.HadwigerCounterexample.idxDec _root_.OAI.HadwigerCounterexample.momFintype _root_.OAI.HadwigerCounterexample.rackFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Orientation Rank Bounds -/

noncomputable section
namespace HadwigerCounterexample
open Finset Matrix Module LinearMap Submodule Function Filter Real
open scoped BigOperators
variable {p : Shape} {n N : ℕ}
namespace Template
variable (v : Solo p)
variable {K s : ℕ}
def offBeat (v : Solo p) (P : AtomKey (p:=p) (v.t ()) N →Prop) (o : Orient p n N) :=
  fun z => P (v.desc z o)

def glow (m : Mixer p n) (w : Wgt (Knobs p.g n)) (A : AtomKey (p:=p) (v.t ()) N →Prop)
    (g δ : ℝ) (x : Profile p n) (o : Orient p n N) :=
  let P := offBeat v A o
  δ ≤ pr w P ∧ g*pr w P ≤ |zsumPeak p w (shanty v m x) P|

end Template
end HadwigerCounterexample

end

end OAI
end

section
-- module Solutions.OAIQ430_HC.HadwigerCounterexample_BasisConditioning
attribute [-instance] _root_.OAI.HadwigerCounterexample.Template.datumFinite _root_.OAI.HadwigerCounterexample.Template.inpFinite _root_.OAI.HadwigerCounterexample.Template.keySlotFinite _root_.OAI.HadwigerCounterexample.arrFintype _root_.OAI.HadwigerCounterexample.drawFintype _root_.OAI.HadwigerCounterexample.idxDec _root_.OAI.HadwigerCounterexample.momFintype _root_.OAI.HadwigerCounterexample.rackFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Basis Conditioning -/

noncomputable section
namespace HadwigerCounterexample
open Matrix Module LinearMap Finset Filter Function
open scoped BigOperators
variable {p : Shape} {n N : ℕ} {I : Type} [Fintype I] [DecidableEq I]

def glintRate (K : ℕ) := bp (-((K^2:ℕ):ℝ)-3)

namespace Template
variable (v : Solo p)

def stains (m : Mixer p n) (f : Vec I →ₗ[F] Profile p n) (z : Knobs p.g n) : Vec I :=
  fun i=> Tsym m (f (Pi.single i 1)) (useAtom p (v.t ()) (v.s ()) (v.f ()) z)

def luminous (v : Solo p) (m : Mixer p n) (w : Wgt (Knobs p.g n)) (D : AtomKey (p:=p) (v.t ())
    N →Prop) (K : ℕ) (i : Orient p n N) :=
  let P := offBeat v D i
  0<pr w P ∧ ∀ (d : ℕ), d≤ K^2 → ∀ f : Vec (Fin d)→ₗ[F] Profile p n,
    Injective f → (∀ x,totalRank (f x)≤K) → ∀ x,
    (7/8:ℝ)*bp (-(d:ℝ)) ≤ pr (onW w P) (fun z=> stains v m f z=x)

end Template
end HadwigerCounterexample

end

end OAI
end

section
-- module Solutions.OAIQ430_HC.HadwigerCounterexample_ScalarStatusAlgebra
attribute [-instance] _root_.OAI.HadwigerCounterexample.Template.datumFinite _root_.OAI.HadwigerCounterexample.Template.inpFinite _root_.OAI.HadwigerCounterexample.Template.keySlotFinite _root_.OAI.HadwigerCounterexample.arrFintype _root_.OAI.HadwigerCounterexample.drawFintype _root_.OAI.HadwigerCounterexample.idxDec _root_.OAI.HadwigerCounterexample.momFintype _root_.OAI.HadwigerCounterexample.rackFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Scalar Status Algebra -/

noncomputable section
namespace HadwigerCounterexample
open Matrix LinearMap Submodule Finset Function Module
open scoped BigOperators

namespace StatusAnalysis
abbrev Nodes := Bool
abbrev Grid := Nodes × Nodes
abbrev Cell (d : ℕ) := Vec (Fin d)

abbrev Par (d : ℕ) := F × Cell d
abbrev Whole (d : ℕ) := Par d × F

abbrev Signal (d e : ℕ) := F × Whole d × Whole e
abbrev View (d e : ℕ) := F × Par d × Par e
abbrev Question (d e : ℕ) := F × F × Cell d × Cell e
variable {d e : ℕ}

def view (d e : ℕ) : Signal d e→ₗ[F] View d e where
  toFun x := (x.1,x.2.1.1,x.2.2.1)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
def testV (d e : ℕ) : View d e →ₗ[F] Question d e where
  toFun x := (x.1,x.2.1.1 + x.2.2.1,x.2.1.2,x.2.2.2)
  map_add' _ _ := Prod.ext rfl (Prod.ext (add_add_add_comm ..) rfl)
  map_smul' _ _ := Prod.ext rfl (Prod.ext (mul_add _ _ _).symm rfl)
def want (d e : ℕ) := testV d e ∘ₗ view d e

def couple (d : ℕ) : Whole d→ₗ[F] F where
  toFun x := x.1.1+x.2
  map_add' _ _ := add_add_add_comm ..
  map_smul' a _ := (mul_add a _ _).symm

def coverBase (V : Space (Signal d e)) := Surjective (view d e ∘ₗ V.subtype)

abbrev Rates := Nodes→ℕ
abbrev Suite (A B : Rates) (i : Grid) := Signal (A i.1) (B i.2)
abbrev LedgerS (A B : Rates) (i : Grid) := Question (A i.1) (B i.2)
abbrev Cabinet (A B : Rates) := ∀ i, LedgerS A B i
abbrev Quota := Vec Nodes
abbrev Court (A B : Rates) := Cabinet A B × Quota × Quota
abbrev StatusSp (A B : Rates) := ∀ i,Space (Suite A B i)
variable {A B : Rates}

def separate (A B : Rates) (i : Grid) :
    Suite A B i →ₗ[F] Court A B :=
  (LinearMap.single F (LedgerS A B) i ∘ₗ want _ _).prod
    ((LinearMap.single F (fun _ : Bool=>F) i.2 ∘ₗ
      (couple (A i.1) ∘ₗ LinearMap.fst F _ _ ∘ₗ LinearMap.snd F _ _)).prod
     (LinearMap.single F (fun _ : Bool=>F) i.1 ∘ₗ
      (couple (B i.2) ∘ₗ LinearMap.snd F _ _ ∘ₗ LinearMap.snd F _ _)))

def speak (A B : Rates) :
    (∀ i,Suite A B i) →ₗ[F] Court A B := ∑ i:Grid,separate A B i ∘ₗ LinearMap.proj i

def scorecard (V : StatusSp A B) (T : Cabinet A B) :=
  ∃ v : ∀ i,Suite A B i,(∀ i,v i∈V i) ∧ speak A B v=(T,0)

structure Critic (A B : Rates) where
  alf : ∀ i : Grid, LedgerS A B i →ₗ[F] F
  altL : Quota
  altR : Quota
def Counter (g : Critic A B) (V : StatusSp A B) :=
  ∀ i:Grid,∀ v∈V i, g.alf i (want _ _ v) =
    g.altL i.2 * couple _ v.2.1 + g.altR i.1 * couple _ v.2.2

end StatusAnalysis
end HadwigerCounterexample

end

end OAI
end

section
-- module Solutions.OAIQ430_HC.HadwigerCounterexample_CoordinateDuality
attribute [-instance] _root_.OAI.HadwigerCounterexample.Template.datumFinite _root_.OAI.HadwigerCounterexample.Template.inpFinite _root_.OAI.HadwigerCounterexample.Template.keySlotFinite _root_.OAI.HadwigerCounterexample.arrFintype _root_.OAI.HadwigerCounterexample.drawFintype _root_.OAI.HadwigerCounterexample.momFintype _root_.OAI.HadwigerCounterexample.rackFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Coordinate Duality -/

noncomputable section
namespace HadwigerCounterexample
open Finset Matrix Module LinearMap Submodule Function
open scoped BigOperators
namespace StatusAnalysis
variable {A B : Rates} {d e : ℕ}

structure DualCoefficients (A B : Rates) where
  left : Quota
  right : Quota
  gam : Grid→F
  hed : Grid→F
  north : (i:Grid)→ Cell (A i.1)
  south : (i:Grid)→ Cell (B i.2)
def DualCoefficients.bet (p : DualCoefficients A B) (i : Grid) (x : LedgerS A B i) :=
  p.gam i * x.1 + p.hed i * x.2.1 + (dotProduct (p.north i) x.2.2.1+
    dotProduct (p.south i) x.2.2.2)
def DualCoefficients.law (p : DualCoefficients A B) (V : StatusSp A B) :=
  ∀ i:Grid,∀ v∈V i, p.bet i (want _ _ v) =
    p.left i.2 * couple _ v.2.1 + p.right i.1 * couple _ v.2.2

abbrev excessK (V : Space (Signal d e)) := V ⊓ LinearMap.ker (view d e)

def overage (V : Space (Signal d e)) := dim V - dim (View d e)
end StatusAnalysis
end HadwigerCounterexample

end

end OAI
end

section
-- module Solutions.OAIQ430_HC.HadwigerCounterexample_LabeledGenerators
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Labeled Generators -/

noncomputable section
namespace HadwigerCounterexample
open Finset Matrix Function LinearMap Submodule Module
open scoped BigOperators
namespace StatusAnalysis
variable {L I X Y : Type} [DecidableEq L] [DecidableEq I] [AddCommGroup X]
    [Module F X] [AddCommGroup Y] [Module F Y]

structure Club (I X L : Type) where
  valid : I→Prop
  writes : I→ X
  addr : I→ Bool→L

abbrev Straps (L : Type) := Bool→Finset L
variable (C : Club I X L)
namespace Club
def zone (s : Straps L) (i) := C.valid i ∧ ∀ b,C.addr i b∉s b
def band (s : Straps L) : Space X := Submodule.span F {x|∃ i, C.zone s i∧C.writes i=x}
def bundle (p : Finset I) (s : Straps L) :=
  (∀ i∈p,zone C s i) ∧ ∀ b : Bool, Set.InjOn (fun i=> C.addr i b) (p : Set I)
def contents (p : Finset I) := ∑ i∈p,C.writes i

def length3 (s : Straps L) (π : X→ₗ[F] Y) (x : X) :=
    ∃ p : Finset I,C.bundle p s ∧ p.card≤3 ∧ C.contents p=x ∧ π x=0
def ration (s : Straps L) (π : X→ₗ[F] Y) : Space X := Submodule.span F (C.length3 s π)

def yield3 (s : Straps L) (π : X→ₗ[F] Y) :=
  ∀ u:Straps L,(∀ b,(u b).card≤2) → ∀ y,∃ i,zone C (s⊔u) i ∧ π (C.writes i)=y

def addrs (p : Finset I) : Straps L := fun b=>p.image (fun i=> C.addr i b)

def different (i j : I) := ∀ b,C.addr i b≠ C.addr j b
end Club
end StatusAnalysis
end HadwigerCounterexample

end

end OAI
end

section
-- module Solutions.OAIQ430_HC.HadwigerCounterexample_FreshGeneratorCorrection
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Fresh Generator Correction -/

noncomputable section
namespace HadwigerCounterexample
open Finset Matrix Function LinearMap Submodule Module
open scoped BigOperators
namespace StatusAnalysis
variable {L I X Y : Type} [DecidableEq L] [DecidableEq I]
variable [AddCommGroup X] [Module F X] [AddCommGroup Y] [Module F Y]
namespace Club
variable (C : Club I X L)

abbrev sizeB (t : Straps L) (r : ℕ) := ∀ i,(t i).card≤ r

def travels (s : Straps L) (n : ℕ) (π : X →ₗ[F] Y) (V : Space X) :=
  ∀ t:Straps L,sizeB t n→ C.band (s⊔t)=V ∧ C.yield3 (s⊔t) π

end Club
end StatusAnalysis
end HadwigerCounterexample

end

end OAI
end

section
-- module Solutions.OAIQ430_HC.HadwigerCounterexample_ReservedLabels
attribute [-instance] _root_.OAI.HadwigerCounterexample.Template.datumFinite _root_.OAI.HadwigerCounterexample.Template.inpFinite _root_.OAI.HadwigerCounterexample.Template.keySlotFinite _root_.OAI.HadwigerCounterexample.arrFintype _root_.OAI.HadwigerCounterexample.drawFintype _root_.OAI.HadwigerCounterexample.momFintype _root_.OAI.HadwigerCounterexample.rackFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Reserved Labels -/

noncomputable section
namespace HadwigerCounterexample
open Matrix Module LinearMap Submodule Function Finset
open scoped BigOperators
namespace StatusAnalysis
variable {I L : Type} [DecidableEq L] [DecidableEq I] {d e : ℕ}
open Club

variable {I : Grid → Type} [∀ i,DecidableEq (I i)] {A B : Rates}
abbrev Congress (I : Grid→Type) (A B : Rates) (L : Type) := ∀ i,Club (I i) (Suite A B i) L
namespace Guild
variable (C : Congress I A B L)
def chapter (s : Straps L) : StatusSp A B := fun i=> (C i).band s
def excess (s : Straps L) := ∑ i:Grid,overage (chapter C s i)

def rich (C : Congress I A B L) :=
  ∀ i:Grid,∀ s:Straps L,sizeB s 902 → ∀ y:View (A i.1) (B i.2),∃ j,
    (C i).zone s j ∧ view _ _ ((C i).writes j)=y

end Guild
end StatusAnalysis
end HadwigerCounterexample

end

end OAI
end

section
-- module Solutions.OAIQ430_HC.HadwigerCounterexample_FourEdgeFamilies
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Four Edge Families -/

noncomputable section
namespace HadwigerCounterexample
open Matrix Module LinearMap Submodule Finset Function
open scoped BigOperators
namespace StatusAnalysis
variable {A B : Rates} {I : Grid→Type} {L : Type} [DecidableEq L] [∀ i,DecidableEq (I i)]
namespace Guild
open Club
variable (C : Congress I A B L)

abbrev Bags (I : Grid→Type) := ∀ i,Finset (I i)
structure Parade (s : Straps L) (v : ∀ i,Suite A B i) (g : Bags I) (p : Finset Grid) : Prop where
  batch (i) (h : i∈p) :
    (C i).bundle (g i) s ∧ (C i).contents (g i)=v i∧ 1≤(g i).card∧(g i).card≤7
  mixed (i j) (hx : i∈p) (hy:j∈p) (he : i≠j) x (hX : x∈g i) y (hY : y∈g j) (b) :
    (C i).addr x b ≠ (C j).addr y b

end Guild
end StatusAnalysis
end HadwigerCounterexample

end

end OAI
end

section
-- module Solutions.OAIQ430_HC.HadwigerCounterexample_PolynomialZeroTests
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Polynomial Zero Tests -/

noncomputable section
namespace HadwigerCounterexample
open Finset Matrix Module LinearMap Submodule Function
open scoped BigOperators
variable {A I J : Type} [Fintype A] [DecidableEq A]

def poly1 (s : Finset A) (x : Vec A) := ∏ i∈s,x i

def Stocks (A : Type) (d : ℕ) : Space (Vec (Vec A)) :=
  open Classical in Submodule.span F {x | ∃ s : Finset A,s.card ≤ d ∧ x = poly1 s}

def spoil (p : Vec A) : Vec (Vec A) →ₗ[F] Vec (Vec A) where
  toFun f := fun i => f (i+p)-f i
  map_add' a b := funext fun i=>by simp only [Pi.add_apply] <;> ring
  map_smul' a b := funext fun i=>by
    simp only [Pi.smul_apply,smul_eq_mul,RingHom.id_apply] <;> ring

end HadwigerCounterexample

end

end OAI
end

section
-- module Solutions.OAIQ430_HC.HadwigerCounterexample_UnaryPositivityBounds
attribute [-instance] _root_.OAI.HadwigerCounterexample.Template.datumFinite _root_.OAI.HadwigerCounterexample.Template.inpFinite _root_.OAI.HadwigerCounterexample.Template.keySlotFinite _root_.OAI.HadwigerCounterexample.arrFintype _root_.OAI.HadwigerCounterexample.drawFintype _root_.OAI.HadwigerCounterexample.idxDec _root_.OAI.HadwigerCounterexample.momFintype _root_.OAI.HadwigerCounterexample.rackFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Unary Positivity Bounds -/

noncomputable section
namespace HadwigerCounterexample
open Finset Matrix Module LinearMap Function Filter
open scoped BigOperators
variable {p : Shape} {n N : ℕ}
namespace Template
variable (v : Solo p)

def patrol (m : Mixer p n) (w : Wgt (Knobs p.g n))
    (S : AtomKey (p:=p) (v.t ()) N→Prop) (K : ℕ) (q : F) (x : Orient p n N) :=
  luminous v m w S K x ∧
    3/4*pr (lawOmega p N (v.t ()) q) S ≤ pr w (offBeat v S x)

variable {K s : ℕ}

def basebeta (p : Shape) (K : ℕ) :=
  bp (-((K^2:ℕ):ℝ)-1)* scanPrice p

end Template
end HadwigerCounterexample

end

end OAI
end

section
-- module Solutions.OAIQ430_HC.HadwigerCounterexample_CommonPredictions
attribute [-instance] _root_.OAI.HadwigerCounterexample.Template.datumFinite _root_.OAI.HadwigerCounterexample.Template.inpFinite _root_.OAI.HadwigerCounterexample.Template.keySlotFinite _root_.OAI.HadwigerCounterexample.arrFintype _root_.OAI.HadwigerCounterexample.drawFintype _root_.OAI.HadwigerCounterexample.idxDec _root_.OAI.HadwigerCounterexample.momFintype _root_.OAI.HadwigerCounterexample.rackFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Common Predictions -/

noncomputable section
namespace HadwigerCounterexample
open Matrix Module LinearMap Function Finset Submodule
open scoped BigOperators
variable {p : Shape} {n N : ℕ}

abbrev Augur (p : Shape) (N : ℕ) := ∀ t : Tag p.g,F→AtomKey (p:=p) t N→F
def mismatch (p : Shape) {n N : ℕ} (g : Augur p N) (F : Pdual p n) (l : Tag p.g)
    (s : Label p.b) (f : Flavor p.g) (x : Orient p n N) (y : Knobs p.g n) :=
  F (useAtom p l s f y)≠ g l (dialed p l f y) (keyOne p l s (lit f l y) x)
def postulates (p : Shape) (o : Orient p n N)
    (g : Augur p N) (w : Pdual p n) (E : Finset (Label p.b)) (δ : ℝ) :=
  ∀ s,s∉E→∀ l f, pr (spins p n) (fun i => mismatch p g w l s f o i)≤δ

def yoke (p : Shape) (m : Mixer p n) (x : UnitType p n N) (i : Bool)
    (u : Profile p n) (α : F) : Pdual p n :=
  innerP p x i + (Tsym m u + α • role p n)

def claimed (p : Shape) (x : UnitType p n N)
    (g : Bool→Augur p N) (m : Mixer p n)
    (w : Bool→Profile p n) (α : Bool→F) (L : Bool → Finset (Label p.b)) (δ : ℝ) :=
  ∀ i,postulates p (onSide x i) (g i) (yoke p m x i (w i) (α i)) (L i) δ

def silent (w : Pdual p n) := ∀ x, x∈Xspace p n → w x=0

def fixStar (p : Shape) (n : ℕ) (l : Tag p.g) :
    Moment p n →ₗ[F] Profile p n :=
  cut p n ∘ₗ LinearMap.single F (fun _ : Tag p.g => Moment p n) l
end HadwigerCounterexample

end

end OAI
end

section
-- module Solutions.OAIQ430_HC.HadwigerCounterexample_PredictionExactification
attribute [-instance] _root_.OAI.HadwigerCounterexample.Template.datumFinite _root_.OAI.HadwigerCounterexample.Template.inpFinite _root_.OAI.HadwigerCounterexample.Template.keySlotFinite _root_.OAI.HadwigerCounterexample.arrFintype _root_.OAI.HadwigerCounterexample.drawFintype _root_.OAI.HadwigerCounterexample.idxDec _root_.OAI.HadwigerCounterexample.momFintype _root_.OAI.HadwigerCounterexample.rackFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Prediction Exactification -/

noncomputable section
namespace HadwigerCounterexample
open Finset Matrix LinearMap Function Filter Real
open scoped BigOperators
variable {p : Shape} {n N : ℕ}

def tabErr (p : Shape) (l : Tag p.g) (s : Label p.b) (o : Orient p n N)
    (x : F) (g : Augur p N) (f : F) :=
  let v := Template.solo p l s Flavor.full
  let u:= scopedBit p n l Flavor.full x
  pr u (fun i=> g l x (v.desc i o)≠ f*x)
def tabRef (p : Shape) (l : Tag p.g) (x : F) (g : Augur p N) (f : F) :=
  pr (lawOmega p N l x) (fun i=> g l x i≠f*x)

def whisper (p : Shape) (g : Augur p N) (x : F) (i : Orient p n N) :=
  ∀ l s b,tabErr p l s i b g x ≤1/32

end HadwigerCounterexample

end

end OAI
end

section
-- module Solutions.OAIQ430_HC.HadwigerCounterexample_StatusCharts
attribute [-instance] _root_.OAI.HadwigerCounterexample.Template.datumFinite _root_.OAI.HadwigerCounterexample.Template.inpFinite _root_.OAI.HadwigerCounterexample.Template.keySlotFinite _root_.OAI.HadwigerCounterexample.arrFintype _root_.OAI.HadwigerCounterexample.drawFintype _root_.OAI.HadwigerCounterexample.idxDec _root_.OAI.HadwigerCounterexample.momFintype _root_.OAI.HadwigerCounterexample.rackFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Status Charts -/

noncomputable section
namespace HadwigerCounterexample
open Finset Matrix Function Module LinearMap Submodule
open scoped BigOperators

namespace StatusAnalysis
abbrev Ax (p : Shape) (n : ℕ) (d : ℕ) := Cell d→ₗ[F] Profile p n
abbrev Charts (p : Shape) (n : ℕ) (d : Rates) := ∀ i, Ax p n (d i)
variable {p : Shape} {n N : ℕ} {d e : Rates}
def charted (v : Charts p n d) (w : Plan p n) :=
  ∀ i,LinearMap.range (v i)=effective w i ∧ Injective (v i)

abbrev Format := Grid→ℕ
abbrev Messenger (q : Format) := Σ i:Grid,Fin (q i)
def sendId (b : Bool) (i : Grid) := if b then i.1 else i.2
def transit (b : Bool) (q : Grid) := if b then q else (q.2,q.1)

def parcel (b : Bool) {q : Format} (x : Messenger q) := sendId b x.1
def manager {q : Format} (b : Bool) (t : Tagging p (Messenger q)) (s : Messenger q→Label p.b)
    (f : Messenger q→Flavor p.g) : Template p (Messenger q) := ⟨parcel b,t,s,f⟩

def roll {u : ℕ} (f : Ax p n u) (g : Pdual p n) : Cell u := fun i=>g (f (Pi.single i 1))

def targetMark (p : Shape) (v : Charts p n d) (M : Cross p n) (i j : Nodes) : Cell (d i) :=
  roll (v i) (contract p M i j + role p n)
def hailing (p : Shape) (v : Charts p n d) (z : Charts p n e) (M : Cross p n) :
    Cabinet d e :=
  fun i => (1,1,targetMark p v M i.1 i.2,targetMark p z (reciprocal p M) i.2 i.1)

abbrev Magazine (p : Shape) (d : ℕ) := Digest p.g × Whole d
def specify (p : Shape) {d : ℕ} (i : Nodes) (v : Ax p n d)
    (m : Mixer p n) (o : UnitType p n N) (l : Tag p.g) (s : Label p.b) (f : Flavor p.g)
    (x : Knobs p.g n) : Magazine p d :=
  let A:=useAtom p l s f x
  (scan p l f x, (role p n A,roll v (Tsym m A)),innerP p o i A)

variable {q : Format}

def printed (b : Bool) (v : Charts p n d) (t : Tagging p (Messenger q))
    (s : Messenger q →Label p.b) (f : Messenger q → Flavor p.g) (m : Mixer p n)
    (o : UnitType p n N) (x : Inputs p n (Messenger q)) :=
  fun i => specify p (parcel b i) (v (parcel b i)) m o (t i) (s i) (f i) (x i)
abbrev Amounts (p : Shape) (q : Format) (d : Rates) (b : Bool) :=
    ∀ i:Messenger q,Magazine p (d (parcel b i))
def sendSum (u : Messenger q→F) (a : Amounts p q d true) (b : Amounts p q e false) :
    ∀ i : Grid, Suite d e i :=
  fun i=> ∑ j:Fin (q i), (u ⟨i,j⟩,(a ⟨i,j⟩).2,(b ⟨i,j⟩).2)

end StatusAnalysis
end HadwigerCounterexample

end

end OAI
end

section
-- module Solutions.OAIQ430_HC.HadwigerCounterexample_ExplicitStatusEquations
attribute [-instance] _root_.OAI.HadwigerCounterexample.Template.datumFinite _root_.OAI.HadwigerCounterexample.Template.inpFinite _root_.OAI.HadwigerCounterexample.Template.keySlotFinite _root_.OAI.HadwigerCounterexample.arrFintype _root_.OAI.HadwigerCounterexample.drawFintype _root_.OAI.HadwigerCounterexample.idxDec _root_.OAI.HadwigerCounterexample.momFintype _root_.OAI.HadwigerCounterexample.rackFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Explicit Status Equations -/

noncomputable section
namespace HadwigerCounterexample
open Matrix Module LinearMap Submodule Finset Function
open scoped BigOperators
namespace StatusAnalysis
variable {d e : Rates} {p : Shape} {n N : ℕ} {q : Format}

def funds {b : Bool} (x : Amounts p q d b) (i : Grid) :
    Whole (d (sendId b i)) :=
  ∑ k: Fin (q i),(x (⟨i,k⟩ : Messenger q)).2
def fullq (z : Messenger q → F) (i : Grid) := ∑ k:Fin (q i),z ⟨i,k⟩

def still (b : Bool) (a : Amounts p q d b) (v : Charts p n d) (M : Cross p n) :=
  (∀ i:Grid,(funds a i).1.2= targetMark p v M (sendId b i) (sendId (!b) i))∧
    ∀ j:Bool,couple _ (funds a (transit b (true,j))) =
      couple _ (funds a (transit b (false,j)))

def rhyme {b : Bool} (a : Amounts p q d b) (x : Amounts p q e (!b)) :=
  ∀ i:Grid,(funds a i).1.1+(funds x i).1.1=1

end StatusAnalysis
end HadwigerCounterexample

end

end OAI
end

section
-- module Solutions.OAIQ430_HC.HadwigerCounterexample_StatusRecipes
attribute [-instance] _root_.OAI.HadwigerCounterexample.Template.datumFinite _root_.OAI.HadwigerCounterexample.Template.inpFinite _root_.OAI.HadwigerCounterexample.Template.keySlotFinite _root_.OAI.HadwigerCounterexample.arrFintype _root_.OAI.HadwigerCounterexample.drawFintype _root_.OAI.HadwigerCounterexample.idxDec _root_.OAI.HadwigerCounterexample.momFintype _root_.OAI.HadwigerCounterexample.rackFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Status Recipes -/

noncomputable section
namespace HadwigerCounterexample
open Finset Matrix Function LinearMap Module Submodule
open scoped BigOperators
namespace StatusAnalysis
variable {p : Shape} {n N : ℕ} {q : Format} {d e : Rates}
def registers {i : ℕ} (p : Shape) (j : Nodes) (v : Ax p n i) (m : Mixer p n)
    (x : UnitType p n N) : Profile p n→ₗ[F] Whole i where
  toFun z := ((role p n z,roll v (Tsym m z)),innerP p x j z)
  map_add' a b := by
    rw [map_add,map_add,map_add]; congr 1
  map_smul' a b := by
    rw [map_smul,map_smul,map_smul]; congr 1
def unionAt {p : Shape} {q : Format} (f : Messenger q → Profile p n) (i : Grid) :=
  ∑ j:Fin (q i), f ⟨i,j⟩

def owing (p : Shape) {q : Format} {d : Rates}
    (b : Bool) (a : Amounts p q d b) (u : Messenger q→ F) :=
  ∀ i,(a i).1.sumBit=u i

end StatusAnalysis
end HadwigerCounterexample

end

end OAI
end

section
-- module Solutions.OAIQ430_HC.HadwigerCounterexample_NumericalGradientTests
attribute [-instance] _root_.OAI.HadwigerCounterexample.Template.datumFinite _root_.OAI.HadwigerCounterexample.Template.inpFinite _root_.OAI.HadwigerCounterexample.Template.keySlotFinite _root_.OAI.HadwigerCounterexample.arrFintype _root_.OAI.HadwigerCounterexample.drawFintype _root_.OAI.HadwigerCounterexample.idxDec _root_.OAI.HadwigerCounterexample.momFintype _root_.OAI.HadwigerCounterexample.rackFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Numerical Gradient Tests -/

noncomputable section
namespace HadwigerCounterexample
open Finset Matrix Module LinearMap Function Submodule
open scoped BigOperators
namespace StatusAnalysis
variable {p : Shape} {n N : ℕ} {q : Format} {d e : Rates}
def mailRole {b} (a : Amounts p q d b) :=
  fun i=>(a i).2.1.1
def mailBias {b} (a : Amounts p q d b) :=
  fun i=>(a i).2.2

def TMill (p : Shape) {b} {d} (t : Tagging p (Messenger q)) (w : Amounts p q d b) :
    Mat (Messenger q) (Messenger q) :=
  let a (x : Tag p.g) (i : Messenger q) := ∑ z:Tag p.g,(w i).1 (Sum.inl (z,x))
  let f (x : Tag p.g) (i : Messenger q) :=
    let c:=(w i).1 (Sum.inr ())
    c+(if t i=x then c else 0)
  Matrix.of fun i j => mailRole w i * mailRole w j +
    ∑ x:Tag p.g,(a x i * f x j + f x i * a x j)

def proclaims {b : Bool} (p : Shape) {d e}
    (a : Amounts p q d b) (w : Amounts p q e (!b)) (t : Tagging p (Messenger q))
    (g : Script p (Messenger q)) :=
  fulfills p t (mailRole a) (mailBias w) (TMill p t a) g (parcel b) (parcel (!b))

end StatusAnalysis
end HadwigerCounterexample

end

end OAI
end

section
-- module Solutions.OAIQ430_HC.HadwigerCounterexample_FiniteTableEnumeration
attribute [-instance] _root_.OAI.HadwigerCounterexample.Template.datumFinite _root_.OAI.HadwigerCounterexample.Template.inpFinite _root_.OAI.HadwigerCounterexample.Template.keySlotFinite _root_.OAI.HadwigerCounterexample.arrFintype _root_.OAI.HadwigerCounterexample.drawFintype _root_.OAI.HadwigerCounterexample.idxDec _root_.OAI.HadwigerCounterexample.momFintype _root_.OAI.HadwigerCounterexample.rackFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Finite Table Enumeration -/

noncomputable section
namespace HadwigerCounterexample
open Matrix Finset LinearMap Submodule Module Function
open scoped BigOperators
variable {p : Shape} {n N : ℕ}
namespace StatusAnalysis
abbrev CouponDeck (p : Shape) {n} (a b : Plan p n) :=
  ∀ i : Place p,Mat (Fin (dim (tabSpace a i))) (Fin (dim (tabSpace b (flipZ p i))))
def nomen (p : Shape) {n} (a b : Plan p n) (v : Cross p n) : CouponDeck p a b :=
  fun i=>pullM (pack (tabSpace a i)) (pack (tabSpace b (flipZ p i))) (v i)

instance deckFin (p : Shape) (n : ℕ) (a b : Plan p n) : Fintype (CouponDeck p a b) := by
  classical
  infer_instance

def deckMax (p : Shape) (K : ℕ) :=
  Fintype.card (Place p)*(2*(K+p.h))^2

end StatusAnalysis
end HadwigerCounterexample

end

end OAI
end

section
-- module Solutions.OAIQ430_HC.HadwigerCounterexample_FinitePhaseAlternative
attribute [-instance] _root_.OAI.HadwigerCounterexample.StatusAnalysis.deckFin _root_.OAI.HadwigerCounterexample.Template.datumFinite _root_.OAI.HadwigerCounterexample.Template.inpFinite _root_.OAI.HadwigerCounterexample.Template.instDecidableEqAbbey _root_.OAI.HadwigerCounterexample.Template.instFintypeAbbey _root_.OAI.HadwigerCounterexample.Template.instFintypeOppDuet _root_.OAI.HadwigerCounterexample.Template.instFintypeSameDuet _root_.OAI.HadwigerCounterexample.Template.keySlotFinite _root_.OAI.HadwigerCounterexample.arrFintype _root_.OAI.HadwigerCounterexample.drawFintype _root_.OAI.HadwigerCounterexample.fintypeLedger _root_.OAI.HadwigerCounterexample.idxDec _root_.OAI.HadwigerCounterexample.knFin _root_.OAI.HadwigerCounterexample.momFintype _root_.OAI.HadwigerCounterexample.rackFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Finite Phase Alternative -/

noncomputable section
namespace HadwigerCounterexample
open Matrix LinearMap Module Submodule Function Finset
open scoped BigOperators
variable {p : Shape} {n N r : ℕ}

def maxSpan (m b r : ℕ) := r*(2^m*(2*b))

structure PhaseReady (p : Shape) (n N m b r k d : ℕ) (mix : Mixer p n)
    (c l ψ ε L H : ℝ) : Prop where
  hb : 1≤b
  hm : 16*r < m
  hk : k≤d
  hc : 0 < c
  hc' : c≤1
  hl : 0<l
  hl' : l≤1
  hψ : 0<ψ
  hε : 0<ε
  hL : 0≤ L
  hH : 0≤ H
  hN : 2*num (Full p n)-N≤ -1
  cap : initCap p N mix ε
  noBranch : ψ+noSweepBudget p N m b r c ψ H<0.005
  frames : scaleBill p n N (maxSpan m b r) L ≤ c/2
  atlas (T : Cov p N) (ht : ∀ i,cdSign p T i≤ maxSpan m b r) :
    num (Atlas p r T)≤bp (0.002*N)
  price : selPrice p r n N (rhUp L c) ε
  price' : selPrice p r n N (rhUp (rhUp L c) l) ε
  localQ : quest p r k n N (rhUp H c) ε
  testFailure : glimpsesBill p k (rhUp L c)+bp (-0.1*N)<l^(k+1)
  testFailure' : 2*glimpsesBill p d (rhUp L c)≤l/2
  beatSlack : 5*l+bp (-0.24*N)<0.005

def voidFrame (p : Shape) {N n} (x : UnitType p n N) (T : Cov p N) :=
  ∀ i z,Disjoint (T z) (imageP p x i z)

end HadwigerCounterexample

end

end OAI
end

section
-- module Solutions.OAIQ430_HC.HadwigerCounterexample_PhaseParameters
attribute [-instance] _root_.OAI.HadwigerCounterexample.Flavor.instDecidableKeeps _root_.OAI.HadwigerCounterexample.StatusAnalysis.deckFin _root_.OAI.HadwigerCounterexample.Template.datumFinite _root_.OAI.HadwigerCounterexample.Template.inpFinite _root_.OAI.HadwigerCounterexample.Template.instFintypeOppDuet _root_.OAI.HadwigerCounterexample.Template.instFintypeSameDuet _root_.OAI.HadwigerCounterexample.Template.keySlotFinite _root_.OAI.HadwigerCounterexample.arrFintype _root_.OAI.HadwigerCounterexample.drawFintype _root_.OAI.HadwigerCounterexample.fintypeLedger _root_.OAI.HadwigerCounterexample.knFin _root_.OAI.HadwigerCounterexample.momFintype _root_.OAI.HadwigerCounterexample.rackFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Phase Parameters -/

noncomputable section
namespace HadwigerCounterexample
open scoped BigOperators Topology
open Filter
variable {p : Shape} {n N : ℕ}

def mstep (r : ℕ) := 100*r+10
def Bstep (r : ℕ) := 2^(mstep r)*2
def denomStep (r : ℕ) := 10000*(r+1)^2*Bstep r

def stage (g r : ℕ) (D : ℝ) := 2*r*num (Comp g)+D+1
def pcoef (g r : ℕ) (D : ℝ) :=
  12*Bstep r+2*(denomStep r:ℝ)*stage g r D
def tinyPhase (g r : ℕ) (D : ℝ) := bp (-(pcoef g r D))
def warn := bp (-10)
def coin : ℝ := 0.0001
def heatloss (r k : ℕ) := 0.001 / (4*(r:ℝ)+k+1 : ℝ)

end HadwigerCounterexample

end

end OAI
end

section
-- module Solutions.OAIQ430_HC.HadwigerCounterexample_PinInjectionTests
attribute [-instance] _root_.OAI.HadwigerCounterexample.Flavor.instDecidableKeeps _root_.OAI.HadwigerCounterexample.StatusAnalysis.deckFin _root_.OAI.HadwigerCounterexample.Template.datumFinite _root_.OAI.HadwigerCounterexample.Template.inpFinite _root_.OAI.HadwigerCounterexample.Template.instDecidableEqAbbey _root_.OAI.HadwigerCounterexample.Template.instFintypeAbbey _root_.OAI.HadwigerCounterexample.Template.instFintypeOppDuet _root_.OAI.HadwigerCounterexample.Template.instFintypeSameDuet _root_.OAI.HadwigerCounterexample.Template.keySlotFinite _root_.OAI.HadwigerCounterexample.arrFintype _root_.OAI.HadwigerCounterexample.drawFintype _root_.OAI.HadwigerCounterexample.fintypeLedger _root_.OAI.HadwigerCounterexample.idxDec _root_.OAI.HadwigerCounterexample.knFin _root_.OAI.HadwigerCounterexample.momFintype _root_.OAI.HadwigerCounterexample.rackFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Pin Injection Tests -/

noncomputable section
namespace HadwigerCounterexample

open Matrix LinearMap Module Submodule Finset Function
open scoped BigOperators
variable {p : Shape} {n N : ℕ}

abbrev Fpins (p : Shape) (n N : ℕ) := UnitType p n N → Plan p n

def rootSet (b : Fpins p n N) (x : UnitType p n N) (i : Bool) (z : Place p) :
    Space (Vec (Fin N)) :=
  (sPin (b x) z i).map (fpAt p (onSide x i) z).mulVecLin

def strikeH (b : Fpins p n N) (z : Place p) (j : Bool) (v : Vec (Fin N)) (y : UnitType p n N) :=
  (fyAt p (onSide y j) (flipZ p z))ᵀ*ᵥ v∈ hPin (b y) z j
def fans (b : Fpins p n N) (z : Place p) (i j : Bool) (x y : UnitType p n N) :=
  ∃ v∈rootSet b x i z,v≠0 ∧ strikeH b z j v y

def fireBill (p : Shape) (k K : ℕ) (H : ℝ) :=
  H*2 * bp ((p.h:ℝ)*K+(K-(p.h:ℝ))*k)

end HadwigerCounterexample

end

end OAI
end

section
-- module Solutions.OAIQ430_HC.HadwigerCounterexample_InjectionWitnesses
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Injection Witnesses -/

noncomputable section
namespace HadwigerCounterexample
open Matrix Module Submodule Function Finset
open scoped BigOperators
variable {I J K : Type} [Fintype I] [Fintype J] [Fintype K]
def moreMatrix_p1 {r : ℕ} (A : Mat I (Fin r)) (v : Vec I) : Mat I (Fin (r+1)) :=
  Matrix.of (fun i => Fin.cons (v i) (A i))

variable {p : Shape} {n N : ℕ}
def pushCost (l : ℝ) (K : ℕ) := l/bp K

end HadwigerCounterexample

end

end OAI
end

section
-- module Solutions.OAIQ430_HC.HadwigerCounterexample_TableInjectionTransfer
attribute [-instance] _root_.OAI.HadwigerCounterexample.StatusAnalysis.deckFin _root_.OAI.HadwigerCounterexample.Template.datumFinite _root_.OAI.HadwigerCounterexample.Template.inpFinite _root_.OAI.HadwigerCounterexample.Template.instDecidableEqAbbey _root_.OAI.HadwigerCounterexample.Template.instFintypeAbbey _root_.OAI.HadwigerCounterexample.Template.instFintypeOppDuet _root_.OAI.HadwigerCounterexample.Template.instFintypeSameDuet _root_.OAI.HadwigerCounterexample.Template.keySlotFinite _root_.OAI.HadwigerCounterexample.arrFintype _root_.OAI.HadwigerCounterexample.drawFintype _root_.OAI.HadwigerCounterexample.fintypeLedger _root_.OAI.HadwigerCounterexample.idxDec _root_.OAI.HadwigerCounterexample.momFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Table Injection Transfer -/

noncomputable section
namespace HadwigerCounterexample
open Matrix LinearMap Module Submodule Function Finset
open scoped BigOperators
variable {p : Shape} {n N : ℕ}
variable {A B : Type}

def named (P : A×A → Prop) (C : ℝ) :=
  ∃ k : ℕ,(k:ℝ) ≤ C ∧ ∃ S : Fin k → A → Prop,∀ y,∃ i,∀ x,P (x,y)↔S i x

def acceptsInj (p : Shape) {n N} (b : Fpins p n N) (x : UnitType p n N×UnitType p n N) :=
  tableInj (b x.1) (b x.2) (actual p x.1 x.2)

def secureAt (p : Shape) {n N} (b : Fpins p n N) (x : UnitType p n N×UnitType p n N) :=
  acceptsInj p b x ∧ acceptsInj p b x.swap

end HadwigerCounterexample

end

end OAI
end

section
-- module Solutions.OAIQ430_HC.HadwigerCounterexample_RelativeInjectionBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Relative Injection Bounds -/

noncomputable section
namespace HadwigerCounterexample

open Matrix LinearMap Module Submodule Function Finset Filter
open scoped BigOperators Topology
variable {p : Shape} {n N : ℕ}

def fringe (N : ℕ) := bp (-0.01*N)
def shine (N : ℕ) := bp (0.01*N)
def edgeError (N : ℕ) := bp (-0.005*N)

end HadwigerCounterexample

end

end OAI
end

section
-- module Solutions.OAIQ430_HC.HadwigerCounterexample_SmallCoverBounds
attribute [-instance] _root_.OAI.HadwigerCounterexample.StatusAnalysis.deckFin _root_.OAI.HadwigerCounterexample.Template.datumFinite _root_.OAI.HadwigerCounterexample.Template.inpFinite _root_.OAI.HadwigerCounterexample.Template.instDecidableEqAbbey _root_.OAI.HadwigerCounterexample.Template.instFintypeAbbey _root_.OAI.HadwigerCounterexample.Template.instFintypeOppDuet _root_.OAI.HadwigerCounterexample.Template.instFintypeSameDuet _root_.OAI.HadwigerCounterexample.Template.keySlotFinite _root_.OAI.HadwigerCounterexample.arrFintype _root_.OAI.HadwigerCounterexample.drawFintype _root_.OAI.HadwigerCounterexample.fintypeLedger _root_.OAI.HadwigerCounterexample.idxDec _root_.OAI.HadwigerCounterexample.momFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Small Cover Bounds -/

noncomputable section
namespace HadwigerCounterexample
open Matrix LinearMap Module Submodule Function Finset
open scoped BigOperators
variable {p : Shape} {n N : ℕ} {A B V : Type} [Fintype A] [Fintype B]

def allSide : Party := fun _ => 1

def cutDown (p : Shape) {n N}
    (T : Cov p N) (Δ : UnitType p n N→ Ambient p N) (w : Wgt (UnitType p n N))
    (x : UnitType p n N) : coverX p T :=
  open scoped Classical in
  if h : w x≠0 ∧ covered p T (Δ x) then ⟨_,h.2⟩ else 0

def juris (p : Shape) {n N} (T : Cov p N) (x : UnitType p n N) (S : Party) :
    Module.Dual F (coverX p T) :=
  joinPhase p (listens p x) S ∘ₗ (coverX p T).subtype

abbrev Daypair (p : Shape) {N} (T : Cov p N) :=
  coverX p T × (Bool → Module.Dual F (coverX p T))

def daypair (p : Shape) {n N}
    (T : Cov p N) (Δ : UnitType p n N→ Ambient p N) (w : Wgt (UnitType p n N))
    (x : UnitType p n N) : Daypair p T :=
  (cutDown p T Δ w x,fun i => juris p T x (unary i))

def shadow (p : Shape) {n N}
    (T : Cov p N) (Δ : UnitType p n N→ Ambient p N) (w : Wgt (UnitType p n N))
    (x y : UnitType p n N) (S : Party) :=
  juris p T y S (cutDown p T Δ w x)

variable [AddCommGroup V] [Module F V] [FiniteDimensional F V]

def circus (p : Shape) {n N}
    (T : Cov p N) (Δ : UnitType p n N→ Ambient p N) (w : Wgt (UnitType p n N)) :
    Mat (UnitType p n N) (UnitType p n N) :=
  Matrix.of (fun x y => shadow p T Δ w x y allSide)

end HadwigerCounterexample

end

end OAI
end

section
-- module Solutions.OAIQ430_HC.HadwigerCounterexample_LowRankKernelAlternative
attribute [-instance] _root_.OAI.HadwigerCounterexample.idxDec
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Low Rank Kernel Alternative -/

noncomputable section
namespace HadwigerCounterexample
open Matrix LinearMap Module Submodule Finset Filter
open scoped BigOperators Topology
variable {A J B : Type} [Fintype A] [Fintype J] [Fintype B]

def rbase (a : A → Vec B) (S : Finset A) :=
  Submodule.span F (Set.image a (S : Set A))

def tilt (m u : ℝ) : Wgt F :=
  fun x => if x=0 then bp (-m) else bp (-u)

end HadwigerCounterexample

end

end OAI
end

section
-- module Solutions.OAIQ430_HC.HadwigerCounterexample_PolynomialRankBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Polynomial Rank Bounds -/

noncomputable section
namespace HadwigerCounterexample
open Matrix Module Submodule Function Finset
open scoped BigOperators
variable {A B : Type} [Fintype A] [Fintype B]

def mpMask (P Q : Mat A B) : Mat A B := Matrix.of (fun x y => P x y * Q x y)

end HadwigerCounterexample

end

end OAI
end

section
-- module Solutions.OAIQ430_HC.HadwigerCounterexample_FourPhaseBits
attribute [-instance] _root_.OAI.HadwigerCounterexample.StatusAnalysis.deckFin _root_.OAI.HadwigerCounterexample.Template.datumFinite _root_.OAI.HadwigerCounterexample.Template.inpFinite _root_.OAI.HadwigerCounterexample.Template.instDecidableEqAbbey _root_.OAI.HadwigerCounterexample.Template.instFintypeAbbey _root_.OAI.HadwigerCounterexample.Template.instFintypeOppDuet _root_.OAI.HadwigerCounterexample.Template.instFintypeSameDuet _root_.OAI.HadwigerCounterexample.Template.keySlotFinite _root_.OAI.HadwigerCounterexample.arrFintype _root_.OAI.HadwigerCounterexample.drawFintype _root_.OAI.HadwigerCounterexample.fintypeLedger _root_.OAI.HadwigerCounterexample.idxDec _root_.OAI.HadwigerCounterexample.knFin _root_.OAI.HadwigerCounterexample.momFintype _root_.OAI.HadwigerCounterexample.rackFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Four Phase Bits -/

noncomputable section
namespace HadwigerCounterexample
open Matrix Module Finset
open scoped BigOperators
variable {p : Shape} {n N : ℕ}
abbrev Quad := Party × Party

def quench (p : Shape) {n N} (Δ : UnitType p n N→ Ambient p N)
    (x : UnitType p n N × UnitType p n N) : Quad :=
  (fun i => tone p x.2 (unary i) (Δ x.1),fun i => tone p x.1 (unary i) (Δ x.2))

def quadDot (x y : Quad) := dotProduct x.1 y.1 + dotProduct x.2 y.2
def quadPhase (x y : Quad) := wsign (quadDot x y)

/-- common even relation on four scores. -/
def repeated (x : Quad) :=
  dotProduct allSide x.1=0 ∧ dotProduct allSide x.2=0

def repeatQ (i : F) : Quad := (fun _ => i,fun _ => i)

def evenP : Finset Party := {0,allSide}
def evenQ : Finset Quad := evenP×ˢevenP

end HadwigerCounterexample

end

end OAI
end

section
-- module Solutions.OAIQ430_HC.HadwigerCounterexample_PolynomialCompatibility
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Polynomial Compatibility -/

noncomputable section
namespace HadwigerCounterexample
open scoped BigOperators
open Matrix Module Finset Filter
variable {p : Shape} {n N d : ℕ}

def poll (d N : ℕ) := (1+(1+d*(N:ℝ))^2)^2

end HadwigerCounterexample

end

end OAI
end

section
-- module Solutions.OAIQ430_HC.HadwigerCounterexample_WeightedPartitions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Weighted Partitions -/

noncomputable section
namespace HadwigerCounterexample
open scoped BigOperators
open Finset
variable {A : Type} [Fintype A]

abbrev Tiles (A : Type) := Finset (Finset A)
def inTiles (T : Tiles A) := fun x:A => ∃ i∈ T,x∈i

def apart (T : Tiles A) :=
  ∀ x,∀ S∈T, ∀ F∈ T,x∈S→x∈F→ S=F

def partMass (w : Wgt A) (S : Finset A) := pr w (fun x => x∈S)
def partW (w : Wgt A) (S : Finset A) := onW w (fun x => x∈S)

def allMass (w : Wgt A) (T : Tiles A) := pr w (inTiles T)
def allW (w : Wgt A) (T : Tiles A) := onW w (inTiles T)

variable {w : Wgt A} {T : Tiles A}

def portionW (w : Wgt A) (T : Tiles A) : Wgt T :=
  fun x => partMass w x.val / allMass w T

end HadwigerCounterexample

end

end OAI
end

section
-- module Solutions.OAIQ430_HC.HadwigerCounterexample_PartitionSelection
attribute [-instance] _root_.OAI.HadwigerCounterexample.StatusAnalysis.deckFin _root_.OAI.HadwigerCounterexample.Template.datumFinite _root_.OAI.HadwigerCounterexample.Template.inpFinite _root_.OAI.HadwigerCounterexample.Template.instDecidableEqAbbey _root_.OAI.HadwigerCounterexample.Template.instFintypeAbbey _root_.OAI.HadwigerCounterexample.Template.instFintypeOppDuet _root_.OAI.HadwigerCounterexample.Template.instFintypeSameDuet _root_.OAI.HadwigerCounterexample.Template.keySlotFinite _root_.OAI.HadwigerCounterexample.arrFintype _root_.OAI.HadwigerCounterexample.drawFintype _root_.OAI.HadwigerCounterexample.fintypeLedger _root_.OAI.HadwigerCounterexample.idxDec _root_.OAI.HadwigerCounterexample.knFin _root_.OAI.HadwigerCounterexample.momFintype _root_.OAI.HadwigerCounterexample.rackFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Partition Selection -/

noncomputable section
namespace HadwigerCounterexample
open Matrix LinearMap Module Submodule Function Finset
open scoped BigOperators
variable {p : Shape} {n N : ℕ}

abbrev CTile (p : Shape) (n N : ℕ) := Finset (UnitType p n N)
abbrev Canopy (p : Shape) (n N : ℕ) := Tiles (UnitType p n N)

structure Ripe (p : Shape) {n N} (w μ : Wgt (UnitType p n N))
    (S : CTile p n N) (a : Pin p n N) (D ζ : ℝ) (K : ℕ) : Prop where
  pos : 0 < partMass w S
  fixpin : ∀ x∈ S,a.agree x
  bound : planRank a.sp≤K
  clear : a.clear ζ (partW w S)
  density x : partW w S x ≤ bp (D*N) * μ x

variable {w μ : Wgt (UnitType p n N)}

def dustPin (p : Shape) (n N : ℕ) : Pin p n N := Pin.make ⊥ 0

end HadwigerCounterexample

end

end OAI
end

section
-- module Solutions.OAIQ430_HC.HadwigerCounterexample_RefinedPinImages
attribute [-instance] _root_.OAI.HadwigerCounterexample.Flavor.instDecidableKeeps _root_.OAI.HadwigerCounterexample.StatusAnalysis.deckFin _root_.OAI.HadwigerCounterexample.Template.datumFinite _root_.OAI.HadwigerCounterexample.Template.inpFinite _root_.OAI.HadwigerCounterexample.Template.instDecidableEqAbbey _root_.OAI.HadwigerCounterexample.Template.instFintypeAbbey _root_.OAI.HadwigerCounterexample.Template.instFintypeOppDuet _root_.OAI.HadwigerCounterexample.Template.instFintypeSameDuet _root_.OAI.HadwigerCounterexample.Template.keySlotFinite _root_.OAI.HadwigerCounterexample.arrFintype _root_.OAI.HadwigerCounterexample.drawFintype _root_.OAI.HadwigerCounterexample.fintypeLedger _root_.OAI.HadwigerCounterexample.idxDec _root_.OAI.HadwigerCounterexample.knFin _root_.OAI.HadwigerCounterexample.momFintype _root_.OAI.HadwigerCounterexample.rackFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Refined Pin Images -/

noncomputable section
namespace HadwigerCounterexample
open Matrix LinearMap Module Submodule Function Finset
open scoped BigOperators
variable {p : Shape} {n N : ℕ}

def front (s : Plan p n) : Plan p n := prSmall s

abbrev Signal (p : Shape) (N : ℕ) {n} (s : Plan p n) := DTuple (p:=p) (fun z => dim (s z)) N

def readPin (x : UnitType p n N) (a : Plan p n) : Signal p N a :=
  fun z => images x z * pack (a z)

abbrev EffSeq {p : Shape} {n} (s : Plan p n) := ∀ i : Bool,effective s i

def entrySeq {p : Shape} {n} (s : Plan p n) (m : Bool → Profile p n) : EffSeq s :=
  open scoped Classical in
  fun i => if h : m i ∈ effective s i then ⟨_,h⟩ else 0

abbrev Story {p : Shape} {n N} (T : Cov p N) (s : Plan p n) :=
  Daypair p T × Signal p N (front s) × EffSeq s

instance fintypeStory {s : Plan p n} {T : Cov p N} : Fintype (Story T s) := by
  classical
  let A := (coverX p T)
  letI : Finite (Module.Dual F A) := Finite.of_injective _ DFunLike.coe_injective
  letI : Fintype (Module.Dual F A) := Fintype.ofFinite _
  letI : Fintype (Daypair p T) := inferInstanceAs (Fintype (Daypair p T))
  letI : ∀ i,Fintype (effective s i) := fun i => Fintype.ofFinite _
  letI : Fintype (EffSeq s) := inferInstanceAs (Fintype (EffSeq s))
  letI : Fintype (Signal p N (front s)) := inferInstanceAs (Fintype (Signal p N (front s)))
  exact inferInstanceAs (Fintype (Story T s))

def story (T : Cov p N) (s : Plan p n) (m : BMark p n N) (x : UnitType p n N) : Story T s :=
  (daypair p T (delta m) (fun _ => 1) x,readPin x (front s),entrySeq s (m x))

def specialLeaf (T : Cov p N) (m : BMark p n N) (a : Pin p n N)
    (G : CTile p n N) (b : Pin p n N) :=
  a.sp ≤ b.sp ∧ front a.sp ≤ b.sp ∧
    ∀ x∈G,∀ y∈G, m x=m y ∧ delta m x=delta m y ∧
      ∀ i,juris p T x (unary i) = juris p T y (unary i)

end HadwigerCounterexample

end

end OAI
end

section
-- module Solutions.OAIQ430_HC.HadwigerCounterexample_UltrafilterRates
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Ultrafilter Rates -/

noncomputable section
namespace HadwigerCounterexample
open Filter Real Finset
open scoped Topology

variable {A B : Type} {l : Filter A} {U : Ultrafilter A} {x y z v a : A → ℝ}

/-- Upper target thresholds, without claiming nonnegativity. -/
def slight (l : Filter A) (x : A→ℝ) := ∀ δ:ℝ,0<δ→∀ᶠ n in l,x n≤δ

/-- At least subexponential mass. -/
def warm (l : Filter A) (z x : A→ℝ) :=
  ∀ ε:ℝ,0<ε → ∀ᶠ i in l,bp (-ε * z i) ≤ x i

end HadwigerCounterexample

end

end OAI
end

section
-- module Solutions.OAIQ430_HC.HadwigerCounterexample_PredictionClasses
attribute [-instance] _root_.OAI.HadwigerCounterexample.StatusAnalysis.deckFin _root_.OAI.HadwigerCounterexample.Template.datumFinite _root_.OAI.HadwigerCounterexample.Template.inpFinite _root_.OAI.HadwigerCounterexample.Template.keySlotFinite _root_.OAI.HadwigerCounterexample.arrFintype _root_.OAI.HadwigerCounterexample.drawFintype _root_.OAI.HadwigerCounterexample.idxDec _root_.OAI.HadwigerCounterexample.momFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Prediction Classes -/

noncomputable section
namespace HadwigerCounterexample
open Filter Matrix Finset
open scoped BigOperators Topology

inductive PredictionClass
| dusk
| dawn (i : Bool)
| twinned
| noon
deriving Inhabited, DecidableEq

variable {p : Shape}
namespace PredictionClass

def active : PredictionClass→Bool→ Prop
| dusk,_=>False
| dawn i,j=>i=j
| twinned,_=>True
| noon,_=>True

def echoes (c : PredictionClass) (i j : Bool) (s r : F) :=
  ((s=1 ∧ c.active i) ↔ (r=1 ∧ c.active j)) ∧
    ((s=1 ∧ c.active i) → (i=j ∨ c=twinned))

def firstBit (α : Party) (i : Bool) := 1+α i

def lit (c : PredictionClass) (α : Party) :=
  (∀ i,¬c.active i → firstBit α i=0) ∧
    (c=twinned → α true=α false)

def assembly {N} (g : Bool→Augur p N) (i j : Bool) (s t : F) : Augur p N :=
  fun l q x => s*g i l q x+t*g j l q x

/-- Enough to test against dual relations. -/
def recital (c : PredictionClass) (p : Shape) {N}
    (g : Bool→Augur p N) (α : Party) (τ : ℝ) :=
  c.lit α ∧ ∀ (i j : Bool) (s t r : F), s*firstBit α i=t*firstBit α j →
    (∀ l q,tabRef p l q (assembly g i j s t) r ≤ τ) → c.echoes i j s t
abbrev season (p : Shape) (M : ℕ) := (n : ℕ)→Augur p (M*n)
def disappearing (U : Ultrafilter ℕ) {M} (g : season p M) (s : F) :=
  ∀ l q, slight (U:Filter ℕ) (fun i=>tabRef p l q (g i) s)

def modest (U : Ultrafilter ℕ) {M}
    (g : Bool→season p M) (α : Party) (i : Bool) :=
  firstBit α i=0 ∧ ∃ s,g i |> fun x=> disappearing U x s

def accords (U : Ultrafilter ℕ) {M}
    (g : Bool→season p M) (α : Party) :=
  α true=α false ∧ ∃ s, disappearing U
    (fun n : ℕ=>fun l q x => g true n l q x+g false n l q x) s

def census (U : Ultrafilter ℕ) {M}
    (g : Bool→season p M) (α : Party) :=
  open scoped Classical in
  if modest U g α true then if modest U g α false then dusk else dawn false
  else if modest U g α false then dawn true
  else if accords U g α then twinned else noon

end PredictionClass
end HadwigerCounterexample

end

end OAI
end

section
-- module Solutions.OAIQ430_HC.HadwigerCounterexample_PhaseClassCompatibility
attribute [-instance] _root_.OAI.HadwigerCounterexample.StatusAnalysis.deckFin _root_.OAI.HadwigerCounterexample.Template.datumFinite _root_.OAI.HadwigerCounterexample.Template.inpFinite _root_.OAI.HadwigerCounterexample.Template.keySlotFinite _root_.OAI.HadwigerCounterexample.arrFintype _root_.OAI.HadwigerCounterexample.drawFintype _root_.OAI.HadwigerCounterexample.idxDec _root_.OAI.HadwigerCounterexample.momFintype _root_.OAI.HadwigerCounterexample.rackFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Phase Class Compatibility -/

noncomputable section
namespace HadwigerCounterexample
open Matrix Finset LinearMap
open scoped BigOperators
variable {p : Shape} {n N : ℕ}
namespace PredictionClass
def compatible (α : Party) (x : F) : PredictionClass→Quad→Prop
| dusk,v=> v=repeatQ x
| dawn i,v=> v.1 i+v.2 i=firstBit α i
| twinned,v=> dotProduct allSide v.1 +dotProduct allSide v.2=0
| noon,_=> True

def matchUp (Δ : UnitType p n N→Ambient p N) (α : Party) (x : F)
    (c : PredictionClass) (v : UnitType p n N × UnitType p n N) :=
  c.compatible α x (quench p Δ v)

end PredictionClass

open PredictionClass

def glint (p : Shape) {n} (x : Bool → Profile p n) := ∑ i, role p n (x i)
def exactInk (p : Shape) (m : Mixer p n) (z : BMark p n N) (x) :=
  ∀ i:Bool,silent (yoke p m x i (z x i) 1)

end HadwigerCounterexample

end

end OAI
end

section
-- module Solutions.OAIQ430_HC.HadwigerCounterexample_LeafMixtures
attribute [-instance] _root_.OAI.HadwigerCounterexample.StatusAnalysis.deckFin _root_.OAI.HadwigerCounterexample.Template.datumFinite _root_.OAI.HadwigerCounterexample.Template.inpFinite _root_.OAI.HadwigerCounterexample.Template.instDecidableEqAbbey _root_.OAI.HadwigerCounterexample.Template.instFintypeAbbey _root_.OAI.HadwigerCounterexample.Template.instFintypeOppDuet _root_.OAI.HadwigerCounterexample.Template.instFintypeSameDuet _root_.OAI.HadwigerCounterexample.Template.keySlotFinite _root_.OAI.HadwigerCounterexample.arrFintype _root_.OAI.HadwigerCounterexample.drawFintype _root_.OAI.HadwigerCounterexample.fintypeLedger _root_.OAI.HadwigerCounterexample.idxDec _root_.OAI.HadwigerCounterexample.knFin _root_.OAI.HadwigerCounterexample.momFintype _root_.OAI.HadwigerCounterexample.rackFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Leaf Mixtures -/

noncomputable section
namespace HadwigerCounterexample
open Matrix Finset LinearMap Filter
open scoped BigOperators
variable {p : Shape} {n N M : ℕ}
structure LeafMixture (p : Shape) (n N : ℕ) where
  T : Canopy p n N
  pin : CTile p n N → Pin p n N

namespace LeafMixture
abbrev X (p : Shape) (n N : ℕ) := UnitType p n N

instance instInhabited : Inhabited (LeafMixture p n N) := ⟨⟨∅,fun _=>dustPin ..⟩⟩

def poller (s : LeafMixture p n N) (x : X p n N) : Pin p n N :=
  open scoped Classical in
  if h : inTiles s.T x then s.pin h.choose else dustPin p n N

def rooting (s : LeafMixture p n N) (x : X p n N) := (s.poller x).sp
def amount (s : LeafMixture p n N) (w : Wgt (X p n N)) := allMass w s.T
def sap (s : LeafMixture p n N) (w : Wgt (X p n N)) := allW w s.T

variable {s : LeafMixture p n N} {w μ : Wgt (X p n N)}
structure strength (s : LeafMixture p n N) (w μ : Wgt (X p n N)) (D ζ : ℝ) (K : ℕ) : Prop where
  part : apart s.T
  leaf : ∀ i∈s.T,Ripe p w μ i (s.pin i) D ζ K
variable {D E ζ η : ℝ} {K L : ℕ}

def within (s : LeafMixture p n N) (P : X p n N→Prop) := ∀ i∈ s.T,∀ x∈ i,P x

def elder (s t : LeafMixture p n N) (P : X p n N→Prop)
    (S : CTile p n N → CTile p n N → Prop) :=
  ∀ i ∈ t.T, ∃ i'∈ s.T,i⊆i' ∧ (∀ x∈i,P x) ∧ S i i'

end LeafMixture
end HadwigerCounterexample

end

end OAI
end

section
-- module Solutions.OAIQ430_HC.HadwigerCounterexample_SyntheticSliceExperiments
attribute [-instance] _root_.OAI.HadwigerCounterexample.LeafMixture.instInhabited _root_.OAI.HadwigerCounterexample.StatusAnalysis.deckFin _root_.OAI.HadwigerCounterexample.Template.datumFinite _root_.OAI.HadwigerCounterexample.Template.inpFinite _root_.OAI.HadwigerCounterexample.Template.keySlotFinite _root_.OAI.HadwigerCounterexample.arrFintype _root_.OAI.HadwigerCounterexample.drawFintype _root_.OAI.HadwigerCounterexample.fintypeStory _root_.OAI.HadwigerCounterexample.idxDec _root_.OAI.HadwigerCounterexample.momFintype _root_.OAI.HadwigerCounterexample.rackFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Synthetic Slice Experiments -/

noncomputable section
namespace HadwigerCounterexample
open Matrix Module Function Finset
open scoped BigOperators
variable {p : Shape} {n : ℕ}

abbrev Punch (p : Shape) := ProbeIdx p.g × Fin p.r
abbrev Gauge (p : Shape) := Punch p × Bool
def gaugeAddr (p : Shape) (i : Gauge p) := if i.2 then 2*i.1.2.val else 2*i.1.2.val+1
def usesPunch (p : Shape) (l : Tag p.g) (f : Flavor p.g) (i : Punch p) := f.keeps l
  (asBlock i.1)
instance instDecidableUsesPunch (p : Shape) (l f i) : Decidable (usesPunch p l f i) := Classical.propDecidable _

abbrev Tickets (p : Shape) := Vec (Gauge p)
def punchField (p : Shape) (x : Knobs p.g n) : Tickets p :=
  fun i => zget (x (asBlock i.1.1)) (gaugeAddr p i)
def issued (p : Shape) (w : Tickets p) (x : Knobs p.g n) := punchField p x=w

def rung (p : Shape) (n : ℕ) (w : Tickets p) : Wgt (Knobs p.g n) :=
  onW (spins p n) (issued p w)
def ticketsFee (p : Shape) := (1/2:ℝ)^Fintype.card (Gauge p)

def tabGram (p : Shape) (l : Tag p.g) (f : Flavor p.g) (x y : Tickets p) :=
    ∑ i:Punch p, if usesPunch p l f i then x (i,true)*y (i,false) else 0

end HadwigerCounterexample

end

end OAI
end

section
-- module Solutions.OAIQ430_HC.HadwigerCounterexample_NominalPointArrays
attribute [-instance] _root_.OAI.HadwigerCounterexample.LeafMixture.instInhabited _root_.OAI.HadwigerCounterexample.StatusAnalysis.deckFin _root_.OAI.HadwigerCounterexample.Template.datumFinite _root_.OAI.HadwigerCounterexample.Template.inpFinite _root_.OAI.HadwigerCounterexample.Template.keySlotFinite _root_.OAI.HadwigerCounterexample.arrFintype _root_.OAI.HadwigerCounterexample.drawFintype _root_.OAI.HadwigerCounterexample.fintypeStory _root_.OAI.HadwigerCounterexample.idxDec _root_.OAI.HadwigerCounterexample.momFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Nominal Point Arrays -/

noncomputable section
namespace HadwigerCounterexample
open Matrix Module LinearMap Function Finset
open scoped BigOperators
variable {p : Shape} {n N : ℕ} {I J U : Type} [Fintype I] [Fintype J] [Fintype U]
variable [DecidableEq I] [DecidableEq J] [DecidableEq U]

def incision (p : Shape) (l : Tag p.g) (s : Label p.b) (f : Flavor p.g)
    (x : I →Knobs p.g n) :
    Mat (Row p n) I := Matrix.of (fun i j=> spring p l s f (x j) i)
def sketchLaw (p : Shape) (n : ℕ) (a : I→ Tickets p) :=
    prodW (fun i => rung p n (a i))

def weightsAff (u : Vec I) := ∑ i,u i=(1:F)
def compound (p : Shape) (x : I →Knobs p.g n) (u : Vec I) := ∑ i:I,u i • x i

def labFee (p : Shape) (I : Type) [Fintype I] := (ticketsFee p)^Fintype.card I

def compoundAll (p : Shape) (n : ℕ) (i : Vec I) :
    (I →Knobs p.g n)→ₗ[F] Knobs p.g n where
  toFun x := compound p x i
  map_add' x y := by simp only [compound,Pi.add_apply,smul_add,sum_add_distrib]
  map_smul' b x := by
    simp only [compound,Pi.smul_apply, RingHom.id_apply,Finset.smul_sum]; exact
      Finset.sum_congr rfl (fun i _=> smul_comm _ _ _)

end HadwigerCounterexample

end

end OAI
end

section
-- module Solutions.OAIQ430_HC.HadwigerCounterexample_SyntheticSliceComparison
attribute [-instance] _root_.OAI.HadwigerCounterexample.LeafMixture.instInhabited _root_.OAI.HadwigerCounterexample.StatusAnalysis.deckFin _root_.OAI.HadwigerCounterexample.Template.datumFinite _root_.OAI.HadwigerCounterexample.Template.inpFinite _root_.OAI.HadwigerCounterexample.Template.keySlotFinite _root_.OAI.HadwigerCounterexample.arrFintype _root_.OAI.HadwigerCounterexample.drawFintype _root_.OAI.HadwigerCounterexample.fintypeStory _root_.OAI.HadwigerCounterexample.idxDec _root_.OAI.HadwigerCounterexample.momFintype _root_.OAI.HadwigerCounterexample.rackFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Synthetic Slice Comparison -/

noncomputable section
namespace HadwigerCounterexample
open Matrix Module LinearMap Function Finset
open scoped BigOperators
variable {p : Shape} {I J : Type} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
variable {n N : ℕ}

abbrev Display (p : Shape) (I : Type) (N : ℕ) := Comp p.g → Rack I N
def displayLaw (p : Shape) (I : Type) [Fintype I] [DecidableEq I] (N : ℕ) (G : Mat I I) :
    Wgt (Display p I N) := prodW (fun (_:Comp p.g) => unifOn (gramGood G))

def drill (p : Shape) (A : Mat (Row p n) I) (o : Orient p n N) : Display p I N :=
  fun i => peer p A A (o i)

def drStage (p : Shape) (I : Type) : Route (Comp p.g × I) (Comp p.g) := Prod.fst

def drQuery (A : Mat (Row p n) I) : NomQuery p n (drStage p I) :=
  fun j => A.submatrix _root_.id (fun i : Port (drStage p I) j => i.val.2)

def labGram (p : Shape) (l : Tag p.g) (s : Flavor p.g) (a : I→ Tickets p) : Mat I I :=
  Matrix.of (fun i j => tabGram p l s (a i) (a j))
end HadwigerCounterexample

end

end OAI
end

section
-- module Solutions.OAIQ430_HC.HadwigerCounterexample_GramArrayConcentration
attribute [-instance] _root_.OAI.HadwigerCounterexample.LeafMixture.instInhabited _root_.OAI.HadwigerCounterexample.StatusAnalysis.deckFin _root_.OAI.HadwigerCounterexample.Template.datumFinite _root_.OAI.HadwigerCounterexample.Template.inpFinite _root_.OAI.HadwigerCounterexample.Template.keySlotFinite _root_.OAI.HadwigerCounterexample.arrFintype _root_.OAI.HadwigerCounterexample.drawFintype _root_.OAI.HadwigerCounterexample.fintypeStory _root_.OAI.HadwigerCounterexample.idxDec _root_.OAI.HadwigerCounterexample.momFintype _root_.OAI.HadwigerCounterexample.rackFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Gram Array Concentration -/

noncomputable section
namespace HadwigerCounterexample
open Finset Matrix Module LinearMap Function Filter
open scoped BigOperators Topology
variable {p : Shape} {I : Type} [Fintype I] [DecidableEq I] {n N : ℕ}
def magazine (p : Shape) (l : Tag p.g) (s : Label p.b) (f : Flavor p.g)
    (P : Display p I N→Prop) (a : I→ Tickets p) (o : Orient p n N) :=
  pr (sketchLaw p n a) (fun i => P (drill p (incision p l s f i) o))

end HadwigerCounterexample

end

end OAI
end

section
-- module Solutions.OAIQ430_HC.HadwigerCounterexample_SyntheticParity
attribute [-instance] _root_.OAI.HadwigerCounterexample.LeafMixture.instInhabited _root_.OAI.HadwigerCounterexample.StatusAnalysis.deckFin _root_.OAI.HadwigerCounterexample.Template.datumFinite _root_.OAI.HadwigerCounterexample.Template.inpFinite _root_.OAI.HadwigerCounterexample.Template.keySlotFinite _root_.OAI.HadwigerCounterexample.arrFintype _root_.OAI.HadwigerCounterexample.drawFintype _root_.OAI.HadwigerCounterexample.fintypeStory _root_.OAI.HadwigerCounterexample.idxDec _root_.OAI.HadwigerCounterexample.momFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Synthetic Parity -/

noncomputable section
namespace HadwigerCounterexample
open Matrix Module LinearMap Submodule Function Finset
open scoped BigOperators
variable {p : Shape} {I J : Type} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
variable {d e n N : ℕ}

abbrev Hue (d : ℕ) := Option (Bool × Fin d)
def beamMap (d : ℕ) : Mat (Hue d) (Hue d) :=
  Matrix.of (fun i j =>
    i.elim 0 (fun x=> j.elim 0 (fun y=> if x.1=true∧y.1=false∧x.2=y.2 then 1 else 0)))
def jet (i : I) := (Pi.single i 1 : Vec I)
abbrev incarn {d : ℕ} (x : Fin d) (b : Bool) : Hue d := some (b,x)
def plumeDiff (d : ℕ) (b : Bool) : Mat (Hue d) (Fin d) :=
  Matrix.of (fun i j => jet none i + jet (incarn j b) i)

def arches (F : Vec (Hue d) → F) : Mat (Fin d) (Fin d) :=
  Matrix.of (fun i j =>
    let x:=jet (incarn i true)
    let y:=jet (incarn j false)
    let z:=jet (none : Hue d)
    F (z+x+y)+F x+(F y+F z))

def libColor (p : Shape) (l : Tag p.g) (u : Vec I) (x : Display p I N) :
    AtomKey (p:=p) l N :=
  fun i b=> if b then (x i.val).1 *ᵥ u else (x i.val).2 *ᵥ u
def libPredict (p : Shape) (l : Tag p.g) (s : Augur p N) (G : Mat I I) (x : Display p I N)
    (u : Vec I) := s l (evmat G u u) (libColor p l u x)
def libAug (p : Shape) (l : Tag p.g) (s : Augur p N) (G : Mat I I) (x : Display p I N) (u : Vec I) :=
  libPredict p l s G x u+evmat G u u

end HadwigerCounterexample

end

end OAI
end

section
-- module Solutions.OAIQ430_HC.HadwigerCounterexample_SyntheticArraySlices
attribute [-instance] _root_.OAI.HadwigerCounterexample.LeafMixture.instInhabited _root_.OAI.HadwigerCounterexample.StatusAnalysis.deckFin _root_.OAI.HadwigerCounterexample.Template.datumFinite _root_.OAI.HadwigerCounterexample.Template.inpFinite _root_.OAI.HadwigerCounterexample.Template.keySlotFinite _root_.OAI.HadwigerCounterexample.arrFintype _root_.OAI.HadwigerCounterexample.drawFintype _root_.OAI.HadwigerCounterexample.fintypeStory _root_.OAI.HadwigerCounterexample.idxDec _root_.OAI.HadwigerCounterexample.momFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Synthetic Array Slices -/

noncomputable section
namespace HadwigerCounterexample
open Finset Matrix Module Function LinearMap
open scoped BigOperators
variable {p : Shape} {d e n N : ℕ}
variable {I J : Type} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]

def exhibit (p : Shape) (A : Mat I J) (x : Display p I N) : Display p J N :=
  fun i => ((x i).1*A,(x i).2*A)

abbrev Sextant (d e : ℕ) := (Fin d ↪ Fin e) × (Fin d↪Fin e)
def reflectSextant (f : Sextant d e) : Hue d ↪ Hue e where
  toFun x := x.map (fun i=> (i.1,(onSide f i.1) i.2))
  inj' := by
    rintro (_|⟨a,b⟩) (_|⟨c,d⟩) h
    · rfl
    · cases h
    · cases h
    have he : (a,(onSide f a) b)=(c,(onSide f c) d) := Option.some.inj h
    have hh : a=c := congrArg Prod.fst he
    subst c; rw [(onSide f a).injective (congrArg Prod.snd he)]
def cartM (f : Sextant d e) := embedMat (reflectSextant f)

end HadwigerCounterexample

end

end OAI
end

section
-- module Solutions.OAIQ430_HC.HadwigerCounterexample_NumericalGramPrescriptions
attribute [-instance] _root_.OAI.HadwigerCounterexample.LeafMixture.instInhabited _root_.OAI.HadwigerCounterexample.StatusAnalysis.deckFin _root_.OAI.HadwigerCounterexample.Template.datumFinite _root_.OAI.HadwigerCounterexample.Template.inpFinite _root_.OAI.HadwigerCounterexample.Template.keySlotFinite _root_.OAI.HadwigerCounterexample.arrFintype _root_.OAI.HadwigerCounterexample.drawFintype _root_.OAI.HadwigerCounterexample.fintypeStory _root_.OAI.HadwigerCounterexample.idxDec _root_.OAI.HadwigerCounterexample.momFintype _root_.OAI.HadwigerCounterexample.rackFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Numerical Gram Prescriptions -/

noncomputable section
namespace HadwigerCounterexample
open Finset Matrix Function LinearMap Module
open scoped BigOperators Pointwise
variable {p : Shape} {n N d e : ℕ} {I : Type} [Fintype I] [DecidableEq I]

def spacePunch (p : Shape) (l : Tag p.g) (f : Flavor p.g) :=
  (Finset.univ.filter (usesPunch p l f)).card

/-- selected pure excludes second tags -/
def creed (p : Shape) (E : Finset (Tag p.g)) :=
  Flavor.pure (Finset.univ.filter fun i : Tag p.g×Tag p.g => i.2∉E)

end HadwigerCounterexample

end

end OAI
end

section
-- module Solutions.OAIQ430_HC.HadwigerCounterexample_ZeroDiscrepancyPrediction
attribute [-instance] _root_.OAI.HadwigerCounterexample.LeafMixture.instInhabited _root_.OAI.HadwigerCounterexample.StatusAnalysis.deckFin _root_.OAI.HadwigerCounterexample.Template.datumFinite _root_.OAI.HadwigerCounterexample.Template.inpFinite _root_.OAI.HadwigerCounterexample.Template.keySlotFinite _root_.OAI.HadwigerCounterexample.arrFintype _root_.OAI.HadwigerCounterexample.drawFintype _root_.OAI.HadwigerCounterexample.fintypeStory _root_.OAI.HadwigerCounterexample.idxDec _root_.OAI.HadwigerCounterexample.momFintype _root_.OAI.HadwigerCounterexample.rackFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Zero Discrepancy Prediction -/

noncomputable section
namespace HadwigerCounterexample
open Finset Matrix Module LinearMap Submodule Function
open scoped BigOperators
variable {p : Shape} {n N : ℕ}
def zoomset (p : Shape) (w : Tag p.g →Moment p n) :=
    Finset.univ.filter (fun i => etab p n Block.S (w i)≠0)

def screenRank (p : Shape) (K : ℕ) := (p.g-1)*(p.h+2*p.J*K)
def screen (p : Shape) (i : Orient p n N) (s : Label p.b) (E : Finset (Tag p.g)) (r : ℕ)
    (g : Augur p N) (δ : ℝ) :=
  ∃ w : Pdual p n,
    (∀ l f,pr (spins p n) (mismatch p g w l s f i) ≤ δ)∧
    ∀ l : Tag p.g,
    ∃ M:Moment p n,M.rank ≤ r ∧ ∀ x : Knobs p.g n,
      let f:= creed p E
      let v:=spring p l s f x
      w (useAtom p l s f x)=dialed p l f x+evmat M v v

end HadwigerCounterexample

end

end OAI
end

section
-- module Solutions.OAIQ430_HC.HadwigerCounterexample_SyntheticFailureBounds
attribute [-instance] _root_.OAI.HadwigerCounterexample.LeafMixture.instInhabited _root_.OAI.HadwigerCounterexample.StatusAnalysis.deckFin _root_.OAI.HadwigerCounterexample.Template.datumFinite _root_.OAI.HadwigerCounterexample.Template.inpFinite _root_.OAI.HadwigerCounterexample.Template.keySlotFinite _root_.OAI.HadwigerCounterexample.arrFintype _root_.OAI.HadwigerCounterexample.drawFintype _root_.OAI.HadwigerCounterexample.fintypeStory _root_.OAI.HadwigerCounterexample.idxDec _root_.OAI.HadwigerCounterexample.momFintype _root_.OAI.HadwigerCounterexample.rackFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Synthetic Failure Bounds -/

noncomputable section
namespace HadwigerCounterexample
open Finset Matrix Module LinearMap Function Filter Real
open scoped BigOperators
variable {p : Shape} {I A : Type} [Fintype I] [DecidableEq I] [Fintype A] {n N d : ℕ}

def fiddleRate (p : Shape) (I : Type) [Fintype I] [DecidableEq I] :=
  num (Vec I)* (labFee p I)⁻¹

def havoc (p : Shape) (l : Tag p.g) (g : Augur p N) (G : Mat (Hue d) (Hue d))
    (r : ℕ) (x : Display p (Hue d) N) := 2*r<(arches (libAug p l g G x)).rank

def mute (p : Shape) (g : Augur p N) (G : Mat Unit Unit) (x : Display p Unit N) :=
  (∑ i:Tag p.g,libPredict p i g G x (jet ()))≠0

end HadwigerCounterexample

end

end OAI
end

section
-- module Solutions.OAIQ430_HC.HadwigerCounterexample_OppositePredictions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Opposite Predictions -/

noncomputable section
namespace HadwigerCounterexample
open Finset Matrix Module LinearMap Function Filter Real
open scoped BigOperators
variable {p : Shape} {e d n N : ℕ}

def singleEx {I : Type} (x : Vec I) : Mat I Unit := Matrix.of (fun i _=>x i)

end HadwigerCounterexample

end

end OAI
end

section
-- module Solutions.OAIQ430_HC.HadwigerCounterexample_PreparationConditions
attribute [-instance] _root_.OAI.HadwigerCounterexample.StatusAnalysis.deckFin _root_.OAI.HadwigerCounterexample.Template.datumFinite _root_.OAI.HadwigerCounterexample.Template.inpFinite _root_.OAI.HadwigerCounterexample.Template.keySlotFinite _root_.OAI.HadwigerCounterexample.arrFintype _root_.OAI.HadwigerCounterexample.drawFintype _root_.OAI.HadwigerCounterexample.idxDec _root_.OAI.HadwigerCounterexample.momFintype _root_.OAI.HadwigerCounterexample.rackFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Preparation Conditions -/

noncomputable section
namespace HadwigerCounterexample
open Filter Finset
open scoped BigOperators Topology
open PredictionClass

structure PreparationParameters where
  D : ℕ
  L : ℝ
  d : ℕ
  e : ℕ
  s : ℕ
  u : ℕ
  k : ℕ
  ζ : ℝ
  B : ℕ

namespace PreparationParameters
def pins (q : PreparationParameters) := 3*q.e+q.s
def rank (q : PreparationParameters) := 2*q.e + 2

def leafOld (q : PreparationParameters) : ℝ := ↑q.D+q.e+2
def leafNew (q : PreparationParameters) : ℝ := q.leafOld+q.u+q.s+2
def spJoint (q : PreparationParameters) : ℝ := (q.D:ℝ)+1

def spear (q : PreparationParameters) := bp (100)*q.L

structure allows (q : PreparationParameters) : Prop where
  pos : 0< q.ζ
  small : q.ζ < 1
  hL : 0≤q.L
  bigS : q.leafOld+q.u+q.ζ ≤ (q.ζ-q.ζ/4) * q.s

variable {p : Shape} {M n N : ℕ}
abbrev tale (p : Shape) (M : ℕ) := ∀ n,Wgt (UnitType p n (M*n))
abbrev rhythms (p : Shape) (M : ℕ) := ∀ n,LeafMixture p n (M*n)
abbrev cycleM (p : Shape) := ∀ n,Mixer p n

def frameSide (p : Shape) (m : Mixer p n) (x : UnitType p n N) :=
  ∀ i,frameLaw m (onSide x i)
def usual (p : Shape) (m : Mixer p n) (N : ℕ) :=
  pairW (raw m N) (raw m N)

structure nascent (q : PreparationParameters) (p : Shape) (N : ℕ) {n}
    (w : Wgt (UnitType p n N)) (m : Mixer p n) : Prop where
  law : IsLaw w
  border : bySide p w m q.L
  total : ∀ x,w x≤bp ((q.D:ℝ)*N)*usual p m N x

structure entered (q : PreparationParameters) (p : Shape) (N : ℕ) {n} (m : Mixer p n)
    (w : Wgt (UnitType p n N)) (s : LeafMixture p n N) : Prop where
  weight : (1/2:ℝ) ≤ s.amount w
  strength : s.strength w (usual p m N) q.leafOld q.ζ q.e
  onTile : s.within (fun x=>w x≠0 ∧ (rawHoles m).unit x ∧ joins x≤2*q.D ∧ frameSide p m x)

structure durable (q : PreparationParameters) (l : Filter ℕ) (p : Shape) (M : ℕ) (m : cycleM p)
    (w : tale p M) (s : rhythms p M) : Prop where
  mass : warm l (fun i=> ((M*i:ℕ):ℝ)) (fun i=>(s i).amount (w i))
  shape : ∀ᶠ n in l,(s n).strength (w n) (usual p (m n) (M*n)) q.leafNew (2*q.ζ) q.pins ∧
    (s n).within (frameSide p (m n))

def seems (q : PreparationParameters) (p : Shape) (m : Mixer p n)
    (s : LeafMixture p n N)
    (x : UnitType p n N) (g : Bool → Augur p N) (z : Bool → Profile p n)
    (L : Bool→Finset (Label p.b)) (α : Party) (ε : ℝ) :=
  (∀ i : Bool,(L i).card≤ q.B ∧ z i∈ effective (s.rooting x) i) ∧
    claimed p x g m z α L ε

def predicts (q : PreparationParameters) (p : Shape) (N : ℕ) {n} (m : Mixer p n)
    (s : LeafMixture p n N) (w : Wgt (UnitType p n N)) (ε : ℝ) :=
  ∃ g : Bool → Augur p N, (0.000001 : ℝ) ≤ pr (s.sap w) (fun x => ∃ z L α, q.seems p m s x g z L α ε)

def silenceOutcome (q : PreparationParameters) (l : Filter ℕ) (p : Shape) (M : ℕ) (m : cycleM p)
    (w : tale p M) (s : rhythms p M) :=
  ∃ ε:ℝ,0<ε∧∀ᶠ n in l, ¬q.predicts p (M*n) (m n) (s n) (w n) ε ∧
    let v:=(s n).sap (w n)
    0.99 < pr (pairW v v) (secureAt p (s n).rooting)

structure Sketch (p : Shape) (M : ℕ) where
  c : PredictionClass
  α : Party
  r : F
  m : ∀ n,BMark p n (M*n)
  L : ∀ n,UnitType p n (M*n) → Bool → Finset (Label p.b)
  g : Bool → PredictionClass.season p M
  ε : ℕ→ℝ

def engrave (b : Sketch p M) (q : PreparationParameters) (m : cycleM p) (s : rhythms p M) (n : ℕ) :=
  fun x : UnitType p n (M*n) =>
  q.seems p (m n) (s n) x (fun i=> b.g i n) (b.m n x) (b.L n x) b.α (b.ε n) ∧
    glint p (b.m n x) = b.r ∧ (b.c=dusk → exactInk p (m n) (b.m n) x)

structure ledger (b : Sketch p M) (l : Filter ℕ) : Prop where
  small : slight l b.ε
  classes : ∃ τ:ℝ, 0<τ∧∀ᶠ n in l,b.c.recital p (fun i=>b.g i n) b.α τ
  light : b.c.lit b.α

structure bright (q : PreparationParameters) (l : Filter ℕ) (p : Shape) (M : ℕ) (m : cycleM p)
    (s : rhythms p M) (b : Sketch p M) : Prop where
  forecasts : ledger b l
  engraved : ∀ᶠ n in l,(s n).within (engrave b q m s n)

def matchProg (b : Sketch p M) (n : ℕ) :=
  matchUp (delta (b.m n)) b.α b.r b.c
def glow (s : rhythms p M) (w : tale p M) (b : Sketch p M) (n : ℕ) :=
  pr (pairW ((s n).sap (w n)) ((s n).sap (w n))) (matchProg b n)
def gleam (s : rhythms p M) (w : tale p M) (b : Sketch p M) (n : ℕ) :=
  pr (pairW ((s n).sap (w n)) ((s n).sap (w n)))
     (fun x=>matchProg b n x∧¬secureAt p (s n).rooting x)
def gilded (s : rhythms p M) (w : tale p M) (b : Sketch p M) (n : ℕ) :=
  pr (pairW ((s n).sap (w n)) ((s n).sap (w n)))
     (fun x=>matchProg b n x∧secureAt p (s n).rooting x)

def glowOutcome (l : Filter ℕ) (p : Shape) (M : ℕ)
    (w : tale p M) (s : rhythms p M) (b : Sketch p M) :=
  ∃ e:ℝ,0<e∧∀ᶠ n in l,e ≤ gilded s w b n

def hardened (q : PreparationParameters) (p : Shape) (N : ℕ) {n}
    (s : LeafMixture p n N) (z : BMark p n N) :=
  ∃ T : Cov p N, cdim p T ≤ q.d ∧ (s.within (fun x=> covered p T (delta z x))) ∧
    ∀ i∈s.T,∃ a,specialLeaf T z a i (s.pin i) ∧
      ∀ x∈i,∀ j,z x j ∈ effective a.sp j

def glimmer (q : PreparationParameters) (l : Filter ℕ) (p : Shape) (M : ℕ)
    (w : tale p M) (s : rhythms p M) (b : Sketch p M) :=
  b.c=dusk ∧ ∃ e:ℝ,0<e∧∀ᶠ n in l,q.hardened p (M*n) (s n) (b.m n) ∧
    e/((M*n:ℕ):ℝ)^4 ≤ glow s w b n ∧ gleam s w b n≤0.001*glow s w b n

def predOutcome (q : PreparationParameters) (l : Filter ℕ) (p : Shape) (M : ℕ) (m : cycleM p)
    (w : tale p M) (s : rhythms p M) :=
    ∃ b : Sketch p M,q.bright l p M m s b ∧ (glowOutcome l p M w s b ∨ q.glimmer l p M w s b)

def intern (q : PreparationParameters) (p : Shape) (n N : ℕ) :=
  ∀ m : Mixer p n,PhaseReady p n N (mstep q.rank) (N/denomStep q.rank) q.rank q.k q.d m
     (tinyPhase p.g q.rank q.spJoint) coin warn (heatloss q.rank q.k) q.spear
     (bp (q.spJoint*N))

def outside (q : PreparationParameters) (p : Shape) (n N : ℕ) :=
   ∀ P:UnitType p n N×UnitType p n N→Prop, named P (bp (3*q.d*(N:ℝ))) →
    named (P ∘ Prod.swap) (bp (3*q.d*(N:ℝ))) →
    ∀ w (b:Fpins p n N) (m:Mixer p n),(∀ x,planRank (b x)≤q.pins) →
    IsLaw w → bySide p w m (shine N) → (∀ x,w x≠0 → ∀ i,frameLaw m (onSide x i)) →
    pr (pairW w w) (fun x=>P x ∧ ¬secureAt p b x) ≤ 0.0005*pr (pairW w w) P+edgeError N
structure planted (q : PreparationParameters) (p : Shape) (M : ℕ) : Prop where
  early : q.allows
  hM : 1≤M
  hg : Odd p.g
  hG : 3≤p.g
  hJ : 1≤p.j
  hR : 1≤p.r
  hB : (q.B:ℝ)<bp ((p.b:ℝ)-2*p.j)
  hD : 8*q.D<p.g*p.g
  room : ∃ d_:ℕ,4*q.D≤p.g*d_∧2*screenRank p q.e+1 ≤ ((p.g-1)/2)*(p.g-d_)*p.r
  wrap : ∀ᶠ n : ℕ in atTop, let N:=M*n;
    2*num (Full p n)<N ∧ (3*q.d+2*q.e:ℝ)*N+2*q.e^2≤ ((q.u:ℝ)-1)*N ∧
    (∀ (m : Mixer p n) (a : Pin p n N), pr (usual p m N) a.agree ≤ fee N (q.ζ/4) (planRank a.sp)) ∧
      q.intern p n N ∧ q.outside p n N

end PreparationParameters
end HadwigerCounterexample

end

end OAI
end

section
-- module Solutions.OAIQ430_HC.HadwigerCounterexample_PreparedOutcomes
attribute [-instance] _root_.OAI.HadwigerCounterexample.StatusAnalysis.deckFin _root_.OAI.HadwigerCounterexample.Template.datumFinite _root_.OAI.HadwigerCounterexample.Template.inpFinite _root_.OAI.HadwigerCounterexample.Template.keySlotFinite _root_.OAI.HadwigerCounterexample.arrFintype _root_.OAI.HadwigerCounterexample.drawFintype _root_.OAI.HadwigerCounterexample.idxDec _root_.OAI.HadwigerCounterexample.momFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Prepared Outcomes -/

noncomputable section
namespace HadwigerCounterexample
open Filter Finset
open scoped BigOperators Topology
open PredictionClass

namespace PreparationParameters
variable {l : Filter ℕ} {p : Shape} {M n N : ℕ} {q : PreparationParameters}
  {m : cycleM p} {s : rhythms p M} {w : tale p M}

variable {b : Sketch p M}

def domed (q : PreparationParameters) (l : Filter ℕ) (s : rhythms p M) (b : Sketch p M) :=
  ∀ᶠ n in l, ∃ T : Cov p (M*n), cdim p T≤q.d ∧
    (s n).within (fun x=>covered p T (delta (b.m n) x))

end PreparationParameters
end HadwigerCounterexample

end

end OAI
end

section
-- module Solutions.OAIQ430_HC.HadwigerCounterexample_PreparedPopulationTrimming
attribute [-instance] _root_.OAI.HadwigerCounterexample.StatusAnalysis.deckFin _root_.OAI.HadwigerCounterexample.Template.datumFinite _root_.OAI.HadwigerCounterexample.Template.inpFinite _root_.OAI.HadwigerCounterexample.Template.keySlotFinite _root_.OAI.HadwigerCounterexample.arrFintype _root_.OAI.HadwigerCounterexample.drawFintype _root_.OAI.HadwigerCounterexample.idxDec _root_.OAI.HadwigerCounterexample.momFintype _root_.OAI.HadwigerCounterexample.rackFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Prepared Population Trimming -/

noncomputable section
namespace HadwigerCounterexample
open Filter Finset
open scoped BigOperators Topology
open PredictionClass

namespace PreparationParameters
variable {l : Filter ℕ} {p : Shape} {M : ℕ} {q : PreparationParameters}
  {m : cycleM p} {s : rhythms p M} {w : tale p M} {b : Sketch p M}

abbrev Campaign (p : Shape) (M : ℕ) := ∀ n,UnitType p n (M*n) → Prop
variable {P : Campaign p M}
structure citable (q : PreparationParameters) (l : Filter ℕ) (p : Shape) (M : ℕ)
    (m : cycleM p) (w : tale p M) (s : rhythms p M) (b : Sketch p M) (P : Campaign p M) : Prop where
  mass : warm l (fun i=> ((M*i:ℕ):ℝ)) (fun i=>pr ((s i).sap (w i)) (P i))
  forecast : ledger b l
  mark : ∀ᶠ i in l, (s i).within (fun x => P i x → engrave b q m s i x)

def potion (s : rhythms p M) (w : tale p M) (P : Campaign p M) : tale p M :=
  fun n => onW ((s n).sap (w n)) (P n)
def charm (s : rhythms p M) (w : tale p M) (P : Campaign p M) (b : Sketch p M) :=
  fun n => pr (pairW (potion s w P n) (potion s w P n)) (matchProg b n)

/-- Tiny cover exists after preparing retained mass, seen on
its support. Requires each old tile contain only original support. -/
def nebulous (q : PreparationParameters) (l : Filter ℕ) (s : rhythms p M) (w : tale p M) (P : Campaign p M)
    (b : Sketch p M) :=
   ∀ᶠ n in l,∃ T : Cov p (M*n),cdim p T≤q.d∧
     ∀ x,potion s w P n x≠0 → covered p T (delta (b.m n) x)

end PreparationParameters
end HadwigerCounterexample

end

end OAI
end

section
-- module Solutions.OAIQ430_HC.HadwigerCounterexample_PhasePreparedOutcomes
attribute [-instance] _root_.OAI.HadwigerCounterexample.StatusAnalysis.deckFin _root_.OAI.HadwigerCounterexample.Template.datumFinite _root_.OAI.HadwigerCounterexample.Template.inpFinite _root_.OAI.HadwigerCounterexample.Template.keySlotFinite _root_.OAI.HadwigerCounterexample.arrFintype _root_.OAI.HadwigerCounterexample.drawFintype _root_.OAI.HadwigerCounterexample.idxDec _root_.OAI.HadwigerCounterexample.momFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Phase Prepared Outcomes -/

noncomputable section
namespace HadwigerCounterexample
open Filter Finset
open scoped BigOperators Topology
open PredictionClass

namespace PreparationParameters
variable {l : Filter ℕ} {p : Shape} {M : ℕ} {q : PreparationParameters}
  {m : cycleM p} {s : rhythms p M} {w : tale p M} {b : Sketch p M} {P Q : Campaign p M}

def satisfied (q : PreparationParameters) (l : Filter ℕ) (p : Shape) (M : ℕ) (m : cycleM p)
    (w : tale p M) :=
  ∃ t : rhythms p M,q.durable l p M m w t ∧ (q.silenceOutcome l p M m w t ∨
    q.predOutcome l p M m w t)

end PreparationParameters
end HadwigerCounterexample

end

end OAI
end

section
-- module Solutions.OAIQ430_HC.HadwigerCounterexample_PreliminaryRestrictions
attribute [-instance] _root_.OAI.HadwigerCounterexample.StatusAnalysis.deckFin _root_.OAI.HadwigerCounterexample.Template.datumFinite _root_.OAI.HadwigerCounterexample.Template.inpFinite _root_.OAI.HadwigerCounterexample.Template.keySlotFinite _root_.OAI.HadwigerCounterexample.arrFintype _root_.OAI.HadwigerCounterexample.drawFintype _root_.OAI.HadwigerCounterexample.idxDec _root_.OAI.HadwigerCounterexample.momFintype _root_.OAI.HadwigerCounterexample.rackFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Preliminary Restrictions -/

noncomputable section
namespace HadwigerCounterexample
open Filter Finset Matrix
open scoped BigOperators Topology
open PredictionClass
namespace PreparationParameters

variable {l : Filter ℕ} {p : Shape} {M n N : ℕ} {q : PreparationParameters} {m : cycleM p}
  {s : rhythms p M} {w : tale p M} {b : Sketch p M} {P : Campaign p M}

def pollen : ℝ := 10^(-9:ℤ)

structure dosed (q : PreparationParameters) (l : Filter ℕ) (p : Shape) (M : ℕ)
    (m : cycleM p) (w : tale p M) (s : rhythms p M) (b : Sketch p M) (P : Campaign p M) : Prop where
  cite : q.citable l p M m w s b P
  lower : ∀ᶠ n in l,pollen ≤ pr ((s n).sap (w n)) (P n)
  capped : ∀ᶠ n in l,∀ x i,totalRank (b.m n x i) ≤ q.e

end PreparationParameters
end HadwigerCounterexample

end

end OAI
end

section
-- module Solutions.OAIQ430_HC.HadwigerCounterexample_PredictionDichotomy
attribute [-instance] _root_.OAI.HadwigerCounterexample.StatusAnalysis.deckFin _root_.OAI.HadwigerCounterexample.Template.datumFinite _root_.OAI.HadwigerCounterexample.Template.inpFinite _root_.OAI.HadwigerCounterexample.Template.keySlotFinite _root_.OAI.HadwigerCounterexample.arrFintype _root_.OAI.HadwigerCounterexample.drawFintype _root_.OAI.HadwigerCounterexample.idxDec _root_.OAI.HadwigerCounterexample.momFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Prediction Dichotomy -/

noncomputable section
namespace HadwigerCounterexample
open Filter Finset Matrix
open scoped BigOperators Topology
open PredictionClass

namespace PreparationParameters

variable {l : Filter ℕ} {p : Shape} {M n N : ℕ} {q : PreparationParameters} {m : cycleM p}
  {s : rhythms p M} {w : tale p M} {b : Sketch p M} {U : Ultrafilter ℕ} {P : Campaign p M}

def outlook (q : PreparationParameters) (l : Filter ℕ) (p : Shape) (M : ℕ)
    (m : cycleM p) (w : tale p M) (s : rhythms p M) :=
  ∃ ε:ℕ→ℝ, slight l ε ∧ ∀ᶠ n in l,q.predicts p (M*n) (m n) (s n) (w n) (ε n)

structure Sage (p : Shape) (n N : ℕ) where
  g : Bool→Augur p N
  m : BMark p n N
  L : UnitType p n N → Bool→ Finset (Label p.b)

instance instInhabitedSage : Inhabited (Sage p n N) := ⟨⟨fun _ _ _ _=>0,fun _=>0,fun _ _=>∅⟩⟩

abbrev Banners := Party × F × Bool

def tender {p : Shape} {n N} (i : Sage p n N) (q : PreparationParameters) (m : Mixer p n)
    (s : LeafMixture p n N) (z : Banners) (ε : ℝ) (x : UnitType p n N) :=
  q.seems p m s x i.g (i.m x) (i.L x) z.1 ε ∧ glint p (i.m x)=z.2.1 ∧
    ((z.2.2=true) ↔ delta i.m x=0)

def crowdSeed : ℝ := 2*pollen
end PreparationParameters
end HadwigerCounterexample

end

end OAI
end

section
-- module Solutions.OAIQ430_HC.HadwigerCounterexample_TerminalCut
attribute [-instance] _root_.OAI.HadwigerCounterexample.StatusAnalysis.deckFin _root_.OAI.HadwigerCounterexample.Template.datumFinite _root_.OAI.HadwigerCounterexample.Template.inpFinite _root_.OAI.HadwigerCounterexample.Template.instFintypeOppDuet _root_.OAI.HadwigerCounterexample.Template.instFintypeSameDuet _root_.OAI.HadwigerCounterexample.Template.keySlotFinite _root_.OAI.HadwigerCounterexample.Volley.instFintypeVisits _root_.OAI.HadwigerCounterexample.aFintype _root_.OAI.HadwigerCounterexample.amongFintype _root_.OAI.HadwigerCounterexample.arrFintype _root_.OAI.HadwigerCounterexample.cgFin _root_.OAI.HadwigerCounterexample.cgOneFin _root_.OAI.HadwigerCounterexample.drawFintype _root_.OAI.HadwigerCounterexample.fintypeLedger _root_.OAI.HadwigerCounterexample.fintypeStory _root_.OAI.HadwigerCounterexample.fullFintype _root_.OAI.HadwigerCounterexample.instFKeys _root_.OAI.HadwigerCounterexample.knFin _root_.OAI.HadwigerCounterexample.momFintype _root_.OAI.HadwigerCounterexample.oframeFintype _root_.OAI.HadwigerCounterexample.orientFintype _root_.OAI.HadwigerCounterexample.rackFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Terminal Cut -/

noncomputable section
namespace HadwigerCounterexample
open scoped BigOperators

variable {α : Type*} [Fintype α]

/-- Individual marginal caps (mapW denotes the actual marginals) and a joint cap. -/
def pairCaps (μ : Wgt α) (m d : ℝ) (w : Wgt (α × α)) :=
  (∀ x, mapW w Prod.fst x ≤ m * μ x) ∧
  (∀ x, mapW w Prod.snd x ≤ m * μ x) ∧
  (∀ p, w p ≤ d * pairW μ μ p)

def incW (w : Wgt α) (p : α) (b : ℝ) : Wgt α :=
  fun x => w x + b * ind (x = p)

end HadwigerCounterexample

end

end OAI
end

section
-- module Solutions.OAIQ430_HC.HadwigerCounterexample_InitialPartitionExistence
attribute [-instance] _root_.OAI.HadwigerCounterexample.StatusAnalysis.deckFin _root_.OAI.HadwigerCounterexample.Template.datumFinite _root_.OAI.HadwigerCounterexample.Template.inpFinite _root_.OAI.HadwigerCounterexample.Template.keySlotFinite _root_.OAI.HadwigerCounterexample.arrFintype _root_.OAI.HadwigerCounterexample.drawFintype _root_.OAI.HadwigerCounterexample.idxDec _root_.OAI.HadwigerCounterexample.momFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Initial Partition Existence -/

noncomputable section
namespace HadwigerCounterexample
open Filter Finset
open scoped BigOperators Topology
namespace PreparationParameters

variable {p : Shape} {n N M : ℕ} {q : PreparationParameters}

structure entry (q : PreparationParameters) (p : Shape) (M : ℕ) : Prop where
  first : q.planted p M
  hF : ∀ᶠ n : ℕ in atTop, let N:=M*n;
    ∀ (m : Mixer p n) (w:Wgt (UnitType p n N)), q.nascent p N w m →
     carried w (rawHoles m).unit → ∃ s : LeafMixture p n N,q.entered p N m w s

end PreparationParameters
end HadwigerCounterexample

end

end OAI
end

section
-- module Solutions.OAIQ430_HC.HadwigerCounterexample_PairedOptions
attribute [-instance] _root_.OAI.HadwigerCounterexample.arrFintype _root_.OAI.HadwigerCounterexample.drawFintype _root_.OAI.HadwigerCounterexample.idxDec _root_.OAI.HadwigerCounterexample.momFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Paired Options -/

noncomputable section
namespace HadwigerCounterexample
open Matrix Module LinearMap Finset Submodule Function
open scoped BigOperators
namespace StatusAnalysis
variable {p : Shape} {n N K : ℕ}

structure Quill (p : Shape) (q : Format) (d : Rates) (b : Bool) where
  sel : Messenger q → Label p.b
  flav : Messenger q → Flavor p.g
  amp : Amounts p q d b
  script : Script p (Messenger q)

structure Typus (p : Shape) (q : Format) (d e : Rates) where
  t : Tagging p (Messenger q)
  z : Messenger q → F
  qA : Quill p q d true
  qB : Quill p q e false

abbrev Volumes := Grid → Fin 8
abbrev Stakes (K : ℕ) := Nodes → Fin (K^2+1)
abbrev Master (K : ℕ) := Volumes × Stakes K × Stakes K
def toFormat (q : Volumes) : Format := fun i=>(q i).val
def toRates {K : ℕ} (d : Stakes K) : Rates := fun i=>(d i).val
abbrev OnFile (p : Shape) {K : ℕ} (q : Master K) :=
  Typus p (toFormat q.1) (toRates q.2.1) (toRates q.2.2)
abbrev Scrip (p : Shape) (K : ℕ) := Σ q : Master K, Fin (2^deckMax p K) × OnFile p q

instance quillFintype (p : Shape) (q : Format) (d : Rates) (b : Bool) :
    Fintype (Quill p q d b) := by
  classical
  let A := (Messenger q → Label p.b) × (Messenger q→Flavor p.g) × Amounts p q d b × Script p (Messenger q)
  let E : A≃Quill p q d b := {
    toFun x:= ⟨x.1,x.2.1,x.2.2.1,x.2.2.2⟩
    invFun x:= (x.sel,x.flav,x.amp,x.script)
    left_inv _ := rfl
    right_inv _:=rfl }
  letI : Fintype (Messenger q → Flavor p.g):= by infer_instance
  letI : Fintype (Amounts p q d b) := by infer_instance
  letI : Fintype (MOne p):= by unfold MOne MIdx; infer_instance
  letI : Fintype (Vec (MOne p)):= by infer_instance
  letI : Fintype (Messenger q →Vec (MOne p)):= by infer_instance
  letI : Fintype (Script p (Messenger q)):= by infer_instance
  exact Fintype.ofEquiv _ E
instance typusFintype (p : Shape) (q : Format) (d e : Rates) : Fintype (Typus p q d e) := by
  classical
  let A:=Tagging p (Messenger q)× (Messenger q→F) ×Quill p q d true×Quill p q e false
  let E : A≃Typus p q d e := {
    toFun x:=⟨x.1,x.2.1,x.2.2.1,x.2.2.2⟩
    invFun x:=(x.t,x.z,x.qA,x.qB)
    left_inv _:=rfl
    right_inv _:=rfl }
  exact Fintype.ofEquiv _ E
instance scripFintype (p : Shape) (K : ℕ) : Fintype (Scrip p K) := by
  classical
  infer_instance

variable {q : Format} {d e : Rates}

namespace Quill
variable {b : Bool} (w : Quill p q d b) (t : Tagging p (Messenger q)) (z : Messenger q→F)

def pen := manager b t w.sel w.flav
def moral :=
    Injective w.sel ∧ owing p b w.amp z ∧ ∀ i, (w.amp i).1.feasible (t i) (w.flav i)

def penSpace (x : Pin p n N) (K : ℕ) :=
   ∀ y:Inputs p n (Messenger q), ((w.pen t).draw y).avoids x.sp (qorth K)

def signed (x y : Pin p n N) (s : Charts p n d) (T : Cross p n) (K : ℕ) :=
    charted s x.sp ∧ w.penSpace t x K ∧ still b w.amp s T ∧ tableInj x.sp y.sp T

def deposit (m : Mixer p n) (o : UnitType p n N) (v : Charts p n d)
    (x : Inputs p n (Messenger q)) :=
  let u := (w.pen t).draw x
  printed b v t w.sel w.flav m o x=w.amp ∧
    u.reads w.script m ∧ ownPart t z (u.keys t o)

def sales (μ : Wgt (UnitType p n N)) (P : UnitType p n N→Prop)
    (m :Mixer p n) (s : Charts p n d) : Wgt (Keys (p:=p) t N) :=
  Volley.hist (w.pen t).draw t μ ((w.pen t).state z n)
    (fun x o=> P o∧w.deposit t z m o s x)

end Quill

namespace Typus
variable (w : Typus p q d e)
def permission :=
  (∀ i,1 ≤ q i∧q i≤7) ∧
  w.qA.moral w.t w.z ∧ w.qB.moral w.t w.z ∧
  (∀ i,fullq w.z i=1) ∧ rhyme w.qA.amp w.qB.amp ∧
  proclaims p w.qA.amp w.qB.amp w.t w.qA.script ∧
    proclaims p w.qB.amp w.qA.amp w.t w.qB.script

def chances (s : Charts p n d) (v : Charts p n e)
    (x y : Pin p n N) (T : Cross p n) (K : ℕ) :=
  w.permission ∧ w.qA.signed w.t x y s T K ∧ w.qB.signed w.t y x v (reciprocal p T) K
end Typus

def notified (m : Mixer p n) (x y : Pin p n N) (T : Cross p n)
    (C : Prop) (o : UnitType p n N) :=
  C ∧ x.agree o ∧ (∀ i,frameLaw m (onSide o i)) ∧ tableFlag x y T o

structure Station (p : Shape) (n N K : ℕ) (s : LeafMixture p n N) where
  cAxes : s.T → (d:Rates)→Charts p n d
  mails : s.T → s.T → Fin (2^deckMax p K) → Cross p n
namespace Station
variable {s : LeafMixture p n N} (v : Station p n N K s)

def bank :=
  (∀ i,dressCode (p:=p) n (s.pin i.val).sp (v.cAxes i)) ∧
  ∀ i j T,∃ k,fitsTable (s.pin i.val).sp (s.pin j.val).sp (v.mails i j k) T
where
  dressCode {p : Shape} (n : ℕ) (f : Plan p n) (V : (d:Rates)→ Charts p n d) :=
    let d:=fun i=>dim (effective f i)
    charted (V d) f

variable (w : Typus p q d e)

def news (i j : s.T) (k : Fin (2^deckMax p K)) :=
  w.chances (v.cAxes i d) (v.cAxes j e) (s.pin i.val) (s.pin j.val) (v.mails i j k) K
def frontPage (m : Mixer p n) (i j : s.T) (k : Fin (2^deckMax p K)) :=
  notified m (s.pin i.val) (s.pin j.val) (v.mails i j k) (news v w i j k)
def backPage (m : Mixer p n) (i j : s.T) (k : Fin (2^deckMax p K)) :=
  notified m (s.pin j.val) (s.pin i.val) (reciprocal p (v.mails i j k)) (news v w i j k)

def leftSales (m : Mixer p n) (μ : Wgt (UnitType p n N)) (i j : s.T)
    (k : Fin (2^deckMax p K)) :=
  w.qA.sales w.t w.z (partW μ i.val) (frontPage v w m i j k) m (v.cAxes i d)
def rightSales (m : Mixer p n) (μ : Wgt (UnitType p n N)) (i j : s.T)
    (k : Fin (2^deckMax p K)) :=
  w.qB.sales w.t w.z (partW μ j.val) (backPage v w m i j k) m (v.cAxes j e)

def matchScore (m:Mixer p n) (μ: Wgt (UnitType p n N)) (i j:s.T)
    (k : Fin (2^deckMax p K)) :=
  overlap (lawNu p N w.t w.z) (leftSales v w m μ i j k) (rightSales v w m μ i j k)

def arena (m:Mixer p n) (μ: Wgt (UnitType p n N)) (k:Fin (2^deckMax p K)) :=
  avg (pairW (portionW μ s.T) (portionW μ s.T)) (fun x=>matchScore v w m μ x.1 x.2 k)
end Station
end StatusAnalysis
end HadwigerCounterexample

end

end OAI
end

section
-- module Solutions.OAIQ430_HC.HadwigerCounterexample_PairedCollisionBounds
attribute [-instance] _root_.OAI.HadwigerCounterexample.arrFintype _root_.OAI.HadwigerCounterexample.drawFintype _root_.OAI.HadwigerCounterexample.idxDec _root_.OAI.HadwigerCounterexample.momFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Paired Collision Bounds -/

noncomputable section
namespace HadwigerCounterexample
open Matrix Module LinearMap Finset Submodule Filter
open scoped BigOperators Topology
namespace StatusAnalysis
variable {p : Shape} {n N K : ℕ} {q : Format} {d e : Rates}

namespace Station
variable {s : LeafMixture p n N} (v : Station p n N K s)

def clash (p : Shape) (m : Mixer p n) (N : ℕ) :=
   fun x : UnitType p n N × UnitType p n N => (rawHoles m).conflict x.1 x.2

def beamPrice (p : Shape) (N : ℕ) := bp (((kmax p:ℝ)+0.02)*N)

structure earnsScore (p : Shape) (n N K : ℕ) (ζ : ℝ) : Prop where
  hr : 1≤p.r
  hn : 2*p.r≤n
  solid : realizeAssum p K
  smooth : 0 ≤ ζ
  low : ζ ≤ 0.004
  light : ζ*(kmax p) ≤ 0.004
  hN : 100 ≤ N
  gram : (dim (CheckGram p n) : ℝ) ≤ 0.01*N
  budget : (K+(kmax p:ℝ))*num (JointIdx p n) ≤ 0.005*N

end Station
end StatusAnalysis
end HadwigerCounterexample

end

end OAI
end

section
-- module Solutions.OAIQ430_HC.HadwigerCounterexample_PairedMassIdentities
attribute [-instance] _root_.OAI.HadwigerCounterexample.arrFintype _root_.OAI.HadwigerCounterexample.drawFintype _root_.OAI.HadwigerCounterexample.idxDec _root_.OAI.HadwigerCounterexample.momFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Paired Mass Identities -/

noncomputable section
namespace HadwigerCounterexample
open Matrix Module LinearMap Finset Submodule Filter
open scoped BigOperators Topology
namespace StatusAnalysis
variable {p : Shape} {n N K M: ℕ} {q : Format} {d e : Rates}

namespace Quill
variable {i:Bool} (w : Quill p q d i)
    (μ : Wgt (UnitType p n N)) (s : Charts p n d)
    (t : Tagging p (Messenger q)) (z : Messenger q → F)
    (m : Mixer p n)
    (P : UnitType p n N→Prop)

def customer := fromFlags μ ((w.pen t).state z n)
  (Y:=Bool)
  (fun o x=> open scoped Classical in decide (w.deposit t z m o s x))
  ((w.pen t).resultKey)
def custom := hung (w.customer μ s t z m) (ownPart t z)

def billboard := fun (o:UnitType p n N) x=> open scoped Classical in decide (w.deposit t z m o s x)

def prowl (o : UnitType p n N) (W : Wgt (Keys (p:=p) t N)) :=
    avg ((w.pen t).state z n) (fun x=>ind (w.deposit t z m o s x)*W ((w.pen t).resultKey o x))

end Quill

end StatusAnalysis
end HadwigerCounterexample

end

end OAI
end

section
-- module Solutions.OAIQ430_HC.HadwigerCounterexample_FourCornerViews
attribute [-instance] _root_.OAI.HadwigerCounterexample.StatusAnalysis.deckFin _root_.OAI.HadwigerCounterexample.StatusAnalysis.scripFintype _root_.OAI.HadwigerCounterexample.Template.instFintypeOppDuet _root_.OAI.HadwigerCounterexample.Template.instFintypeSameDuet _root_.OAI.HadwigerCounterexample.arrFintype _root_.OAI.HadwigerCounterexample.drawFintype _root_.OAI.HadwigerCounterexample.fintypeStory _root_.OAI.HadwigerCounterexample.momFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Four Corner Views -/

noncomputable section
namespace HadwigerCounterexample
open Finset Real Matrix Function
open scoped BigOperators
variable {A B C : Type} [Fintype A] [Fintype B] [Fintype C]

abbrev Corn := Bool × Bool

def criss (E : A ≃ B × C) (p : A × A) (x : Corn) :=
  E.symm ((onSide (Prod.map E E p) x.1).1,(onSide (Prod.map E E p) x.2).2)
def quart (E : A≃B×C) (U : Wgt A) (p : A×A) :=
  ∏ i:Corn,U (criss E p i)

variable {E : A≃ B × C}

def spread (U : Wgt (B× C)) (i : (B×C) × B×C) :=
  U (i.1.1,i.1.2)*U (i.1.1,i.2.2)* (U (i.2.1,i.1.2)*U (i.2.1,i.2.2))

end HadwigerCounterexample

end

end OAI
end

section
-- module Solutions.OAIQ430_HC.HadwigerCounterexample_SinglePositionExpansion
attribute [-instance] _root_.OAI.HadwigerCounterexample.LeafMixture.instInhabited _root_.OAI.HadwigerCounterexample.PreparationParameters.instInhabitedSage _root_.OAI.HadwigerCounterexample.StatusAnalysis.deckFin _root_.OAI.HadwigerCounterexample.StatusAnalysis.quillFintype _root_.OAI.HadwigerCounterexample.StatusAnalysis.scripFintype _root_.OAI.HadwigerCounterexample.StatusAnalysis.typusFintype _root_.OAI.HadwigerCounterexample.arrFintype _root_.OAI.HadwigerCounterexample.drawFintype _root_.OAI.HadwigerCounterexample.fintypeStory _root_.OAI.HadwigerCounterexample.idxDec _root_.OAI.HadwigerCounterexample.instDecidableUsesPunch _root_.OAI.HadwigerCounterexample.momFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Single Position Expansion -/

noncomputable section
namespace HadwigerCounterexample
open Finset Function Matrix
open scoped BigOperators
variable {I A B C : Type} [Fintype I] [DecidableEq I]
variable {p : Shape} {n N : ℕ}
variable {X : I → Type}

abbrev Aside (i : I) := {j:I//j≠i}
def chair (X : I →Type) (i:I) := Equiv.piSplitAt i X

variable [∀ i,Fintype (X i)]

def arm (i j : I) (x : Corn) := if j=i then x.1 else x.2

namespace Template
variable (v : Template p I)

def beyond (v : Template p I) (i : I) : Template p (Aside i) :=
  collect p v Subtype.val
def chairK (v : Template p I) (i : I) (N : ℕ) :
    Keys (p:=p) v.t N ≃ (AtomKey (p:=p) (v.t i) N × Keys (p:=p) (v.beyond i).t N) :=
  chair _ _
def chairI (_ : Template p I) (i : I) (n : ℕ) :
    Inputs p n I ≃ Knobs p.g n × Inputs p n (Aside i) := chair _ _

def earns (v : Template p I) (s : Script p I) (m : Mixer p n) (q : I→F)
    (o : UnitType p n N) (x : Inputs p n I) :=
  (v.draw x).reads s m ∧ ownPart (p:=p) v.t q (v.resultKey o x)
end Template
end HadwigerCounterexample

end

end OAI
end

section
-- module Solutions.OAIQ430_HC.HadwigerCounterexample_FourCornerMasks
attribute [-instance] _root_.OAI.HadwigerCounterexample.LeafMixture.instInhabited _root_.OAI.HadwigerCounterexample.PreparationParameters.instInhabitedSage _root_.OAI.HadwigerCounterexample.StatusAnalysis.deckFin _root_.OAI.HadwigerCounterexample.StatusAnalysis.quillFintype _root_.OAI.HadwigerCounterexample.StatusAnalysis.scripFintype _root_.OAI.HadwigerCounterexample.StatusAnalysis.typusFintype _root_.OAI.HadwigerCounterexample.arrFintype _root_.OAI.HadwigerCounterexample.drawFintype _root_.OAI.HadwigerCounterexample.fintypeStory _root_.OAI.HadwigerCounterexample.idxDec _root_.OAI.HadwigerCounterexample.instDecidableUsesPunch _root_.OAI.HadwigerCounterexample.momFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Four Corner Masks -/

noncomputable section
namespace HadwigerCounterexample
open Finset Matrix Filter Function
open scoped BigOperators
variable {p : Shape} {I : Type} [Fintype I] [DecidableEq I] {n N : ℕ}

def wingpair (I : Type) : (Bool→ I)≃ I × I where
  toFun x := (x true,x false)
  invFun x := onSide x
  left_inv i := by funext j; cases j <;> rfl
  right_inv _ := rfl

namespace Template
variable (v : Template p I)
abbrev PackSlot (v : Template p I) := Bool × KeySlots p v.t

abbrev PackStack (v : Template p I) (N : ℕ) := Rack v.PackSlot N

def untwin (v : Template p I) (N) :
    v.PackStack N ≃ Keys (p:=p) v.t N × Keys (p:=p) v.t N :=
  let E:=scatter v.t N
  ((relay Bool (KeySlots p v.t) N).trans (wingpair _)).trans (E.symm.prodCongr E.symm)

def yieldK (v : Template p I) (j : I) (c : Corn) (x : v.PackStack N) :=
  criss (v.chairK j N) (v.untwin N x) c
def seam (v : Template p I) : Route v.PackSlot (Ports p) := tied (globPort p v.t v.aim) Bool

def sees (v : Template p I) (j : I) (c : Corn) (w : v.PackSlot) :=
  arm j w.2.1 c=w.1
instance instDecidableSees (v : Template p I) (j c w) : Decidable (sees v j c w) := Classical.propDecidable _

def cantRail (v : Template p I) (j : I) := open Classical in
  (crowded v.seam).filter (fun x => ¬∃ c,sees v j c x.1 ∧ sees v j c x.2)

theorem cant_mem (v : Template p I) (j) (x) :
    x∈cantRail v j ↔ x∈crowded v.seam ∧ ¬∃ c,sees v j c x.1 ∧ sees v j c x.2 := mem_filter

def cantVec (v : Template p I) (j : I) (Z : GeoM v.seam) : Vec (cantRail v j) :=
  fun x => directions _ Z ⟨x.val,((cant_mem ..).mp x.property).1⟩

def gatedStack (v : Template p I) (j : I) (q : I→F) (x : v.PackStack N) :=
  ∀ i:Corn,ownPart (p:=p) v.t q (yieldK v j i x)

def packSecs (v : Template p I) (j : I) (U : Wgt (Keys (p:=p) v.t N)) (x : v.PackStack N) :=
  ∏ i:Corn,U (yieldK v j i x)

end Template
end HadwigerCounterexample

end

end OAI
end

section
-- module Solutions.OAIQ430_HC.HadwigerCounterexample_UnseenCrossingFactorization
attribute [-instance] _root_.OAI.HadwigerCounterexample.LeafMixture.instInhabited _root_.OAI.HadwigerCounterexample.PreparationParameters.instInhabitedSage _root_.OAI.HadwigerCounterexample.StatusAnalysis.deckFin _root_.OAI.HadwigerCounterexample.StatusAnalysis.quillFintype _root_.OAI.HadwigerCounterexample.StatusAnalysis.scripFintype _root_.OAI.HadwigerCounterexample.StatusAnalysis.typusFintype _root_.OAI.HadwigerCounterexample.arrFintype _root_.OAI.HadwigerCounterexample.drawFintype _root_.OAI.HadwigerCounterexample.fintypeStory _root_.OAI.HadwigerCounterexample.idxDec _root_.OAI.HadwigerCounterexample.instDecidableUsesPunch _root_.OAI.HadwigerCounterexample.momFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Unseen Crossing Factorization -/

noncomputable section
namespace HadwigerCounterexample
open Finset Matrix Module LinearMap Function Filter
open scoped BigOperators
variable {p : Shape} {n N : ℕ} {I J : Type} [Fintype I] [DecidableEq I] [Fintype J]
variable [DecidableEq J]
namespace Template
variable (v : Template p I)

def spot (w : v.PackSlot) (A : PlusRack Unit N) :=
  upliftR (fun _:Unit=>w) A

def chairCut (v : Template p I) (j : I) (U : Wgt (Keys (p:=p) v.t N)) (δ : ℝ) :=
  thinCut unif U (Prod.fst ∘ v.chairK j N) (Prod.snd ∘ v.chairK j N) δ

end Template
end HadwigerCounterexample

end

end OAI
end

section
-- module Solutions.OAIQ430_HC.HadwigerCounterexample_FourCornerTrials
attribute [-instance] _root_.OAI.HadwigerCounterexample.LeafMixture.instInhabited _root_.OAI.HadwigerCounterexample.PreparationParameters.instInhabitedSage _root_.OAI.HadwigerCounterexample.StatusAnalysis.deckFin _root_.OAI.HadwigerCounterexample.StatusAnalysis.quillFintype _root_.OAI.HadwigerCounterexample.StatusAnalysis.scripFintype _root_.OAI.HadwigerCounterexample.StatusAnalysis.typusFintype _root_.OAI.HadwigerCounterexample.arrFintype _root_.OAI.HadwigerCounterexample.drawFintype _root_.OAI.HadwigerCounterexample.fintypeStory _root_.OAI.HadwigerCounterexample.idxDec _root_.OAI.HadwigerCounterexample.instDecidableUsesPunch _root_.OAI.HadwigerCounterexample.momFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Four Corner Trials -/

noncomputable section
namespace HadwigerCounterexample
open Finset Matrix Module LinearMap Function
open scoped BigOperators
variable {p : Shape} {n N : ℕ} {I : Type} [Fintype I] [DecidableEq I]

namespace Template
variable (v : Template p I)
def protean (v : Template p I) (T : Wgt (Inputs p n I))
    (U : Wgt (Keys (p:=p) v.t N)) (o : UnitType p n N) :=
  fun x => T x*U (v.resultKey o x)

def crane (v : Template p I) (j : I) (T : Wgt (Inputs p n I))
    (U : Wgt (Keys (p:=p) v.t N))
    (w : I → Wgt (Knobs p.g n)) (o : UnitType p n N) :=
  let x:= prodW w
  avg (pairW x x) (quart (v.chairI j n) (v.protean T U o))

end Template
end HadwigerCounterexample

end

end OAI
end

section
-- module Solutions.OAIQ430_HC.HadwigerCounterexample_CutIntegralBounds
attribute [-instance] _root_.OAI.HadwigerCounterexample.LeafMixture.instInhabited _root_.OAI.HadwigerCounterexample.PreparationParameters.instInhabitedSage _root_.OAI.HadwigerCounterexample.StatusAnalysis.deckFin _root_.OAI.HadwigerCounterexample.StatusAnalysis.quillFintype _root_.OAI.HadwigerCounterexample.StatusAnalysis.scripFintype _root_.OAI.HadwigerCounterexample.StatusAnalysis.typusFintype _root_.OAI.HadwigerCounterexample.arrFintype _root_.OAI.HadwigerCounterexample.drawFintype _root_.OAI.HadwigerCounterexample.fintypeStory _root_.OAI.HadwigerCounterexample.idxDec _root_.OAI.HadwigerCounterexample.instDecidableUsesPunch _root_.OAI.HadwigerCounterexample.momFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Cut Integral Bounds -/

noncomputable section
namespace HadwigerCounterexample
open Finset Real Matrix Function Filter
open scoped BigOperators Topology
variable {p : Shape} {n N M : ℕ} {I A : Type} [Fintype I] [DecidableEq I] [Fintype A]

def chairpan (p : I→Wgt A) (x : Bool×I) := p x.2
def reparse (I A : Type) : (Bool×I→ A)≃ (I→A) × (I→A) :=
  (show (_:Type)≃(Bool→I→A) from ⟨curry,uncurry,fun _=>rfl,fun _=>rfl⟩).trans (wingpair _)

namespace Template
variable (v : Template p I)

def panels (v : Template p I) := collect p v (Prod.snd : Bool × I → I)
def rekeys (v : Template p I) (k : Keys (p:=p) v.panels.t N) :
    Keys (p:=p) v.t N ×Keys (p:=p) v.t N := (fun i=>k (true,i),fun i=>k (false,i))

def clue (v : Template p I) (j : I) (T : Wgt (Inputs p n I)) (U : Wgt (Keys (p:=p) v.t N))
    (x : Inputs p n (Bool × I)) (y : Keys (p:=p) v.panels.t N) :=
  quart (chairI v j n) T (reparse _ _ x)*quart (chairK v j N) U (rekeys v y)

def scene (v : Template p I) (T : Wgt (Inputs p n I)) (U : Wgt (Keys (p:=p) v.t N))
    (w f : I→ Wgt (Knobs p.g n)) (o : UnitType p n N) :=
  avg (prodW w) (fun x => protean v T U o x * prodW f x)

def blackout (v : Template p I) (T : Wgt (Inputs p n I)) (U : Wgt (Keys (p:=p) v.t N))
    (w : I→Wgt (Knobs p.g n)) (ε : ℝ) (o : UnitType p n N) :=
  ∃ f:I→Wgt (Knobs p.g n),(∀ i j,|f i j|≤1) ∧ ε < |scene v T U w f o|

end Template
end HadwigerCounterexample

end

end OAI
end

section
-- module Solutions.OAIQ430_HC.HadwigerCounterexample_UnaryCellComparisons
attribute [-instance] _root_.OAI.HadwigerCounterexample.LeafMixture.instInhabited _root_.OAI.HadwigerCounterexample.PreparationParameters.instInhabitedSage _root_.OAI.HadwigerCounterexample.StatusAnalysis.deckFin _root_.OAI.HadwigerCounterexample.StatusAnalysis.quillFintype _root_.OAI.HadwigerCounterexample.StatusAnalysis.scripFintype _root_.OAI.HadwigerCounterexample.StatusAnalysis.typusFintype _root_.OAI.HadwigerCounterexample.arrFintype _root_.OAI.HadwigerCounterexample.drawFintype _root_.OAI.HadwigerCounterexample.fintypeStory _root_.OAI.HadwigerCounterexample.idxDec _root_.OAI.HadwigerCounterexample.instDecidableUsesPunch _root_.OAI.HadwigerCounterexample.momFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Unary Cell Comparisons -/

noncomputable section
namespace HadwigerCounterexample
open Matrix Module Finset Function Filter
open scoped BigOperators
variable {p : Shape} {n N : ℕ} {I J A : Type} [Fintype I] [DecidableEq I] [Fintype J]

namespace Template
variable (v : Template p I)

def curtain (v : Template p I) (q : I→F) (U : Wgt (Keys (p:=p) v.t N)) :=
  fun x => ind (ownPart (p:=p) v.t q x)*U x
def propel (v : Template p I) (s : Script p I) (m : Mixer p n) :=
  fun z => ind ((v.draw z).reads s m)

abbrev Localist (v : Template p I) (N : ℕ) :=
  ∀ i,Wgt (AtomKey (p:=p) (v.t i) N)
def board (v : Template p I) (q : I→F) (U : Wgt (Keys (p:=p) v.t N))
    (f : v.Localist N) :=
  avg unif (fun i=> curtain v q U i * prodW f i)
def shadowed (v : Template p I) (q : I→F) (U : Wgt (Keys (p:=p) v.t N)) (ε : ℝ) :=
  ∀ f : v.Localist N,(∀ i j,|f i j|≤1)→ |board v q U f| ≤ ε

def astonish (v : Template p I) (q : I→F) (U : Wgt (Keys (p:=p) v.t N))
    (s : Script p I) (m : Mixer p n) (w f : I→Wgt (Knobs p.g n)) (o) :=
  scene v (propel v s m) (curtain v q U) w f o
def exceeds (v : Template p I) (q : I→F) (U : Wgt (Keys (p:=p) v.t N))
    (s : Script p I) (m : Mixer p n) (w : I→Wgt (Knobs p.g n)) (ε : ℝ)
    (o : UnitType p n N) :=
  blackout v (propel v s m) (curtain v q U) w ε o

structure Paint (v : Template p I) (N : ℕ) where
  coeff : ℝ
  flies : ∀ i,AtomKey (p:=p) (v.t i) N → Prop
def Paint.cost {v : Template p I} (w : Paint v N) (x : Keys (p:=p) v.t N) :=
  w.coeff * prodW (fun i j => ind (w.flies i j)) x
def mural (v : Template p I) (w : J → Paint v N) := fun x => ∑ i:J,(w i).cost x
def design (v : Template p I) (w : Wgt (Keys (p:=p) v.t N)) (M : ℝ) (r : ℕ) :=
  ∃ x:Fin r→Paint v N,w=mural v x∧ ∀ i,|(x i).coeff|≤M

def patched (v : Template p I) (x : I)
    (a : AtomKey (p:=p) (v.t x) N → A)
    (B : A → Wgt (Keys (p:=p) (v.beyond x).t N)) :=
  fun (i:Keys (p:=p) v.t N) => B (a (i x)) ((v.chairK x N i).2)

noncomputable def paintJoin (v : Template p I) (x : I)
    (d : AtomKey (p:=p) (v.t x) N → Prop)
    (p' : Paint (v.beyond x) N) : Paint v N where
  coeff := p'.coeff
  flies i := if h:i=x then by subst x; exact d else p'.flies (⟨i,h⟩ : Aside x)

end Template
end HadwigerCounterexample

end

end OAI
end

section
-- module Solutions.OAIQ430_HC.HadwigerCounterexample_FixedPositionTests
attribute [-instance] _root_.OAI.HadwigerCounterexample.LeafMixture.instInhabited _root_.OAI.HadwigerCounterexample.PreparationParameters.instInhabitedSage _root_.OAI.HadwigerCounterexample.StatusAnalysis.deckFin _root_.OAI.HadwigerCounterexample.StatusAnalysis.quillFintype _root_.OAI.HadwigerCounterexample.StatusAnalysis.scripFintype _root_.OAI.HadwigerCounterexample.StatusAnalysis.typusFintype _root_.OAI.HadwigerCounterexample.arrFintype _root_.OAI.HadwigerCounterexample.drawFintype _root_.OAI.HadwigerCounterexample.fintypeStory _root_.OAI.HadwigerCounterexample.idxDec _root_.OAI.HadwigerCounterexample.instDecidableUsesPunch _root_.OAI.HadwigerCounterexample.momFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Fixed Position Tests -/

noncomputable section
namespace HadwigerCounterexample
open Finset Matrix Function LinearMap
open scoped BigOperators
variable {p : Shape} {n N : ℕ} {I : Type} [Fintype I] [DecidableEq I]

namespace Template
variable (v : Template p I)

def bolts (v : Template p I) {i j : I}
    (x : AtomKey (p:=p) (v.t i) N) (y : AtomKey (p:=p) (v.t j) N) :=
  ∀ e (h : inc e (v.t i)) (h' : inc e (v.t j)),
    dotProduct (x ⟨e,h⟩ true) (y ⟨e,h'⟩ false)=0 ∧
    dotProduct (y ⟨e,h'⟩ true) (x ⟨e,h⟩ false)=0
def boundTail (_ : Template p I) (j : I)
    (q : I→F) := fun i : Aside j => q i.val
def scriptTail (s : Script p I) (j : I) : Script p (Aside j) :=
  fun i k=> s i.val k.val

def huts (v : Template p I) (m : Mixer p n) (s : Script p I) (i k:I)
    (x y : Knobs p.g n) :=
  v.aim i=v.aim k → ∀ j:MOne p,
    s i k j=evmat (orderedM m j) (v.croon i x) (v.croon k y) ∧
    s k i j=evmat (orderedM m j) (v.croon k y) (v.croon i x)

def nib (v : Template p I) (o : UnitType p n N) (i : I) (z : Knobs p.g n) :=
  v.callOne i z (onSide o (v.aim i))

def lintel (v : Template p I) (j : I) (m : Mixer p n) (s : Script p I)
    (o : UnitType p n N) (x : Knobs p.g n) (i : Aside j) (z : Knobs p.g n) :=
  v.bolts (nib v o j x) (nib v o i.val z) ∧ v.huts m s j i.val x z

end Template
end HadwigerCounterexample

end

end OAI
end

section
-- module Solutions.OAIQ430_HC.HadwigerCounterexample_RecursiveComparisonErrors
attribute [-instance] _root_.OAI.HadwigerCounterexample.LeafMixture.instInhabited _root_.OAI.HadwigerCounterexample.PreparationParameters.instInhabitedSage _root_.OAI.HadwigerCounterexample.StatusAnalysis.deckFin _root_.OAI.HadwigerCounterexample.StatusAnalysis.quillFintype _root_.OAI.HadwigerCounterexample.StatusAnalysis.scripFintype _root_.OAI.HadwigerCounterexample.StatusAnalysis.typusFintype _root_.OAI.HadwigerCounterexample.arrFintype _root_.OAI.HadwigerCounterexample.drawFintype _root_.OAI.HadwigerCounterexample.fintypeStory _root_.OAI.HadwigerCounterexample.idxDec _root_.OAI.HadwigerCounterexample.instDecidableUsesPunch _root_.OAI.HadwigerCounterexample.momFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Recursive Comparison Errors -/

noncomputable section
namespace HadwigerCounterexample
open Finset Function Filter Matrix
open scoped BigOperators
variable {p : Shape} {I : Type} [Fintype I] [DecidableEq I] {n N : ℕ}
namespace Template
variable (v : Template p I)

def drained (m : Mixer p n) (C : ℝ) (w : Wgt (UnitType p n N)) :=
    let μ := raw m N; let H:=bp ((1/32:ℝ)*n)
    IsLaw w ∧ (∀ x,mapW w Prod.fst x ≤ H*μ x) ∧ (∀ x,mapW w Prod.snd x≤H*μ x) ∧
      ∀ x,w x ≤ bp (C*N)*pairW μ μ x

def engaged (v : Template p I) (q : I→F) (U : Wgt (Keys (p:=p) v.t N))
    (n : ℕ) (C e ε : ℝ) :=
  ∀ (m : Mixer p n),2*num (Full p n)<N →
    ∀ (w : Wgt (UnitType p n N)),drained m C w →
    ∀ (s : Script p I) (x : I→Wgt (Knobs p.g n)),(∀ i,IsLaw (x i)) →
      (∀ i,mapW (x i) (freePart p)=unif) → pr w (exceeds v q U s m x ε) ≤ e

end Template
end HadwigerCounterexample

end

end OAI
end

section
-- module Solutions.OAIQ430_HC.HadwigerCounterexample_AnalyticParameters
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Analytic Parameters -/

noncomputable section
namespace HadwigerCounterexample
open Filter Finset Matrix
open scoped BigOperators Topology
open StatusAnalysis StatusAnalysis.Station

def frameBills (g K : ℕ) :=
  2*Fintype.card (Comp g)*K*qorth K

structure AnalyticParameters (p : Shape) (M : ℕ) (b : PreparationParameters) (r : ℕ) : Prop where
  enter : b.entry p M
  thickness : 4≤ M
  profiles : 2*profileA p b.pins < r
  jump : 1≤p.J
  bigJ : r≤p.J
  gleaming : bp (-((p.J-r:ℕ):ℝ))*bp r < glintRate b.pins
  penRoom : (b.pins+1)*qorth b.pins≤p.j+1
  forbid : frameBills p.g b.pins+1000 ≤ b.B
  spare : 3*b.B < Fintype.card (Label p.b)
  secure : ∀ᶠ n : ℕ in atTop, Station.earnsScore p n (M*n) b.pins (2*b.ζ)

namespace PreparationParameters
variable {b : PreparationParameters} {p : Shape} {N M r : ℕ} {l : Filter ℕ} {m : cycleM p}
  {s : rhythms p M} {w : tale p M}

def conflicted {n : ℕ} (p : Shape) (m : Mixer p n) (N : ℕ) (w : Wgt (UnitType p n N)) :=
  pr (pairW w w) (clash p m N)<bp (-100*p.g*(N:ℝ))

structure veil (p : Shape) (M : ℕ) (b : PreparationParameters) (r : ℕ)
    (l : Filter ℕ) (m : cycleM p) (s : rhythms p M) (w : tale p M) : Prop where
  easel : AnalyticParameters p M b r
  timeL : l≤atTop
  durableS : b.durable l p M m w s
  moment : ∀ᶠ n in l,b.nascent p (M*n) (w n) (m n) ∧ unaryGood (m n) b.pins r ∧
    binaryGood (m n) ∧ conflicted p (m n) (M*n) (w n)

abbrev Stations (p : Shape) (M K : ℕ) (s : rhythms p M) :=
  ∀ n : ℕ, Station p n (M*n) K (s n)

structure Align (b : PreparationParameters) (r : ℕ) (p : Shape) (M n : ℕ) (m : Mixer p n)
    (u : Wgt (UnitType p n (M*n))) : Prop where
  rum : binaryGood m
  hymn : unaryGood m b.pins r
  age : 2*p.r ≤ n
  cols : 2*num (Full p n)<(M*n:ℕ)
  drain : Template.drained m b.spJoint u

end PreparationParameters
end HadwigerCounterexample

end

end OAI
end

section
-- module Solutions.OAIQ430_HC.HadwigerCounterexample_SurrogateStatusLaws
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Surrogate Status Laws -/

noncomputable section
namespace HadwigerCounterexample
open Filter Finset Matrix Function
open scoped BigOperators Topology

variable {A B C H : Type} [Fintype A] [Fintype B] [Fintype C] [Fintype H]
variable {p : Shape} {n N K M r : ℕ}
abbrev Silhouette (p : Shape) (N r : ℕ) :=
  ∀ t : Tag p.g,F→AtomKey (p:=p) t N→Fin r

namespace StatusAnalysis
structure Appearance (p : Shape) where
  l : Tag p.g
  s : Label p.b
  f : Flavor p.g
  q : F

instance instFintypeAppearance : Fintype (Appearance p) := by
  classical
  let A := Tag p.g × Label p.b × Flavor p.g × F
  let E : A ≃ Appearance p := {
    toFun x:=⟨x.1,x.2.1,x.2.2.1,x.2.2.2⟩
    invFun x:=(x.l,x.s,x.f,x.q)
    left_inv _:=rfl
    right_inv _:=rfl }
  exact Fintype.ofEquiv _ E

namespace Appearance
variable (x : Appearance p)
def apt := canDial p x.l x.f x.q
def trot := Template.solo p x.l x.s x.f
def wit (x : Appearance p) (n : ℕ) := scopedBit p n x.l x.f x.q
def face (o : Orient p n N) (w : Knobs p.g n) : AtomKey (p:=p) x.l N :=
  x.trot.desc w o
def profile {d : ℕ} (i : Nodes) (o : UnitType p n N) (m : Mixer p n) (v : Ax p n d)
    (z : Knobs p.g n) : Magazine p d :=
  specify p i v m o x.l x.s x.f z

variable (Y : Silhouette p N r)
def showTag (o : Orient p n N) := fun w=>Y x.l x.q (x.face o w)

def reference := mapW (lawOmega p N x.l x.q) (Y x.l x.q)
def empirical (o : Orient p n N) := mapW (x.wit n) (x.showTag Y o)

variable {d : ℕ}
def reflected (i : Nodes) (o : UnitType p n N) (m : Mixer p n) (v : Ax p n d) (a : Fin r) :=
  mapW (stained (x.wit n) (x.showTag Y (onSide o i)) a) (x.profile i o m v)

def close (o : Orient p n N) (ε : ℝ) :=
  varOne (x.reference Y) (x.empirical Y o) ≤ ε
end Appearance

end StatusAnalysis
end HadwigerCounterexample

end

end OAI
end

section
-- module Solutions.OAIQ430_HC.HadwigerCounterexample_CellPositivityScales
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Cell Positivity Scales -/

noncomputable section
namespace HadwigerCounterexample
open Filter Finset Matrix Function
open scoped BigOperators Topology
variable {p:Shape} {n N K M r : ℕ}
namespace StatusAnalysis
open Template
variable {b : PreparationParameters}

namespace Appearance
variable (x : Appearance p) {s0 : ℕ}

def foil (x : Appearance p) (Y : Silhouette p N r) (o : Orient p n N)
    (m : Mixer p n) (K : ℕ) (δ : ℝ) :=
    ∀ (z:Digest p.g) (i:Fin r), z.feasible x.l x.f → z.sumBit=x.q →
      δ ≤ x.reference Y i → Template.patrol x.trot m (scopedScan p n x.l x.f z)
        (fun y => Y x.l x.q y=i) K x.q o

end Appearance

def smoothSilk (p : Shape) (ε δ:ℝ) (Y:Silhouette p N r)
    (m:Mixer p n) (K:ℕ) (o:Orient p n N) :=
    ∀ x : Appearance p,(x.apt → x.close Y o ε) ∧ x.foil Y o m K δ

variable {s0 : ℕ}

def gauze (p : Shape) (ε δ:ℝ) (Y:Silhouette p N r)
    (m:Mixer p n) (K:ℕ) (o:UnitType p n N) :=
  ∀ i,smoothSilk p ε δ Y m K (onSide o i)

end StatusAnalysis
end HadwigerCounterexample

end

end OAI
end

section
-- module Solutions.OAIQ430_HC.HadwigerCounterexample_ConditionalSignaturePositivity
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Conditional Signature Positivity -/

noncomputable section
namespace HadwigerCounterexample
open Filter Finset Matrix Function
open scoped BigOperators Topology
variable {p:Shape} {n N K r d : ℕ}
namespace StatusAnalysis
open Template

namespace Appearance
variable (x : Appearance p) (Y : Silhouette p N r)

def nearly (p: Shape) (z: Digest p.g) (u: Par d) (x: Magazine p d) :=
  x.1=z∧ x.2.1=u

def fitsink (x : Appearance p) (w : Magazine p d) :=
   w.1.feasible x.l x.f ∧ w.1.sumBit=x.q ∧ w.1.diagO=w.2.1.1

end Appearance

end StatusAnalysis
end HadwigerCounterexample

end

end OAI
end

section
-- module Solutions.OAIQ430_HC.HadwigerCounterexample_ProductComparisonScales
attribute [-instance] _root_.OAI.HadwigerCounterexample.LeafMixture.instInhabited _root_.OAI.HadwigerCounterexample.PreparationParameters.instInhabitedSage _root_.OAI.HadwigerCounterexample.StatusAnalysis.deckFin _root_.OAI.HadwigerCounterexample.StatusAnalysis.instFintypeAppearance _root_.OAI.HadwigerCounterexample.StatusAnalysis.quillFintype _root_.OAI.HadwigerCounterexample.StatusAnalysis.scripFintype _root_.OAI.HadwigerCounterexample.StatusAnalysis.typusFintype _root_.OAI.HadwigerCounterexample.arrFintype _root_.OAI.HadwigerCounterexample.drawFintype _root_.OAI.HadwigerCounterexample.fintypeStory _root_.OAI.HadwigerCounterexample.idxDec _root_.OAI.HadwigerCounterexample.instDecidableUsesPunch _root_.OAI.HadwigerCounterexample.momFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Product Comparison Scales -/

noncomputable section
namespace HadwigerCounterexample
open Matrix Module Function Finset Filter
open scoped BigOperators
variable {p : Shape} {n N M : ℕ} {I : Type} [Fintype I] [DecidableEq I]
namespace Template
variable (v : Template p I)

def play (v : Template p I) (M : ℕ) (C b ε : ℝ) :=
  ∃ (r : ℕ) (c : ℝ),0 < c ∧ ∀ᶠ n : ℕ in atTop, let N:=M*n; ∀ (q : I→F)
    (U : Wgt (Keys (p:=p) v.t N)), (∀ i, |U i|≤ b) →
    ∃ T,design v T b r∧ shadowed v q (U-T) ε ∧ engaged v q (U-T) n C (bp (-c*n)) ε

end Template
end HadwigerCounterexample

end

end OAI
end

section
-- module Solutions.OAIQ430_HC.HadwigerCounterexample_SurrogateQueryScores
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Surrogate Query Scores -/

noncomputable section
namespace HadwigerCounterexample
open Filter Finset Matrix Function
open scoped BigOperators Topology
open Template
variable {p : Shape} {n N K M r : ℕ}
namespace StatusAnalysis
variable {q:Format} {d : Rates} {b:Bool}
namespace Quill

variable (w : Quill p q d b) (t : Tagging p (Messenger q)) (z : Messenger q → F)

def allure (i : Messenger q) : Appearance p := ⟨t i,w.sel i,w.flav i,z i⟩

def policies (n:ℕ) := fun i => (w.allure t z i).wit n
variable (o : UnitType p n N)
def stencil (s : Charts p n d) (m : Mixer p n) (i : Messenger q) (v : Knobs p.g n) :=
  let j:=parcel b i
  ind ((w.allure t z i).profile j o m (s j) v=w.amp i)

variable (m : Mixer p n)
def seraph (s : Charts p n d) (Y:Silhouette p N r) (i:Messenger q) : Wgt (AtomKey (p:=p) (t i) N) :=
  let j:=parcel b i
  fun h=> (w.allure t z i).reflected Y j o m (s j) (Y (t i) (z i) h) (w.amp i)
def mirror (s : Charts p n d) (Y:Silhouette p N r) := fun x:Keys (p:=p) t N=>
    (w.pen t).kappa*prodW (w.seraph t z o m s Y) x

def sheen (s : Charts p n d) (Y:Silhouette p N r) (W:Wgt (Keys (p:=p) t N)) :=
  avg (lawNu p N t z) (fun x=>w.mirror t z o m s Y x*W x)

end Quill
end StatusAnalysis
end HadwigerCounterexample

end

end OAI
end

section
-- module Solutions.OAIQ430_HC.HadwigerCounterexample_SurrogateProductBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Surrogate Product Bounds -/

noncomputable section
namespace HadwigerCounterexample
open Filter Finset Matrix Function
open scoped BigOperators Topology
variable {p:Shape} {n N K r:ℕ} {A:Type} [Fintype A]
open Template
namespace StatusAnalysis

def pigments {q : Template p A} (z : A→F) (Y : Silhouette p N r) (F : Paint q N) :=
   ∀ i:A, ∃ H : Fin r → Prop,∀ x,F.flies i x ↔ H (Y (q.t i) (z i) x)

namespace Quill
variable {q : Format} {d : Rates} {b : Bool} (w : Quill p q d b)
  (t : Tagging p (Messenger q)) (z : Messenger q→F)
  (o : UnitType p n N) (m:Mixer p n)

def suede (s:Charts p n d) (f : Paint (w.pen t) N) (i : Messenger q) (x : Knobs p.g n) :=
  w.stencil t z o s m i x*
    ind (f.flies i ((w.allure t z i).face (onSide o (parcel b i)) x))

def insidePaint (s : Charts p n d) (Y:Silhouette p N r) (f : Paint (w.pen t) N)
    (i : Messenger q) : Wgt (AtomKey (p:=p) (t i) N) :=
  fun x=> ind (f.flies i x) * seraph w t z o m s Y i x

end Quill
end StatusAnalysis
end HadwigerCounterexample

end

end OAI
end

section
-- module Solutions.OAIQ430_HC.HadwigerCounterexample_RectangleComparisons
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Rectangle Comparisons -/

noncomputable section
namespace HadwigerCounterexample
open Filter Finset Matrix Function
open scoped BigOperators Topology
variable {p:Shape} {n N r : ℕ}
open Template
namespace StatusAnalysis

namespace Quill
variable {q : Format} {d : Rates} {b : Bool}
    (w : Quill p q d b) (t : Tagging p (Messenger q)) (z : Messenger q→F)
    (m : Mixer p n)

structure mirrorSpan (s:ℕ) (ε : ℝ) (Y:Silhouette p N r) (o:UnitType p n N) : Prop where
  law : ∀ i,IsLaw (w.policies t z n i)
  frame : ∀ i,frameLaw m (onSide o i)
  close : ∀ i,(w.allure t z i).close Y (onSide o (parcel b i)) ε
  ready : ∀ u:Messenger q → Wgt (Knobs p.g n),(∀ i x, |u i x|≤1) →
    let v:=w.pen t; let x:=w.policies t z n
    |avg (prodW x) (fun y=>ind (v.performs w.script m o y)*prodW u y)-v.kappa*∏ i:Messenger q,
      avg (x i) (u i)|≤ ε
  reference : ∀ f:∀ i:Messenger q,Wgt (AtomKey (p:=p) (t i) N),(∀ i x,|f i x|≤1) →
     |avg (lawNu p N t z) (prodW f) - ∏ i:Messenger q,avg (lawOmega p N (t i) (z i)) (f i)| ≤ ε

structure witnessPaint (ε:ℝ) (W T : Wgt (Keys (p:=p) t N))
    (o : UnitType p n N) : Prop where
  shadow : ∀ f : (w.pen t).Localist N,(∀ i j, |f i j|≤1) →
    |avg (lawNu p N t z) (fun x=>(W x-T x)*prodW f x)|≤ε
  tested : ¬ exceeds (w.pen t) z (W-T) w.script m (w.policies t z n) ε o

end Quill
end StatusAnalysis
end HadwigerCounterexample

end

end OAI
end

section
-- module Solutions.OAIQ430_HC.HadwigerCounterexample_CommonPartitionRefinement
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Common Partition Refinement -/

noncomputable section
namespace HadwigerCounterexample
open Filter Finset Matrix Function
open scoped BigOperators Topology
variable {p:Shape} {n N K M r : ℕ}

def refines {r r':ℕ} (Y:Silhouette p N r) (Y':Silhouette p N r') :=
    ∀ l q, ∃ f:Fin r→Fin r',∀ x,Y' l q x=f (Y l q x)

variable {A B : Type} [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]

def bouquet (f : A→ℕ) := Fintype.card ((i:A)→ Fin (f i))
def bundleY (f:A→ℕ) (w: (i:A)→ Silhouette p N (f i)) :
    Silhouette p N (bouquet f) :=
  fun l q x=> Fintype.equivFin ((i:A)→ Fin (f i)) (fun i=> w i l q x)

def duoY {r s} (Y : Silhouette p N r) (X : Silhouette p N s) :
    Silhouette p N (r*s) :=
  open scoped Classical in fun i q x => finProdFinEquiv (Y i q x,X i q x)

namespace StatusAnalysis
variable (v : Template p A)

def paletteSize (A B : Type) [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B] := Fintype.card (B × A → Bool)

end StatusAnalysis
end HadwigerCounterexample

end

end OAI
end

section
-- module Solutions.OAIQ430_HC.HadwigerCounterexample_UniformSideComparisons
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Uniform Side Comparisons -/

noncomputable section
namespace HadwigerCounterexample
open Filter Finset Matrix Function
open scoped BigOperators Topology
open Template
variable {p:Shape} {M n N r s0 : ℕ}
namespace StatusAnalysis
namespace Quill
variable {q : Format} {d : Rates} {b:Bool}
    (w : Quill p q d b) (t : Tagging p (Messenger q)) (z : Messenger q→F)
variable {b' : PreparationParameters}

def matchesArea (Y: Silhouette p N r) (o:UnitType p n N) (δ:ℝ) :=
  ∀ i:Messenger q,(w.allure t z i).close Y (onSide o (parcel b i)) δ

def flunk (Y: Silhouette p N r) (W:Wgt (Keys (p:=p) t N)) (m: Mixer p n)
    (δ ε:ℝ) (o : UnitType p n N) :=
  PreparationParameters.frameSide p m o ∧ matchesArea w t z Y o δ ∧
    ∃ s : Charts p n d, ε< |w.prowl s t z m o W-w.sheen t z o m s Y W|

def markedTest (M : ℕ) (b' : PreparationParameters) (s0 n : ℕ) {r}
    (X : Silhouette p (M*n) r) (W : Wgt (Keys (p:=p) t (M*n))) (L u ε:ℝ) :=
    let N:=M*n; ∀ r:ℕ,∀ Y:Silhouette p N r,refines Y X →
    ∀ (m : Mixer p n) (U:Wgt (UnitType p n N)), b'.Align s0 p M n m U →
      pr U (w.flunk t z Y W m u ε) ≤ L

end Quill
end StatusAnalysis
end HadwigerCounterexample

end

end OAI
end

section
-- module Solutions.OAIQ430_HC.HadwigerCounterexample_SurrogateAggregation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Surrogate Aggregation -/

noncomputable section
namespace HadwigerCounterexample
open Finset Matrix Module LinearMap Filter Function
open scoped BigOperators Topology
open Template
namespace StatusAnalysis
variable {p : Shape} {n N K M r : ℕ}
variable {q:Format} {d e : Rates} {b:Bool}

namespace Quill
variable (w:Quill p q d b) (t: Tagging p (Messenger q))
  (z : Messenger q→F) (μ:Wgt (UnitType p n N)) (P:UnitType p n N→Prop)
  (m:Mixer p n) (s:Charts p n d) (Y: Silhouette p N r)
def showcase := fun x=> avg μ (fun i=> ind (P i)*w.mirror t z i m s Y x)

def displayMass := fun x=>lawNu p N t z x*w.showcase t z μ P m s Y x

end Quill

namespace Typus
variable (w: Typus p q d e) (o o' : UnitType p n N) (s:Charts p n d) (t:Charts p n e)
    (m : Mixer p n) (Y:Silhouette p N r)

/-- Per-position beta status overlap at fixed orientation pair. -/
def chimera (i:Messenger q) :=
    let l:=w.t i; let z:=w.z i
    let f:=w.qA.seraph w.t w.z o m s Y i; let g:=w.qB.seraph w.t w.z o' m t Y i
    dip (lawOmega p N l z) f g
def momus := (w.qA.pen w.t).kappa*(w.qB.pen w.t).kappa
def constellation := w.momus*(∏ i:Messenger q, w.chimera o o' s t m Y i)

end Typus
end StatusAnalysis
end HadwigerCounterexample

end

end OAI
end

section
-- module Solutions.OAIQ430_HC.HadwigerCounterexample_LeafSurrogateExperiments
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Leaf Surrogate Experiments -/

noncomputable section
namespace HadwigerCounterexample
open Matrix LinearMap Function Finset Filter
open scoped BigOperators Topology
namespace StatusAnalysis
variable {p : Shape} {n N K s M : ℕ}
  {w : LeafMixture p n N} {q : Format} {d e : Rates}

namespace Station
variable (t : Station p n N K w) (x : Typus p q d e)
  (m : Mixer p n) (μ : Wgt (UnitType p n N)) (k : Fin (2^deckMax p K))
variable (Y : Silhouette p N s) (i j : w.T)

def stageLeft :=
  x.qA.showcase x.t x.z (partW μ i.val) (t.frontPage x m i j k) m (t.cAxes i d) Y
def stageRight :=
  x.qB.showcase x.t x.z (partW μ j.val) (t.backPage x m i j k) m (t.cAxes j e) Y
def stagePlane :=
  dip (lawNu p N x.t x.z) (t.stageLeft x m μ k Y i j) (t.stageRight x m μ k Y i j)

def twilight (o : UnitType p n N × UnitType p n N) :=
    ind (t.frontPage x m i j k o.1 ∧ t.backPage x m i j k o.2)*
      x.constellation o.1 o.2 (t.cAxes i d) (t.cAxes j e) m Y

def eclipse :=
  avg (pairW (partW μ i.val) (partW μ j.val)) (t.twilight x m k Y i j)

def stratum :=
  let v:=portionW μ w.T
  avg (pairW v v) (fun i=>t.eclipse x m μ k Y i.1 i.2)

end Station

end StatusAnalysis
end HadwigerCounterexample

end

end OAI
end

section
-- module Solutions.OAIQ430_HC.HadwigerCounterexample_UniformLeafComparisons
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Uniform Leaf Comparisons -/

noncomputable section
namespace HadwigerCounterexample
open Filter Function Matrix Finset
open scoped BigOperators Topology
namespace StatusAnalysis
variable {p:Shape} {M n N s0 K r:ℕ} {q:Format} {d e:Rates} {b:Bool} {b':PreparationParameters}

namespace Quill
variable (w:Quill p q d b)
  (t:Tagging p (Messenger q)) (z: Messenger q→F)
def accounting (m:Mixer p n) (s:Charts p n d)
    (μ:Wgt (UnitType p n N)) (r : ℕ) (δ R ε η : ℝ) :=
    let Q:= w.custom μ s t z m
    let ν:= lawNu p N t z
    (∀ i,Q i→SubLaw i ∧ lsupp i ν) ∧ roster Q r ε∧smallSet Q ν δ η∧ rosterTail Q ν R η

structure penny (m:Mixer p n) (s:Charts p n d) (μ:Wgt (UnitType p n N))
    (R η ε:ℝ) (r:ℕ) : Prop where
  sales i : w.custom μ s t z m i → SubLaw i∧lsupp i (lawNu p N t z)
  roll : roster (w.custom μ s t z m) r ε
  tailS : rosterTail (w.custom μ s t z m) (lawNu p N t z) R η

end Quill

end StatusAnalysis
end HadwigerCounterexample

end

end OAI
end

section
-- module Solutions.OAIQ430_HC.HadwigerCounterexample_KeyProjectionBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Key Projection Bounds -/

noncomputable section
namespace HadwigerCounterexample
open Filter Finset Matrix LinearMap
open scoped BigOperators Topology
variable {p:Shape} {n N M K r s0 : ℕ}
namespace StatusAnalysis
open Station
namespace Station
variable {q:Format} {d e:Rates} {w : LeafMixture p n N} (t : Station p n N K w)
    (x:Typus p q d e) (m:Mixer p n) (μ:Wgt (UnitType p n N)) (k:Fin (2^deckMax p K))
    (Y:Silhouette p N r)

variable {B : Type} [Fintype B]
def taxLeft (P : Keys (p:=p) x.t N →B) (i j : w.T) :=
    varOne (mapW (fun a=> lawNu p N x.t x.z a * stageLeft t x m μ k Y i j a) P)
      (mapW (t.leftSales x m μ i j k) P)
def taxRight (P : Keys (p:=p) x.t N →B) (i j : w.T) :=
    varOne (mapW (fun a=> lawNu p N x.t x.z a * stageRight t x m μ k Y i j a) P)
      (mapW (t.rightSales x m μ i j k) P)
def due (P : Keys (p:=p) x.t N→B) :=
    avg (pairW (portionW μ w.T) (portionW μ w.T)) (fun i=>
       taxLeft t x m μ k Y P i.1 i.2+taxRight t x m μ k Y P i.1 i.2)
def dueEnough {l:ℕ} (ε η:ℝ) (P : Keys (p:=p) x.t N→ Fin l) :=
    ∀ r:ℕ,∀ Y:Silhouette p N r, due t x m μ k Y P ≤ η → stratum t x m μ k Y ≤ ε
end Station

open PreparationParameters
end StatusAnalysis
end HadwigerCounterexample

end

end OAI
end

section
-- module Solutions.OAIQ430_HC.HadwigerCounterexample_SimultaneousProjection
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Simultaneous Projection -/

noncomputable section
namespace HadwigerCounterexample
open Filter Finset Matrix
open scoped BigOperators Topology
namespace StatusAnalysis
open Station PreparationParameters

variable {p : Shape} {M s0 n N K : ℕ} {q:Format} {d e:Rates}
    {l:Filter ℕ} {b:PreparationParameters} {m:cycleM p} {w:tale p M} {s:rhythms p M}

def sparks (v : Stations p M b.pins s) (i:Scrip p b.pins) (m:cycleM p) (w:tale p M)
    {r} (n:ℕ) (Y: Silhouette p (M*n) r) :=
  Station.stratum (v n) i.2.2 (m n) (w n) i.2.1 Y

def bullseye (v: Stations p M K s) (m:cycleM p) (w:tale p M) (x:Typus p q d e)
    (k : Fin (2^deckMax p K)) (ε : ℝ) {r : ℕ} (n : ℕ) (Y : Silhouette p (M*n) r)
    (τ u:ℝ) :=
  ∀ (r':ℕ) (Y':Silhouette p (M*n) r'),refines Y' Y →
  ∀ τ' δ:ℝ,τ'≤τ →
    pr ((s n).sap (w n)) (fun i=>¬ gauze p τ' δ Y' (m n) K i) ≤u →
    Station.stratum (v n) x (m n) (w n) k Y'≤ ε

end StatusAnalysis
end HadwigerCounterexample

end

end OAI
end

section
-- module Solutions.OAIQ430_HC.HadwigerCounterexample_ConditionalLargeSetHits
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Conditional Large Set Hits -/

noncomputable section
namespace HadwigerCounterexample
open Filter Finset Matrix LinearMap Function
open scoped BigOperators Topology
open Template
variable {p:Shape} {M n N K r s0:ℕ}
namespace StatusAnalysis
namespace Quill
variable {q:Format} {d:Rates} {b:Bool} (w:Quill p q d b) (t : Tagging p (Messenger q))
    (z:Messenger q→F) (m:Mixer p n)

def prelim (K:ℕ) (s:Charts p n d) (i:Messenger q) :=
   d (parcel b i)≤ K^2 ∧ Injective (s (parcel b i)) ∧
   ∀ x,totalRank (s (parcel b i) x)≤ K

def sameInk (i:Messenger q) (v: Magazine p (d (parcel b i))) :=
  Appearance.nearly p (w.amp i).1 (w.amp i).2.1 v

structure steady (K:ℕ) (s:Charts p n d) (o: UnitType p n N) : Prop where
  frame : PreparationParameters.frameSide p m o
  steadyAxes (i:Messenger q) : prelim (b:=b) K s i
  enough i : (w.amp i).1.diagO=(w.amp i).2.1.1
  sufficesP i :
    let j:= parcel b i; let x:=w.allure t z i
    carried (w.policies t z n i) (fun y=> w.sameInk i (x.profile j o m (s j) y) →
      x.profile j o m (s j) y=w.amp i)

end Quill
end StatusAnalysis
end HadwigerCounterexample

end

end OAI
end

section
-- module Solutions.OAIQ430_HC.HadwigerCounterexample_LargeSetHits
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Large Set Hits -/

noncomputable section
namespace HadwigerCounterexample
open Filter Finset Matrix Function
open scoped BigOperators Topology
open Template
variable {p:Shape} {M n N K r s0:ℕ}
namespace StatusAnalysis
namespace Quill
variable {q:Format} {d:Rates} {b:Bool} (w:Quill p q d b)
    (t:Tagging p (Messenger q)) (z:Messenger q→F)
def dilate (K:ℕ) := (w.pen t).kappa*((basebeta p K)/2)^Fintype.card (Messenger q)

variable {b':PreparationParameters}
def sober (K:ℕ) (H:Keys (p:=p) t N→Prop) (m:Mixer p n) (α:ℝ) (o:UnitType p n N) :=
  ∀ s:Charts p n d,w.steady t z m K s o → α≤w.prowl s t z m o (fun x=>ind (H x))

end Quill
end StatusAnalysis
end HadwigerCounterexample

end

end OAI
end

section
-- module Solutions.OAIQ430_HC.HadwigerCounterexample_SuperlevelBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Superlevel Bounds -/

noncomputable section
namespace HadwigerCounterexample
open Filter Finset Matrix
open scoped BigOperators Topology
variable {A : Type} [Fintype A]

def cliff (u f : Wgt A) (t:ℝ) (x : A) := 2*t*u x ≤ f x

end HadwigerCounterexample

end

end OAI
end

section
-- module Solutions.OAIQ430_HC.HadwigerCounterexample_RareLeafEvents
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Rare Leaf Events -/

noncomputable section
namespace HadwigerCounterexample
open Filter Finset Matrix Function
open scoped BigOperators Topology
open Template
variable {p:Shape} {M n N K s0:ℕ}
namespace StatusAnalysis
variable {q:Format} {d e:Rates} {b:Bool}

namespace Quill
variable (w:Quill p q d b) (m:Mixer p n) (t : Tagging p (Messenger q))
    (z : Messenger q→F)
def qualified (s:Charts p n d) (K :ℕ) (μ:Wgt (UnitType p n N)) (P : UnitType p n N→Prop) (a:ℝ) :=
    2*a ≤ pr μ P ∧ ∀ i,P i →μ i ≠0→ w.steady t z m K s i

end Quill

namespace Station
variable {w:LeafMixture p n N} (t:Station p n N K w) (x:Typus p q d e)
    (m:Mixer p n) (k: Fin (2^deckMax p K)) (μ:Wgt (UnitType p n N))

def charter (a:ℝ) (i:w.T×w.T) :=
    x.permission ∧
      x.qA.qualified m x.t x.z (t.cAxes i.1 d) K (partW μ i.1.val) (t.frontPage x m i.1 i.2 k) a ∧
      x.qB.qualified m x.t x.z (t.cAxes i.2 e) K (partW μ i.2.val) (t.backPage x m i.1 i.2 k) a

def berth (a:ℝ) :=
    pr (pairW (portionW μ w.T) (portionW μ w.T)) (charter t x m k μ a)

end Station

end StatusAnalysis
end HadwigerCounterexample

end

end OAI
end

section
-- module Solutions.OAIQ430_HC.HadwigerCounterexample_CompatibleOptionRealization
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Compatible Option Realization -/

noncomputable section
namespace HadwigerCounterexample
open Finset Matrix Function Module LinearMap
open scoped BigOperators
variable {p:Shape} {n N M K s0:ℕ}
namespace StatusAnalysis

variable {q:Format} {d e: Rates} {b:Bool}
abbrev Stalls (p:Shape) := Bool→Finset (Label p.b)

def booths (p:Shape) (K:ℕ) (s: Plan p n) (H:Stalls p) :=
   (∀ i,(H i).card≤frameBills p.g K) ∧
   ∀ i j, protectedBy p (sPin s j i) (qorth K) (H i)

structure Fabric (p:Shape) (q:Format) (d:Rates) (b:Bool) where
  sel : Messenger q → Label p.b
  flav : Messenger q → Flavor p.g
  amp : Amounts p q d b

namespace Fabric
variable (w:Fabric p q d b) (t:Tagging p (Messenger q))
def hang (s:Script p (Messenger q)) : Quill p q d b :=
  ⟨w.sel,w.flav,w.amp,s⟩
def up (w:Fabric p q d b) (t:Tagging p (Messenger q)) (z: Messenger q→F) :=
    (w.hang 0).moral t z

end Fabric

variable {i j:Bool} {L:ℕ}

def berthTicket (a b:Pin p n N) (T: Cross p n)
    (x:UnitType p n N × UnitType p n N) :=
    tableInj a.sp b.sp T ∧ tableInj b.sp a.sp (reciprocal p T)
      ∧ fitsTable a.sp b.sp T (actual p x.1 x.2)

def cardTone (m:BMark p n N) (x:UnitType p n N) (T:Cross p n) (j:Bool) : F :=
   ∑ i:Bool,contract p T i j (m x i)

end StatusAnalysis
end HadwigerCounterexample

end

end OAI
end

section
-- module Solutions.OAIQ430_HC.HadwigerCounterexample_RareTestEvents
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Rare Test Events -/

noncomputable section
namespace HadwigerCounterexample
open Filter Finset Matrix LinearMap Module Function
open scoped BigOperators Topology
variable {p:Shape} {n N K M : ℕ}
namespace StatusAnalysis

def singles : Format:=fun _=>1
def volume1 : Volumes:=fun _=>1

variable {d:Rates}
def coordSpec (m:BMark p n N) (o:UnitType p n N) (s:Charts p n d)
    (w:∀ i:Nodes,Cell (d i)) := ∀ i,s i (w i)= m o i

def beacon (p:Shape) (s:Charts p n d) (w:∀ i:Nodes,Cell (d i)) (b:Bool)
    (T: Cross p n) (z : Digest p.g) : Amounts p singles d b :=
   fun k =>
     let i:=parcel b k
     let j:= parcel (!b) k
     let x:=targetMark p s T i j
     (z,(z.diagO,x), z.diagO+dotProduct x (w i))

end StatusAnalysis
end HadwigerCounterexample

end

end OAI
end

section
-- module Solutions.OAIQ430_HC.HadwigerCounterexample_CompatibleTableEvents
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Compatible Table Events -/

noncomputable section
namespace HadwigerCounterexample
open Filter Finset Matrix LinearMap Function
open scoped BigOperators Topology
open Template
namespace StatusAnalysis
open PreparationParameters PredictionClass

variable {p:Shape} {n M K s0 N :ℕ} {w:LeafMixture p n N} {q:PreparationParameters}

structure Settled (t: LeafMixture p n N) (m:Mixer p n) (q:PreparationParameters)
    (U : Wgt (UnitType p n N)) (z:BMark p n N) (k:F) : Prop where
    readyC :
    IsLaw U ∧ t.strength U (usual p m N) q.leafNew (2*q.ζ) q.pins ∧
    t.within (fun o=>frameSide p m o ∧ exactInk p m z o ∧
       (∀ i,z o i∈effective (t.rooting o) i) ∧ glint p (z o)=k)
    hard : q.hardened p N t z

def shimmer (z:BMark p n N) (r:F) (x:UnitType p n N× UnitType p n N) :=
   quench p (delta z) x=repeatQ r

end StatusAnalysis
end HadwigerCounterexample

end

end OAI
end

section
-- module Solutions.OAIQ430_HC.HadwigerCounterexample_IncompatibleMassBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Incompatible Mass Bounds -/

noncomputable section
namespace HadwigerCounterexample
open Filter Finset Matrix LinearMap Function
open scoped BigOperators Topology
open Template
namespace StatusAnalysis
open PreparationParameters Station PredictionClass
variable {p : Shape} {n N K M s0 : ℕ} {q : PreparationParameters}

def feeSeal (p:Shape) (K:ℕ) := (1/4 : ℝ)/num (Fin (2^deckMax p K))
end StatusAnalysis
end HadwigerCounterexample

end

end OAI
end

section
-- module Solutions.OAIQ430_HC.HadwigerCounterexample_FiniteDualSystems
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Finite Dual Systems -/

noncomputable section
namespace HadwigerCounterexample
open Filter Matrix Finset Function LinearMap Module
open scoped BigOperators Topology
open Template
variable {p : Shape} {N n r K : ℕ}
namespace StatusAnalysis

/-- envelope information to certify a generator, shared l and q. -/
structure Zodiac (p : Shape) where
  l : Tag p.g
  q : F
  s : Bool → Label p.b
  f : Bool→Flavor p.g

namespace Zodiac
def aspect (w : Zodiac p) (b : Bool) : Appearance p :=
  ⟨w.l,w.s b,w.f b,w.q⟩
def common (w : Zodiac p) := ∀ b,(w.aspect b).apt
end Zodiac
instance zodiac_dec (p:Shape): DecidableEq (Zodiac p) := Classical.typeDecidableEq _

abbrev Terrain (p:Shape) (r:ℕ):= Tag p.g → F → Wgt (Fin r)
abbrev Gazette (p:Shape) (r:ℕ) (d : Rates) :=
   (i:Nodes)→Appearance p → Fin r→ Wgt (Magazine p (d i))

variable {d e : Rates}
namespace DualAnalysis

def wisp (p : Shape) (Y : Silhouette p N r) : Terrain p r :=
 fun i z => mapW (lawOmega p N i z) (Y i z)
def wake (p : Shape) (Y : Silhouette p N r) (m:Mixer p n) (o:UnitType p n N)
    (s : Charts p n d) : Gazette p r d :=
 fun i x a=> x.reflected Y i o m (s i) a

def origami (p:Shape) (r:ℕ) (u:Terrain p r) (δ:ℝ) :=
   (∀ i q,IsLaw (u i q)) ∧ ∀ i q,1/2 ≤ pr (u i q) (fun x=>δ ≤ u i q x)
structure reports (p:Shape) (r:ℕ) (u:Terrain p r) (s:Gazette p r d)
    (β δ:ℝ) : Prop where
  law : ∀ i (x:Appearance p),x.apt → ∀ k:Fin r,IsLaw (s i x k)
  supp : ∀ i (x:Appearance p),x.apt →∀ k,carried (s i x k) x.fitsink
  generous : ∀ i (x:Appearance p), x.f=Flavor.full → x.apt →
     ∀ k:Fin r,δ ≤ u x.l x.q k → ∀ v: Par (d i),
       β ≤ pr (s i x k) (fun w=>w.2.1=v)

def playbook (p : Shape) (K : ℕ) := num (Magazine p (K^2) × Magazine p (K^2))

abbrev Scriptum (p:Shape) (d e: Rates) (i : Grid) :=
   Zodiac p × Magazine p (d i.1) × Magazine p (e i.2)
abbrev Touch (p:Shape) (d e : Rates) (i : Grid) := Magazine p (d i.1) × Magazine p (e i.2)
variable (u:Terrain p r) (s:Gazette p r d) (t:Gazette p r e)
  (η:ℝ)
def couplePage (x:Zodiac p) (i:Grid) :=
    fun j:Fin r=> pairW (s i.1 (x.aspect true) j) (t i.2 (x.aspect false) j)
def circlet (x:Zodiac p) (i:Grid) : Wgt (Touch p d e i) :=
    mixW (u x.l x.q) (couplePage s t x i)
def eligible (x:Zodiac p) (i:Grid) (a : Touch p d e i) :=
    x.common ∧ (x.aspect true).fitsink a.1 ∧ (x.aspect false).fitsink a.2 ∧
      η ≤ circlet u s t x i a
def stellar (A B : Stalls p) : Congress (Scriptum p d e) d e (Label p.b) :=
    fun i=> {
      valid x:= x.1.s true∉ A i.1 ∧ x.1.s false∉ B i.2 ∧ eligible u s t η x.1 i x.2
      writes x:= (x.1.q,x.2.1.2,x.2.2.2)
      addr x:= x.1.s
    }

end DualAnalysis
end StatusAnalysis
end HadwigerCounterexample

end

end OAI
end

section
-- module Solutions.OAIQ430_HC.HadwigerCounterexample_RelationMismatchBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Relation Mismatch Bounds -/

noncomputable section
namespace HadwigerCounterexample
open Filter Matrix Finset Function Submodule LinearMap
open scoped BigOperators Topology
open Template
variable {p:Shape} {N n r K : ℕ}
namespace StatusAnalysis
namespace DualAnalysis
open Club Guild
variable {d e : Rates}
    {u:Terrain p r} {s:Gazette p r d} {t:Gazette p r e}
    {β η δ:ℝ}

def seeking (p : Shape) (A : Stalls p) :=
  ∀ i, (A i).card+902 < Fintype.card (Label p.b)

structure RhymeSet (d : ℕ) where
    bit : F
    coal : Cell d
    headBit : F
    gamma : F

def RhymeSet.read {k : ℕ} (s:RhymeSet k) (q:F) (x: Whole k) :=
    s.bit*x.2+ dotProduct s.coal x.1.2+ (s.bit+s.headBit)*x.1.1+s.gamma*q

def RhymeSet.soot {k : ℕ} (s:RhymeSet k) {p:Shape} (x:Appearance p) (y:Magazine p k) :=
    s.read x.q y.2

def leftChime (q:DualCoefficients d e) (i:Grid) : RhymeSet (d i.1) :=
   ⟨q.left i.2,q.north i,q.hed i,0⟩
def rightChime (q:DualCoefficients d e) (i:Grid) : RhymeSet (e i.2) :=
   ⟨q.right i.1,q.south i,q.hed i,q.gam i⟩

def charge (u:Terrain p r) (x: Zodiac p) (X:Gazette p r d) (Y:Gazette p r e)
    (i:Grid) (a:RhymeSet (d i.1)) (b:RhymeSet (e i.2)) :=
    pr (circlet u X Y x i) (fun y=>a.soot (x.aspect true) y.1≠ b.soot (x.aspect false) y.2)

def outstraps (a:Stalls p) (s:Straps (Label p.b)) (b:Bool):Stalls p:=
   fun i=>a i∪s b

end DualAnalysis
end StatusAnalysis
end HadwigerCounterexample

end

end OAI
end

section
-- module Solutions.OAIQ430_HC.HadwigerCounterexample_FiniteOptionLabels
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Finite Option Labels -/

noncomputable section
namespace HadwigerCounterexample
open Filter Matrix Finset Function Submodule LinearMap
open scoped BigOperators Topology
open Template
variable {p:Shape} {N n r K : ℕ}
namespace StatusAnalysis
namespace DualAnalysis
open Club Guild
variable {d e: Rates}
    {u:Terrain p r} {s:Gazette p r d} {t:Gazette p r e}
    {β η δ:ℝ}

abbrev Engagement (p:Shape) (q : Format) (d e:Rates) :=
  (i : Messenger q) → Scriptum p d e i.1

variable (p:Shape)
namespace Engagement

def tags {q:Format} (f:Engagement p q d e) :=
   fun i:Messenger q=> (f i).1.l
def bits {q:Format} (f:Engagement p q d e) :=
   fun i:Messenger q=> (f i).1.q
def genre0 {q:Format} (f:Engagement p q d e): Fabric p q d true :=
  {sel i:= (f i).1.s true
   flav i:= (f i).1.f true
   amp i:= (f i).2.1}
def genre1 {q:Format} (f:Engagement p q d e): Fabric p q e false :=
  {sel i:= (f i).1.s false
   flav i:= (f i).1.f false
   amp i:= (f i).2.2}
def binding {q:Format} (f:Engagement p q d e) (a b:Script p (Messenger q)) :
    Typus p q d e :=
  ⟨tags p f,bits p f,(genre0 p f).hang a,(genre1 p f).hang b⟩

end Engagement

end DualAnalysis
end StatusAnalysis
end HadwigerCounterexample

end

end OAI
end

section
-- module Solutions.OAIQ430_HC.HadwigerCounterexample_BinaryStatusComparison
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Binary Status Comparison -/

noncomputable section
namespace HadwigerCounterexample
open Finset Matrix Filter Function Submodule Module LinearMap
open scoped BigOperators
variable {A B J H : Type} [Fintype A] [Fintype B] [Fintype J]

def majority (w : Wgt A) (f : A→F) :=
    if 1/2≤ pr w (fun i=>f i=0) then (0:F) else 1

namespace StatusAnalysis
namespace DualAnalysis
variable {p:Shape} {d e: Rates} {r K:ℕ}
abbrev Pulsar (p:Shape) (r:ℕ):= Tag p.g → F → Fin r→F
variable (u:Terrain p r) (s:Gazette p r d) (t:Gazette p r e)

def shot (i:Nodes) (x:Appearance p) (a:RhymeSet (d i)) (f:Pulsar p r) :=
  avg (u x.l x.q) (fun j=>pr (s i x j) (fun v=> a.soot x v ≠f x.l x.q j))
def praise (u:Terrain p r) (s:Gazette p r d) (i:Nodes)
    (A:Finset (Label p.b)) (a:RhymeSet (d i)) (f:Pulsar p r) (ε:ℝ) :=
   ∀ x:Appearance p,x.s∉A →x.apt → shot u s i x a f≤ε
def counsel (i:Grid) (A B:Finset (Label p.b))
    (a : RhymeSet (d i.1)) (b : RhymeSet (e i.2)) (ε :ℝ) :=
   ∀ x:Zodiac p,x.common → x.s true∉A →x.s false∉ B →charge u x s t i a b≤ε

def amazes (p:Shape) (z:Label p.b) (l: Tag p.g) (q:F):Appearance p:=⟨l,z,Flavor.full,q⟩
def amends (p:Shape) (x y:Appearance p): Zodiac p :=
  {l:=x.l
   q:=x.q
   s i:=if i then x.s else y.s
   f i:=if i then x.f else y.f}
end DualAnalysis
end StatusAnalysis
end HadwigerCounterexample

end

end OAI
end

section
-- module Solutions.OAIQ430_HC.HadwigerCounterexample_FinitePredictions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Finite Predictions -/

noncomputable section
namespace HadwigerCounterexample
open Matrix Filter Finset LinearMap Module Function
open scoped BigOperators Topology
open Template
namespace StatusAnalysis
namespace DualAnalysis
variable {p:Shape} {r n N K:ℕ} {d:Rates}

def fromPulse (Y: Silhouette p N r) (f:Pulsar p r) : Augur p N :=
  fun l q x=> f l q (Y l q x)

def yokeSet {n:ℕ} (w:Cell n) (α:F) : RhymeSet n :=
    ⟨1,w,1+α,0⟩
def compass (i : Bool) (o:UnitType p n N) (s:Charts p n d)
    (m:Mixer p n) (w:Cell (d i)) (α:F) :=
  yoke p m o i (s i w) α

end DualAnalysis
end StatusAnalysis
end HadwigerCounterexample

end

end OAI
end

section
-- module Solutions.OAIQ430_HC.HadwigerCounterexample_PredictedDualCoefficients
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Predicted Dual Coefficients -/

noncomputable section
namespace HadwigerCounterexample
open Filter Finset Matrix Module LinearMap
open scoped BigOperators Topology
variable {p:Shape} {r n:ℕ}
namespace StatusAnalysis
namespace DualAnalysis

variable {d e:Rates} {u:Terrain p r} {s:Gazette p r d} {t:Gazette p r e}

open PredictionClass

def scaled (a:F) (w:RhymeSet n):RhymeSet n :=
  ⟨a*w.bit,a • w.coal,a*w.headBit,a*w.gamma⟩
def Pulsar.mult (g:Pulsar p r)(a:F) : Pulsar p r := fun i j k=>a*g i j k

abbrev styles (d:Rates) := ∀ i:Nodes, Cell (d i)

structure PredictionData (p:Shape) (d e:Rates) (r:ℕ) where
  α : Party
  g : Nodes→ Pulsar p r
  X : styles d
  Y : styles e

def PredictionData.colored (v:PredictionData p d e r) (u:Terrain p r) (s:Gazette p r d) (t:Gazette p r e)
    (A B:Stalls p) (ε:ℝ) :=
    (∀ i,praise u s i (A i) (yokeSet (v.X i) (v.α i)) (v.g i) ε) ∧
    (∀ i,praise u t i (B i) (yokeSet (v.Y i) (v.α i)) (v.g i) ε)

def ChorusCost (w:PredictionData p d e r) (v:DualCoefficients d e) (i:Grid) (u:Terrain p r)
    (l:Tag p.g) (q:F) :=
  pr (u l q) (fun k=>v.left i.2*w.g i.1 l q k+v.right i.1*w.g i.2 l q k≠v.gam i*q)

end DualAnalysis
end StatusAnalysis
end HadwigerCounterexample

end

end OAI
end

section
-- module Solutions.OAIQ430_HC.HadwigerCounterexample_PredictedDualEvaluation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Predicted Dual Evaluation -/

noncomputable section
namespace HadwigerCounterexample
open Matrix Finset Function LinearMap Module
open scoped BigOperators
namespace StatusAnalysis
namespace DualAnalysis
open PredictionClass
variable {p:Shape} {n N r :ℕ} {A B:Rates}

def chorusClass (p:Shape) (v:PredictionData p A B r) (u:Terrain p r) (c:PredictionClass) (τ :ℝ) :=
  c.lit v.α ∧
    (c=dusk→∀ i l q k,v.g i l q k=0) ∧
    ∀ (z:DualCoefficients A B), c≠dusk →
      (∀ i,z.hed i=z.left i.2 * firstBit v.α i.1 ∧ z.hed i=z.right i.1*firstBit v.α i.2) →
      (∀ i l q, ChorusCost v z i u l q≤τ) →
      ∀ i j,c.echoes i j (z.left j) (z.right i)

end DualAnalysis
end StatusAnalysis
end HadwigerCounterexample

end

end OAI
end

section
-- module Solutions.OAIQ430_HC.HadwigerCounterexample_PredictionExtraction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Prediction Extraction -/

noncomputable section
namespace HadwigerCounterexample
open Filter Matrix Function Submodule LinearMap Module Finset
open scoped BigOperators
namespace StatusAnalysis
namespace DualAnalysis
variable {p:Shape} {r n:ℕ} {A B: Rates}
    {u:Terrain p r} {s:Gazette p r A} {t:Gazette p r B}
open PredictionClass Club Guild

structure countStory (p:Shape) (K:ℕ) (η δ ε β :ℝ) (u:Terrain p r) : Prop where
  h : origami p r u δ
  hb : 0≤β
  he : 0≤ ε
  ht : 0≤η
  bill : playbook p K * η ≤ ε
  high : 6*ε < 1/2*β

structure Stirrings (p:Shape) (r:ℕ) (u:Terrain p r) (s:Gazette p r A) (t:Gazette p r B)
    (p0:DualCoefficients A B) (S T:Stalls p) (ε:ℝ) : Prop where

  recollect (i:Grid): ∃ f:Pulsar p r,praise u s i.1 (S i.1) (leftChime p0 i) f (3*ε) ∧
      praise u t i.2 (T i.2) (rightChime p0 i) f (3*ε)

abbrev Dict (p : Shape) (r:ℕ) := Nodes → F → F→ Pulsar p r
def anthology (p : Shape) (r : ℕ) (u:Terrain p r) (s:Gazette p r A)
    (d:Dict p r) (L:ℕ) (ε:ℝ) :=
    ∀ (B: Stalls p) (i:Nodes), (B i).card ≤ L →
      ∀ (f:Pulsar p r) (a:RhymeSet (A i)), praise u s i (B i) a f ε →
        ∀ l q, pr (u l q) (fun x=> f l q x ≠ d i a.bit a.gamma l q x) ≤ 2*ε

def Pulsar.shift (g:Pulsar p r) (a:F): Pulsar p r := fun l q x => g l q x+a*q

abbrev Snip := F×F×F
abbrev Memo := Nodes × (Nodes→Snip)

def Memo.words (d:Dict p r) (i:Memo) : Nodes→ Pulsar p r :=
   fun j=> let h:=i.2 j; (d i.1 h.1 h.2.1).shift h.2.2

def announced (u:Terrain p r) (s:Gazette p r A) (d:Dict p r) (L:ℕ) (ε:ℝ) :=
   ∃ i:Memo,∃ (v:styles A) (a:Party) (S:Stalls p),∀ j,
       (S j).card≤L ∧ praise u s j (S j) (yokeSet (v j) (a j)) (Memo.words d i j) ε

end DualAnalysis
end StatusAnalysis
end HadwigerCounterexample

end

end OAI
end

section
-- module Solutions.OAIQ430_HC.HadwigerCounterexample_PositiveTestMass
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Positive Test Mass -/

noncomputable section
namespace HadwigerCounterexample
open Matrix Function Filter Finset LinearMap Module
open scoped BigOperators Topology
open Template
variable {p:Shape} {n N K M s0 r :ℕ}
namespace StatusAnalysis
open PreparationParameters Station PredictionClass Club Guild DualAnalysis
variable {q:PreparationParameters} {w:LeafMixture p n N}

abbrev Aspect (p:Shape) (n N :ℕ) (w:LeafMixture p n N) := w.T × UnitType p n N
abbrev ViewPair (p:Shape) (n N :ℕ) (w:LeafMixture p n N) := Aspect p n N w × Aspect p n N w

def troupe (w:LeafMixture p n N) (U:Wgt (UnitType p n N)) :=
    semi (portionW U w.T) (fun i=>partW U i.val)
def cirque (w:LeafMixture p n N) (U:Wgt (UnitType p n N)) :=
   pairW (troupe w U) (troupe w U)
def eligiblePair (v:Station p n N K w) (m:Mixer p n) (i j:Aspect p n N w)
    (Y:Silhouette p N r) (a:ℝ) :=
   ∃ k:Scrip p K, k.2.2.permission ∧ a ≤ v.twilight k.2.2 m k.2.1 Y i.1 j.1 (i.2,j.2)

def supportBudget (p:Shape) (K:ℕ) (η a:ℝ) :=
   0<a ∧ ∀ k:Scrip p K,a ≤ k.2.2.momus* η^Fintype.card (Messenger (toFormat k.1.1))

variable {U : Wgt (UnitType p n N)} {m : Mixer p n}

structure Lead (U: Wgt (UnitType p n N)) (w : LeafMixture p n N) (m:Mixer p n) (q:PreparationParameters) : Prop where
  strength : w.strength U (usual p m N) q.leafNew (2*q.ζ) q.pins
  amount : 0<w.amount U
  law : IsLaw U
  coverC : w.within (frameSide p m)

end StatusAnalysis
end HadwigerCounterexample

end

end OAI
end

section
-- module Solutions.OAIQ430_HC.HadwigerCounterexample_AggregateCostBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Aggregate Cost Bounds -/

noncomputable section
namespace HadwigerCounterexample
open Finset Matrix Filter Function
open scoped BigOperators Topology
open Template
variable {p:Shape} {n N r M s0 K:ℕ}
namespace StatusAnalysis
open PreparationParameters Station DualAnalysis

structure Beams (b:PreparationParameters) (m:Mixer p n) (Y:Silhouette p N r)
    (w:LeafMixture p n N)(U:Wgt (UnitType p n N)) (v:Station p n N b.pins w)
    (a ε δ τ :ℝ):Prop where
   soft : origami p r (wisp p Y) δ
   rare : pr (w.sap U) (fun i=>¬gauze p δ δ Y m b.pins i) ≤ τ
   zone : pr (cirque w U) (fun x=> eligiblePair v m x.1 x.2 Y a) ≤ τ
   haze : 0<δ∧ δ≤ ε

end StatusAnalysis
end HadwigerCounterexample

end

end OAI
end

section
-- module Solutions.OAIQ430_HC.HadwigerCounterexample_FiniteGraphTransfer
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Finite Graph Transfer -/

noncomputable section

namespace HadwigerCounterexample
open Finset Real
open scoped BigOperators
variable {A V : Type*}

/-- k distinct samples in S (unordered). -/
def badS (S : A → Prop) (k : ℕ) (x : V → A) :=
  ∃ T : Finset V, T.card = k ∧ ∀ v ∈ T, S (x v)

/-- k pair exceptions using disjoint sample positions (ordered pairs). -/
def badE (E : A × A → Prop) (k : ℕ) (x : V → A) :=
  ∃ e : Fin k ⊕ Fin k → V, Function.Injective e ∧
    ∀ i, E (x (e (.inl i)), x (e (.inr i)))

end HadwigerCounterexample

end

end OAI
end

section
-- module Solutions.OAIQ430_HC.HadwigerCounterexample_ExponentialGraphTransfer
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Exponential Graph Transfer -/

noncomputable section
namespace HadwigerCounterexample
open Real Filter

def ord (g N : ℕ) := (2:ℕ)^(1000*g*N)

end HadwigerCounterexample

end

end OAI
end

section
-- module Solutions.OAIQ430_HC.HadwigerCounterexample_FiniteComparisonBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Finite Comparison Bounds -/

noncomputable section
namespace HadwigerCounterexample
open Matrix Function Finset Module LinearMap Filter
open scoped BigOperators Topology
open Template
variable {p:Shape} {n N K M r s0:ℕ}
namespace StatusAnalysis
open PreparationParameters Station PredictionClass DualAnalysis Club Guild

def trimBeta (p : Shape) (K:ℕ):=basebeta p K/2

structure Jubilee (p : Shape) (K:ℕ) (ε η:ℝ) : Prop where
  pos : 0<η
  book : playbook p K*η≤ε
  sturdyR : playbook p K*η<1/2*trimBeta p K^2
  low : 6*ε<1/2*trimBeta p K

variable {b:PreparationParameters}

variable {w:LeafMixture p n N} {m:Mixer p n}

structure Loupe (p : Shape) (n N K : ℕ) (s:LeafMixture p n N) where
   r : s.T → Stakes K
   H : s.T → Stalls p

structure Shipped (w:LeafMixture p n N) (K:ℕ) (u:Station p n N K w) (t:Loupe p n N K w) : Prop where
   charts i: charted (u.cAxes i (toRates (t.r i))) (w.pin i.val).sp
   baseline i: booths p K (w.pin i.val).sp (t.H i)

variable (w:LeafMixture p n N) (L:Loupe p n N b.pins w) (t:Station p n N b.pins w)
def routeC {K} (w:LeafMixture p n N) (L:Loupe p n N K w) (t:Station p n N K w)
    (x:Aspect p n N w) :=
   t.cAxes x.1 (toRates (L.r x.1))
abbrev KAspect {p:Shape} {n N:ℕ} (w:LeafMixture p n N):=Aspect p n N w

end StatusAnalysis
end HadwigerCounterexample

end

end OAI
end

section
-- module Solutions.OAIQ430_HC.HadwigerCounterexample_ForbiddenPredictions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Forbidden Predictions -/

noncomputable section
namespace HadwigerCounterexample
open Filter Matrix Module LinearMap Finset Function
open scoped BigOperators Topology
open Template
namespace StatusAnalysis
open PreparationParameters Station PredictionClass Club Guild DualAnalysis
variable {p : Shape} {n N M r s0 K : ℕ} {w:LeafMixture p n N} {b:PreparationParameters}

def witnessed (w:LeafMixture p n N) (v:Station p n N K w) (L:Loupe p n N K w)
    (m:Mixer p n) (Y:Silhouette p N r)
    (δ ε:ℝ) (B:ℕ) (d:Dict p r) (x: Aspect p n N w) :=
  gauze p δ δ Y m K x.2 ∧ announced (wisp p Y) (wake p Y m x.2 (routeC w L v x)) d B ε

end StatusAnalysis
end HadwigerCounterexample

end

end OAI
end

section
-- module Solutions.OAIQ430_HC.HadwigerCounterexample_PredictionClassBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Prediction Class Bounds -/

noncomputable section
namespace HadwigerCounterexample
open Filter Finset Function Module LinearMap Matrix
open scoped BigOperators Topology
open Template
variable {p:Shape} {n N r M K s0:ℕ}
namespace StatusAnalysis
open PreparationParameters Station PredictionClass DualAnalysis Club Guild
variable {w:LeafMixture p n N} {b:PreparationParameters} {B:Sketch p M}
variable {d e: Rates}

structure hue (c:PredictionClass) (Y:Silhouette p N r) (f:Bool→ Pulsar p r)
    (u:Bool→Augur p N) (α:Party) (τ:ℝ) :Prop where
    consistent : c.lit α
    pulse_eq : c≠dusk → ∀ i,fromPulse Y (f i)=u i
    atDawn : c=dusk→∀ i,f i=0
    recording : c.recital p u α τ

end StatusAnalysis
end HadwigerCounterexample

end

end OAI
end

section
-- module Solutions.OAIQ430_HC.HadwigerCounterexample_FinalContradiction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Final Contradiction -/

noncomputable section
namespace HadwigerCounterexample
open Filter Matrix Finset Module LinearMap Function
open scoped BigOperators Topology
open Template
namespace StatusAnalysis
open PreparationParameters Station PredictionClass Club Guild DualAnalysis
variable {p:Shape} {n N M r s0:ℕ} {w:rhythms p M}
    {m:cycleM p} {u:tale p M} {b:PreparationParameters} {l:Filter ℕ}

instance stationInhabited (p : Shape) (n N K : ℕ) (w:LeafMixture p n N) :
    Inhabited (Station p n N K w) := ⟨⟨fun _ _ _=>0,fun _ _ _=>0⟩⟩

end StatusAnalysis
end HadwigerCounterexample

end

end OAI
end

section
-- module Solutions.OAIQ430_HC.HadwigerCounterexample_ParameterExistence
attribute [-instance] _root_.OAI.HadwigerCounterexample.StatusAnalysis.instFintypeAppearance _root_.OAI.HadwigerCounterexample.StatusAnalysis.stationInhabited _root_.OAI.HadwigerCounterexample.StatusAnalysis.zodiac_dec
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Parameter Existence -/

noncomputable section
namespace HadwigerCounterexample
open Filter Matrix
open scoped BigOperators Topology
open StatusAnalysis StatusAnalysis.Station

def birthG : ℕ := 10^9+1
structure Ribbon (b : PreparationParameters) : Prop where
  life : b.allows
  hd : b.D=4000*birthG
  mercury : b.L=bp 1000
  rain : (b.D:ℝ)+b.ζ ≤ (b.ζ-b.ζ/4)*b.e
  hk : b.k≤ b.d
  beam : b.spJoint+1 ≤ 0.49*b.k
  dul : 3*b.d+2*b.e+2≤b.u
  size : frameBills birthG b.pins+1000 ≤ b.B
  dust : 2*b.ζ ≤0.004∧2*b.ζ*(56*((birthG-1:ℕ):ℝ))≤0.004

def layout (g b j J r : ℕ) : Shape := ⟨g,b,j,J,r,1000*r⟩

end HadwigerCounterexample

end

end OAI
end

section
-- module Solutions.OAIQ430_HC.HadwigerMatching_BranchCounting
attribute [-instance] _root_.OAI.HadwigerCounterexample.StatusAnalysis.deckFin _root_.OAI.HadwigerCounterexample.StatusAnalysis.scripFintype _root_.OAI.HadwigerCounterexample.Template.datumFinite _root_.OAI.HadwigerCounterexample.Template.inpFinite _root_.OAI.HadwigerCounterexample.Template.instFintypeOppDuet _root_.OAI.HadwigerCounterexample.Template.instFintypeSameDuet _root_.OAI.HadwigerCounterexample.Template.keySlotFinite _root_.OAI.HadwigerCounterexample.Volley.instFintypeVisits _root_.OAI.HadwigerCounterexample.aFintype _root_.OAI.HadwigerCounterexample.amongFintype _root_.OAI.HadwigerCounterexample.arrFintype _root_.OAI.HadwigerCounterexample.cgFin _root_.OAI.HadwigerCounterexample.cgOneFin _root_.OAI.HadwigerCounterexample.drawFintype _root_.OAI.HadwigerCounterexample.fintypeLedger _root_.OAI.HadwigerCounterexample.fintypeStory _root_.OAI.HadwigerCounterexample.fullDecidableEq _root_.OAI.HadwigerCounterexample.fullFintype _root_.OAI.HadwigerCounterexample.idxDec _root_.OAI.HadwigerCounterexample.instFKeys _root_.OAI.HadwigerCounterexample.jointDecidableEq _root_.OAI.HadwigerCounterexample.knFin _root_.OAI.HadwigerCounterexample.momFintype _root_.OAI.HadwigerCounterexample.oframeFintype _root_.OAI.HadwigerCounterexample.orientFintype _root_.OAI.HadwigerCounterexample.rackFintype _root_.OAI.HadwigerCounterexample.rowDecidableEq
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Cardinal bounds for pairwise disjoint nonempty branch sets. -/
namespace HadwigerMatching
open scoped BigOperators

variable {V : Type*} {t : ℕ}

/-- The number of one-vertex branches. -/
def singletonBranchCount (B : Fin t → Finset V) : ℕ :=
  (Finset.univ.filter fun i => (B i).card = 1).card

/-- The number of two-vertex branches. -/
def doubletonBranchCount (B : Fin t → Finset V) : ℕ :=
  (Finset.univ.filter fun i => (B i).card = 2).card

end HadwigerMatching

end OAI
end

section
-- module Solutions.OAIQ430_HC.HadwigerMatching_SmallBranches
attribute [-instance] _root_.OAI.HadwigerCounterexample.StatusAnalysis.deckFin _root_.OAI.HadwigerCounterexample.StatusAnalysis.scripFintype _root_.OAI.HadwigerCounterexample.Template.datumFinite _root_.OAI.HadwigerCounterexample.Template.inpFinite _root_.OAI.HadwigerCounterexample.Template.instFintypeOppDuet _root_.OAI.HadwigerCounterexample.Template.instFintypeSameDuet _root_.OAI.HadwigerCounterexample.Template.keySlotFinite _root_.OAI.HadwigerCounterexample.Volley.instFintypeVisits _root_.OAI.HadwigerCounterexample.aFintype _root_.OAI.HadwigerCounterexample.amongFintype _root_.OAI.HadwigerCounterexample.arrFintype _root_.OAI.HadwigerCounterexample.cgFin _root_.OAI.HadwigerCounterexample.cgOneFin _root_.OAI.HadwigerCounterexample.drawFintype _root_.OAI.HadwigerCounterexample.fintypeLedger _root_.OAI.HadwigerCounterexample.fintypeStory _root_.OAI.HadwigerCounterexample.fullDecidableEq _root_.OAI.HadwigerCounterexample.fullFintype _root_.OAI.HadwigerCounterexample.idxDec _root_.OAI.HadwigerCounterexample.instFKeys _root_.OAI.HadwigerCounterexample.jointDecidableEq _root_.OAI.HadwigerCounterexample.knFin _root_.OAI.HadwigerCounterexample.momFintype _root_.OAI.HadwigerCounterexample.oframeFintype _root_.OAI.HadwigerCounterexample.orientFintype _root_.OAI.HadwigerCounterexample.rackFintype _root_.OAI.HadwigerCounterexample.rowDecidableEq
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Cliques and touching matchings formed by singleton and doubleton branches. -/
namespace HadwigerMatching
open scoped BigOperators
variable {V : Type*} [DecidableEq V] {t : ℕ}

def singletonVertices (B : Fin t → Finset V) : Finset V :=
  (Finset.univ.filter fun i => (B i).card = 1).biUnion B

def twoVertexBranches (B : Fin t → Finset V) : Finset (Finset V) :=
  (Finset.univ.filter fun i => (B i).card = 2).image B

end HadwigerMatching

end OAI
end

section
-- module Solutions.OAIQ430_HC.HadwigerCounterexample_Main
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Counterexamples to Hadwiger's conjecture

The binary frame construction yields arbitrarily large graphs with independence
number at most two and small touching matchings. The matching–minor inequality
then separates their complete-minor order from their ordinary chromatic number.

This formalizes the construction theorem and the ordinary chromatic consequence
in OpenAI, *A counterexample to Hadwiger's conjecture* (September 23, 2026).
-/

noncomputable section
namespace HadwigerCounterexample
open Matrix Filter Finset
open scoped BigOperators Topology

variable {p:Shape} {n N M s0 :ℕ} {b: PreparationParameters}
open PreparationParameters

def conflictLowerBound (p: Shape) (m:Mixer p n) (N:ℕ) (b:PreparationParameters) :=
   ∀ w:Wgt (UnitType p n N), b.nascent p N w m → carried w (rawHoles m).unit →
     bp (-100*p.g*(N:ℝ))≤ pr (pairW w w) (fun i=>(rawHoles m).conflict i.1 i.2)

open HadwigerMatching

end HadwigerCounterexample

end

end OAI
end


