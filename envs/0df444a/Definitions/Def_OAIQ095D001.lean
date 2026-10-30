-- Prove2me | Definitions.Def_OAIQ095D001
-- name    : OAIQ095D001
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-30T05:56:22.545915+00:00
-- url     : https://prove2.me/theorems/c638a899-d841-4db0-a283-4dfb83deae81
-- title:
--   Definitions bundle OAIQ095D001 of the split of OpenAI, The additive indecomposability of the primes (Ostmann's inverse Goldbach conjecture)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.Ostmann.inverseGoldbach` and `OAI.Ostmann.twoInfiniteSummandsImpossible`, carved from OpenAI's openai/math development (OpenAI, *The additive indecomposability of the primes (Ostmann's inverse Goldbach conjecture)*, OpenAI Math Release, September 24, 2026, result family 13, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 885 declarations of OpenAI's Lean: 550 definitions, 56 inductive types or structures, 5 instances and 274 theorems. The definitions and types are `OAI.Ostmann.ArithmeticResidueSplit`, `OAI.Ostmann.ArithmeticResidueSplit.numerator`, `OAI.Ostmann.ArithmeticResidueSplit.reduce`, `OAI.Ostmann.ArithmeticResidueSplit.support`, `OAI.Ostmann.ArithmeticResidueSplit.toData`, `OAI.Ostmann.ArithmeticSplitData`, `OAI.Ostmann.ArithmeticSplitData.hasFrequencies`, `OAI.Ostmann.ArithmeticSplitData.reducedModulus`, `OAI.Ostmann.ArithmeticSplitData.test`, `OAI.Ostmann.AtomSourceBefore`, `OAI.Ostmann.BadBulkArrangement`, `OAI.Ostmann.BadPartitionPair`, `OAI.Ostmann.BadPartitionWitness`, `OAI.Ostmann.BadPartitionWitness.Matching`, `OAI.Ostmann.BadTreeArrangement`, `OAI.Ostmann.BalancedIncidenceCycle`, `OAI.Ostmann.BilinearCube`, `OAI.Ostmann.BinarySplitPlan`, `OAI.Ostmann.BranchingWordHistory`, `OAI.Ostmann.BranchingWordHistory.Valid`, `OAI.Ostmann.BranchingWordHistory.flipSigned`, `OAI.Ostmann.BranchingWordHistory.formulaLeaves`, `OAI.Ostmann.BranchingWordHistory.leafCount`, `OAI.Ostmann.BranchingWordHistory.pivotFormulas`, `OAI.Ostmann.BranchingWordHistory.updatedFormulas`, `OAI.Ostmann.BulkIntegrand`, `OAI.Ostmann.BulkIntegrand.average`, `OAI.Ostmann.BulkIntegrand.averages`, `OAI.Ostmann.BulkIntegrand.constMul`, `OAI.Ostmann.BulkIntegrand.sub`, `OAI.Ostmann.CharacterAnchorCell`, `OAI.Ostmann.CharacterAnchorCell.cell`, `OAI.Ostmann.CharacterCell`, `OAI.Ostmann.CharacterHIndex`, `OAI.Ostmann.CharacterRole`, `OAI.Ostmann.CharacterShellTestIndex`, `OAI.Ostmann.CharacterTargetWord`, `OAI.Ostmann.CharacterTargetWord.cell`, `OAI.Ostmann.CharacterTargetWord.code`, `OAI.Ostmann.CircleSeparated` and 566 more.
--
--   **Sources.** They come from these modules of lean/OAI/NumberTheory, in whole or in part: `Mathlib_Analysis_SpecialFunctions_ImproperIntegrals`, `Mathlib_Analysis_SpecialFunctions_Pow_Real`, `Mathlib_MeasureTheory_Integral_IntervalIntegral_Basic`, `Mathlib_NumberTheory_LSeries_RiemannZeta`, `Mathlib_NumberTheory_LSeries_RiemannZetaAbelContinuation`, `Mathlib_NumberTheory_LSeries_RiemannZetaAbelKernel`, `Mathlib_NumberTheory_LSeries_RiemannZetaPartialSum`, `Ostmann_Arithmetic_ArithmeticLifts`, `Ostmann_Arithmetic_ArithmeticResidueSplit`, `Ostmann_Arithmetic_ArithmeticSplitData`, `Ostmann_Arithmetic_ArithmeticSplitTreeSupport`, `Ostmann_Arithmetic_BulkCoordinateInsertion`, `Ostmann_Arithmetic_BulkFrequencyFactor`, `Ostmann_Arithmetic_BulkFrequencyResidues`, `Ostmann_Arithmetic_BulkIntegrands`, `Ostmann_Arithmetic_BulkLeafPolynomials`, `Ostmann_Arithmetic_BulkLogContinuity`, `Ostmann_Arithmetic_BulkNodePolynomials`, `Ostmann_Arithmetic_BulkNodeSupportPolynomials`, `Ostmann_Arithmetic_BulkSeparatedKernelBound`, `Ostmann_Arithmetic_BulkSlotPolynomials`, `Ostmann_Arithmetic_ClearedHistoryBounds`, `Ostmann_Arithmetic_ClearedHistoryPivot`, `Ostmann_Arithmetic_FrequencyModelCoefficients`, `Ostmann_Arithmetic_FrequencyModelPaths`, `Ostmann_Arithmetic_FrequencyTreeSum`, `Ostmann_Arithmetic_FrozenRegularSupport`, `Ostmann_Arithmetic_GlobalHistoryCoefficient`, `Ostmann_Arithmetic_IntegerHistoryReconstruction`, `Ostmann_Arithmetic_MovingAmplitudeIndex`, `Ostmann_Arithmetic_MovingArithmeticBlocks`, `Ostmann_Arithmetic_MovingArithmeticSupport`, `Ostmann_Arithmetic_MovingBulkFrames`, `Ostmann_Arithmetic_MovingBulkLogFactors`, `Ostmann_Arithmetic_MovingCutoffPolynomials`, `Ostmann_Arithmetic_MovingFieldGiant`, `Ostmann_Arithmetic_MovingFieldSpectator`, `Ostmann_Arithmetic_MovingFormulaNodes`, `Ostmann_Arithmetic_MovingFourierPolynomials`, `Ostmann_Arithmetic_MovingFourierVariation`, `Ostmann_Arithmetic_MovingFrequencyCoefficient`, `Ostmann_Arithmetic_MovingFrequencyResidues`, `Ostmann_Arithmetic_MovingGiantArchimedean`, `Ostmann_Arithmetic_MovingGiantFormulas`, `Ostmann_Arithmetic_MovingGiantRows`, `Ostmann_Arithmetic_MovingGiantSamples`, `Ostmann_Arithmetic_MovingGiantTree`, `Ostmann_Arithmetic_MovingIndexedLineSystem`, `Ostmann_Arithmetic_MovingIntegralFrequencySplit`, `Ostmann_Arithmetic_MovingLineComposition`, `Ostmann_Arithmetic_MovingLogLeaves`, `Ostmann_Arithmetic_MovingModularSpectator`, `Ostmann_Arithmetic_MovingNodeGuards`, `Ostmann_Arithmetic_MovingOccurrenceRelabel`, `Ostmann_Arithmetic_MovingOccurrenceSquares`, `Ostmann_Arithmetic_MovingOccurrenceUnits`, `Ostmann_Arithmetic_MovingOriginalWeightRelabel`, `Ostmann_Arithmetic_MovingPairwiseSupport`, `Ostmann_Arithmetic_MovingPatternBulkBudgets`, `Ostmann_Arithmetic_MovingPrimeOccurrences`, `Ostmann_Arithmetic_MovingRealResidues`, `Ostmann_Arithmetic_MovingRegularSlots`, `Ostmann_Arithmetic_MovingRegularTemplate`, `Ostmann_Arithmetic_MovingRepresentativeLineSystem`, `Ostmann_Arithmetic_MovingRepresentativeSquares`, `Ostmann_Arithmetic_MovingResidueTests`, `Ostmann_Arithmetic_MovingSampleCoordinates`, `Ostmann_Arithmetic_MovingSampleIntegrality`, `Ostmann_Arithmetic_MovingSampleMap`, `Ostmann_Arithmetic_MovingSampleSizes`, `Ostmann_Arithmetic_MovingSampleSlots`, `Ostmann_Arithmetic_MovingSampleValues`, `Ostmann_Arithmetic_MovingSampledRecursion`, `Ostmann_Arithmetic_MovingSignedSpectator`, `Ostmann_Arithmetic_MovingSignedUnits`, `Ostmann_Arithmetic_MovingSlotOccurrences`, `Ostmann_Arithmetic_MovingSlotPolynomials`, `Ostmann_Arithmetic_MovingSlotRealization`, `Ostmann_Arithmetic_MovingSlotRelabel`, `Ostmann_Arithmetic_MovingSlotStateRelabel`, `Ostmann_Arithmetic_MovingSlotSystem`, `Ostmann_Arithmetic_MovingSquareSupport`, `Ostmann_Arithmetic_MovingTemplatePair`, `Ostmann_Arithmetic_MovingTemplatePrior`, `Ostmann_Arithmetic_MovingTransferSlots`, `Ostmann_Arithmetic_MovingUnitSampleBound`, `Ostmann_Arithmetic_RealBulkKernel`, `Ostmann_Arithmetic_RealNodeSupport`, `Ostmann_Arithmetic_RealSlotEvaluation`, `Ostmann_Arithmetic_ReconstructionIntegrality`, `Ostmann_Arithmetic_RecursiveNodeExpansion`, `Ostmann_Arithmetic_ReducedFrequencySum`, `Ostmann_Arithmetic_SequentialSupport`, `Ostmann_Arithmetic_SmoothPolynomialWeight`, `Ostmann_Arithmetic_SmoothPrimeComparison`, `Ostmann_Arithmetic_SplitPrefixProducts`, `Ostmann_Arithmetic_SquareLiftExclusions`, `Ostmann_Arithmetic_SquareRootProbability`, `Ostmann_Arithmetic_TotalAtomUnits`, `Ostmann_Characters_AdditiveFourier`, `Ostmann_Characters_AnchorPairCode`, `Ostmann_Characters_CRTFourier`, `Ostmann_Characters_CharacterAnchorCells`, `Ostmann_Characters_CharacterHCoordinates`, `Ostmann_Characters_CharacterResolventBound`, `Ostmann_Characters_CharacterScheduleRoles`, `Ostmann_Characters_CharacterTargetCellData`, `Ostmann_Characters_CharacterTargetCode`, `Ostmann_Characters_CharacterTargetWords`, `Ostmann_Characters_CycleQuartets`, `Ostmann_Characters_LogCutoffPolynomial`, `Ostmann_Characters_MixedExternalAverage`, `Ostmann_Characters_MixedFourier`, `Ostmann_Characters_MonotoneWeightVariation`, `Ostmann_Characters_NormalizedFourierProfile`, `Ostmann_Characters_NormalizedResidueIndicator`, `Ostmann_Characters_PolynomialGiantRows`, `Ostmann_Characters_PolynomialGiantTests`, `Ostmann_Characters_PolynomialRangeGuards`, `Ostmann_Characters_PolynomialValueBounds`, `Ostmann_Characters_PolynomialVariableSupport`, `Ostmann_Characters_PolynomialWeightPair`, `Ostmann_Characters_PrimitiveCharacterReduction`, `Ostmann_Characters_PublishedBonami`, `Ostmann_Characters_QuartetLocalBounds`, `Ostmann_Characters_QuartetMovingAction`, `Ostmann_Characters_QuartetProductFibers`, `Ostmann_Characters_TensorUnitMean`, `Ostmann_Characters_TreeAncestorScheme`, `Ostmann_Characters_TreeArrangementFraction`, `Ostmann_Characters_TreeCoordinates`, `Ostmann_Characters_TreeLeafIndex`, `Ostmann_Characters_TreeLeafProducts`, `Ostmann_Characters_TreeSplitResidues`, `Ostmann_Construction_AdaptivePivotCoefficients`, `Ostmann_Construction_AncestorPivotPrecision`, `Ostmann_Construction_ArrangementProducts`, `Ostmann_Construction_AtomSourceDescent`, `Ostmann_Construction_BranchingHistoryReplay`, `Ostmann_Construction_ConstituentCopiedAssignment`, `Ostmann_Construction_ConstituentHProductLower`, `Ostmann_Construction_ConstituentScheduleEquiv`, `Ostmann_Construction_ConstituentScheduleMap`, `Ostmann_Construction_ConstituentWords`, `Ostmann_Construction_ConstructedHistoryGuards`, `Ostmann_Construction_CopyScheduleSupport`, `Ostmann_Construction_EnumeratedSchedulePhase`, `Ostmann_Construction_ExpandedHistoryFormula`, `Ostmann_Construction_ExpandedOutsideCoordinates`, `Ostmann_Construction_ExpandedRangeReplay`, `Ostmann_Construction_ExpandedScheduleCoordinates`, `Ostmann_Construction_ExpandedScheduleRanges`, `Ostmann_Construction_ExpandedUnitReplay`, `Ostmann_Construction_ExpandedWordPairBound`, `Ostmann_Construction_FinalParityPaths`, `Ostmann_Construction_FinalReassignments`, `Ostmann_Construction_FiniteCellMeans`, `Ostmann_Construction_FiniteFormulaRenaming`, `Ostmann_Construction_FixedPivotCoordinates`, `Ostmann_Construction_FixedPivotFormulas`, `Ostmann_Construction_FixedPivotTopConditions`, `Ostmann_Construction_FrozenInitialSpectatorData`, `Ostmann_Construction_FullAtomTransferWeight`, `Ostmann_Construction_FullHistoryGuards`, `Ostmann_Construction_GiantOuterFactors`, `Ostmann_Construction_GiantReversalRows`, `Ostmann_Construction_GraphCopySchedule`, `Ostmann_Construction_HarmonicWordPriors`, `Ostmann_Construction_HistoryFormula`, `Ostmann_Construction_HistoryFormulaFourier`, `Ostmann_Construction_HistoryFourierPolynomial`, `Ostmann_Construction_HistoryGiantSources`, `Ostmann_Construction_HistoryPolynomialSpecialization`, `Ostmann_Construction_HistoryRealEvaluation`, `Ostmann_Construction_HistoryResidueGate`, `Ostmann_Construction_HistorySubstitution`, `Ostmann_Construction_InitialMovingBulkTree`, `Ostmann_Construction_InitialMovingSlots`, `Ostmann_Construction_InsertedAtomAssignment`, `Ostmann_Construction_InsertedConstituentWords`, `Ostmann_Construction_MatchedRetainedPhase`, `Ostmann_Construction_ModularAdaptiveCoefficients`, `Ostmann_Construction_ModularCompensatedPrecision`, `Ostmann_Construction_PrimeCellPartitionConstruction`, `Ostmann_Construction_PrimeCellWordPriors`, `Ostmann_Construction_PrimeLogCellMeans`, `Ostmann_Construction_PrimeWordCoefficient`, `Ostmann_Construction_RecursiveTransferWeight`, `Ostmann_Construction_ReverseCopyMap`, `Ostmann_Construction_ScheduleAtomSystem`, `Ostmann_Construction_ScheduleFullCoprime`, `Ostmann_Construction_ScheduleGraphInvariants`, `Ostmann_Construction_SchedulePivotSlots`, `Ostmann_Construction_SchedulePivotUnary`, `Ostmann_Construction_ScheduleWordSlots`, `Ostmann_Construction_ScheduledAnchorMatchingCount`, `Ostmann_Construction_ScheduledBulkMatchingCount`, `Ostmann_Construction_ScheduledFinalPermutation`, `Ostmann_Construction_ScheduledFrequencyHistory`, `Ostmann_Construction_ScheduledHistoryEmbedding`, `Ostmann_Construction_ScheduledInputPhase`, `Ostmann_Construction_ScheduledNodeFrequencies`, `Ostmann_Construction_ScheduledNodeUnits`, `Ostmann_Construction_ScheduledPivotPartition`, `Ostmann_Construction_ScheduledRegularUnary`, `Ostmann_Construction_ScheduledTreeBulkCoordinates`, `Ostmann_Construction_ScheduledWordLeafCoordinates`, `Ostmann_Construction_ScheduledWordLeafProducts`, `Ostmann_Construction_SelectedAnchorMatchingCount`, `Ostmann_Construction_SelectedBulkCoordinates`, `Ostmann_Construction_SelectedCompensationCells`, `Ostmann_Construction_SeparatedMatchingCount`, `Ostmann_Construction_SmoothLogCellProfile`, `Ostmann_Construction_SmoothPrimeMeanTest`, `Ostmann_Construction_SpectatorBulkComparison`, `Ostmann_Construction_SpectatorProductNorm`, `Ostmann_Construction_TailGoodPrimeCells`, `Ostmann_Construction_TargetPrimeWords`, `Ostmann_Construction_TopPrimeSupport`, `Ostmann_Construction_TransferFrequencyRange`, `Ostmann_Construction_TransferGraph`, `Ostmann_Construction_TransferHistoryUniqueness`, `Ostmann_Construction_TransferredPivotSubstitution`, `Ostmann_Construction_TypicalCharacterShells`, `Ostmann_Construction_WeightedWordLeaves`, `Ostmann_Construction_WordPrimeBounds`, `Ostmann_Construction_WordPrimeCheckBound`, `Ostmann_Construction_WordPrimeReplay`, `Ostmann_Construction_WordRangeBounds`, `Ostmann_Construction_WordRangePolynomial`, `Ostmann_Construction_WordRangeReplay`, `Ostmann_Construction_WordRangeWeight`, `Ostmann_Construction_WordRootRange`, `Ostmann_Construction_WordTransferArrays`, `Ostmann_Construction_WordTransferCoefficient`, `Ostmann_Construction_WordTransferCounts`, `Ostmann_Construction_WordTransferFormulaBounds`, `Ostmann_Construction_WordTransferFullPeriod`, `Ostmann_Construction_WordTransferGuard`, `Ostmann_Construction_WordTransferGuardFamily`, `Ostmann_Construction_WordTransferGuardPolynomial`, `Ostmann_Construction_WordTransferGuardReplay`, `Ostmann_Construction_WordTransferTemplate`, `Ostmann_Construction_WordTransferUniformCoefficient`, `Ostmann_Construction_WordUnitCoefficient`, `Ostmann_Construction_WordUnitReplay`, `Ostmann_Defs`, `Ostmann_Preliminaries_AdditiveSieveProof`, `Ostmann_Preliminaries_CircleSeparatedPoints`, `Ostmann_Preliminaries_DivisorPowerBound`, `Ostmann_Preliminaries_LargeSummandTails`, `Ostmann_Preliminaries_MertensHarmonicBands`, `Ostmann_Preliminaries_MertensPrimeBands`, `Ostmann_Preliminaries_MertensThetaKernel`, `Ostmann_Preliminaries_OccupiedResidueCollision`, `Ostmann_Preliminaries_PrimeDivisors`, `Ostmann_Preliminaries_Projection`, `Ostmann_Preliminaries_PublishedAdditiveSieve`, `Ostmann_Preliminaries_PublishedSummandBounds`, `Ostmann_Preliminaries_Residues`, `Ostmann_Preliminaries_Stability`, `Ostmann_Preliminaries_StableSummandTails`, `Ostmann_Preliminaries_SummandTails`, `Ostmann_Preliminaries_TailCollisionCutoff`, `Ostmann_Preliminaries_TailStability`, `Ostmann_QuadraticCenter_FixedQuadraticFamily`, `Ostmann_QuadraticCenter_SquarefreeFrequency`, `Ostmann_QuadraticSieve_PublishedQuadraticSieve`, `Ostmann_Quadratic_QuadraticRoughBound`, `Ostmann_Quadratic_QuadraticRowNorm`, `Ostmann_Quadratic_QuadraticSieveFinite`, `Ostmann_Quadratic_QuadraticSieveGrowth`, `Ostmann_Quadratic_QuadraticSieveTranspose`, `Ostmann_Quadratic_QuadraticSieveWeight`, `Ostmann_Quadratic_QuadraticSignedInfiniteSum`, `Ostmann_Quadratic_QuadraticSmoothedEnergy`, `Ostmann_Quadratic_QuadraticSquarefreePart`, `Ostmann_Supply_BilinearCube`, `Ostmann_Supply_CollisionPrimeCellBudget`, `Ostmann_Tree_ArrangementGraph`, `Ostmann_Tree_BadArrangementCount`, `Ostmann_Tree_BadPartitionCounts`, `Ostmann_Tree_PartitionMatching`, `Ostmann_Tree_PreorderNodePaths`, `Ostmann_Tree_RationalQuartetCut`, `Ostmann_Tree_RationalQuartetValue`, `Ostmann_Tree_RationalTree`, `Ostmann_Tree_RationalTreeLeaves`, `Ostmann_Tree_SampleEqualityPatterns`, `Ostmann_Tree_TwoVertexReindex`, `Ostmann_ZeroDensity_ArithmeticRieszMean`, `Ostmann_ZeroDensity_CanonicalThetaSize`, `Ostmann_ZeroDensity_CharacterGammaContour`, `Ostmann_ZeroDensity_CharacterTrivialZero`, `Ostmann_ZeroDensity_ComplexCharacterTrigonometric`, `Ostmann_ZeroDensity_DensityCRTProduct`, `Ostmann_ZeroDensity_DensityCorrelation`, `Ostmann_ZeroDensity_DensityFourier`, `Ostmann_ZeroDensity_DirichletLogDerivativeBound`, `Ostmann_ZeroDensity_FiniteLaplaceDensity`, `Ostmann_ZeroDensity_GammaContourBounds`, `Ostmann_ZeroDensity_GammaRealContourBound`, `Ostmann_ZeroDensity_HighZeroTailBound`, `Ostmann_ZeroDensity_ImprimitiveEulerBound`, `Ostmann_ZeroDensity_NonquadraticZeroBound`, `Ostmann_ZeroDensity_OneZeroBoundaryCut`, `Ostmann_ZeroDensity_PrimePartialSummation`, `Ostmann_ZeroDensity_PrimeSumInputs`, `Ostmann_ZeroDensity_PrimitiveRieszErrorDecay`, `Ostmann_ZeroDensity_PrincipalRieszIntegral`, `Ostmann_ZeroDensity_PrincipalRieszRectangle`, `Ostmann_ZeroDensity_RealCharacterPairEuler`, `Ostmann_ZeroDensity_RealCharacterTrigonometric`, `Ostmann_ZeroDensity_RealZeroPairExclusion`, `Ostmann_ZeroDensity_RectangleBoundary`, `Ostmann_ZeroDensity_RectangleGeometry`, `Ostmann_ZeroDensity_RectangleLogIntegrals`, `Ostmann_ZeroDensity_RegularizedZeta`, `Ostmann_ZeroDensity_ResidueCountingBound`, `Ostmann_ZeroDensity_ResidueRieszFinite`, `Ostmann_ZeroDensity_RieszCharacterMainSum`, `Ostmann_ZeroDensity_RieszContourRectangle`, `Ostmann_ZeroDensity_RieszExponentialParameters`, `Ostmann_ZeroDensity_RieszLeftEstimate`, `Ostmann_ZeroDensity_RieszMellinInversion`, `Ostmann_ZeroDensity_RieszMellinKernel`, `Ostmann_ZeroDensity_RieszPoleRectangle`, `Ostmann_ZeroDensity_RieszResidueTruncation`, `Ostmann_ZeroDensity_RieszTailEstimate`, `Ostmann_ZeroDensity_RieszTruncation`, `Ostmann_ZeroDensity_RieszUnsmoothing`, `Ostmann_ZeroDensity_RieszVerticalWeight`, `Ostmann_ZeroDensity_SmoothMellinBounds`, `Ostmann_ZeroDensity_SmoothMellinDerivatives`, `Ostmann_ZeroDensity_SmoothPrincipalMean`, `Ostmann_ZeroDensity_TailDensityMask`, `Ostmann_ZeroDensity_ThetaMainTerm`, `Ostmann_ZeroDensity_TreeDensity`, `Ostmann_ZeroDensity_WeightedRieszRectangle`, `Ostmann_ZeroDensity_WeightedRieszTails`, `Ostmann_ZeroDensity_ZeroFreeNumerics`.
--
--   **Imports.** It imports the published bundle `Def_OstmannComplete`.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ095D003`, `OAIQ095D004` and `OAIQ095D005`; the statements `OAI.Ostmann.eventual_original_tail_commonCenter`, `OAI.Ostmann.exists_selected_small_primes`, `OAI.Ostmann.publishedQuadraticLargeSieve`, `OAI.Ostmann.publishedSummandSizeBound`, `OAI_Ostmann_quadratic_rough_iteration` and `OAI.Ostmann.quadratic_rough_power_growth`.
-- source:
--   OpenAI, The additive indecomposability of the primes (Ostmann's inverse Goldbach conjecture), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 13; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/the-additive-indecomposability-of-the-primes-September-24-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/NumberTheory at commit 7ef5c0c

import Mathlib
import Definitions.Def_OstmannComplete

section
-- module Solutions.OAIQ095_OS.Compat
namespace OAI

/-! Compatibility with the newer Lean core OpenAI's code was written against: lemmas it uses by
names this environment (Lean 4.33.1, Mathlib 0df444a) does not have yet. Each is the
corresponding `if_pos` / `if_neg` / `dif_pos` / `dif_neg`. The `dite` forms are stated as
`dite p a b`, not with the `if hp : p then …` notation: its eta-expanded lambdas form is a higher-order pattern
that `rw` cannot find (DepthThree, PeriodicTiling 2026-10-25). -/
section OAICompat434
theorem dite_eq_left {α : Sort _} {c : Prop} {_ : Decidable c} {a : c → α} {b : ¬c → α} (h : c) :
    dite c a b = a h := dif_pos h
theorem dite_eq_right {α : Sort _} {c : Prop} {_ : Decidable c} {a : c → α} {b : ¬c → α} (h : ¬c) :
    dite c a b = b h := dif_neg h
end OAICompat434

end OAI
end

section
-- module Solutions.OAIQ095_OS.Mathlib_Analysis_SpecialFunctions_ImproperIntegrals
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-!
# Improper-integral estimates

Elementary power-integral evaluations and convergence criteria for interval integrals on
half-lines.
-/

section

open Real Set Filter MeasureTheory intervalIntegral
open scoped Topology

/-- `∫_{1}^∞ u^{-re s - 1} = 1 / re s` for `0 < re s`. -/
theorem integral_Ioi_rpow_neg_re_sub_one {s : ℂ} (hs : 0 < s.re) :
    ∫ u in Ioi (1 : ℝ), u ^ (-s.re - 1) = 1 / s.re := by
  have ha : (-s.re - 1) < -1 := by linarith
  have hc : 0 < (1 : ℝ) := zero_lt_one
  have h := integral_Ioi_rpow_of_lt (a := (-s.re - 1)) ha (c := (1 : ℝ)) hc
  have h' : ∫ u in Ioi (1 : ℝ), u ^ (-s.re - 1) = - (1 : ℝ) ^ (-s.re) / (-s.re) := by
    simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using h
  calc
    ∫ u in Ioi (1 : ℝ), u ^ (-s.re - 1)
        = - (1 : ℝ) ^ (-s.re) / (-s.re) := h'
    _ = - (1 : ℝ) / (-s.re) := by simp [Real.one_rpow]
    _ = 1 / s.re := by simp
end
end

section
-- module Solutions.OAIQ095_OS.Mathlib_Analysis_SpecialFunctions_Pow_Real
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-!
# Real-power estimates

Elementary logarithmic and real-power inequalities used in decay and growth estimates.
-/
section

namespace Real

/-- For `1 < u` and `ε > 0`, `log u * u^(-1-ε) ≤ (2/ε) * u^(-1-ε/2)`. -/
theorem log_mul_rpow_neg_le_two_div_mul_rpow_neg {ε : ℝ} (hε : 0 < ε) {u : ℝ} (hu : 1 < u) :
    Real.log u * u ^ (-1 - ε) ≤ (2 / ε) * u ^ (-1 - ε / 2) := by
  have hu0 : 0 < u := lt_trans zero_lt_one hu
  have hεne : ε ≠ 0 := ne_of_gt hε
  have hpos_coeff : 0 < 2 / ε := by
    simpa [one_div, div_eq_mul_inv] using mul_pos (by norm_num : (0 : ℝ) < 2) (inv_pos.mpr hε)
  have hle_exp : (ε / 2) * Real.log u ≤ Real.exp ((ε / 2) * Real.log u) :=
    le_trans (by linarith) (Real.add_one_le_exp ((ε / 2) * Real.log u))
  have hlog_bound : Real.log u ≤ (2 / ε) * Real.exp ((ε / 2) * Real.log u) := by
    calc
      Real.log u = (2 / ε) * ((ε / 2) * Real.log u) := by field_simp [hεne]
      _ ≤ (2 / ε) * Real.exp ((ε / 2) * Real.log u) :=
        mul_le_mul_of_nonneg_left hle_exp (le_of_lt hpos_coeff)
  have hexp_rpow : Real.exp ((ε / 2) * Real.log u) = u ^ (ε / 2) := by
    simp [Real.rpow_def_of_pos hu0, mul_comm]
  have hmul : Real.log u * u ^ (-1 - ε) ≤ ((2 / ε) * u ^ (ε / 2)) * u ^ (-1 - ε) :=
    mul_le_mul_of_nonneg_right (by simpa [hexp_rpow] using hlog_bound)
      (le_of_lt (Real.rpow_pos_of_pos hu0 _))
  have hpow_mul : u ^ (ε / 2) * u ^ (-1 - ε) = u ^ (-1 - ε / 2) := by
    rw [← Real.rpow_add hu0, show ε / 2 + (-1 - ε) = -1 - ε / 2 by ring]
  calc
    Real.log u * u ^ (-1 - ε)
        ≤ ((2 / ε) * u ^ (ε / 2)) * u ^ (-1 - ε) := hmul
    _ = (2 / ε) * u ^ (-1 - ε / 2) := by rw [mul_assoc, hpow_mul]

end Real
end
end

section
-- module Solutions.OAIQ095_OS.Mathlib_MeasureTheory_Integral_IntervalIntegral_Basic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-!
# Interval-integral congruence lemmas

Congruence for interval integrals when the integrands agree on the oriented interval.
-/

section

open Set MeasureTheory

namespace intervalIntegral

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {f g : ℝ → E} {μ : Measure ℝ}

/-- If two functions agree on `Ioc a b`, their interval integrals agree. -/
theorem integral_congr_Ioc_of_le {a b : ℝ} (hab : a ≤ b)
    (h : ∀ u ∈ Ioc a b, f u = g u) :
    ∫ u in a..b, f u ∂μ = ∫ u in a..b, g u ∂μ := by
  refine integral_congr_ae' (Filter.Eventually.of_forall ?_) (Filter.Eventually.of_forall ?_) <;>
    intro u hu
  · exact h u hu
  · have hempty : Ioc b a = ∅ := Ioc_eq_empty hab.not_gt
    exact (hempty ▸ hu).elim

end intervalIntegral
end
end

section
-- module Solutions.OAIQ095_OS.Mathlib_NumberTheory_LSeries_RiemannZeta
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-!
# Extra Riemann zeta API

Vertical lines, prime-power bounds, and Euler-product identities supporting strip
and convexity bounds in `RiemannZetaConvexity`.

## Main results

* `verticalLine`, `verticalLine_re`, `verticalLine_add_const`
* `Nat.Primes.norm_one_sub_cpow_neg_vertical_le` and companions
* `riemannZeta_div_riemannZeta_eq_tprod_inv_one_add`, `norm_riemannZeta_div_riemannZeta`
* `norm_riemannZeta_eulerProduct`, `tprod_inv_one_add_real_le_riemannZeta_norm_on_verticalLine`
-/

section

open scoped BigOperators Topology
open Complex Filter Real Set

/-- `1 / (n : ℂ) ^ s` rewrites to `(n : ℂ) ^ (-s)` away from `n = 0`. -/
theorem one_div_natCast_cpow_eq_ite_cpow_neg (s : ℂ) (hs : s ≠ 0) (n : ℕ) :
    1 / (n : ℂ) ^ s = if n = 0 then 0 else (n : ℂ) ^ (-s) := by
  by_cases h : n = 0
  · simp [h, Complex.zero_cpow hs]
  · simp [h, one_div, Complex.cpow_neg]

end
end

section
-- module Solutions.OAIQ095_OS.Mathlib_NumberTheory_LSeries_RiemannZetaAbelKernel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-!
# Fractional-part kernel for the Abel zeta formula

`K_s(u) = {u} · u^{-s-1}` and its integrability / domination lemmas, used in
`RiemannZetaPartialSum` and `RiemannZetaAbelContinuation`.

## Main results

* `zetaAbelFractKernel`, `norm_zetaAbelFractKernel_le`
* `ZetaAbelFractKernel.intervalIntegrable`, `integrableOn_Ioi`, `tendsto_integral_Ioi`
* `ZetaAbelFractKernel.hasDerivAt_in_param`, `kernel_deriv_norm_bound_on_ball`
* `ZetaAbelFractKernel.integral_analytic`
-/

section

open scoped Topology
open Real Set Filter Topology MeasureTheory Complex

/-- Fractional-part kernel `{u} · u^{-s-1}` (`K_s` in the Abel formula). -/
noncomputable def zetaAbelFractKernel (s : ℂ) (u : ℝ) : ℂ :=
  ((Int.fract u : ℝ) : ℂ) * (u : ℂ) ^ (-s - 1)

namespace ZetaAbelFractKernel

lemma aestronglyMeasurable (s : ℂ) (S : Set ℝ) (_ : MeasurableSet S) :
    AEStronglyMeasurable (fun u => zetaAbelFractKernel s u) (volume.restrict S) := by
  refine (measurable_fract.complex_ofReal.mul ?_).aestronglyMeasurable
  simpa using Complex.measurable_ofReal.pow_const (-s - 1)

lemma aestronglyMeasurable_param_deriv (z : ℂ) :
    AEStronglyMeasurable (fun u : ℝ => -((Real.log u) : ℂ) * zetaAbelFractKernel z u)
      (volume.restrict (Ioi (1 : ℝ))) := by
  have hmeas : Measurable (fun u : ℝ => zetaAbelFractKernel z u) :=
    (measurable_fract.complex_ofReal.mul <| by simpa using Complex.measurable_ofReal.pow_const (-z - 1))
  simpa only [neg_mul] using
    (Real.measurable_log.complex_ofReal.fun_mul hmeas).fun_neg.aestronglyMeasurable

lemma eventually_aestronglyMeasurable_param (s : ℂ) :
    ∀ᶠ z in 𝓝 s,
      AEStronglyMeasurable (fun u : ℝ => zetaAbelFractKernel z u) (volume.restrict (Ioi (1 : ℝ))) :=
  Eventually.of_forall fun z => aestronglyMeasurable z (Ioi (1 : ℝ)) measurableSet_Ioi

lemma ae_on_Ioi_of_all {p : ℝ → Prop} (h : ∀ u ∈ Ioi (1 : ℝ), p u) :
    ∀ᵐ u ∂(volume.restrict (Ioi (1 : ℝ))), p u :=
  ae_restrict_iff' measurableSet_Ioi |>.2 (ae_of_all _ fun u hu => h u hu)

lemma dist_lt_of_mem_ball_half {z s : ℂ} {δ : ℝ} (hz : z ∈ Metric.ball s (δ / 2)) (hδ : 0 < δ) :
    dist z s < δ :=
  lt_trans (Metric.mem_ball.mp hz) (half_lt_self hδ)

/-- Dominated differentiation under `∫_{(1,∞)} F z`. -/
lemma hasDerivAt_integral_param_dominated_Ioi
  (F F' : ℂ → ℝ → ℂ) (s : ℂ) (δ : ℝ) (hδ : 0 < δ)
  (hmeas : ∀ᶠ z in 𝓝 s, AEStronglyMeasurable (F z) (volume.restrict (Ioi (1 : ℝ))))
  (hFint : Integrable (F s) (volume.restrict (Ioi (1 : ℝ))))
  (hF'meas : AEStronglyMeasurable (F' s) (volume.restrict (Ioi (1 : ℝ))))
  (bound : ℝ → ℝ) (hbound_int : Integrable bound (volume.restrict (Ioi (1 : ℝ))))
  (hbound : ∀ᵐ u ∂(volume.restrict (Ioi (1 : ℝ))), ∀ z ∈ Metric.ball s δ, ‖F' z u‖ ≤ bound u)
  (hderiv : ∀ᵐ u ∂(volume.restrict (Ioi (1 : ℝ))), ∀ z ∈ Metric.ball s δ,
    HasDerivAt (fun w => F w u) (F' z u) z) :
  HasDerivAt (fun z => ∫ u in Ioi (1 : ℝ), F z u) (∫ u in Ioi (1 : ℝ), F' s u) s := by
  have h :=
    hasDerivAt_integral_of_dominated_loc_of_deriv_le
      (μ := volume.restrict (Ioi (1 : ℝ))) (F := F) (F' := F') (x₀ := s)
      (s := Metric.ball s δ) (bound := bound) (Metric.ball_mem_nhds s hδ)
      (hF_meas := hmeas) (hF_int := hFint) (hF'_meas := hF'meas)
      (h_bound := hbound) (bound_integrable := hbound_int) (h_diff := hderiv)
  rcases h with ⟨_, hDeriv⟩
  exact hDeriv

end ZetaAbelFractKernel
end
end

section
-- module Solutions.OAIQ095_OS.Mathlib_NumberTheory_LSeries_RiemannZetaPartialSum
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-!
# Abel-summation partial sums for the Riemann zeta function

For `re s > 1`, the partial Dirichlet sum `∑_{n<N} (n+1)^{-s}` satisfies the classical
Abel tail identity in `ZetaPartialSum.abel_formula`, and converges to `riemannZeta s`.

Used in `RiemannZetaAbelContinuation` to match the Abel integral formula for `re s > 1`.
-/

section

open scoped BigOperators Topology
open Real Set Filter Topology MeasureTheory Complex Nat ZetaAbelFractKernel

/-- Partial sum of the Dirichlet series defining `ζ` for `re s > 1`. -/
noncomputable def zetaPartialSum (s : ℂ) (N : ℕ) : ℂ :=
  ∑ n ∈ Finset.range N, (n + 1 : ℂ) ^ (-s)

namespace ZetaPartialSum

lemma natCast_floor_eq_sub_fract (u : ℝ) (hu : 0 ≤ u) :
    (Nat.floor u : ℂ) = (u : ℂ) - ((Int.fract u : ℝ) : ℂ) := by
  have hfloorR : (Nat.floor u : ℝ) = (Int.floor u : ℝ) := by
    simpa using natCast_floor_eq_intCast_floor (R := ℝ) (a := u) hu
  have hfloorC : (Nat.floor u : ℂ) = ((Int.floor u : ℝ) : ℂ) := congrArg (fun x : ℝ => (x : ℂ)) hfloorR
  have hIFR : (Int.floor u : ℝ) = u - Int.fract u := (eq_sub_iff_add_eq).2 (Int.floor_add_fract u)
  have hIFC : ((Int.floor u : ℝ) : ℂ) = ((u - Int.fract u : ℝ) : ℂ) := congrArg (fun x : ℝ => (x : ℂ)) hIFR
  exact hfloorC.trans (by simpa [sub_eq_add_neg] using hIFC)

lemma cpow_integral (s : ℂ) (hs : s ≠ 1) (N : ℕ) (hN : 1 ≤ N) :
    s * ∫ u in (1 : ℝ)..N, (u : ℂ) ^ (-s) = s / (1 - s) * ((N : ℂ) ^ (1 - s) - 1) := by
  have h01leN : (1 : ℝ) ≤ (N : ℝ) := mod_cast hN
  have hint : ∫ u in (1 : ℝ)..N, (u : ℂ) ^ (-s)
      = ((N : ℂ) ^ ((-s) + 1) - (1 : ℂ) ^ ((-s) + 1)) / ((-s) + 1) := by
    have hrne : -s ≠ (-1 : ℂ) := fun h => hs (neg_inj.mp h)
    simpa using integral_cpow (a := (1 : ℝ)) (b := (N : ℝ)) (r := -s)
      (Or.inr ⟨hrne, by simp [uIcc_of_le h01leN]⟩)
  calc s * ∫ u in (1 : ℝ)..N, (u : ℂ) ^ (-s)
      = s * (((N : ℂ) ^ ((-s) + 1) - (1 : ℂ) ^ ((-s) + 1)) / ((-s) + 1)) := by
        simpa using congrArg (s * ·) hint
      _ = s * (((N : ℂ) ^ (1 - s) - 1) / (1 - s)) := by
        rw [one_cpow, show (1 : ℂ) - s = -s + 1 from by ring]
      _ = s / (1 - s) * ((N : ℂ) ^ (1 - s) - 1) := by field_simp

lemma tendsto_natCast_cpow_zero_of_neg_re (w : ℂ) (hw : w.re < 0) :
    Tendsto (fun N : ℕ => (N : ℂ) ^ w) atTop (𝓝 0) := by
  rw [tendsto_zero_iff_norm_tendsto_zero]
  have h1 : (fun N : ℕ => (N : ℝ) ^ w.re) =ᶠ[atTop] fun N : ℕ => ‖(N : ℂ) ^ w‖ := by
    filter_upwards [eventually_gt_atTop 0] with N hN
    rw [Complex.norm_natCast_cpow_of_pos hN w]
  rw [tendsto_congr' (EventuallyEq.symm h1)]
  rw [show w.re = -(-w.re) from by ring]
  exact (tendsto_rpow_neg_atTop (neg_pos.mpr hw)).comp tendsto_natCast_atTop_atTop

/-- `zetaPartialSum` converges to `riemannZeta` for `re s > 1`. -/
theorem tendsto_riemannZeta (s : ℂ) (hs : 1 < s.re) :
    Tendsto (fun N : ℕ => zetaPartialSum s N) atTop (𝓝 (riemannZeta s)) := by
  set g : ℕ → ℂ := fun n => if n = 0 then 0 else (n : ℂ) ^ (-s)
  set h : ℕ → ℂ := fun n => (n + 1 : ℂ) ^ (-s)
  have hsne : s ≠ 0 := by
    intro h0
    have : (0 : ℝ) < s.re := lt_trans (show (0 : ℝ) < 1 by norm_num) hs
    simpa [h0] using ne_of_gt this
  have hgSumm : Summable g := by
    simpa [g, one_div_natCast_cpow_eq_ite_cpow_neg s hsne] using
      (Complex.summable_one_div_nat_cpow (p := s)).2 hs
  have hhSumm : Summable h := by
    have : Summable (fun n => g (n + 1)) := (summable_nat_add_iff (f := g) (k := 1)).2 hgSumm
    simpa [Function.comp_apply, h, g] using this
  have hg0 : g 0 = 0 := by simp [g]
  have h_tsum_eq : (∑' n, h n) = ∑' n, g n := by
    have : (∑' n, g n) = ∑' n, g (n + 1) := by simpa [hg0, add_comm] using Summable.tsum_eq_zero_add hgSumm
    simpa [h, g] using this.symm
  have hzeta : riemannZeta s = ∑' n, g n := by
    simpa [g, one_div_natCast_cpow_eq_ite_cpow_neg s hsne] using
      zeta_eq_tsum_one_div_nat_cpow (s := s) hs
  simpa [zetaPartialSum, h, h_tsum_eq.trans hzeta.symm] using Summable.tendsto_sum_tsum_nat hhSumm

end ZetaPartialSum
end
end

section
-- module Solutions.OAIQ095_OS.Mathlib_NumberTheory_LSeries_RiemannZetaAbelContinuation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-!
# Abel-summation continuation of the Riemann zeta function

For `s ≠ 1` in the half-plane `{re s > σ₀}` with `σ₀ = 1/10`, the Riemann zeta function equals the
Abel-summation tail formula from [`Mathlib.NumberTheory.AbelSummation`]: writing `{u}` for the
fractional part of `u > 0` and `K_s(u) = {u} · u^{-s-1}`, one has

`ζ(s) = 1 + (s - 1)⁻¹ - s ∫_{(1,∞)} K_s(u) du`.

The threshold `σ₀`, the domain, the kernel, and the renormalized integral are bundled in
`zetaAbelContinuationReLower`, `zetaAbelContinuationDomain`, `zetaAbelFractKernel`, and
`zetaAbelContinuationFormula`. The equality with `riemannZeta` on that domain is proved by analytic
continuation from `re s > 1`, where the formula is the classical Abel partial-sum limit.

Kernel and partial-sum input live in `RiemannZetaAbelKernel` and `RiemannZetaPartialSum`.

## Main results

* `zetaAbelContinuationDomain`, `zetaAbelContinuationFormula`
* `riemannZeta_eq_zetaAbelContinuationFormula`
* `norm_zetaAbelContinuationFormula_le`, `analyticOn_zetaAbelContinuationFormula`
-/

section

open scoped Topology
open Real Set Filter Topology MeasureTheory Complex ZetaPartialSum ZetaAbelFractKernel

/-- Lower threshold on `re s` for the Abel integral continuation of `ζ`. -/
noncomputable def zetaAbelContinuationReLower : ℝ := 1 / 10

theorem zetaAbelContinuationReLower_pos : 0 < zetaAbelContinuationReLower := by
  change 0 < (1 / 10 : ℝ)
  norm_num

theorem one_lt_zetaAbelContinuationReLower : zetaAbelContinuationReLower < (1 : ℝ) := by
  change (1 / 10 : ℝ) < 1
  norm_num

/-- Domain `{s : ℂ | s ≠ 1 ∧ re s > 1/10}` where the Abel continuation of `ζ` is proved. -/
def zetaAbelContinuationDomain : Set ℂ :=
  {s | s ≠ (1 : ℂ) ∧ zetaAbelContinuationReLower < s.re}

theorem isOpen_zetaAbelContinuationDomain : IsOpen zetaAbelContinuationDomain := by
  change IsOpen ({s : ℂ | s ≠ 1} ∩ {s : ℂ | zetaAbelContinuationReLower < s.re})
  exact isOpen_compl_singleton.inter (isOpen_lt continuous_const Complex.continuous_re)

theorem two_mem_zetaAbelContinuationDomain : (2 : ℂ) ∈ zetaAbelContinuationDomain := by
  refine ⟨by norm_num, ?_⟩
  change (1 / 10 : ℝ) < (2 : ℂ).re
  norm_num

theorem zetaAbelContinuationDomain_re_pos {s : ℂ} (hs : s ∈ zetaAbelContinuationDomain) :
    0 < s.re := lt_trans zetaAbelContinuationReLower_pos hs.2

/-- Abel renormalization `1 + (s-1)⁻¹ - s ∫_{(1,∞)} K_s`. -/
noncomputable def zetaAbelContinuationFormula (s : ℂ) : ℂ :=
  1 + 1 / (s - 1) - s * ∫ u in Ioi (1 : ℝ), zetaAbelFractKernel s u
end
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_ArithmeticLifts
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Uniform lifts of a nonzero line modulo a prime square

The reduction map has exactly `p` lifts over every residue. A line with a
unit coefficient has exactly `p` zero lifts among the `p²` pairs over a
fixed solution modulo `p`. This is the relative `1/p` loss in §8.
-/

namespace Ostmann

open scoped BigOperators

/-- The actual reduction map modulo a prime. -/
def squareReduction (p : ℕ) : ZMod (p ^ 2) →+* ZMod p :=
  ZMod.castHom (dvd_pow_self p (by decide : 2 ≠ 0)) (ZMod p)

@[simp] theorem squareReduction_natCast (p n : ℕ) :
    squareReduction p (n : ZMod (p ^ 2)) = (n : ZMod p) := map_natCast _ _

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_SequentialSupport
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Multiplying support bounds under the original independent prior

The test at a split can depend on the entire already exposed prefix. This
records the order of exposure, so future validity never changes its law.
-/

namespace Ostmann

open scoped BigOperators Classical

@[implicit_reducible] def SplitSamples (A : Type) : ℕ → Type _
  | 0 => Unit
  | n + 1 => A × SplitSamples A n

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_ReducedFrequencySum
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Multiplicity of the reduced frequency modulus -/

namespace Ostmann

open scoped BigOperators

def reducedFrequency (g s : ℕ) : ℕ := s / s.gcd g

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_SquareRootProbability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The divisor loss in the square-congruence probability -/

namespace Ostmann

open scoped BigOperators Classical

theorem le_divisors_card_mul_totient (q : ℕ) (hq : q ≠ 0) :
    q ≤ q.divisors.card * q.totient := by
  calc
    _ = ∑ d ∈ q.divisors, d.totient := (Nat.sum_totient q).symm
    _ ≤ ∑ _d ∈ q.divisors, q.totient := Finset.sum_le_sum fun d hd =>
      Nat.le_of_dvd (Nat.totient_pos.mpr (Nat.pos_of_ne_zero hq))
        (Nat.totient_dvd_of_dvd (Nat.dvd_of_mem_divisors hd))
    _ = _ := by simp

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Characters_TreeLeafProducts
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Leaf-product fibers in a full binary tree -/

namespace Ostmann

open scoped BigOperators

@[implicit_reducible] def TreeLeafTuple (U : Type*) : ℕ → Type _
  | 0 => U
  | n + 1 => TreeLeafTuple U n × TreeLeafTuple U n

@[implicit_reducible] def treeLeafProduct {U : Type*} [CommMonoid U] : (n : ℕ) → TreeLeafTuple U n → U
  | 0, x => x
  | n + 1, xy => treeLeafProduct n xy.1 * treeLeafProduct n xy.2

abbrev TreeLeafFiber (U : Type*) [CommGroup U] (n : ℕ) (P : U) :=
  {x : TreeLeafTuple U n // treeLeafProduct n x = P}

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_ArithmeticSplitData
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Fixed residue data at an exposed arithmetic split -/

namespace Ostmann

open scoped BigOperators Classical

/-- All entries are known before the child product is exposed. The units
contain the current giants and the nonbulk constants. -/
structure ArithmeticSplitData (Q : ℕ) where
  frequency : ℤ
  frequency_ne_zero : frequency ≠ 0
  frequency_dvd : frequency.natAbs ∣ Q
  leftFrequency : ℤ
  rightFrequency : ℤ
  leftFactor : (ZMod frequency.natAbs)ˣ
  rightFactor : (ZMod frequency.natAbs)ˣ
  parentProduct : (ZMod frequency.natAbs)ˣ

instance ArithmeticSplitData.modulusNeZero {Q : ℕ} (d : ArithmeticSplitData Q) :
    NeZero d.frequency.natAbs := ⟨Int.natAbs_ne_zero.mpr d.frequency_ne_zero⟩

def ArithmeticSplitData.reducedModulus {Q : ℕ} (d : ArithmeticSplitData Q) : ℕ :=
  reducedFrequency (d.leftFrequency.natAbs.gcd d.rightFrequency.natAbs) d.frequency.natAbs

def ArithmeticSplitData.test {Q : ℕ} (d : ArithmeticSplitData Q) (x : (ZMod Q)ˣ) : Prop :=
  (d.leftFrequency : ZMod d.frequency.natAbs) *
      (d.leftFactor * (d.parentProduct / ZMod.unitsMap d.frequency_dvd x) :
        (ZMod d.frequency.natAbs)ˣ) =
    (d.rightFrequency : ZMod d.frequency.natAbs) *
      (d.rightFactor * ZMod.unitsMap d.frequency_dvd x : (ZMod d.frequency.natAbs)ˣ)

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_ArithmeticSplitTreeSupport
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Multiplying the actual split probabilities at fixed frequencies -/

namespace Ostmann

open scoped BigOperators Classical

structure NodeFrequencies where
  root : ℤ
  left : ℤ
  right : ℤ

def NodeFrequencies.reducedModulus (f : NodeFrequencies) : ℕ :=
  reducedFrequency (f.left.natAbs.gcd f.right.natAbs) f.root.natAbs

def ArithmeticSplitData.hasFrequencies {Q : ℕ} (d : ArithmeticSplitData Q)
    (f : NodeFrequencies) : Prop :=
  d.frequency = f.root ∧ d.leftFrequency = f.left ∧ d.rightFrequency = f.right

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_ArithmeticResidueSplit
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Constructing the support data from an actual residue numerator -/

namespace Ostmann

open scoped Classical

/-- The two coefficients contain the current giant and its nonbulk
factors. They are allowed to fail the required unit tests. -/
structure ArithmeticResidueSplit (Q : ℕ) where
  frequencies : NodeFrequencies
  frequency_ne_zero : frequencies.root ≠ 0
  frequency_dvd : frequencies.root.natAbs ∣ Q
  leftFactor : ZMod Q
  rightFactor : ZMod Q
  parentProduct : (ZMod Q)ˣ

def ArithmeticResidueSplit.reduce {Q : ℕ} (d : ArithmeticResidueSplit Q) :
    ZMod Q →+* ZMod d.frequencies.root.natAbs :=
  ZMod.castHom d.frequency_dvd _

def ArithmeticResidueSplit.numerator {Q : ℕ} (d : ArithmeticResidueSplit Q)
    (x : (ZMod Q)ˣ) : ZMod Q :=
  (d.frequencies.left : ZMod Q) * d.leftFactor * ↑(d.parentProduct / x) -
    (d.frequencies.right : ZMod Q) * d.rightFactor * ↑x

def ArithmeticResidueSplit.support {Q : ℕ} (d : ArithmeticResidueSplit Q)
    (x : (ZMod Q)ˣ) : Prop :=
  IsUnit (d.reduce d.leftFactor) ∧ IsUnit (d.reduce d.rightFactor) ∧
    d.reduce (d.numerator x) = 0

noncomputable def ArithmeticResidueSplit.toData {Q : ℕ} (d : ArithmeticResidueSplit Q) :
    Option (ArithmeticSplitData Q) :=
  if hL : IsUnit (d.reduce d.leftFactor) then
    if hR : IsUnit (d.reduce d.rightFactor) then
      some {
        frequency := d.frequencies.root
        frequency_ne_zero := d.frequency_ne_zero
        frequency_dvd := d.frequency_dvd
        leftFrequency := d.frequencies.left
        rightFrequency := d.frequencies.right
        leftFactor := hL.unit
        rightFactor := hR.unit
        parentProduct := ZMod.unitsMap d.frequency_dvd d.parentProduct }
    else none
  else none

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_BulkIntegrands
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Bounded measurable bulk integrands, including sharp gates

The sharp terminal windows need not be continuous. This small function space
retains their actual values while providing the finite-measure operations used
in the bulk comparison.
-/

namespace Ostmann
open MeasureTheory
open scoped Classical

structure BulkIntegrand (σ : Type*) where
  toFun : (σ → ℝ) → ℂ
  measurable : Measurable toFun
  bounded : ∃ C : ℝ, 0 ≤ C ∧ ∀ x, ‖toFun x‖ ≤ C

instance instCoeFunBulkIntegrandForallForallRealComplex {σ : Type*} : CoeFun (BulkIntegrand σ) (fun _ => (σ → ℝ) → ℂ) := ⟨BulkIntegrand.toFun⟩

@[ext] theorem BulkIntegrand.ext {σ : Type*} {f g : BulkIntegrand σ}
    (h : ∀ x, f x = g x) : f = g := by
  cases f
  cases g
  have he := funext h
  cases he
  rfl

noncomputable def BulkIntegrand.sub {σ : Type*} (f g : BulkIntegrand σ) : BulkIntegrand σ where
  toFun x := f x - g x
  measurable := f.measurable.sub g.measurable
  bounded := by
    obtain ⟨A, hA, hf⟩ := f.bounded
    obtain ⟨B, hB, hg⟩ := g.bounded
    exact ⟨A + B, add_nonneg hA hB, fun x => (norm_sub_le _ _).trans (add_le_add (hf x) (hg x))⟩

noncomputable def BulkIntegrand.average {σ : Type*} [Fintype σ]
    (μ : Measure ℝ) [IsFiniteMeasure μ] (i : σ) (f : BulkIntegrand σ) : BulkIntegrand σ where
  toFun x := ∫ t, f (Function.update x i t) ∂μ
  measurable := by
    have hj : Measurable (fun z : (σ → ℝ) × ℝ => f (Function.update z.1 i z.2)) :=
      f.measurable.comp (continuous_update i).measurable
    exact hj.stronglyMeasurable.integral_prod_right'.measurable
  bounded := by
    obtain ⟨C, hC, hf⟩ := f.bounded
    refine ⟨C * μ.real Set.univ, mul_nonneg hC measureReal_nonneg, fun x => ?_⟩
    exact norm_integral_le_of_norm_le_const (Filter.Eventually.of_forall fun _t => hf _)

noncomputable def BulkIntegrand.averages {σ : Type*} [Fintype σ] (μ : σ → Measure ℝ)
    [∀ i, IsFiniteMeasure (μ i)] : List σ → BulkIntegrand σ → BulkIntegrand σ
  | [], f => f
  | i :: l, f => (f.averages μ l).average (μ i) i

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_BulkCoordinateInsertion
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Freeze the nonbulk coordinates and integrate the selected bulk slots -/

namespace Ostmann
open MeasureTheory
open scoped Classical

noncomputable def bulkCoordinateInsert {σ J : Type*}
    (base : σ → ℝ) (e : J ↪ σ) (y : J → ℝ) (i : σ) : ℝ :=
  if h : ∃ j, e j = i then y h.choose else base i

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Characters_TreeCoordinates
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Rational coordinates at a tree split

These identities are equations `tree-difference-ratio`, `tree-held-square`,
and `tree-p-square` of the manuscript. Nonzero hypotheses state precisely
that the reconstructed node is valid.
-/

namespace Ostmann

def reconstructedEntry {K : Type*} [Field K] (s sL sR u HL HR : K) : K :=
  (sL * HR - sR * HL) / (s * u)

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_FrequencyTreeSum
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Summing internal frequencies from the root downwards -/

namespace Ostmann

open scoped BigOperators

@[implicit_reducible] def FrequencyTree (A : Type) : ℕ → Type
  | 0 => A
  | n + 1 => A × FrequencyTree A n × FrequencyTree A n

@[implicit_reducible] def frequencyRoot {A : Type} : (n : ℕ) → FrequencyTree A n → A
  | 0, x => x
  | _ + 1, x => x.1

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_TransferFrequencyRange
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The actual finite range of a transferred frequency -/

namespace Ostmann

open scoped BigOperators Classical

/-- A fixed covering range for the signed output frequency. Zero is excluded
in the summand, so the same interval also works when the range is empty. -/
noncomputable def transferFrequencyRange (V : ℕ) : Finset ℤ := Finset.Icc (-(V : ℤ)) V

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_TransferHistoryUniqueness
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # A fixed top assignment and root frequency determine the full valid history -/

namespace Ostmann

/-- A state records the current actual labels. Child states insert the
reconstructed pivot and retain the corresponding branch. -/
structure TransferHistorySystem (State : Type*) where
  leftProduct : State → ℕ
  rightProduct : State → ℕ
  childBound : State → ℕ
  pivotBound : State → ℕ
  leftState : State → ℕ → State
  rightState : State → ℕ → State

/-- The conditions used by the rigidity argument are all original support
conditions or the strict product-range inequality. -/
structure ValidTransferNode {State : Type*} (sys : TransferHistorySystem State)
    (σ : State) (s v w : ℤ) (P : ℕ) : Prop where
  root_ne_zero : s ≠ 0
  root_unit : IsCoprime s (sys.rightProduct σ : ℤ)
  relation : v * sys.rightProduct σ - w * sys.leftProduct σ = s * P
  pivot_pos : 0 < P
  pivot_bound : P ≤ sys.pivotBound σ
  left_bound : v.natAbs ≤ sys.childBound σ
  right_bound : w.natAbs ≤ sys.childBound σ
  range_gap : 2 * sys.pivotBound σ * sys.childBound σ < sys.rightProduct σ
  pivot_unit : P.Coprime w.natAbs

def ValidTransferHistory {State : Type*} (sys : TransferHistorySystem State) :
    (n : ℕ) → State → FrequencyTree ℤ n → Prop
  | 0, _, _ => True
  | n + 1, σ, x => ∃ P : ℕ,
      ValidTransferNode sys σ x.1 (frequencyRoot n x.2.1) (frequencyRoot n x.2.2) P ∧
      ValidTransferHistory sys n (sys.leftState σ P) x.2.1 ∧
      ValidTransferHistory sys n (sys.rightState σ P) x.2.2

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Characters_MonotoneWeightVariation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Variation of the smooth factors on monotone argument intervals -/

namespace Ostmann

open scoped BigOperators

def clipRealInterval (lo hi x : ℝ) : ℝ := max lo (min hi x)

theorem clipRealInterval_bounds (lo hi x : ℝ) (h : lo ≤ hi) :
    lo ≤ clipRealInterval lo hi x ∧ clipRealInterval lo hi x ≤ hi := by
  exact ⟨le_max_left _ _, max_le h (min_le_left _ _)⟩

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Characters_PublishedBonami
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Published finite-cube hypercontractive input

A. Bonami, *Étude des coefficients de Fourier des fonctions de Lᵖ(G)*,
Annales de l'Institut Fourier 20 (1970), no. 2, 335–402,
Chapter III, Theorems 2–3, printed pp. 374–376.
DOI: 10.5802/aif.357; https://www.numdam.org/item/10.5802/aif.357.pdf .

`PublishedBonamiBound` is only the real finite Boolean-cube consequence with
p=2 and q=2l: applying the noise operator with multiplier
(2l-1)^(-card Q/2) gives this weighted even-moment inequality. This is an
explicit hypothesis, not a global axiom. No assertion about primes, Jacobi
symbols, translating residues or the target sumset is included in it.
-/

namespace Ostmann

open scoped BigOperators

noncomputable def rademacherMonomial {P : Finset ℕ} (Q : Finset P) (ε : P → Bool) : ℝ :=
  ∏ p ∈ Q, if ε p then 1 else -1

def PublishedBonamiBound : Prop :=
  ∀ (P : Finset ℕ) (l : ℕ), 0 < l → ∀ a : Finset P → ℝ,
    (Fintype.card (P → Bool) : ℝ)⁻¹ *
      ∑ ε : P → Bool, |∑ Q : Finset P, a Q * rademacherMonomial Q ε| ^ (2 * l) ≤
      (∑ Q : Finset P, ((2 * l - 1 : ℕ) : ℝ) ^ Q.card * (a Q) ^ 2) ^ l

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Characters_AdditiveFourier
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Probability-normalized additive Fourier identities

These finite identities provide the normalization used in Section 6.
Fourier inversion is the library's discrete Fourier inversion theorem.
-/

namespace Ostmann

open scoped BigOperators ComplexConjugate

/-- The additive Fourier transform with probability normalization. -/
noncomputable def additiveFourier {p : ℕ} [NeZero p]
    (f : ZMod p → ℂ) (a : ZMod p) : ℂ :=
  (p : ℂ)⁻¹ * ZMod.dft f a

theorem additiveFourier_apply {p : ℕ} [NeZero p] (f : ZMod p → ℂ) (a : ZMod p) :
    additiveFourier f a = (p : ℂ)⁻¹ *
      ∑ x : ZMod p, f x * ZMod.stdAddChar (-(x * a)) := by
  simp only [additiveFourier, ZMod.dft_apply, smul_eq_mul, mul_comm]

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Characters_CRTFourier
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Chinese remainder factorization of the finite Fourier transform -/

namespace Ostmann

open scoped BigOperators

theorem stdAddChar_mul_factor {m n : ℕ} [NeZero m] [NeZero n]
    (x : ZMod (m * n)) :
    ZMod.stdAddChar ((n : ZMod (m * n)) * x) =
      ZMod.stdAddChar ((ZMod.castHom (Nat.dvd_mul_right m n) (ZMod m)) x) := by
  obtain ⟨a, rfl⟩ := ZMod.intCast_surjective x
  rw [map_intCast]
  have he : (n : ZMod (m * n)) * (a : ZMod (m * n)) = ((n * a : ℤ) : ZMod (m * n)) := by
    push_cast
    rfl
  rw [he, ZMod.stdAddChar_coe, ZMod.stdAddChar_coe]
  congr 1
  push_cast
  have hn : (n : ℂ) ≠ 0 := by exact_mod_cast NeZero.ne n
  field_simp

theorem crt_fst {m n : ℕ} (h : m.Coprime n) (x : ZMod (m * n)) :
    ((ZMod.chineseRemainder h) x).1 =
      (ZMod.castHom (Nat.dvd_mul_right m n) (ZMod m)) x := by
  simp only [ZMod.chineseRemainder, RingEquiv.coe_mk, Equiv.coe_fn_mk,
    ZMod.castHom_apply, Prod.fst_zmod_cast]

theorem crt_snd {m n : ℕ} (h : m.Coprime n) (x : ZMod (m * n)) :
    ((ZMod.chineseRemainder h) x).2 =
      (ZMod.castHom (Nat.dvd_mul_left n m) (ZMod n)) x := by
  simp only [ZMod.chineseRemainder, RingEquiv.coe_mk, Equiv.coe_fn_mk,
    ZMod.castHom_apply, Prod.snd_zmod_cast]

theorem crt_stdAddChar {m n : ℕ} [NeZero m] [NeZero n]
    (h : m.Coprime n) (x : ZMod (m * n)) :
    ZMod.stdAddChar x =
      ZMod.stdAddChar ((n : ZMod m)⁻¹ * ((ZMod.chineseRemainder h) x).1) *
      ZMod.stdAddChar ((m : ZMod n)⁻¹ * ((ZMod.chineseRemainder h) x).2) := by
  let a : ZMod m := (n : ZMod m)⁻¹ * ((ZMod.chineseRemainder h) x).1
  let b : ZMod n := (m : ZMod n)⁻¹ * ((ZMod.chineseRemainder h) x).2
  have ha : IsUnit (n : ZMod m) := (ZMod.isUnit_iff_coprime n m).mpr h.symm
  have hb : IsUnit (m : ZMod n) := (ZMod.isUnit_iff_coprime m n).mpr h
  have hx : x = (n : ZMod (m * n)) * a.val + (m : ZMod (m * n)) * b.val := by
    apply (ZMod.chineseRemainder h).injective
    apply Prod.ext
    · rw [crt_fst, crt_fst]
      simp only [map_add, map_mul, map_natCast, ZMod.natCast_self, zero_mul, add_zero,
        ZMod.natCast_zmod_val]
      dsimp [a]
      rw [← mul_assoc, ZMod.mul_inv_of_unit _ ha, one_mul, crt_fst]
      rfl
    · rw [crt_snd, crt_snd]
      simp only [map_add, map_mul, map_natCast, ZMod.natCast_self, zero_mul, zero_add,
        ZMod.natCast_zmod_val]
      dsimp [b]
      rw [← mul_assoc, ZMod.mul_inv_of_unit _ hb, one_mul, crt_snd]
      rfl
  have hn : ZMod.stdAddChar ((m : ZMod (m * n)) * (b.val : ZMod (m * n))) =
      ZMod.stdAddChar b := by
    have he : (m : ZMod (m * n)) * (b.val : ZMod (m * n)) =
        ((m * b.val : ℕ) : ZMod (m * n)) := by push_cast; rfl
    calc
      _ = Complex.exp (2 * Real.pi * Complex.I * ((m * b.val : ℕ) : ℂ) / (m * n)) := by
        rw [he, ← Int.cast_natCast, ZMod.stdAddChar_coe]
        push_cast
        rfl
      _ = Complex.exp (2 * Real.pi * Complex.I * (b.val : ℂ) / n) := by
        congr 1
        push_cast
        have hm : (m : ℂ) ≠ 0 := by exact_mod_cast NeZero.ne m
        field_simp
      _ = ZMod.stdAddChar b := by
        simpa only [ZMod.stdAddChar_apply] using (ZMod.toCircle_apply b).symm
  change ZMod.stdAddChar x = ZMod.stdAddChar a * ZMod.stdAddChar b
  calc
    _ = ZMod.stdAddChar ((n : ZMod (m * n)) * (a.val : ZMod (m * n)) + (m : ZMod (m * n)) * (b.val : ZMod (m * n))) := by rw [hx]
    _ = _ := by
      rw [AddChar.map_add_eq_mul, stdAddChar_mul_factor, hn]
      simp only [map_natCast, ZMod.natCast_zmod_val]

/-- Probability normalization makes the coprime Fourier transform a product. -/
theorem additiveFourier_crt {m n : ℕ} [NeZero m] [NeZero n]
    (h : m.Coprime n) (f : ZMod m → ℂ) (g : ZMod n → ℂ) (u : ZMod (m * n)) :
    additiveFourier (fun x => f ((ZMod.chineseRemainder h) x).1 *
      g ((ZMod.chineseRemainder h) x).2) u =
      additiveFourier f ((n : ZMod m)⁻¹ * ((ZMod.chineseRemainder h) u).1) *
      additiveFourier g ((m : ZMod n)⁻¹ * ((ZMod.chineseRemainder h) u).2) := by
  let e := ZMod.chineseRemainder h
  have he (x : ZMod (m * n)) : ZMod.stdAddChar (-(x * u)) =
      ZMod.stdAddChar (-( (e x).1 * ((n : ZMod m)⁻¹ * (e u).1))) *
      ZMod.stdAddChar (-( (e x).2 * ((m : ZMod n)⁻¹ * (e u).2))) := by
    rw [crt_stdAddChar h]
    simp only [map_neg, map_mul]
    change ZMod.stdAddChar ((n : ZMod m)⁻¹ * -((e x).1 * (e u).1)) *
      ZMod.stdAddChar ((m : ZMod n)⁻¹ * -((e x).2 * (e u).2)) = _
    congr 2 <;> ring
  have hs : (∑ x : ZMod (m * n), f (e x).1 * g (e x).2 * ZMod.stdAddChar (-(x * u))) =
      (∑ a : ZMod m, f a * ZMod.stdAddChar (-(a * ((n : ZMod m)⁻¹ * (e u).1)))) *
      (∑ b : ZMod n, g b * ZMod.stdAddChar (-(b * ((m : ZMod n)⁻¹ * (e u).2)))) := by
    simp_rw [he]
    rw [← e.symm.bijective.sum_comp (fun x =>
      f (e x).1 * g (e x).2 *
      (ZMod.stdAddChar (-((e x).1 * ((n : ZMod m)⁻¹ * (e u).1))) *
       ZMod.stdAddChar (-((e x).2 * ((m : ZMod n)⁻¹ * (e u).2)))))]
    simp only [e.apply_symm_apply]
    rw [Fintype.sum_prod_type, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro a ha
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro b hb
    ring
  rw [additiveFourier_apply, hs, additiveFourier_apply, additiveFourier_apply,
    Nat.cast_mul, mul_inv]
  ring

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_ZeroDensity_DensityFourier
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The normalized Fourier transform of the actual centered density -/

namespace Ostmann

open scoped BigOperators

noncomputable def centeredDensity {q : ℕ} (S : Finset (ZMod q)) (x : ZMod q) : ℝ :=
  (if x ∈ S then 1 else 0) - (S.card : ℝ) / q

noncomputable def densityFourier {q : ℕ} [NeZero q] (f : ZMod q → ℂ) (a : ZMod q) : ℂ :=
  (Real.sqrt (q : ℝ) : ℂ) * additiveFourier f a

theorem centeredDensity_abs_le {q : ℕ} [NeZero q] (S : Finset (ZMod q)) (x : ZMod q) :
    |centeredDensity S x| ≤ 1 := by
  have hq : (0 : ℝ) < q := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne q)
  have hcard : (S.card : ℝ) ≤ q := by
    exact_mod_cast (show S.card ≤ q by simpa using Finset.card_le_card (Finset.subset_univ S))
  have hσ : (S.card : ℝ) / q ≤ 1 := (div_le_one hq).mpr hcard
  have hσ0 : 0 ≤ (S.card : ℝ) / q := by positivity
  unfold centeredDensity
  split <;> rw [abs_le] <;> constructor <;> linarith

theorem centeredDensity_sum {q : ℕ} [NeZero q] (S : Finset (ZMod q)) :
    ∑ x : ZMod q, centeredDensity S x = 0 := by
  classical
  have hq : (q : ℝ) ≠ 0 := by exact_mod_cast NeZero.ne q
  unfold centeredDensity
  rw [Finset.sum_sub_distrib]
  have hsum : (∑ x : ZMod q, if x ∈ S then (1 : ℝ) else 0) = S.card := by simp
  rw [hsum]
  simp only [Finset.sum_const, Finset.card_univ, ZMod.card, nsmul_eq_mul]
  field_simp
  ring

theorem densityFourier_centered_zero {q : ℕ} [NeZero q] (S : Finset (ZMod q)) :
    densityFourier (fun x => (centeredDensity S x : ℂ)) 0 = 0 := by
  simp only [densityFourier, additiveFourier_apply, mul_zero, neg_zero, AddChar.map_zero_eq_one, mul_one]
  have hsum : (∑ x : ZMod q, (centeredDensity S x : ℂ)) = 0 := by
    rw [← Complex.ofReal_sum, centeredDensity_sum, Complex.ofReal_zero]
  rw [hsum, mul_zero, mul_zero]

/-- Probability-normalized CRT Fourier factorization remains exact after
multiplication by the square root of the modulus. -/
theorem densityFourier_crt {m n : ℕ} [NeZero m] [NeZero n]
    (h : m.Coprime n) (f : ZMod m → ℂ) (g : ZMod n → ℂ) (u : ZMod (m * n)) :
    densityFourier (fun x => f ((ZMod.chineseRemainder h) x).1 *
      g ((ZMod.chineseRemainder h) x).2) u =
      densityFourier f ((n : ZMod m)⁻¹ * ((ZMod.chineseRemainder h) u).1) *
      densityFourier g ((m : ZMod n)⁻¹ * ((ZMod.chineseRemainder h) u).2) := by
  simp only [densityFourier, additiveFourier_crt h f g u, Nat.cast_mul,
    Real.sqrt_mul (Nat.cast_nonneg m), Complex.ofReal_mul]
  ring

/-- Each local centered Fourier transform vanishes at zero. The CRT product
therefore vanishes at every nonunit of the composite modulus. -/
theorem densityFourier_crt_nonunit {m n : ℕ} [NeZero m] [NeZero n]
    (h : m.Coprime n) (f : ZMod m → ℂ) (g : ZMod n → ℂ)
    (hf : ∀ x, ¬IsUnit x → densityFourier f x = 0)
    (hg : ∀ x, ¬IsUnit x → densityFourier g x = 0)
    (u : ZMod (m * n)) (hu : ¬IsUnit u) :
    densityFourier (fun x => f ((ZMod.chineseRemainder h) x).1 *
      g ((ZMod.chineseRemainder h) x).2) u = 0 := by
  rw [densityFourier_crt]
  by_cases h₁ : IsUnit ((n : ZMod m)⁻¹ * ((ZMod.chineseRemainder h) u).1)
  · have h₂ : ¬IsUnit ((m : ZMod n)⁻¹ * ((ZMod.chineseRemainder h) u).2) := by
      intro h₂
      have ha := isUnit_of_mul_isUnit_right h₁
      have hb := isUnit_of_mul_isUnit_right h₂
      obtain ⟨a, ha⟩ := ha.exists_right_inv
      obtain ⟨b, hb⟩ := hb.exists_right_inv
      have he : IsUnit ((ZMod.chineseRemainder h) u) :=
        IsUnit.of_mul_eq_one (a, b) (Prod.ext ha hb)
      have hh := he.map (ZMod.chineseRemainder h).symm.toMonoidHom
      change IsUnit ((ZMod.chineseRemainder h).symm ((ZMod.chineseRemainder h) u)) at hh
      exact hu (by simpa only [RingEquiv.symm_apply_apply] using hh)
    rw [hg _ h₂, mul_zero]
  · rw [hf _ h₁, zero_mul]

/-- This supplies the local hypotheses for every prime factor of `L`. -/
theorem densityFourier_centered_prime_nonunit {p : ℕ} [Fact p.Prime]
    (S : Finset (ZMod p)) (x : ZMod p) (hx : ¬IsUnit x) :
    densityFourier (fun y => (centeredDensity S y : ℂ)) x = 0 := by
  have hx0 : x = 0 := by simpa only [isUnit_iff_ne_zero, not_not] using hx
  rw [hx0, densityFourier_centered_zero]

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_ZeroDensity_DensityCRTProduct
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Constructing the density product and its Fourier hypotheses -/

namespace Ostmann

open scoped BigOperators

/-- A bounded density product with its proved local-mean-zero consequence. -/
structure DensityCRTData (q : ℕ) [NeZero q] where
  value : ZMod q → ℂ
  norm_le_one : ∀ x, ‖value x‖ ≤ 1
  fourier_nonunit : ∀ x, ¬IsUnit x → densityFourier value x = 0

namespace DensityCRTData

noncomputable def one : DensityCRTData 1 where
  value := fun _ => 1
  norm_le_one := by intro x; simp
  fourier_nonunit := by
    intro x hx
    exact (hx (by have h : x = 1 := Subsingleton.elim _ _; rw [h]; exact isUnit_one)).elim

noncomputable def prime (p : ℕ) [Fact p.Prime] (S : Finset (ZMod p)) : DensityCRTData p where
  value := fun x => (centeredDensity S x : ℂ)
  norm_le_one := by
    intro x
    simpa only [Complex.norm_real, Real.norm_eq_abs] using centeredDensity_abs_le S x
  fourier_nonunit := densityFourier_centered_prime_nonunit S

noncomputable def mul {m n : ℕ} [NeZero m] [NeZero n]
    (h : m.Coprime n) (A : DensityCRTData m) (B : DensityCRTData n) : DensityCRTData (m * n) where
  value := fun x => A.value ((ZMod.chineseRemainder h) x).1 * B.value ((ZMod.chineseRemainder h) x).2
  norm_le_one := by
    intro x
    rw [norm_mul]
    exact (mul_le_mul (A.norm_le_one _) (B.norm_le_one _) (norm_nonneg _) zero_le_one).trans_eq (mul_one 1)
  fourier_nonunit := densityFourier_crt_nonunit h A.value B.value A.fourier_nonunit B.fourier_nonunit

end DensityCRTData

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_ZeroDensity_DensityCorrelation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The prime-by-prime correlation bound for centered densities -/

namespace Ostmann

open scoped BigOperators ComplexConjugate

/-- Which of the two squarefree divisors contains a prime of their union. -/
inductive CorrelationSide where
  | left
  | right
  | both

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_ZeroDensity_PrimePartialSummation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Partial summation for the reciprocal-prime progression measure

This is the bridge from the published theta estimate (Montgomery--Vaughan,
Corollary 11.20, equations (11.32) and (11.34)) to the interval weights used
in Section 8. The conversion itself is proved here.
-/

namespace Ostmann

open scoped BigOperators
open MeasureTheory

noncomputable def primeProgressionLog (q a n : ℕ) : ℝ :=
  if n.Prime ∧ Nat.ModEq q n a then Real.log n else 0

noncomputable def primeProgressionTheta (q a : ℕ) (x : ℝ) : ℝ :=
  ∑ n ∈ Finset.Icc 0 ⌊x⌋₊, primeProgressionLog q a n

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_ZeroDensity_ThetaMainTerm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The exceptional theta term and its harmonic density

Differentiating the published theta main term cancels its factor `β`.
The corresponding harmonic density is retained exactly.
-/

namespace Ostmann

open MeasureTheory

noncomputable def thetaMainTerm (φ χ β x : ℝ) : ℝ :=
  (x - χ * x ^ β / β) / φ

noncomputable def thetaMainDensity (φ χ β x : ℝ) : ℝ :=
  (1 - χ * x ^ (β - 1)) / φ

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_ZeroDensity_DirichletLogDerivativeBound
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # A uniform Euler-series bound for real arguments

This part uses proved Mathlib theorems only: the continued zeta pole, the
Euler logarithmic derivative, and the norm bound for Dirichlet characters.
-/

namespace Ostmann

open scoped BigOperators ComplexOrder
open Complex LSeries

theorem residue_one_eq_vonMangoldt :
    ArithmeticFunction.vonMangoldt.residueClass (0 : ZMod 1) = ArithmeticFunction.vonMangoldt := by
  funext n
  simp [ArithmeticFunction.vonMangoldt.residueClass, Subsingleton.elim (n : ZMod 1) 0]

theorem exists_vonMangoldt_series_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ s : ℝ, 1 < s → s ≤ 2 →
      ‖LSeries (fun n => (ArithmeticFunction.vonMangoldt n : ℂ)) (s : ℂ)‖ ≤ 1 / (s - 1) + C := by
  let F := ArithmeticFunction.vonMangoldt.LFunctionResidueClassAux (0 : ZMod 1)
  have hcont : ContinuousOn (fun s : ℝ => F (s : ℂ)) (Set.Icc 1 2) := by
    apply ArithmeticFunction.vonMangoldt.continuousOn_LFunctionResidueClassAux (0 : ZMod 1) |>.comp
      Complex.continuous_ofReal.continuousOn
    intro s hs
    exact hs.1
  obtain ⟨M, hM⟩ := isCompact_Icc.exists_bound_of_continuousOn hcont
  refine ⟨|M| + 1, by positivity, ?_⟩
  intro s hs hs2
  have hunit : IsUnit (0 : ZMod 1) := by
    rw [Subsingleton.elim (0 : ZMod 1) 1]
    exact isUnit_one
  have heq := ArithmeticFunction.vonMangoldt.eqOn_LFunctionResidueClassAux hunit
    (show (s : ℂ) ∈ {z : ℂ | 1 < z.re} by exact hs)
  rw [residue_one_eq_vonMangoldt] at heq
  simp only [Nat.totient_one, Nat.cast_one, inv_one] at heq
  have he : LSeries (fun n => (ArithmeticFunction.vonMangoldt n : ℂ)) (s : ℂ) =
      F (s : ℂ) + 1 / ((s : ℂ) - 1) := by
    change F (s : ℂ) = _ at heq
    rw [heq]
    ring
  have hnorm : ‖1 / ((s : ℂ) - 1)‖ = 1 / (s - 1) := by
    rw [← Complex.ofReal_one, ← Complex.ofReal_sub, ← Complex.ofReal_div,
      Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by positivity)]
  rw [he]
  have hb := norm_add_le (F (s : ℂ)) (1 / ((s : ℂ) - 1))
  rw [hnorm] at hb
  have hg := hM s ⟨hs.le, hs2⟩
  have hMabs := le_abs_self M
  linarith

theorem dirichlet_logDerivative_le_vonMangoldt {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (s : ℝ) (hs : 1 < s) :
    ‖deriv (DirichletCharacter.LFunction χ) (s : ℂ) /
      DirichletCharacter.LFunction χ (s : ℂ)‖ ≤
      ‖LSeries (fun n => (ArithmeticFunction.vonMangoldt n : ℂ)) (s : ℂ)‖ := by
  let a : ℕ → ℂ := fun n => (ArithmeticFunction.vonMangoldt n : ℂ)
  have hs' : 1 < (s : ℂ).re := hs
  have ha : LSeriesSummable a (s : ℂ) := ArithmeticFunction.LSeriesSummable_vonMangoldt hs'
  have ht := χ.LSeriesSummable_twist_vonMangoldt hs'
  have he := χ.LSeries_twist_vonMangoldt_eq hs'
  rw [← χ.deriv_LFunction_eq_deriv_LSeries hs', ← χ.LFunction_eq_LSeries hs'] at he
  have hn (n : ℕ) : ‖LSeries.term (fun n => χ n * a n) (s : ℂ) n‖ ≤
      ‖LSeries.term a (s : ℂ) n‖ := by
    apply LSeries.norm_term_le
    rw [norm_mul]
    exact mul_le_of_le_one_left (norm_nonneg _) (χ.norm_le_one _)
  have hr (n : ℕ) : ‖LSeries.term a (s : ℂ) n‖ = (LSeries.term a (s : ℂ) n).re := by
    have hp : (0 : ℂ) ≤ a n := by
      change (0 : ℂ) ≤ (ArithmeticFunction.vonMangoldt n : ℂ)
      exact_mod_cast ArithmeticFunction.vonMangoldt_nonneg (n := n)
    have hh := congrArg Complex.re (Complex.eq_coe_norm_of_nonneg (LSeries.term_nonneg hp s))
    simpa only [Complex.ofReal_re] using hh.symm
  calc
    _ = ‖LSeries (fun n => χ n * a n) (s : ℂ)‖ := by
      change LSeries (fun n => χ n * a n) (s : ℂ) = _ at he
      rw [he]
      simp only [neg_div, norm_neg]
    _ ≤ ∑' n, ‖LSeries.term (fun n => χ n * a n) (s : ℂ) n‖ := norm_tsum_le_tsum_norm ht.norm
    _ ≤ ∑' n, ‖LSeries.term a (s : ℂ) n‖ := ht.norm.tsum_le_tsum hn ha.norm
    _ = (LSeries a (s : ℂ)).re := by simp_rw [hr]; exact (Complex.re_tsum ha).symm
    _ ≤ ‖LSeries a (s : ℂ)‖ := Complex.re_le_norm _

theorem exists_dirichlet_logDerivative_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q)
      (s : ℝ), 1 < s → s ≤ 2 →
      ‖deriv (DirichletCharacter.LFunction χ) (s : ℂ) /
        DirichletCharacter.LFunction χ (s : ℂ)‖ ≤ 1 / (s - 1) + C := by
  obtain ⟨C, hC, hbound⟩ := exists_vonMangoldt_series_bound
  refine ⟨C, hC, ?_⟩
  intro q hq χ s hs hs2
  exact (dirichlet_logDerivative_le_vonMangoldt χ s hs).trans (hbound s hs hs2)

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_SmoothPolynomialWeight
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Finite products of the smooth factors appearing in a history

Profiles are clipped to their prescribed argument ranges. This leaves their
values unchanged on the retained range and requires no continuity of the sharp
range indicator; those indicators are separate functions of the root cell.
-/

namespace Ostmann

open scoped BigOperators

structure ClippedPolynomialFactor where
  polynomial : Polynomial ℝ
  profile : ℝ → ℂ
  lo : ℝ
  hi : ℝ
  bound : ℝ
  lip : ℝ
  lo_le_hi : lo ≤ hi
  bound_nonneg : 0 ≤ bound
  lip_nonneg : 0 ≤ lip
  norm_le : ∀ x ∈ Set.Icc lo hi, ‖profile x‖ ≤ bound
  lipschitz : ∀ x ∈ Set.Icc lo hi, ∀ y ∈ Set.Icc lo hi,
    ‖profile x - profile y‖ ≤ lip * |x - y|

noncomputable def ClippedPolynomialFactor.value (f : ClippedPolynomialFactor) (x : ℝ) : ℂ :=
  f.profile (clipRealInterval f.lo f.hi (f.polynomial.eval x))

theorem ClippedPolynomialFactor.value_of_mem (f : ClippedPolynomialFactor) (x : ℝ)
    (hx : f.polynomial.eval x ∈ Set.Icc f.lo f.hi) :
    f.value x = f.profile (f.polynomial.eval x) := by
  simp only [value, clipRealInterval, min_eq_right hx.2, max_eq_right hx.1]

theorem ClippedPolynomialFactor.norm_value (f : ClippedPolynomialFactor) (x : ℝ) :
    ‖f.value x‖ ≤ f.bound :=
  f.norm_le _ (clipRealInterval_bounds f.lo f.hi _ f.lo_le_hi)

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Characters_PolynomialWeightPair
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The actual off-diagonal product of two polynomial weights -/

namespace Ostmann

open scoped BigOperators ComplexConjugate Classical

noncomputable def ClippedPolynomialFactor.conjugate (f : ClippedPolynomialFactor) :
    ClippedPolynomialFactor where
  polynomial := f.polynomial
  profile := fun x => conj (f.profile x)
  lo := f.lo
  hi := f.hi
  bound := f.bound
  lip := f.lip
  lo_le_hi := f.lo_le_hi
  bound_nonneg := f.bound_nonneg
  lip_nonneg := f.lip_nonneg
  norm_le := fun x hx => by simpa only [Complex.norm_conj] using f.norm_le x hx
  lipschitz := fun x hx y hy => by
    rw [← map_sub, Complex.norm_conj]
    exact f.lipschitz x hx y hy

@[simp] theorem ClippedPolynomialFactor.conjugate_value (f : ClippedPolynomialFactor) (x : ℝ) :
    f.conjugate.value x = conj (f.value x) := rfl

def pairedPolynomialKeep {t u : ℕ} (keep : (Fin t → Bool) → Bool)
    (keep' : (Fin u → Bool) → Bool) (c : Fin (t + u) → Bool) : Bool :=
  keep (fun i => c (Fin.castAdd u i)) && keep' (fun i => c (Fin.natAdd t i))

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Characters_PolynomialRangeGuards
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The actual argument-range cutoffs as polynomial inequalities -/

namespace Ostmann

open scoped BigOperators Classical

noncomputable def polynomialRangeBounds {n : ℕ} (F : Fin n → ClippedPolynomialFactor) :
    Fin (n + n) → Polynomial ℝ :=
  Fin.append (fun i => (F i).polynomial - Polynomial.C (F i).lo)
    (fun i => Polynomial.C (F i).hi - (F i).polynomial)

noncomputable def polynomialRangeKeep (n : ℕ) (code : Fin (n + n) → Bool) : Bool :=
  decide (∀ i : Fin n, code (Fin.castAdd n i) = true ∧ code (Fin.natAdd n i) = true)

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_GiantReversalRows
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Coefficient rows of the giant reversals

At a reversal one current giant is retained and the other becomes
`(v * Hminus - w * Hplus) / u`, with all three coefficients units modulo
the internal prime. The two current giants remain independent linear
forms in the top giants, so every subsequent numerator is a nonzero row.
-/

namespace Ostmann

/-- Coefficients of the two current giants in the two top giants. -/
@[ext] structure GiantRows (R : Type*) where
  a : R
  b : R
  c : R
  d : R

namespace GiantRows

variable {R : Type*} [CommRing R]

def identity : GiantRows R := ⟨1, 0, 0, 1⟩

def det (T : GiantRows R) : R := T.a * T.d - T.b * T.c

def eval (T : GiantRows R) (x y : R) : R × R :=
  (T.a * x + T.b * y, T.c * x + T.d * y)

/-- `left = true` retains the first giant; `false` retains the second. -/
def reverse (T : GiantRows R) (left : Bool) (v w u : Rˣ) : GiantRows R :=
  if left then
    ⟨T.a, T.b, (u⁻¹ : Rˣ) * ((v : R) * T.c - (w : R) * T.a),
      (u⁻¹ : Rˣ) * ((v : R) * T.d - (w : R) * T.b)⟩
  else
    ⟨(u⁻¹ : Rˣ) * ((v : R) * T.c - (w : R) * T.a),
      (u⁻¹ : Rˣ) * ((v : R) * T.d - (w : R) * T.b), T.c, T.d⟩

end GiantRows

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Characters_PolynomialGiantRows
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Clearing denominators along the giant histories

The five integer polynomials below represent both coefficient rows with a
common denominator. Each reversal uses only multiplication and subtraction;
their degree grows by at most the degree of the new slot data.
-/

namespace Ostmann

noncomputable section

structure PolynomialGiantRows (σ : Type*) where
  rows : GiantRows (MvPolynomial σ ℤ)
  denominator : MvPolynomial σ ℤ

namespace PolynomialGiantRows

variable {σ : Type*}

def identity : PolynomialGiantRows σ := ⟨GiantRows.identity, 1⟩

def reverse (T : PolynomialGiantRows σ) (left : Bool) (v w u : MvPolynomial σ ℤ) :
    PolynomialGiantRows σ :=
  if left then
    ⟨⟨u * T.rows.a, u * T.rows.b, v * T.rows.c - w * T.rows.a,
      v * T.rows.d - w * T.rows.b⟩, T.denominator * u⟩
  else
    ⟨⟨v * T.rows.c - w * T.rows.a, v * T.rows.d - w * T.rows.b,
      u * T.rows.c, u * T.rows.d⟩, T.denominator * u⟩

/-- Normalized coefficients after evaluating all small prime variables. -/
def normalized {K : Type*} [Field K] (T : PolynomialGiantRows σ)
    (φ : MvPolynomial σ ℤ →+* K) : GiantRows K :=
  ⟨φ T.rows.a / φ T.denominator, φ T.rows.b / φ T.denominator,
    φ T.rows.c / φ T.denominator, φ T.rows.d / φ T.denominator⟩

/-- A simultaneous degree bound for the four cleared coefficients and denominator. -/
def DegreeLE (T : PolynomialGiantRows σ) (d : ℕ) : Prop :=
  T.rows.a.totalDegree ≤ d ∧ T.rows.b.totalDegree ≤ d ∧
    T.rows.c.totalDegree ≤ d ∧ T.rows.d.totalDegree ≤ d ∧ T.denominator.totalDegree ≤ d

end PolynomialGiantRows

structure PolynomialReversal (σ : Type*) where
  left : Bool
  v : MvPolynomial σ ℤ
  w : MvPolynomial σ ℤ
  u : MvPolynomial σ ℤ

end

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_HistoryPolynomialSpecialization
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Actual cleared history polynomials with one prime left variable -/

namespace Ostmann

open scoped BigOperators Classical

noncomputable def specializeHistoryVariable {σ : Type*}
    (a : σ → ℝ) (i : σ) : MvPolynomial σ ℤ →+* Polynomial ℝ :=
  MvPolynomial.eval₂Hom (Polynomial.C.comp (Int.castRingHom ℝ))
    (fun j => if j = i then Polynomial.X else Polynomial.C (a j))

noncomputable def normalizedHistoryPolynomial {σ : Type*}
    (P : MvPolynomial σ ℤ) (a : σ → ℝ) (i : σ) (d : ℝ) : Polynomial ℝ :=
  Polynomial.C d⁻¹ * specializeHistoryVariable a i P

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Preliminaries_PrimeDivisors
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Prime-divisor budget in the collision argument

A distinct pair of integers at distance at most `X` contributes at most
`log X` to the sum of `log p` over primes at which it collides. This is the
elementary counting step behind the larger-sieve use in §§2–3.
-/

namespace Ostmann

open scoped BigOperators

/-- Distinct prime divisors of a positive integer have total logarithmic
weight at most the logarithm of that integer. -/
theorem sum_log_prime_divisors_le (P : Finset ℕ) {n : ℕ} (hn : 0 < n)
    (hprime : ∀ p ∈ P, p.Prime) (hdiv : ∀ p ∈ P, p ∣ n) :
    ∑ p ∈ P, Real.log (p : ℝ) ≤ Real.log (n : ℝ) := by
  have hsub : P ⊆ n.primeFactors := by
    intro p hp
    exact Nat.mem_primeFactors.mpr ⟨hprime p hp, hdiv p hp, Nat.ne_of_gt hn⟩
  have hprod_dvd : (∏ p ∈ P, p) ∣ n :=
    (Finset.prod_dvd_prod_of_subset P n.primeFactors id hsub).trans (Nat.prod_primeFactors_dvd n)
  have hprod_pos : 0 < ∏ p ∈ P, p := Finset.prod_pos (fun p hp => (hprime p hp).pos)
  have hprod_le : (∏ p ∈ P, p) ≤ n := Nat.le_of_dvd hn hprod_dvd
  rw [← Real.log_prod (fun p hp => by exact_mod_cast (hprime p hp).ne_zero),
    ← Nat.cast_prod]
  exact Real.log_le_log (by exact_mod_cast hprod_pos) (by exact_mod_cast hprod_le)

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Characters_PolynomialGiantTests
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Cleared coefficient and minor tests for the giant lines -/

namespace Ostmann

noncomputable section

structure PolynomialGiantLine (σ : Type*) where
  a : MvPolynomial σ ℤ
  b : MvPolynomial σ ℤ
  denominator : MvPolynomial σ ℤ

/-- The numerator `v * Hminus - w * Hplus`, with the ancestor denominator
still cleared. The current compensation variable does not occur here. -/
def PolynomialGiantRows.numeratorLine {σ : Type*} (T : PolynomialGiantRows σ)
    (v w : MvPolynomial σ ℤ) : PolynomialGiantLine σ :=
  ⟨v * T.rows.c - w * T.rows.a, v * T.rows.d - w * T.rows.b, T.denominator⟩

namespace PolynomialGiantLine

variable {σ : Type*}

def normalized {K : Type*} [Field K] (L : PolynomialGiantLine σ)
    (φ : MvPolynomial σ ℤ →+* K) : K × K :=
  (φ L.a / φ L.denominator, φ L.b / φ L.denominator)

def minor (L M : PolynomialGiantLine σ) : MvPolynomial σ ℤ := L.a * M.b - L.b * M.a

end PolynomialGiantLine

end

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Characters_PolynomialValueBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Size of the cleared arithmetic tests at actual prime values

A uniform bound on the slot values gives an explicit bound on every cleared
coefficient and denominator. This avoids any assumed bound on the height of
newly constructed polynomials.
-/

namespace Ostmann

namespace PolynomialGiantRows

variable {σ : Type*}

def ValueLE (T : PolynomialGiantRows σ) (φ : MvPolynomial σ ℤ →+* ℝ) (H : ℝ) : Prop :=
  |φ T.rows.a| ≤ H ∧ |φ T.rows.b| ≤ H ∧ |φ T.rows.c| ≤ H ∧
    |φ T.rows.d| ≤ H ∧ |φ T.denominator| ≤ H

end PolynomialGiantRows

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Characters_PolynomialVariableSupport
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Variables absent from the arithmetic coefficient tests

Clearing ancestor denominators introduces only variables from the existing
slots. In particular a compensation type omitted from those slots stays absent
from every coefficient polynomial and every minor formed from them.
-/

namespace Ostmann

namespace PolynomialGiantRows

variable {σ : Type*}

def UsesOnly (T : PolynomialGiantRows σ) (S : Finset σ) : Prop :=
  T.rows.a.vars ⊆ S ∧ T.rows.b.vars ⊆ S ∧ T.rows.c.vars ⊆ S ∧
    T.rows.d.vars ⊆ S ∧ T.denominator.vars ⊆ S

end PolynomialGiantRows

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_HistoryResidueGate
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Constructing the residue gate for cleared integer history tests -/

namespace Ostmann

open scoped Classical

def smallDivisionTest (N d : ℤ) (s : ℕ) : Prop :=
  d ∣ N ∧ IsUnit ((N / d : ℤ) : ZMod s)

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_ClearedHistoryPivot
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Constructed integer numerators for the recursive pivot substitutions -/

namespace Ostmann

open scoped BigOperators Classical

structure ClearedHistoryValue (σ : Type*) where
  numerator : MvPolynomial σ ℤ
  denominator : ℤ
  denominator_ne_zero : denominator ≠ 0

namespace ClearedHistoryValue

variable {σ : Type*}

noncomputable def ofVariable (i : σ) : ClearedHistoryValue σ := ⟨MvPolynomial.X i, 1, one_ne_zero⟩

noncomputable def constant (a : ℤ) : ClearedHistoryValue σ := ⟨MvPolynomial.C a, 1, one_ne_zero⟩

noncomputable def prod {I : Type*} (S : Finset I) (f : I → ClearedHistoryValue σ) :
    ClearedHistoryValue σ :=
  ⟨∏ i ∈ S, (f i).numerator, ∏ i ∈ S, (f i).denominator,
    Finset.prod_ne_zero_iff.mpr (fun i _ => (f i).denominator_ne_zero)⟩

/-- This is exactly `(v * right - w * left) / s`, with integer clearing of
all previously inserted denominators. -/
noncomputable def pivot (left right : ClearedHistoryValue σ) (v w s : ℤ) (hs : s ≠ 0) :
    ClearedHistoryValue σ :=
  ⟨MvPolynomial.C (v * left.denominator) * right.numerator -
      MvPolynomial.C (w * right.denominator) * left.numerator,
    s * left.denominator * right.denominator,
    mul_ne_zero (mul_ne_zero hs left.denominator_ne_zero) right.denominator_ne_zero⟩

noncomputable def eval (F : ClearedHistoryValue σ) (x : σ → ℚ) : ℚ :=
  MvPolynomial.eval₂ (Int.castRingHom ℚ) x F.numerator / F.denominator

end ClearedHistoryValue

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_ClearedHistoryBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Degree and value control survives clearing every history denominator -/

namespace Ostmann.ClearedHistoryValue

open scoped BigOperators Classical

variable {σ : Type*}

def Bounded (F : ClearedHistoryValue σ) (x : σ → ℝ) (H : ℝ) : Prop :=
  |MvPolynomial.eval₂ (Int.castRingHom ℝ) x F.numerator| ≤ H ∧ |(F.denominator : ℝ)| ≤ H

end Ostmann.ClearedHistoryValue

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_HistoryFormula
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The actual product-and-pivot formulas of a fixed arithmetic history -/

namespace Ostmann

inductive HistoryFormula (σ : Type*) where
  | prime (i : σ)
  | external (z : ℤ)
  | product (left right : HistoryFormula σ)
  | solve (left right : HistoryFormula σ) (v w s : ℤ) (hs : s ≠ 0)

namespace HistoryFormula

variable {σ : Type*}

noncomputable def cleared : HistoryFormula σ → ClearedHistoryValue σ
  | .prime i => .ofVariable i
  | .external z => .constant z
  | .product f g => .prod Finset.univ (fun b : Bool => if b then f.cleared else g.cleared)
  | .solve f g v w s hs => .pivot f.cleared g.cleared v w s hs

def cost : HistoryFormula σ → ℕ
  | .prime _ => 1
  | .external _ => 1
  | .product f g => f.cost + g.cost
  | .solve f g _ _ _ _ => f.cost + g.cost + 2

def frequencies : HistoryFormula σ → List ℤ
  | .prime _ => []
  | .external _ => []
  | .product f g => f.frequencies ++ g.frequencies
  | .solve f g _ _ s _ => s :: (f.frequencies ++ g.frequencies)

def InputsBounded (R : ℝ) : HistoryFormula σ → Prop
  | .prime _ => True
  | .external z => |(z : ℝ)| ≤ R
  | .product f g => f.InputsBounded R ∧ g.InputsBounded R
  | .solve f g v w s _ => f.InputsBounded R ∧ g.InputsBounded R ∧
      |(v : ℝ)| ≤ R ∧ |(w : ℝ)| ≤ R ∧ |(s : ℝ)| ≤ R

end HistoryFormula

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_HistorySubstitution
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Substitution constructs the actual rational expressions of a reversed history -/

namespace Ostmann.HistoryFormula

variable {σ τ : Type*}

noncomputable def value (F : HistoryFormula σ) (x : σ → ℚ) : ℚ := F.cleared.eval x

def bind (f : σ → HistoryFormula τ) : HistoryFormula σ → HistoryFormula τ
  | .prime i => f i
  | .external z => .external z
  | .product l r => .product (l.bind f) (r.bind f)
  | .solve l r v w s hs => .solve (l.bind f) (r.bind f) v w s hs

noncomputable def listProduct : List (HistoryFormula σ) → HistoryFormula σ
  | [] => .external 1
  | f :: fs => .product f (listProduct fs)

end Ostmann.HistoryFormula

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_IntegerHistoryReconstruction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The cleared formulas evaluate to the actual integer pivot reconstructions -/

namespace Ostmann

open scoped Classical

structure HistoryPivotStep (σ : Type*) where
  target : σ
  left : List σ
  right : List σ
  v : ℤ
  w : ℤ
  s : ℤ
  s_ne_zero : s ≠ 0

namespace HistoryPivotStep

variable {σ : Type*}

noncomputable def formula (step : HistoryPivotStep σ) : HistoryFormula σ :=
  .solve (.listProduct (step.left.map .prime)) (.listProduct (step.right.map .prime))
    step.v step.w step.s step.s_ne_zero

def numerator (step : HistoryPivotStep σ) (x : σ → ℤ) : ℤ :=
  step.v * (step.right.map x).prod - step.w * (step.left.map x).prod

def Valid (step : HistoryPivotStep σ) (x : σ → ℤ) : Prop := step.s ∣ step.numerator x

noncomputable def applyInteger (step : HistoryPivotStep σ) (x : σ → ℤ) : σ → ℤ :=
  Function.update x step.target (step.numerator x / step.s)

end HistoryPivotStep

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_ReconstructionIntegrality
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Every original integer-divisibility gate is a cleared polynomial test -/

namespace Ostmann

open scoped Classical

def HistoryFormula.IntegralAt {σ : Type*} (F : HistoryFormula σ) (x : σ → ℤ) : Prop :=
  ∃ y : ℤ, F.value (fun i => (x i : ℚ)) = y

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_FiniteCellMeans
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Means on the actual fibers of a finite partition -/

namespace Ostmann

open scoped BigOperators Classical

noncomputable def finiteCellMass (P : Finset ℕ) (label : ℕ → ℕ) (μ : ℕ → ℝ) (h : ℕ) : ℝ :=
  ∑ p ∈ P.filter (fun p => label p = h), μ p

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_PrimeCellPartitionConstruction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Constructing the actual prime log/residue partition

The fiber identities used by the joint comparison follow from separated
log intervals and residue classes. They are not additional distribution
hypotheses.
-/

namespace Ostmann

open scoped BigOperators Classical

noncomputable def primeLogCellSet (q a : ℕ) (s t : ℝ) : Finset ℕ :=
  (Finset.Ioc ⌊Real.exp s⌋₊ ⌊Real.exp t⌋₊).filter
    (fun p => p.Prime ∧ Nat.ModEq q p a)

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_PrimeLogCellMeans
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Actual prime log cells and their means -/

namespace Ostmann

open Filter
open scoped BigOperators Classical

/-- The cell `(h,h+1]` containing the logarithm of a prime. -/
noncomputable def primeLogIndex (p : ℕ) : ℕ := ⌈Real.log (p : ℝ)⌉₊ - 1

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_PrimeCellWordPriors
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The original harmonic law on each selected prime cell -/

namespace Ostmann

open Filter
open scoped BigOperators Classical

noncomputable def primeCellWordPrior (P : Finset ℕ) (h : ℕ) (p : P) : ℝ :=
  if primeLogIndex p = h then
    ((p : ℕ) : ℝ)⁻¹ / finiteCellMass P primeLogIndex (fun p => (p : ℝ)⁻¹) h else 0

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_HarmonicWordPriors
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Harmonic laws for all word roles on one common prime sample space -/

namespace Ostmann

open scoped BigOperators Classical

noncomputable def primeSubsetPrior (P Q : Finset ℕ) (p : P) : ℝ :=
  if (p : ℕ) ∈ Q then (p : ℝ)⁻¹ / (∑ q ∈ Q, (q : ℝ)⁻¹) else 0

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_FullHistoryGuards
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Fourier ranges and all additional history inequalities in one exact guard -/

namespace Ostmann

open scoped BigOperators Classical

noncomputable def fullHistoryPolynomials {n t : ℕ} (F : Fin n → ClippedPolynomialFactor)
    (H : Fin t → Polynomial ℝ) : Fin ((n + n) + t) → Polynomial ℝ :=
  Fin.append (polynomialRangeBounds F) H

noncomputable def fullHistoryKeep {n t : ℕ} (keep : (Fin t → Bool) → Bool) :
    (Fin ((n + n) + t) → Bool) → Bool :=
  pairedPolynomialKeep (polynomialRangeKeep n) keep

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_ConstructedHistoryGuards
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Exact range and residue guards for the reconstructed original pivots -/

namespace Ostmann

open scoped BigOperators Classical

noncomputable def formulaPolynomial {σ : Type*} (F : HistoryFormula σ)
    (a : σ → ℝ) (coord : σ) : Polynomial ℝ :=
  normalizedHistoryPolynomial F.cleared.numerator a coord F.cleared.denominator

noncomputable def formulaRangePolynomials {σ : Type*} {n : ℕ}
    (F : Fin n → HistoryFormula σ) (a : σ → ℝ) (coord : σ) (lo hi : Fin n → ℝ) :
    Fin (n + n) → Polynomial ℝ :=
  Fin.append (fun i => formulaPolynomial (F i) a coord - Polynomial.C (lo i))
    (fun i => Polynomial.C (hi i) - formulaPolynomial (F i) a coord)

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Characters_NormalizedFourierProfile
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Bounds for the actual normalized level-zero Fourier profile -/

namespace Ostmann

open scoped SchwartzMap

theorem abs_inv_sub_inv_le_of_one_le (x y : ℝ) (hx : 1 ≤ x) (hy : 1 ≤ y) :
    |x⁻¹ - y⁻¹| ≤ |x - y| := by
  have hx0 : 0 < x := by linarith
  have hy0 : 0 < y := by linarith
  have he : x⁻¹ - y⁻¹ = (y - x) / (x * y) := by field_simp
  rw [he, abs_div, abs_of_pos (mul_pos hx0 hy0), abs_sub_comm]
  exact div_le_self (abs_nonneg _) (by nlinarith [mul_nonneg (sub_nonneg.mpr hx) (sub_nonneg.mpr hy)])

theorem abs_sqrt_sub_sqrt_le_of_one_le (x y : ℝ) (hx : 1 ≤ x) (hy : 1 ≤ y) :
    |Real.sqrt x - Real.sqrt y| ≤ |x - y| := by
  have hsx : 1 ≤ Real.sqrt x := Real.one_le_sqrt.mpr hx
  have hsy : 1 ≤ Real.sqrt y := Real.one_le_sqrt.mpr hy
  have he : (Real.sqrt x - Real.sqrt y) * (Real.sqrt x + Real.sqrt y) = x - y := by
    nlinarith [Real.sq_sqrt (by linarith : 0 ≤ x), Real.sq_sqrt (by linarith : 0 ≤ y)]
  have hab : |Real.sqrt x - Real.sqrt y| * (Real.sqrt x + Real.sqrt y) = |x - y| := by
    rw [← abs_of_nonneg (show 0 ≤ Real.sqrt x + Real.sqrt y by positivity), ← abs_mul, he]
  nlinarith [abs_nonneg (Real.sqrt x - Real.sqrt y)]

theorem abs_inv_sqrt_sub_inv_sqrt_le (x y : ℝ) (hx : 1 ≤ x) (hy : 1 ≤ y) :
    |(Real.sqrt x)⁻¹ - (Real.sqrt y)⁻¹| ≤ |x - y| :=
  (abs_inv_sub_inv_le_of_one_le _ _ (Real.one_le_sqrt.mpr hx) (Real.one_le_sqrt.mpr hy)).trans
    (abs_sqrt_sub_sqrt_le_of_one_le x y hx hy)

noncomputable def normalizedFourierProfile (ψ : ℝ → ℂ) (v z : ℝ) : ℂ :=
  Complex.ofReal ((Real.sqrt z)⁻¹) * ψ (-v * z⁻¹)

theorem normalizedFourierProfile_norm (ψ : ℝ → ℂ) (v B z : ℝ)
    (hψ : ∀ t, ‖ψ t‖ ≤ B) (hz : 1 ≤ z) :
    ‖normalizedFourierProfile ψ v z‖ ≤ B := by
  have hs : 0 ≤ (Real.sqrt z)⁻¹ := inv_nonneg.mpr (Real.sqrt_nonneg _)
  have hs1 : (Real.sqrt z)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (Real.one_le_sqrt.mpr hz)
  rw [normalizedFourierProfile, norm_mul, Complex.norm_real, Real.norm_of_nonneg hs]
  exact (mul_le_mul hs1 (hψ _) (norm_nonneg _) (by norm_num)).trans_eq (one_mul B)

theorem normalizedFourierProfile_lipschitz (ψ : ℝ → ℂ) (v B D x y : ℝ)
    (hψ : ∀ t, ‖ψ t‖ ≤ B) (hD : 0 ≤ D)
    (hlip : ∀ s t, ‖ψ s - ψ t‖ ≤ D * |s - t|) (hx : 1 ≤ x) (hy : 1 ≤ y) :
    ‖normalizedFourierProfile ψ v x - normalizedFourierProfile ψ v y‖ ≤
      (B + D * |v|) * |x - y| := by
  have hxroot : 0 ≤ (Real.sqrt x)⁻¹ := inv_nonneg.mpr (Real.sqrt_nonneg _)
  have hxroot1 : (Real.sqrt x)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (Real.one_le_sqrt.mpr hx)
  have harg : |-v * x⁻¹ - -v * y⁻¹| ≤ |v| * |x - y| := by
    rw [← mul_sub, abs_mul, abs_neg]
    exact mul_le_mul_of_nonneg_left (abs_inv_sub_inv_le_of_one_le x y hx hy) (abs_nonneg _)
  have hψdiff : ‖ψ (-v * x⁻¹) - ψ (-v * y⁻¹)‖ ≤ D * |v| * |x - y| :=
    (hlip _ _).trans (by simpa only [mul_assoc] using mul_le_mul_of_nonneg_left harg hD)
  have he : normalizedFourierProfile ψ v x - normalizedFourierProfile ψ v y =
      Complex.ofReal ((Real.sqrt x)⁻¹) * (ψ (-v * x⁻¹) - ψ (-v * y⁻¹)) +
      (Complex.ofReal ((Real.sqrt x)⁻¹) - Complex.ofReal ((Real.sqrt y)⁻¹)) * ψ (-v * y⁻¹) := by
    unfold normalizedFourierProfile
    ring
  rw [he]
  apply (norm_add_le _ _).trans
  rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_of_nonneg hxroot,
    ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
  have h1 := mul_le_mul hxroot1 hψdiff (norm_nonneg _) (by norm_num : (0 : ℝ) ≤ 1)
  have h2 := mul_le_mul (abs_inv_sqrt_sub_inv_sqrt_le x y hx hy) (hψ (-v * y⁻¹))
    (norm_nonneg _) (abs_nonneg _)
  nlinarith only [h1, h2]

/-- A Schwartz profile supplies its bounded derivative and Lipschitz constant
from existing library seminorms, with no analytic input left as an assumption. -/
theorem schwartz_profile_bounds (ψ : 𝓢(ℝ, ℂ)) :
    (∀ t, ‖ψ t‖ ≤ SchwartzMap.seminorm ℝ 0 0 ψ) ∧
    (∀ s t, ‖ψ s - ψ t‖ ≤ SchwartzMap.seminorm ℝ 0 1 ψ * |s - t|) := by
  refine ⟨fun t => ψ.norm_le_seminorm ℝ t, ?_⟩
  intro s t
  have hb (x : ℝ) : ‖deriv ψ x‖ ≤ SchwartzMap.seminorm ℝ 0 1 ψ := by
    simpa only [pow_zero, one_mul, iteratedDeriv_one] using ψ.le_seminorm' ℝ 0 1 x
  have hd : ∀ x ∈ (Set.univ : Set ℝ), DifferentiableAt ℝ ψ x :=
    fun x _ => (ψ.smooth 1).differentiable (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top) x
  have ht := convex_univ.norm_image_sub_le_of_norm_deriv_le hd (fun x _ => hb x)
    (Set.mem_univ t) (Set.mem_univ s)
  simpa only [Real.norm_eq_abs] using ht

theorem schwartz_profile_lip_nonneg (ψ : 𝓢(ℝ, ℂ)) : 0 ≤ SchwartzMap.seminorm ℝ 0 1 ψ := by
  apply (norm_nonneg (deriv ψ 0)).trans
  simpa only [pow_zero, one_mul, iteratedDeriv_one] using ψ.le_seminorm' ℝ 0 1 0

/-- Concrete clipped factor for the Fourier weight on its declared M/X range. -/
noncomputable def fourierPolynomialFactor (P : Polynomial ℝ) (ψ : 𝓢(ℝ, ℂ))
    (v lo hi : ℝ) (hlo : 1 ≤ lo) (hhi : lo ≤ hi) : ClippedPolynomialFactor where
  polynomial := P
  profile := normalizedFourierProfile ψ v
  lo := lo
  hi := hi
  bound := SchwartzMap.seminorm ℝ 0 0 ψ
  lip := SchwartzMap.seminorm ℝ 0 0 ψ + SchwartzMap.seminorm ℝ 0 1 ψ * |v|
  lo_le_hi := hhi
  bound_nonneg := (norm_nonneg (ψ 0)).trans (ψ.norm_le_seminorm ℝ 0)
  lip_nonneg := add_nonneg ((norm_nonneg (ψ 0)).trans (ψ.norm_le_seminorm ℝ 0))
    (mul_nonneg (schwartz_profile_lip_nonneg ψ) (abs_nonneg v))
  norm_le := fun x hx => normalizedFourierProfile_norm ψ v _ x
    (schwartz_profile_bounds ψ).1 (hlo.trans hx.1)
  lipschitz := fun x hx y hy => normalizedFourierProfile_lipschitz ψ v _ _ x y
    (schwartz_profile_bounds ψ).1 (schwartz_profile_lip_nonneg ψ)
    (schwartz_profile_bounds ψ).2 (hlo.trans hx.1) (hlo.trans hy.1)

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_HistoryFourierPolynomial
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Fourier weights of reconstructed histories in the long prime variable -/

namespace Ostmann

open scoped SchwartzMap Classical

noncomputable def historyFourierFactor {σ : Type*} (P : MvPolynomial σ ℤ)
    (a : σ → ℝ) (i : σ) (d X : ℝ) (ψ : 𝓢(ℝ, ℂ))
    (v lo hi : ℝ) (hlo : 1 ≤ lo) (hhi : lo ≤ hi) : ClippedPolynomialFactor :=
  fourierPolynomialFactor (normalizedHistoryPolynomial P a i (d * X)) ψ v lo hi hlo hhi

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_HistoryFormulaFourier
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Fourier factors of the constructed history formulas, with derived budgets -/

namespace Ostmann

open scoped BigOperators SchwartzMap Classical

noncomputable def formulaFourierFactors {σ : Type*} {n : ℕ}
    (F : Fin n → HistoryFormula σ) (a : σ → ℝ) (coord : σ)
    (X : Fin n → ℝ) (ψ : 𝓢(ℝ, ℂ)) (v lo hi : Fin n → ℝ)
    (hlo : ∀ j, 1 ≤ lo j) (hhi : ∀ j, lo j ≤ hi j) : Fin n → ClippedPolynomialFactor :=
  fun j => historyFourierFactor (F j).cleared.numerator a coord
    (F j).cleared.denominator (X j) ψ (v j) (lo j) (hi j) (hlo j) (hhi j)

noncomputable def formulaFourierBudget {n : ℕ} (ψ : 𝓢(ℝ, ℂ)) (v lo hi : Fin n → ℝ) : ℝ :=
  ∏ j, (2 * SchwartzMap.seminorm ℝ 0 0 ψ +
    (SchwartzMap.seminorm ℝ 0 0 ψ + SchwartzMap.seminorm ℝ 0 1 ψ * |v j|) * (hi j - lo j))

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_GlobalHistoryCoefficient
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The global history coefficient and its exact one-variable polynomial form -/

namespace Ostmann

open scoped BigOperators SchwartzMap Classical

noncomputable def HistoryFormula.realValue {σ : Type*} (F : HistoryFormula σ) (x : σ → ℤ) : ℝ :=
  MvPolynomial.eval₂ (Int.castRingHom ℝ) (fun i => (x i : ℝ)) F.cleared.numerator /
    F.cleared.denominator

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_TransferredPivotSubstitution
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Eliminating the extended integer by its exact signed quotient -/

namespace Ostmann

open scoped BigOperators ComplexConjugate Classical

/-- The positive integer retained by a transferred frequency, when its
integrality and range indicators hold. -/
def reconstructedPivot (N s : ℤ) : ℕ := (N / s).toNat

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_RecursiveTransferWeight
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The recursive weight with its actual reconstructed integer pivots -/

namespace Ostmann

open scoped BigOperators Classical

def historyPivot {State : Type*} (sys : TransferHistorySystem State)
    (σ : State) (s v w : ℤ) : ℕ :=
  reconstructedPivot (v * sys.rightProduct σ - w * sys.leftProduct σ) s

/-- The node indicator contains precisely the arithmetic support used for
history rigidity. Other original range/bin cutoffs are carried by `cutoff`. -/
noncomputable def recursiveTransferWeight {State : Type*} (sys : TransferHistorySystem State)
    (leaf : State → ℤ → ℂ) (cutoff : State → ℤ → ℤ → ℤ → ℝ) :
    (n : ℕ) → State → FrequencyTree ℤ n → ℂ
  | 0, σ, v => leaf σ v
  | n + 1, σ, t =>
      let v := frequencyRoot n t.2.1
      let w := frequencyRoot n t.2.2
      let P := historyPivot sys σ t.1 v w
      if ValidTransferNode sys σ t.1 v w P then
        (cutoff σ t.1 v w : ℂ) *
          recursiveTransferWeight sys leaf cutoff n (sys.leftState σ P) t.2.1 *
          star (recursiveTransferWeight sys leaf cutoff n (sys.rightState σ P) t.2.2)
      else 0

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_ZeroDensity_TreeDensity
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Iterating the elementary tree density estimate

A split plan allows the remaining unit parameters to depend on every
previous split coordinate. The bound is uniform over those choices.
The separate rational-coordinate lemmas identify the manuscript's tree
with this inverse-square split law on valid ancestor data.
-/

namespace Ostmann

open scoped BigOperators

/-- Parameters for an ordered binary tree, with adaptive descendant data. -/
def BinarySplitPlan (U : Type) : ℕ → Type
  | 0 => Unit
  | n + 1 => U × (U → BinarySplitPlan U n) × (U → BinarySplitPlan U n)

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Tree_RationalTree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Recursive rational tree data

The product coefficient is an index of the data type. At every split,
its child indices encode exactly the consistency conditions on the
fixed constants in `src36`.
-/

namespace Ostmann

open scoped BigOperators

inductive RationalTreeData (U : Type*) [CommGroup U] : ℕ → U → Type _
  | leaf (s C : U) : RationalTreeData U 0 C
  | node {n : ℕ} (s CL CR u : U)
      (left : RationalTreeData U n (u * CL))
      (right : RationalTreeData U n (u * CR)) : RationalTreeData U (n + 1) (CL * CR)

@[implicit_reducible] def RationalTreeData.frequency {U : Type*} [CommGroup U] {n : ℕ} {C : U} :
    RationalTreeData U n C → U
  | .leaf s _ => s
  | .node s _ _ _ _ _ => s

noncomputable def rationalTreeArgument {p : ℕ} [Fact p.Prime]
    (s C D XL XR P : (ZMod p)ˣ) : (ZMod p)ˣ := s / (D * XL * XR * C * P)

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Tree_RationalTreeLeaves
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The rational tree under independent uniform leaf sampling -/

namespace Ostmann

open scoped BigOperators

/-- The manuscript's diagram value, permitting arbitrary conjugation choices at the leaves. -/
noncomputable def rationalTreeAmplitude {p : ℕ} [Fact p.Prime]
    (g : ZMod p → ℂ) (D : (ZMod p)ˣ) :
    {n : ℕ} → {C : (ZMod p)ˣ} → RationalTreeData (ZMod p)ˣ n C →
      (ZMod p)ˣ → (ZMod p)ˣ → TreeLeafTuple Bool n → TreeLeafTuple (ZMod p)ˣ n → ℂ
  | _, _, .leaf s C, XL, XR, c, m =>
    match (c : Bool) with
    | true => star (g (rationalTreeArgument s C D XL XR m))
    | false => g (rationalTreeArgument s C D XL XR m)
  | n + 1, _, .node s CL CR u left right, XL, XR, c, ab =>
    let HL : (ZMod p)ˣ := XL * CL * treeLeafProduct n ab.1
    let HR : (ZMod p)ˣ := XR * CR * treeLeafProduct n ab.2
    let v := reconstructedEntry (s : ZMod p) left.frequency right.frequency u HL HR
    if hv : v = 0 then 0 else
      rationalTreeAmplitude g D left (Units.mk0 v hv) XL c.1 ab.1 *
        rationalTreeAmplitude g D right (Units.mk0 v hv) XR c.2 ab.2

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Characters_TreeLeafIndex
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Labeled leaves and bottom quartets of a full binary tree -/

namespace Ostmann

open scoped BigOperators

def TreeLeafIndex : ℕ → Type
  | 0 => Unit
  | n + 1 => TreeLeafIndex n ⊕ TreeLeafIndex n

instance treeLeafIndexFintype (n : ℕ) : Fintype (TreeLeafIndex n) := by
  induction n with
  | zero => exact inferInstanceAs (Fintype Unit)
  | succ n ih => exact @instFintypeSum _ _ ih ih

def treeLeafTupleEquiv (A : Type*) : (n : ℕ) →
    TreeLeafTuple A n ≃ (TreeLeafIndex n → A)
  | 0 =>
    { toFun := fun a _ => a
      invFun := fun f => f ()
      left_inv := fun _ => rfl
      right_inv := fun f => by funext u; cases u; rfl }
  | n + 1 => (Equiv.prodCongr (treeLeafTupleEquiv A n) (treeLeafTupleEquiv A n)).trans
      (Equiv.sumArrowEquivProdArrow (TreeLeafIndex n) (TreeLeafIndex n) A).symm

theorem card_treeLeafIndex (n : ℕ) : Fintype.card (TreeLeafIndex n) = 2 ^ n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change Fintype.card (TreeLeafIndex n ⊕ TreeLeafIndex n) = _
    rw [Fintype.card_sum, ih, pow_succ]
    omega

noncomputable def indexedRationalAmplitude {p : ℕ} [Fact p.Prime]
    (g : ZMod p → ℂ) (D : (ZMod p)ˣ) {n : ℕ} {C : (ZMod p)ˣ}
    (T : RationalTreeData (ZMod p)ˣ n C) (XL XR : (ZMod p)ˣ)
    (c : TreeLeafTuple Bool n) (m : TreeLeafIndex n → (ZMod p)ˣ) : ℂ :=
  rationalTreeAmplitude g D T XL XR c ((treeLeafTupleEquiv (ZMod p)ˣ n).symm m)

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Characters_MixedFourier
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Symmetries of the mixed Fourier bound

Conjugation and multiplication of the field argument by a unit preserve
both the energy hypothesis and the mixed character/Fourier bound. These
are the orientation changes used by the bottom pairs.
-/

namespace Ostmann

open scoped BigOperators ComplexConjugate

def MixedFourierBound {p : ℕ} [Fact p.Prime] (g : ZMod p → ℂ) (ε : ℝ) : Prop :=
  ∀ (χ : MulChar (ZMod p) ℂ) (a : ZMod p),
    ‖additiveFourier (fun x => g x * χ x) a‖ ≤ ε

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Tree_RationalQuartetValue
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Bottom quartets in the actual rational-tree recursion -/

namespace Ostmann

open scoped BigOperators

@[simp] theorem rationalTreeFrequency_cast {U : Type*} [CommGroup U]
    {n : ℕ} {C C' : U} (h : C = C') (T : RationalTreeData U n C) :
    (h ▸ T).frequency = T.frequency := by
  cases h
  rfl

@[simp] theorem rationalTreeAmplitude_cast {p : ℕ} [Fact p.Prime]
    (g : ZMod p → ℂ) (D : (ZMod p)ˣ) {n : ℕ} {C C' : (ZMod p)ˣ}
    (h : C = C') (T : RationalTreeData (ZMod p)ˣ n C)
    (XL XR : (ZMod p)ˣ) (c : TreeLeafTuple Bool n) (m : TreeLeafTuple (ZMod p)ˣ n) :
    rationalTreeAmplitude g D (h ▸ T) XL XR c m =
      rationalTreeAmplitude g D T XL XR c m := by
  cases h
  rfl

/-- The fixed data above a bottom quartet; its four leaf products remain free. -/
structure RationalQuartetData (U : Type*) [CommGroup U] where
  s : U
  sL : U
  sR : U
  u : U
  CL : U
  CR : U
  s₁ : U
  s₂ : U
  s₃ : U
  s₄ : U
  uL : U
  uR : U
  C₁ : U
  C₂ : U
  C₃ : U
  C₄ : U
  left_product : C₁ * C₂ = u * CL
  right_product : C₃ * C₄ = u * CR

def RationalQuartetData.tree {U : Type*} [CommGroup U] (Q : RationalQuartetData U) :
    RationalTreeData U 2 (Q.CL * Q.CR) :=
  .node Q.s Q.CL Q.CR Q.u
    (Q.left_product ▸ (.node Q.sL Q.C₁ Q.C₂ Q.uL
      (.leaf Q.s₁ (Q.uL * Q.C₁)) (.leaf Q.s₂ (Q.uL * Q.C₂))))
    (Q.right_product ▸ (.node Q.sR Q.C₃ Q.C₄ Q.uR
      (.leaf Q.s₃ (Q.uR * Q.C₃)) (.leaf Q.s₄ (Q.uR * Q.C₄))))

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Characters_QuartetProductFibers
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Independent product fibers at the bottom quartet level -/

namespace Ostmann

open scoped BigOperators

@[implicit_reducible] def quartetBlockTupleEquiv (A : Type*) : (n : ℕ) →
    TreeLeafTuple A (n + 2) ≃ TreeLeafTuple (TreeLeafTuple A 2) n
  | 0 => Equiv.refl _
  | n + 1 => Equiv.prodCongr (quartetBlockTupleEquiv A n) (quartetBlockTupleEquiv A n)

def quartetBlockEquiv (A : Type*) (n : ℕ) :
    TreeLeafTuple A (n + 2) ≃ (TreeLeafIndex n → TreeLeafTuple A 2) :=
  (quartetBlockTupleEquiv A n).trans (treeLeafTupleEquiv (TreeLeafTuple A 2) n)

def quartetProducts {U : Type*} [CommGroup U] (n : ℕ)
    (m : TreeLeafTuple U (n + 2)) : TreeLeafIndex n → U :=
  fun i => treeLeafProduct 2 (quartetBlockEquiv U n m i)

abbrev QuartetProductFiber (U : Type*) [CommGroup U] (n : ℕ) (P : TreeLeafIndex n → U) :=
  {m : TreeLeafTuple U (n + 2) // quartetProducts n m = P}

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_MovingGiantTree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The moving-giant arithmetic in Section 8.1

The integer constants record actual products of regular small entries. At a
reversal, the sampled compensation product `u` is inserted into both children:
their constants are `u * CL` and `u * CR`. The pivot is reconstructed over the
integers first, and only its giant factor is passed to either child.
-/

namespace Ostmann
open scoped Classical ComplexConjugate

inductive MovingGiantTree : ℕ → ℕ → Type
  | leaf (s : ℤ) (C : ℕ) : MovingGiantTree 0 C
  | node {n : ℕ} (s : ℤ) (CL CR u : ℕ)
      (left : MovingGiantTree n (u * CL))
      (right : MovingGiantTree n (u * CR)) : MovingGiantTree (n + 1) (CL * CR)

@[implicit_reducible] def MovingGiantTree.frequency :
    {n C : ℕ} → MovingGiantTree n C → ℤ
  | _, _, .leaf s _ => s
  | _, _, .node s _ _ _ _ _ => s

def movingGiantPivot (s v w : ℤ) (CL CR u XL XR ML MR : ℕ) : ℕ :=
  reconstructedPivot (v * ((XR * CR * MR : ℕ) : ℤ) -
    w * ((XL * CL * ML : ℕ) : ℤ)) s / u

def MovingGiantTree.UnitsAt (q : ℕ) : {n C : ℕ} → MovingGiantTree n C → Prop
  | _, _, .leaf s C => (s : ZMod q) ≠ 0 ∧ (C : ZMod q) ≠ 0
  | _, _, .node s CL CR u left right =>
      (s : ZMod q) ≠ 0 ∧ (CL : ZMod q) ≠ 0 ∧ (CR : ZMod q) ≠ 0 ∧
      (u : ZMod q) ≠ 0 ∧ left.UnitsAt q ∧ right.UnitsAt q

def TreeNaturalLift {q : ℕ} : (n : ℕ) →
    TreeLeafTuple ℕ n → TreeLeafTuple (ZMod q)ˣ n → Prop
  | 0, x, y => ((show ℕ from x) : ZMod q) = (show (ZMod q)ˣ from y)
  | n + 1, x, y => TreeNaturalLift n x.1 y.1 ∧ TreeNaturalLift n x.2 y.2

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_RecursiveNodeExpansion
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The exact preorder list of reconstructed arithmetic tests -/

namespace Ostmann

open scoped Classical

structure ReconstructedTransferNode (State : Type*) where
  state : State
  root : ℤ
  left : ℤ
  right : ℤ

namespace ReconstructedTransferNode

noncomputable def pivot {State : Type*} (sys : TransferHistorySystem State)
    (node : ReconstructedTransferNode State) : ℕ :=
  historyPivot sys node.state node.root node.left node.right

def Valid {State : Type*} (sys : TransferHistorySystem State)
    (node : ReconstructedTransferNode State) : Prop :=
  ValidTransferNode sys node.state node.root node.left node.right (node.pivot sys)

end ReconstructedTransferNode

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_BranchingHistoryReplay
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Ostmann

open scoped Classical

inductive BranchingWordHistory (σ : Type*) where
  | leaf (word : List σ)
  | node (step : HistoryPivotStep σ) (left right : BranchingWordHistory σ)

namespace BranchingWordHistory

variable {σ : Type*}

def Valid : BranchingWordHistory σ → (σ → ℤ) → Prop
  | .leaf _, _ => True
  | .node step left right, x =>
      step.Valid x ∧ left.Valid (step.applyInteger x) ∧ right.Valid (step.applyInteger x)

def flipSigned {α : Type*} (z : Bool × α) : Bool × α := (!z.1, z.2)

noncomputable def updatedFormulas (step : HistoryPivotStep σ) (env : σ → HistoryFormula σ) :
    σ → HistoryFormula σ :=
  Function.update env step.target (step.formula.bind env)

noncomputable def formulaLeaves : BranchingWordHistory σ → (σ → HistoryFormula σ) →
    List (Bool × HistoryFormula σ)
  | .leaf word, env => [(true, HistoryFormula.listProduct (word.map env))]
  | .node step left right, env =>
      left.formulaLeaves (updatedFormulas step env) ++
        (right.formulaLeaves (updatedFormulas step env)).map flipSigned

noncomputable def pivotFormulas : BranchingWordHistory σ → (σ → HistoryFormula σ) →
    List (HistoryFormula σ)
  | .leaf _, _ => []
  | .node step left right, env =>
      step.formula.bind env ::
        (left.pivotFormulas (updatedFormulas step env) ++
          right.pivotFormulas (updatedFormulas step env))

/-- Counts use the original branching structure, independent of assignments. -/
def leafCount : BranchingWordHistory σ → ℕ
  | .leaf _ => 1
  | .node _ left right => left.leafCount + right.leafCount

theorem formulaLeaves_length (history : BranchingWordHistory σ) (env : σ → HistoryFormula σ) :
    (history.formulaLeaves env).length = history.leafCount := by
  induction history generalizing env with
  | leaf word => rfl
  | node step left right hl hr => simp only [formulaLeaves, List.length_append, List.length_map, hl, hr, leafCount]

end BranchingWordHistory
end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_WordTransferTemplate
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The concrete transfer system of word products and reconstructed pivots -/

namespace Ostmann

open scoped Classical

universe u

structure WordTransferNode (σ : Type u) where
  target : σ
  left : List σ
  right : List σ
  childBound : ℕ
  pivotBound : ℕ

inductive WordTransferTemplate (σ : Type u) : ℕ → Type u where
  | leaf (word : List σ) : WordTransferTemplate σ 0
  | node {n : ℕ} (data : WordTransferNode σ)
      (left right : WordTransferTemplate σ n) : WordTransferTemplate σ (n + 1)

abbrev WordTransferState (σ : Type u) := Σ n : ℕ, WordTransferTemplate σ n × (σ → ℕ)

def WordTransferTemplate.state {σ : Type u} {n : ℕ}
    (template : WordTransferTemplate σ n) (x : σ → ℕ) : WordTransferState σ := ⟨n, template, x⟩

noncomputable def wordTransferLeft {σ : Type u} : WordTransferState σ → ℕ
  | ⟨0, _, _⟩ => 1
  | ⟨_ + 1, .node d _ _, x⟩ => (d.left.map x).prod

noncomputable def wordTransferRight {σ : Type u} : WordTransferState σ → ℕ
  | ⟨0, _, _⟩ => 1
  | ⟨_ + 1, .node d _ _, x⟩ => (d.right.map x).prod

noncomputable def wordTransferChildBound {σ : Type u} : WordTransferState σ → ℕ
  | ⟨0, _, _⟩ => 0
  | ⟨_ + 1, .node d _ _, _⟩ => d.childBound

noncomputable def wordTransferPivotBound {σ : Type u} : WordTransferState σ → ℕ
  | ⟨0, _, _⟩ => 0
  | ⟨_ + 1, .node d _ _, _⟩ => d.pivotBound

noncomputable def wordTransferLeftState {σ : Type u} : WordTransferState σ → ℕ → WordTransferState σ
  | ⟨0, t, x⟩, _ => ⟨0, t, x⟩
  | ⟨n + 1, .node d l _, x⟩, P => ⟨n, l, Function.update x d.target P⟩

noncomputable def wordTransferRightState {σ : Type u} : WordTransferState σ → ℕ → WordTransferState σ
  | ⟨0, t, x⟩, _ => ⟨0, t, x⟩
  | ⟨n + 1, .node d _ r, x⟩, P => ⟨n, r, Function.update x d.target P⟩

noncomputable def wordTransferSystem (σ : Type u) : TransferHistorySystem (WordTransferState σ) where
  leftProduct := wordTransferLeft
  rightProduct := wordTransferRight
  childBound := wordTransferChildBound
  pivotBound := wordTransferPivotBound
  leftState := wordTransferLeftState
  rightState := wordTransferRightState

def NonzeroInternalFrequencies : (n : ℕ) → FrequencyTree ℤ n → Prop
  | 0, _ => True
  | n + 1, t => t.1 ≠ 0 ∧ NonzeroInternalFrequencies n t.2.1 ∧ NonzeroInternalFrequencies n t.2.2

def wordTransferStep {σ : Type u} (d : WordTransferNode σ)
    (s v w : ℤ) (hs : s ≠ 0) : HistoryPivotStep σ where
  target := d.target
  left := d.left
  right := d.right
  s := s
  v := v
  w := w
  s_ne_zero := hs

noncomputable def WordTransferTemplate.branching {σ : Type u} :
    {n : ℕ} → WordTransferTemplate σ n → (t : FrequencyTree ℤ n) →
      NonzeroInternalFrequencies n t → BranchingWordHistory σ
  | 0, .leaf word, _, _ => .leaf word
  | n + 1, .node d l r, t, ht =>
      .node (wordTransferStep d t.1 (frequencyRoot n t.2.1) (frequencyRoot n t.2.2) ht.1)
        (l.branching t.2.1 ht.2.1) (r.branching t.2.2 ht.2.2)

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_WordTransferCounts
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Exact expression counts for the concrete transfer template -/

namespace Ostmann.WordTransferTemplate

variable {σ : Type*} {n : ℕ}

theorem branching_leafCount (template : WordTransferTemplate σ n)
    (t : FrequencyTree ℤ n) (hn : NonzeroInternalFrequencies n t) :
    (template.branching t hn).leafCount = 2 ^ n := by
  induction template with
  | leaf word => rfl
  | @node n d l r hl hr =>
    simp only [branching, BranchingWordHistory.leafCount, hl, hr]
    rw [pow_succ]
    omega

theorem branching_leafFormulas_length (template : WordTransferTemplate σ n)
    (t : FrequencyTree ℤ n) (hn : NonzeroInternalFrequencies n t) (env : σ → HistoryFormula σ) :
    ((template.branching t hn).formulaLeaves env).length = 2 ^ n := by
  rw [BranchingWordHistory.formulaLeaves_length, branching_leafCount]

end Ostmann.WordTransferTemplate

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_WeightedWordLeaves
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The literal frequency and polynomial of every reconstructed Fourier leaf -/

namespace Ostmann

open scoped Classical

structure WeightedWordLeaf (σ : Type*) where
  positive : Bool
  frequency : ℤ
  formula : HistoryFormula σ

namespace WeightedWordLeaf

def flip {σ : Type*} (z : WeightedWordLeaf σ) : WeightedWordLeaf σ :=
  ⟨!z.positive, z.frequency, z.formula⟩

def toSignedFormula {σ : Type*} (z : WeightedWordLeaf σ) : Bool × HistoryFormula σ :=
  (z.positive, z.formula)

noncomputable def evaluate {σ : Type*} (a : σ → ℚ) (z : WeightedWordLeaf σ) : Bool × ℤ × ℚ :=
  (z.positive, z.frequency, z.formula.value a)

end WeightedWordLeaf

noncomputable def WordTransferTemplate.weightedLeaves {σ : Type*} :
    {n : ℕ} → WordTransferTemplate σ n → (t : FrequencyTree ℤ n) →
      NonzeroInternalFrequencies n t → (σ → HistoryFormula σ) → List (WeightedWordLeaf σ)
  | 0, .leaf word, v, _, env => [⟨true, v, HistoryFormula.listProduct (word.map env)⟩]
  | n + 1, .node d l r, t, ht, env =>
      let step := wordTransferStep d t.1 (frequencyRoot n t.2.1) (frequencyRoot n t.2.2) ht.1
      l.weightedLeaves t.2.1 ht.2.1 (BranchingWordHistory.updatedFormulas step env) ++
        (r.weightedLeaves t.2.2 ht.2.2 (BranchingWordHistory.updatedFormulas step env)).map WeightedWordLeaf.flip

theorem weightedWordLeaf_flip_projection {σ : Type*} (l : List (WeightedWordLeaf σ)) :
    (l.map WeightedWordLeaf.flip).map WeightedWordLeaf.toSignedFormula =
      (l.map WeightedWordLeaf.toSignedFormula).map BranchingWordHistory.flipSigned := by
  simp only [List.map_map]
  rfl

theorem WordTransferTemplate.weightedLeaves_projection {σ : Type*} {n : ℕ}
    (template : WordTransferTemplate σ n) (t : FrequencyTree ℤ n)
    (hn : NonzeroInternalFrequencies n t) (env : σ → HistoryFormula σ) :
    (template.weightedLeaves t hn env).map WeightedWordLeaf.toSignedFormula =
      (template.branching t hn).formulaLeaves env := by
  induction template generalizing env with
  | leaf word => rfl
  | @node n d l r hl hr =>
    simp only [weightedLeaves, branching, BranchingWordHistory.formulaLeaves,
      List.map_append, weightedWordLeaf_flip_projection, hl, hr]

theorem WordTransferTemplate.weightedLeaves_length {σ : Type*} {n : ℕ}
    (template : WordTransferTemplate σ n) (t : FrequencyTree ℤ n)
    (hn : NonzeroInternalFrequencies n t) (env : σ → HistoryFormula σ) :
    (template.weightedLeaves t hn env).length = 2 ^ n := by
  have he := congrArg List.length (template.weightedLeaves_projection t hn env)
  rw [List.length_map, template.branching_leafFormulas_length t hn env] at he
  exact he

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_WordTransferFormulaBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Derived polynomial sizes for the concrete fixed-depth word transfer -/

namespace Ostmann.WordTransferTemplate

open scoped Classical

variable {σ : Type*}

def WordsBounded (B : ℕ) : {n : ℕ} → WordTransferTemplate σ n → Prop
  | 0, .leaf word => word.length + 1 ≤ B
  | _ + 1, .node d l r => d.left.length + d.right.length + 4 ≤ B ∧
      l.WordsBounded B ∧ r.WordsBounded B

end Ostmann.WordTransferTemplate

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_WordTransferGuard
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Exact polynomial support of one original arithmetic transfer node -/

namespace Ostmann

open scoped Classical

noncomputable def HistoryFormula.integerValue {σ : Type*} (F : HistoryFormula σ) (x : σ → ℤ) : ℤ :=
  MvPolynomial.eval₂Hom (RingHom.id ℤ) x F.cleared.numerator / F.cleared.denominator

structure WordTransferGuard (σ : Type*) where
  pivot : HistoryFormula σ
  rightProduct : HistoryFormula σ
  root : ℤ
  left : ℤ
  right : ℤ
  childBound : ℕ
  pivotBound : ℕ

noncomputable def WordTransferGuard.ValidAt {σ : Type*} (g : WordTransferGuard σ) (x : σ → ℤ) : Prop :=
  smallDivisionTest (MvPolynomial.eval₂Hom (RingHom.id ℤ) x g.pivot.cleared.numerator)
    g.pivot.cleared.denominator g.right.natAbs ∧
  smallDivisionTest (MvPolynomial.eval₂Hom (RingHom.id ℤ) x g.rightProduct.cleared.numerator)
    g.rightProduct.cleared.denominator g.root.natAbs ∧
  1 ≤ g.pivot.realValue x ∧ g.pivot.realValue x ≤ g.pivotBound ∧
  (2 * g.pivotBound * g.childBound : ℕ) < g.rightProduct.realValue x ∧
  g.left.natAbs ≤ g.childBound ∧ g.right.natAbs ≤ g.childBound

noncomputable def wordTransferGuard {σ : Type*} (d : WordTransferNode σ)
    (s v w : ℤ) (hs : s ≠ 0) (env : σ → HistoryFormula σ) : WordTransferGuard σ where
  pivot := (wordTransferStep d s v w hs).formula.bind env
  rightProduct := HistoryFormula.listProduct (d.right.map env)
  root := s
  left := v
  right := w
  childBound := d.childBound
  pivotBound := d.pivotBound

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_WordTransferGuardReplay
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # All branching support tests are the original recursive arithmetic support -/

namespace Ostmann

open scoped Classical

noncomputable def WordTransferTemplate.guards {σ : Type*} :
    {n : ℕ} → WordTransferTemplate σ n → (t : FrequencyTree ℤ n) →
      NonzeroInternalFrequencies n t → (σ → HistoryFormula σ) → List (WordTransferGuard σ)
  | 0, .leaf _, _, _, _ => []
  | n + 1, .node d l r, t, hn, env =>
      let step := wordTransferStep d t.1 (frequencyRoot n t.2.1) (frequencyRoot n t.2.2) hn.1
      wordTransferGuard d t.1 (frequencyRoot n t.2.1) (frequencyRoot n t.2.2) hn.1 env ::
        (l.guards t.2.1 hn.2.1 (BranchingWordHistory.updatedFormulas step env) ++
          r.guards t.2.2 hn.2.2 (BranchingWordHistory.updatedFormulas step env))

theorem WordTransferTemplate.guards_length {σ : Type*} {n : ℕ}
    (template : WordTransferTemplate σ n) (t : FrequencyTree ℤ n)
    (hn : NonzeroInternalFrequencies n t) (env : σ → HistoryFormula σ) :
    (template.guards t hn env).length = 2 ^ n - 1 := by
  induction template generalizing env with
  | leaf word => rfl
  | @node n d l r hl hr =>
    simp only [guards, List.length_cons, List.length_append, hl, hr, pow_succ]
    have := Nat.one_le_two_pow (n := n)
    omega

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_WordTransferGuardPolynomial
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The exact one-variable polynomial form of each branching node guard -/

namespace Ostmann

open scoped Classical

noncomputable def WordTransferGuard.residueAt {σ : Type*} (g : WordTransferGuard σ) (x : σ → ℤ) : Prop :=
  smallDivisionTest (MvPolynomial.eval₂Hom (RingHom.id ℤ) x g.pivot.cleared.numerator)
    g.pivot.cleared.denominator g.right.natAbs ∧
  smallDivisionTest (MvPolynomial.eval₂Hom (RingHom.id ℤ) x g.rightProduct.cleared.numerator)
    g.rightProduct.cleared.denominator g.root.natAbs

def WordTransferGuard.frequencyBounds {σ : Type*} (g : WordTransferGuard σ) : Prop :=
  g.left.natAbs ≤ g.childBound ∧ g.right.natAbs ≤ g.childBound

noncomputable def WordTransferGuard.polynomials {σ : Type*}
    (g : WordTransferGuard σ) (a : σ → ℤ) (coord : σ) : Fin 3 → Polynomial ℝ :=
  ![formulaPolynomial g.pivot (fun j => (a j : ℝ)) coord - Polynomial.C 1,
    Polynomial.C (g.pivotBound : ℝ) - formulaPolynomial g.pivot (fun j => (a j : ℝ)) coord,
    formulaPolynomial g.rightProduct (fun j => (a j : ℝ)) coord -
      Polynomial.C ((2 * g.pivotBound * g.childBound + 1 : ℕ) : ℝ)]

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_WordTransferGuardFamily
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # One residue gate and one polynomial partition for a complete guard family -/

namespace Ostmann

open scoped BigOperators Classical

noncomputable def wordGuardPolynomials {σ : Type*} {k : ℕ} (G : Fin k → WordTransferGuard σ)
    (a : σ → ℤ) (coord : σ) : Fin (k + (k + k)) → Polynomial ℝ :=
  Fin.append (fun i => (G i).polynomials a coord 0)
    (Fin.append (fun i => (G i).polynomials a coord 1) (fun i => (G i).polynomials a coord 2))

noncomputable def wordGuardKeep {σ : Type*} {k : ℕ} (G : Fin k → WordTransferGuard σ)
    (code : Fin (k + (k + k)) → Bool) : Bool :=
  decide (∀ i, (G i).frequencyBounds) && decide (∀ j, code j = true)

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_WordTransferFullPeriod
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The full small-frequency modulus, including every node's unit tests -/

namespace Ostmann

open scoped Classical

def allFrequencyList : (n : ℕ) → FrequencyTree ℤ n → List ℤ
  | 0, t => [t]
  | n + 1, t => t.1 :: (allFrequencyList n t.2.1 ++ allFrequencyList n t.2.2)

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_MovingGiantSamples
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Constructing the moving-giant tree from the sampled compensation slots

Each reversing node samples four positions per leaf of either child. Their
products are inserted into both child regular lists. The constructor proves
the required product consistency; it does not ask for a pre-existing diagram.
-/

namespace Ostmann
open scoped BigOperators

/-- The four actual compensation positions per child leaf at a reversal. -/
inductive MovingGiantSamples : ℕ → Type
  | leaf : MovingGiantSamples 0
  | node {n : ℕ} (samples : TreeLeafTuple (Fin 4 → ℕ) n)
      (left right : MovingGiantSamples n) : MovingGiantSamples (n + 1)

def compensationLeafProducts : (n : ℕ) →
    TreeLeafTuple (Fin 4 → ℕ) n → TreeLeafTuple ℕ n
  | 0, x => (∏ i : Fin 4, (show Fin 4 → ℕ from x) i : ℕ)
  | n + 1, x => (compensationLeafProducts n x.1, compensationLeafProducts n x.2)

def MovingGiantTree.castConstant {n C D : ℕ} (h : C = D)
    (T : MovingGiantTree n C) : MovingGiantTree n D := h ▸ T

@[simp] theorem MovingGiantTree.castConstant_frequency {n C D : ℕ} (h : C = D)
    (T : MovingGiantTree n C) : (T.castConstant h).frequency = T.frequency := by
  subst D
  rfl

@[simp] theorem MovingGiantTree.castConstant_units {n C D : ℕ} (h : C = D)
    (T : MovingGiantTree n C) (q : ℕ) : (T.castConstant h).UnitsAt q ↔ T.UnitsAt q := by
  subst D
  rfl

def MovingGiantSamples.UnitsAt (q : ℕ) : {n : ℕ} → MovingGiantSamples n → Prop
  | _, .leaf => True
  | n + 1, .node samples left right =>
      ((treeLeafProduct n (compensationLeafProducts n samples) : ℕ) : ZMod q) ≠ 0 ∧
      left.UnitsAt q ∧ right.UnitsAt q

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_MovingGiantRows
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Ordered coefficient rows for the moving-giant reversal

In the manuscript's order both children put the inserted giant first. The
left child is therefore the exchanged version of the retained-first reversal.
This exchange preserves the nonvanishing determinant used in the line bounds.
-/

namespace Ostmann
namespace GiantRows

variable {R : Type*} [CommRing R]

def swap (T : GiantRows R) : GiantRows R := ⟨T.c, T.d, T.a, T.b⟩

@[simp] theorem eval_swap (T : GiantRows R) (x y : R) :
    T.swap.eval x y = ((T.eval x y).2, (T.eval x y).1) := rfl

/-- Both source children order their giants as `(new, retained)`. -/
def movingReverse (T : GiantRows R) (left : Bool) (v w u : Rˣ) : GiantRows R :=
  if left then (T.reverse true v w u).swap else T.reverse false v w u

end GiantRows

namespace PolynomialGiantRows

variable {σ : Type*}

noncomputable def swap (T : PolynomialGiantRows σ) : PolynomialGiantRows σ :=
  ⟨T.rows.swap, T.denominator⟩

noncomputable def movingReverse (T : PolynomialGiantRows σ) (left : Bool)
    (v w u : MvPolynomial σ ℤ) : PolynomialGiantRows σ :=
  if left then (T.reverse true v w u).swap else T.reverse false v w u

@[simp] theorem normalized_swap {K : Type*} [Field K] (T : PolynomialGiantRows σ)
    (φ : MvPolynomial σ ℤ →+* K) : T.swap.normalized φ = (T.normalized φ).swap := rfl

end PolynomialGiantRows
end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_MovingSlotPolynomials
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Actual slot products in the moving-giant line polynomials

Lists retain multiplicities: an ancestral compensation prime may occur in
several descendant regular products. No squarefree polynomial is substituted.
-/

namespace Ostmann
open scoped BigOperators Classical

noncomputable def movingSlotProduct {σ : Type*} (slots : List σ) : MvPolynomial σ ℤ :=
  (slots.map MvPolynomial.X).prod

noncomputable def movingSlotCoefficient {σ : Type*} (s : ℤ) (slots : List σ) :
    MvPolynomial σ ℤ := MvPolynomial.C s * movingSlotProduct slots

/-- The products multiplying the current two giants, together with the actual
compensation product in the denominator. Giants themselves are excluded. -/
structure MovingSlotReversal (σ : Type*) where
  left : Bool
  rootFrequency : ℤ
  leftFrequency : ℤ
  rightFrequency : ℤ
  leftSlots : List σ
  rightSlots : List σ
  compensationSlots : List σ

namespace MovingSlotReversal

noncomputable def polynomial {σ : Type*} (s : MovingSlotReversal σ) : PolynomialReversal σ where
  left := s.left
  v := movingSlotCoefficient s.leftFrequency s.rightSlots
  w := movingSlotCoefficient s.rightFrequency s.leftSlots
  u := movingSlotCoefficient s.rootFrequency s.compensationSlots

def lengthLE {σ : Type*} (s : MovingSlotReversal σ) (d : ℕ) : Prop :=
  s.rightSlots.length ≤ d ∧ s.leftSlots.length ≤ d ∧ s.compensationSlots.length ≤ d

def frequencyLE {σ : Type*} (s : MovingSlotReversal σ) (F : ℝ) : Prop :=
  |(s.leftFrequency : ℝ)| ≤ F ∧ |(s.rightFrequency : ℝ)| ≤ F ∧
    |(s.rootFrequency : ℝ)| ≤ F

end MovingSlotReversal
end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_MovingSlotOccurrences
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Actual occurrence paths and absence of their compensation type -/

namespace Ostmann
open scoped Classical

/-- At a node, the two regular lists exclude its moving giants. The
compensation list is inserted in both children by the sampler. -/
inductive MovingSlotData (σ : Type*) : ℕ → Type _
  | leaf (s : ℤ) (regular : List σ) : MovingSlotData σ 0
  | node {n : ℕ} (s : ℤ) (leftRegular rightRegular compensation : List σ)
      (left right : MovingSlotData σ n) : MovingSlotData σ (n + 1)

def MovingSlotData.frequency {σ : Type*} : {n : ℕ} → MovingSlotData σ n → ℤ
  | _, .leaf s _ => s
  | _, .node s _ _ _ _ _ => s

def MovingSlotData.step {σ : Type*} {n : ℕ} (s : ℤ) (CL CR u : List σ)
    (left right : MovingSlotData σ n) (b : Bool) : MovingSlotReversal σ where
  left := b
  rootFrequency := s
  leftFrequency := left.frequency
  rightFrequency := right.frequency
  leftSlots := CL
  rightSlots := CR
  compensationSlots := u

structure MovingSlotOccurrence (σ : Type*) where
  level : ℕ
  current : MovingSlotReversal σ
  path : List (MovingSlotReversal σ)

def MovingSlotOccurrence.extend {σ : Type*} (o : MovingSlotOccurrence σ)
    (s : MovingSlotReversal σ) : MovingSlotOccurrence σ :=
  { o with path := o.path ++ [s] }

/-- Each root-to-occurrence path is recorded in the order of the cleared
ancestor recursion, so the newest reversal occurs first. -/
def MovingSlotData.occurrences {σ : Type*} : {n : ℕ} → MovingSlotData σ n → List (MovingSlotOccurrence σ)
  | _, .leaf _ _ => []
  | n + 1, .node s CL CR u left right =>
      ⟨n + 1, step s CL CR u left right false, []⟩ ::
        (left.occurrences.map (fun o => o.extend (step s CL CR u left right true))) ++
        (right.occurrences.map (fun o => o.extend (step s CL CR u left right false)))

def MovingSlotData.Levels {σ : Type*} (tier : σ → ℕ) :
    {n : ℕ} → MovingSlotData σ n → Prop
  | _, .leaf _ _ => True
  | n + 1, .node _ CL CR u left right =>
      (∀ i ∈ CL, n + 1 ≤ tier i) ∧ (∀ i ∈ CR, n + 1 ≤ tier i) ∧
      (∀ i ∈ u, tier i = n) ∧ left.Levels tier ∧ right.Levels tier

def MovingSlotOccurrence.AvoidsBelow {σ : Type*} (tier : σ → ℕ)
    (o : MovingSlotOccurrence σ) : Prop :=
  (∀ s ∈ o.path, (∀ i ∈ s.leftSlots, o.level ≤ tier i) ∧
    (∀ i ∈ s.rightSlots, o.level ≤ tier i) ∧
    (∀ i ∈ s.compensationSlots, o.level ≤ tier i)) ∧
  (∀ i ∈ o.current.leftSlots, o.level ≤ tier i) ∧
  (∀ i ∈ o.current.rightSlots, o.level ≤ tier i)

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_MovingSampleSlots
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Labelled four-slot samples and the concrete occurrence paths -/

namespace Ostmann
open scoped Classical

/-- The same sampler as `MovingGiantSamples`, before the prime labels have
been evaluated. Four actual positions are used at each child leaf. -/
inductive MovingSampleSlots (σ : Type*) : ℕ → Type _
  | leaf : MovingSampleSlots σ 0
  | node {n : ℕ} (samples : TreeLeafTuple (Fin 4 → σ) n)
      (left right : MovingSampleSlots σ n) : MovingSampleSlots σ (n + 1)

def movingCompensationSlots {σ : Type*} : (n : ℕ) →
    TreeLeafTuple (Fin 4 → σ) n → TreeLeafTuple (List σ) n
  | 0, x => List.ofFn (show Fin 4 → σ from x)
  | n + 1, x => (movingCompensationSlots n x.1, movingCompensationSlots n x.2)

def flattenMovingSlots {σ : Type*} : (n : ℕ) → TreeLeafTuple (List σ) n → List σ
  | 0, x => (show List σ from x)
  | n + 1, x => flattenMovingSlots n x.1 ++ flattenMovingSlots n x.2

def MovingSampleSlots.Levels {σ : Type*} (tier : σ → ℕ) :
    {n : ℕ} → MovingSampleSlots σ n → Prop
  | _, .leaf => True
  | n + 1, .node samples left right =>
      (∀ i ∈ flattenMovingSlots n (movingCompensationSlots n samples), tier i = n) ∧
      left.Levels tier ∧ right.Levels tier

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_MovingSampleSizes
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Concrete degree budgets for the sampled moving-giant paths -/

namespace Ostmann

def MovingLeafLengthLE {σ : Type*} : (n : ℕ) → TreeLeafTuple (List σ) n → ℕ → Prop
  | 0, x, A => (show List σ from x).length ≤ A
  | n + 1, x, A => MovingLeafLengthLE n x.1 A ∧ MovingLeafLengthLE n x.2 A

def MovingSlotData.SizeLE {σ : Type*} (D : ℕ) : {n : ℕ} → MovingSlotData σ n → Prop
  | _, .leaf _ _ => True
  | _, .node _ CL CR u left right =>
      CL.length ≤ D ∧ CR.length ≤ D ∧ u.length ≤ D ∧ left.SizeLE D ∧ right.SizeLE D

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_SmoothPrimeComparison
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Prime comparison for the actual clipped polynomial factors -/

namespace Ostmann
open MeasureTheory
open scoped BigOperators

theorem ClippedPolynomialFactor.continuous_value (f : ClippedPolynomialFactor) :
    Continuous f.value := by
  have hp : LipschitzOnWith ⟨f.lip, f.lip_nonneg⟩ f.profile (Set.Icc f.lo f.hi) := by
    apply LipschitzOnWith.of_dist_le_mul
    intro x hx y hy
    change dist (f.profile x) (f.profile y) ≤ f.lip * dist x y
    simpa only [dist_eq_norm, Real.norm_eq_abs] using f.lipschitz x hx y hy
  have hc : Continuous (fun x => clipRealInterval f.lo f.hi (f.polynomial.eval x)) :=
    continuous_const.max (continuous_const.min f.polynomial.continuous)
  apply continuousOn_univ.mp
  exact hp.continuousOn.comp hc.continuousOn
    (fun x _ => clipRealInterval_bounds f.lo f.hi _ f.lo_le_hi)

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_MovingSlotRealization
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Integer realization of the source-ordered slot rows -/

namespace Ostmann
open scoped BigOperators Classical

namespace MovingSlotReversal

/-- Each list is evaluated as its actual natural product, with multiplicities. -/
def naturalProduct {σ : Type*} (value : σ → ℕ) (slots : List σ) : ℕ :=
  (slots.map value).prod

def naturalPivot {σ : Type*} (s : MovingSlotReversal σ) (value : σ → ℕ) (XL XR : ℕ) : ℕ :=
  movingGiantPivot s.rootFrequency s.leftFrequency s.rightFrequency
    (naturalProduct value s.leftSlots) (naturalProduct value s.rightSlots)
    (naturalProduct value s.compensationSlots) XL XR 1 1

def naturalStep {σ : Type*} (s : MovingSlotReversal σ) (value : σ → ℕ)
    (pair : ℕ × ℕ) : ℕ × ℕ :=
  (s.naturalPivot value pair.1 pair.2, if s.left then pair.1 else pair.2)

/-- This is exactly the integer equation at a supported reversal. -/
def IntegralAt {σ : Type*} (s : MovingSlotReversal σ) (value : σ → ℕ)
    (pair : ℕ × ℕ) : Prop :=
  0 < s.naturalPivot value pair.1 pair.2 ∧
  s.leftFrequency * ((pair.2 * naturalProduct value s.rightSlots : ℕ) : ℤ) -
    s.rightFrequency * ((pair.1 * naturalProduct value s.leftSlots : ℕ) : ℤ) =
    s.rootFrequency * ((naturalProduct value s.compensationSlots *
      s.naturalPivot value pair.1 pair.2 : ℕ) : ℤ)

noncomputable def naturalReduction {σ : Type*} (q : ℕ) (value : σ → ℕ) :
    MvPolynomial σ ℤ →+* ZMod q :=
  MvPolynomial.eval₂Hom (Int.castRingHom (ZMod q)) (fun i => (value i : ZMod q))

end MovingSlotReversal

/-- A path is written with its newest reversal first, matching the cleared
row recursion. Each step is performed over the integers before reduction. -/
def movingSlotNaturalPath {σ : Type*} (value : σ → ℕ) :
    List (MovingSlotReversal σ) → (ℕ × ℕ) → ℕ × ℕ
  | [], pair => pair
  | s :: path, pair => s.naturalStep value (movingSlotNaturalPath value path pair)

def MovingSlotPathIntegral {σ : Type*} (value : σ → ℕ) :
    List (MovingSlotReversal σ) → (ℕ × ℕ) → Prop
  | [], _ => True
  | s :: path, pair => MovingSlotPathIntegral value path pair ∧
      s.IntegralAt value (movingSlotNaturalPath value path pair)

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_MovingOccurrenceUnits
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Unit coefficients for the actual sampled occurrence paths -/

namespace Ostmann
open scoped Classical

def MovingSlotReversal.Frequencies {σ : Type*} (s : MovingSlotReversal σ)
    (P : ℤ → Prop) : Prop := P s.leftFrequency ∧ P s.rightFrequency ∧ P s.rootFrequency

def MovingSlotData.Frequencies {σ : Type*} (P : ℤ → Prop) : {n : ℕ} → MovingSlotData σ n → Prop
  | _, .leaf s _ => P s
  | _, .node s _ _ _ left right => P s ∧ left.Frequencies P ∧ right.Frequencies P

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_MovingSampleValues
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The labelled sampler evaluates to the actual natural prime sampler -/

namespace Ostmann
open scoped BigOperators

def movingCompensationValues {σ : Type*} (value : σ → ℕ) : (n : ℕ) →
    TreeLeafTuple (Fin 4 → σ) n → TreeLeafTuple (Fin 4 → ℕ) n
  | 0, x => fun i => value ((show Fin 4 → σ from x) i)
  | n + 1, x => (movingCompensationValues value n x.1, movingCompensationValues value n x.2)

def MovingSampleSlots.values {σ : Type*} (value : σ → ℕ) :
    {n : ℕ} → MovingSampleSlots σ n → MovingGiantSamples n
  | _, .leaf => .leaf
  | n + 1, .node samples left right =>
      .node (movingCompensationValues value n samples) (left.values value) (right.values value)

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_MovingSampleIntegrality
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Full integer support for the labelled moving-giant sampler -/

namespace Ostmann
open scoped Classical

/-- The labelled history is interpreted by the same positive integer pivots
as the original sampler. No primality is imposed on a reconstructed giant. -/
def MovingSlotData.Integral {σ : Type*} (value : σ → ℕ) :
    {n : ℕ} → MovingSlotData σ n → ℕ → ℕ → Prop
  | _, .leaf _ _, _, _ => True
  | _, .node s CL CR u left right, XL, XR =>
      let step := MovingSlotData.step s CL CR u left right false
      let p := step.naturalPivot value XL XR
      step.IntegralAt value (XL, XR) ∧ left.Integral value p XL ∧ right.Integral value p XR

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_MovingSlotSystem
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The original recursive weight on moving-giant states

A reconstructed pivot is the composite `u*p`; only its quotient `p` becomes
the new giant. The compensation primes remain in the regular child lists.
-/

namespace Ostmann
open scoped Classical

structure MovingSlotState (σ : Type*) where
  depth : ℕ
  data : MovingSlotData σ depth
  leftGiant : ℕ
  rightGiant : ℕ

def MovingSlotState.leftProduct {σ : Type*} (value : σ → ℕ) (x : MovingSlotState σ) : ℕ :=
  match x with
  | ⟨0, .leaf _ _, _, _⟩ => 1
  | ⟨_ + 1, .node _ CL _ _ _ _, XL, _⟩ => XL * MovingSlotReversal.naturalProduct value CL

def MovingSlotState.rightProduct {σ : Type*} (value : σ → ℕ) (x : MovingSlotState σ) : ℕ :=
  match x with
  | ⟨0, .leaf _ _, _, _⟩ => 1
  | ⟨_ + 1, .node _ _ CR _ _ _, _, XR⟩ => XR * MovingSlotReversal.naturalProduct value CR

def MovingSlotState.compensation {σ : Type*} (value : σ → ℕ) (x : MovingSlotState σ) : ℕ :=
  match x with
  | ⟨0, .leaf _ _, _, _⟩ => 1
  | ⟨_ + 1, .node _ _ _ u _ _, _, _⟩ => MovingSlotReversal.naturalProduct value u

def MovingSlotState.child {σ : Type*} (value : σ → ℕ) (left : Bool)
    (x : MovingSlotState σ) (P : ℕ) : MovingSlotState σ :=
  match x with
  | ⟨0, .leaf s regular, XL, XR⟩ => ⟨0, .leaf s regular, XL, XR⟩
  | ⟨n + 1, .node _ _ _ u L R, XL, XR⟩ =>
      ⟨n, if left then L else R, P / MovingSlotReversal.naturalProduct value u,
        if left then XL else XR⟩

def movingSlotSystem {σ : Type*} (value : σ → ℕ) (childBound pivotBound : ℕ → ℕ) :
    TransferHistorySystem (MovingSlotState σ) where
  leftProduct := MovingSlotState.leftProduct value
  rightProduct := MovingSlotState.rightProduct value
  childBound x := childBound x.depth
  pivotBound x := pivotBound x.depth
  leftState := MovingSlotState.child value true
  rightState := MovingSlotState.child value false

def MovingSlotData.Follows {σ : Type*} : {n : ℕ} →
    MovingSlotData σ n → FrequencyTree ℤ n → Prop
  | _, .leaf s _, t => s = frequencyRoot 0 t
  | _n + 1, .node s _ _ _ left right, t =>
      s = t.1 ∧ left.Follows t.2.1 ∧ right.Follows t.2.2

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_TransferGraph
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The graph update and the regular-row invariant in one transfer -/

namespace Ostmann

/-- The true branch is the positive copy. -/
def transferCopySign (t : Bool) : ℤ := if t then 1 else -1

/-- `none` is the erased pivot; `some (inl h)` is a copied slot and
`some (inr y)` is a shared outside slot. -/
def transferredGraph {H Y : Type*}
    (b : Option (H ⊕ Y) → Option (H ⊕ Y) → ℤ) :
    ((Bool × H) ⊕ Y) → ((Bool × H) ⊕ Y) → ℤ
  | .inl (t, h), .inl (u, k) =>
      if t = u then transferCopySign t * b (some (.inl h)) (some (.inl k))
      else transferCopySign t * b (some (.inl h)) none
  | .inl (t, h), .inr y => transferCopySign t * b (some (.inl h)) (some (.inr y))
  | .inr y, .inl (t, h) => transferCopySign t * b (some (.inr y)) (some (.inl h))
  | .inr _, .inr _ => 0

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Characters_AnchorPairCode
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Anchor codes from the actual graph update -/

namespace Ostmann

def anchorSignPair (α ε : ℤ) (t : Bool) : ℤ × ℤ :=
  if t then (1, -α * ε) else (-α * ε, 1)

def copyPathParity (t : ℕ → Bool) : ℕ → ℤ
  | 0 => 1
  | j + 1 => transferCopySign (t j) * copyPathParity t j

def finiteCopyPath {n : ℕ} (t : Fin n → Bool) (j : ℕ) : Bool :=
  if h : j < n then t ⟨j, h⟩ else false

def finiteAnchorCode {n : ℕ} (α : Fin n → ℤ) (t : Fin n → Bool) : Fin n → ℤ × ℤ :=
  fun j => anchorSignPair (α j) (copyPathParity (finiteCopyPath t) j) (t j)

def finalCopyParity {n : ℕ} (t : Fin n → Bool) : ℤ := copyPathParity (finiteCopyPath t) n

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_FinalParityPaths
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The two equally sized final-parity classes of actual copy paths -/

namespace Ostmann

open scoped Classical

abbrev ParityPaths (n : ℕ) (ε : ℤ) := {t : Fin (n + 1) → Bool // finalCopyParity t = ε}

noncomputable abbrev FinalParityReassignments (n m : ℕ) :=
  Fin m → (Equiv.Perm (ParityPaths n 1) × Equiv.Perm (ParityPaths n (-1)))

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_FinalReassignments
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The actual independent, parity-preserving bulk reassignments -/

namespace Ostmann

open scoped Classical

abbrev ParityPathSum (n : ℕ) := ParityPaths n 1 ⊕ ParityPaths n (-1)

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_GraphCopySchedule
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The graph on the literal copied and retained slot labels

The ambient label type includes both alternatives at a transfer. The actual
partition restricts the copied alternative to H and the retained alternative to
Y. Thus copying and retaining never identify two surviving slots. -/

namespace Ostmann

universe u

/-- A copied label remembers its sign; a retained label remembers its old slot. -/
def CopyScheduleVertex (I : Type u) : ℕ → Type u
  | 0 => I
  | n + 1 => (Bool × CopyScheduleVertex I n) ⊕ CopyScheduleVertex I n

noncomputable def copyScheduleOutside {I : Type*} : (n : ℕ) → I → CopyScheduleVertex I n
  | 0, i => i
  | n + 1, i => Sum.inr (copyScheduleOutside n i)

noncomputable def copySchedulePositive {I : Type*} : (n : ℕ) → I → CopyScheduleVertex I n
  | 0, i => i
  | n + 1, i => Sum.inl (true, copySchedulePositive n i)

noncomputable def copySchedulePath {I : Type*} :
    (n : ℕ) → (Fin n → Bool) → I → CopyScheduleVertex I n
  | 0, _, i => i
  | n + 1, t, i => Sum.inl (t (Fin.last n), copySchedulePath n (fun j => t j.castSucc) i)

/-- Collapse only the erased pivot. Both surviving alternatives have their
original predecessor, as in the manuscript's H/Y partition. -/
def copySchedulePredecessor {I : Type*} {n : ℕ} (p : CopyScheduleVertex I n) :
    Option (CopyScheduleVertex I n ⊕ CopyScheduleVertex I n) → CopyScheduleVertex I n
  | none => p
  | some (.inl i) => i
  | some (.inr i) => i

noncomputable def copyScheduleGraph {I : Type*} (g : I → I → ℤ) (pivot : ℕ → I) :
    (n : ℕ) → CopyScheduleVertex I n → CopyScheduleVertex I n → ℤ
  | 0 => g
  | n + 1 => transferredGraph (fun i j =>
      copyScheduleGraph g pivot n
        (copySchedulePredecessor (copySchedulePositive n (pivot n)) i)
        (copySchedulePredecessor (copySchedulePositive n (pivot n)) j))

@[simp] theorem copySchedulePath_snoc {I : Type*} {n : ℕ}
    (t : Fin n → Bool) (b : Bool) (i : I) :
    copySchedulePath (n + 1) (Fin.snoc t b) i =
      Sum.inl (b, copySchedulePath n t i) := by
  simp only [copySchedulePath, Fin.snoc_last, Fin.snoc_castSucc]
  rfl

@[simp] theorem copyScheduleGraph_outside_copy {I : Type*}
    (g : I → I → ℤ) (pivot : ℕ → I) (n : ℕ)
    (a i : CopyScheduleVertex I n) (b : Bool) :
    copyScheduleGraph g pivot (n + 1) (.inr a) (.inl (b, i)) =
      transferCopySign b * copyScheduleGraph g pivot n a i := rfl

@[simp] theorem copyScheduleGraph_copy_outside {I : Type*}
    (g : I → I → ℤ) (pivot : ℕ → I) (n : ℕ)
    (i a : CopyScheduleVertex I n) (b : Bool) :
    copyScheduleGraph g pivot (n + 1) (.inl (b, i)) (.inr a) =
      transferCopySign b * copyScheduleGraph g pivot n i a := rfl

@[simp] theorem copyScheduleGraph_copy_copy {I : Type*}
    (g : I → I → ℤ) (pivot : ℕ → I) (n : ℕ)
    (i j : CopyScheduleVertex I n) (b c : Bool) :
    copyScheduleGraph g pivot (n + 1) (.inl (b, i)) (.inl (c, j)) =
      if b = c then transferCopySign b * copyScheduleGraph g pivot n i j
      else transferCopySign b * copyScheduleGraph g pivot n i
        (copySchedulePositive n (pivot n)) := rfl

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_CopyScheduleSupport
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The actual H/Y/pivot partition of the copied-slot schedule -/

namespace Ostmann

inductive CopyScheduleRole where
  | word
  | pivot (step : ℕ)
  | anchor (step : ℕ)
  | outside
  deriving DecidableEq

namespace CopyScheduleRole

def copiedAt (j : ℕ) : CopyScheduleRole → Bool
  | .word => true
  | .pivot k => decide (j < k)
  | .anchor k => decide (j = k)
  | .outside => false

def erasedAt (j : ℕ) : CopyScheduleRole → Bool
  | .pivot k => decide (j = k)
  | _ => false

def afterCopy (b : Bool) : CopyScheduleRole → CopyScheduleRole
  | .word => .word
  | .pivot k => if b then .pivot k else .outside
  | _ => .outside

end CopyScheduleRole

/-- The role of an actual copy, including the inactive negative pivot copies. -/
def copyScheduleRole {I : Type*} (role : I → CopyScheduleRole) :
    (n : ℕ) → CopyScheduleVertex I n → CopyScheduleRole
  | 0, i => role i
  | n + 1, .inl (b, i) => (copyScheduleRole role n i).afterCopy b
  | n + 1, .inr i => copyScheduleRole role n i

/-- Exactly the surviving labels. Copied labels come from H, retained labels
come from Y, and every constituent of the current pivot is removed. -/
def CopyScheduleSurvives {I : Type*} (role : I → CopyScheduleRole) :
    (n : ℕ) → CopyScheduleVertex I n → Prop
  | 0, _ => True
  | n + 1, .inl (_, i) => CopyScheduleSurvives role n i ∧
      (copyScheduleRole role n i).copiedAt n = true
  | n + 1, .inr i => CopyScheduleSurvives role n i ∧
      (copyScheduleRole role n i).copiedAt n = false ∧
      (copyScheduleRole role n i).erasedAt n = false

abbrev CopyScheduleH {I : Type*} (role : I → CopyScheduleRole) (n : ℕ) :=
  {i : CopyScheduleVertex I n // CopyScheduleSurvives role n i ∧
    (copyScheduleRole role n i).copiedAt n = true}

abbrev CopyScheduleY {I : Type*} (role : I → CopyScheduleRole) (n : ℕ) :=
  {i : CopyScheduleVertex I n // CopyScheduleSurvives role n i ∧
    (copyScheduleRole role n i).copiedAt n = false ∧
    (copyScheduleRole role n i).erasedAt n = false}

theorem copyScheduleRole_path {I : Type*} (role : I → CopyScheduleRole)
    (i : I) (hi : role i = .word) (n : ℕ) (t : Fin n → Bool) :
    copyScheduleRole role n (copySchedulePath n t i) = .word := by
  induction n with
  | zero => exact hi
  | succ n ih =>
    change (copyScheduleRole role n (copySchedulePath n (fun k => t k.castSucc) i)).afterCopy _ = _
    rw [ih]
    rfl

theorem copyScheduleSurvives_path {I : Type*} (role : I → CopyScheduleRole)
    (i : I) (hi : role i = .word) (n : ℕ) (t : Fin n → Bool) :
    CopyScheduleSurvives role n (copySchedulePath n t i) := by
  induction n with
  | zero => trivial
  | succ n ih =>
    change CopyScheduleSurvives role n (copySchedulePath n (fun k => t k.castSucc) i) ∧ _
    exact ⟨ih _, by rw [copyScheduleRole_path role i hi]; rfl⟩

theorem copyScheduleRole_positive {I : Type*} (role : I → CopyScheduleRole)
    (i : I) (k : ℕ) (hi : role i = .pivot k) (n : ℕ) :
    copyScheduleRole role n (copySchedulePositive n i) = .pivot k := by
  induction n with
  | zero => exact hi
  | succ n ih =>
    change (copyScheduleRole role n (copySchedulePositive n i)).afterCopy true = _
    rw [ih]
    rfl

theorem copyScheduleSurvives_positive {I : Type*} (role : I → CopyScheduleRole)
    (i : I) (k : ℕ) (hi : role i = .pivot k) (n : ℕ) (hn : n ≤ k) :
    CopyScheduleSurvives role n (copySchedulePositive n i) := by
  induction n with
  | zero => trivial
  | succ n ih =>
    change CopyScheduleSurvives role n (copySchedulePositive n i) ∧ _
    refine ⟨ih (by omega), ?_⟩
    rw [copyScheduleRole_positive role i k hi]
    simpa [CopyScheduleRole.copiedAt] using (show n < k by omega)

@[simp] theorem copyScheduleRole_outside {I : Type*} (role : I → CopyScheduleRole)
    (n : ℕ) (i : I) : copyScheduleRole role n (copyScheduleOutside n i) = role i := by
  induction n with
  | zero => rfl
  | succ n ih => exact ih

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_ScheduleWordSlots
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The surviving word slots are precisely the full binary copy paths -/

namespace Ostmann

noncomputable instance copyScheduleVertexFintype {I : Type*} [Fintype I] (n : ℕ) :
    Fintype (CopyScheduleVertex I n) := by
  induction n with
  | zero => exact inferInstanceAs (Fintype I)
  | succ n ih =>
    letI := ih
    exact inferInstanceAs (Fintype ((Bool × CopyScheduleVertex I n) ⊕ CopyScheduleVertex I n))

theorem copySchedulePath_injective {I : Type*} (n : ℕ) :
    Function.Injective (fun x : (Fin n → Bool) × I => copySchedulePath n x.1 x.2) := by
  induction n with
  | zero =>
    intro x y h
    apply Prod.ext
    · exact Subsingleton.elim _ _
    · exact h
  | succ n ih =>
    rintro ⟨t, i⟩ ⟨u, j⟩ h
    change Sum.inl (t (Fin.last n), copySchedulePath n (fun k => t k.castSucc) i) =
      Sum.inl (u (Fin.last n), copySchedulePath n (fun k => u k.castSucc) j) at h
    have he := Prod.mk.inj (Sum.inl.inj h)
    have hp : ((fun k : Fin n => t k.castSucc), i) = ((fun k : Fin n => u k.castSucc), j) := ih he.2
    apply Prod.ext
    · funext k
      refine Fin.lastCases he.1 (fun a => ?_) k
      exact congrFun (congrArg Prod.fst hp) a
    · exact congrArg (fun z : (Fin n → Bool) × I => z.2) hp

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_SchedulePivotSlots
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The active pivot group has exactly its original constituent slots -/

namespace Ostmann

theorem CopyScheduleRole.afterCopy_eq_pivot (r : CopyScheduleRole) (b : Bool) (k : ℕ) :
    r.afterCopy b = .pivot k ↔ b = true ∧ r = .pivot k := by
  cases r <;> cases b <;> simp [afterCopy]

theorem copySchedulePositive_injective {I : Type*} (n : ℕ) :
    Function.Injective (copySchedulePositive (I := I) n) := by
  induction n with
  | zero => exact fun _ _ h => h
  | succ n ih =>
    intro i j h
    exact ih (Prod.mk.inj (Sum.inl.inj h)).2

/-- No old pivot can remain active: the active group is copied positively
until its own step and is then erased in its entirety. -/
theorem surviving_pivot_is_positive {I : Type*} (role : I → CopyScheduleRole)
    (n k : ℕ) (v : CopyScheduleVertex I n)
    (hv : CopyScheduleSurvives role n v) (hw : copyScheduleRole role n v = .pivot k) :
    n ≤ k ∧ ∃ i : I, role i = .pivot k ∧ v = copySchedulePositive n i := by
  induction n with
  | zero => exact ⟨Nat.zero_le _, v, hw, rfl⟩
  | succ n ih =>
    cases v with
    | inl q =>
      rcases q with ⟨b, v⟩
      change CopyScheduleSurvives role n v ∧ _ at hv
      change (copyScheduleRole role n v).afterCopy b = .pivot k at hw
      obtain ⟨rfl, hrole⟩ := (CopyScheduleRole.afterCopy_eq_pivot _ b k).mp hw
      have hnk : n < k := by
        have hc := hv.2
        rw [hrole] at hc
        simpa [CopyScheduleRole.copiedAt] using hc
      obtain ⟨_, i, hi, rfl⟩ := ih v hv.1 hrole
      exact ⟨by omega, i, hi, rfl⟩
    | inr v =>
      change CopyScheduleSurvives role n v ∧ _ ∧ _ at hv
      change copyScheduleRole role n v = .pivot k at hw
      obtain ⟨hnk, _⟩ := ih v hv.1 hw
      have hc := hv.2.1
      have he := hv.2.2
      rw [hw] at hc he
      have hnlt : ¬n < k := by simpa [CopyScheduleRole.copiedAt] using hc
      have hnne : n ≠ k := by simpa [CopyScheduleRole.erasedAt] using he
      omega

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_ReverseCopyMap
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Reversing the literal copied-atom schedule

This construction is at the atom level: a current pivot group is one atom
carrying its total product. -/

namespace Ostmann

open scoped Classical

abbrev CopyScheduleAtoms {I : Type*} (role : I → CopyScheduleRole) (n : ℕ) :=
  {i : CopyScheduleVertex I n // CopyScheduleSurvives role n i}

/-- The chosen child reads its H copy and the common Y. The erased pivot
is represented by the coordinate that the arithmetic node reconstructs. -/
noncomputable def reverseCopyLabelMap {I σ : Type*} (role : I → CopyScheduleRole)
    (n : ℕ) (b : Bool) (pivot : σ) (current : CopyScheduleAtoms role (n + 1) → σ)
    (i : CopyScheduleAtoms role n) : σ :=
  if hc : (copyScheduleRole role n i.val).copiedAt n = true then
    current ⟨.inl (b, i.val), i.property, hc⟩
  else if he : (copyScheduleRole role n i.val).erasedAt n = true then pivot
  else current ⟨.inr i.val, i.property, Bool.eq_false_iff.mpr hc, Bool.eq_false_iff.mpr he⟩

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_ExpandedScheduleCoordinates
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Fresh finite pivot coordinates for expanded prime-word templates -/

namespace Ostmann

open scoped Classical

abbrev ExpandedScheduledVariable (α : Type*) (depth : ℕ) :=
  α ⊕ (Fin (depth + 1) × (Fin depth → Bool))

def ExpandedCoordinateAfter {α : Type*} {depth : ℕ} (j : ℕ) : ExpandedScheduledVariable α depth → Prop
  | .inl _ => True
  | .inr p => j ≤ p.1.val

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_ScheduleAtomSystem
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The literal reverse transfer system on current atom values -/

namespace Ostmann

open scoped BigOperators Classical

abbrev ScheduleAtomState {I : Type*} (role : I → CopyScheduleRole) :=
  Σ n : ℕ, CopyScheduleAtoms role n → ℕ

noncomputable def scheduleAtomLeft {I : Type*} [Fintype I] (role : I → CopyScheduleRole) :
    ScheduleAtomState role → ℕ
  | ⟨0, _⟩ => 1
  | ⟨n + 1, x⟩ => ∏ i : CopyScheduleH role n, x ⟨.inl (true, i.val), i.property⟩

noncomputable def scheduleAtomRight {I : Type*} [Fintype I] (role : I → CopyScheduleRole) :
    ScheduleAtomState role → ℕ
  | ⟨0, _⟩ => 1
  | ⟨n + 1, x⟩ => ∏ i : CopyScheduleH role n, x ⟨.inl (false, i.val), i.property⟩

def scheduleAtomBound {I : Type*} (role : I → CopyScheduleRole) (bound : ℕ → ℕ) :
    ScheduleAtomState role → ℕ
  | ⟨0, _⟩ => 0
  | ⟨n + 1, _⟩ => bound n

noncomputable def scheduleAtomChild {I : Type*} (role : I → CopyScheduleRole) (b : Bool) :
    ScheduleAtomState role → ℕ → ScheduleAtomState role
  | ⟨0, x⟩, _ => ⟨0, x⟩
  | ⟨n + 1, x⟩, P => ⟨n, reverseCopyLabelMap role n b P x⟩

noncomputable def scheduleAtomSystem {I : Type*} [Fintype I] (role : I → CopyScheduleRole)
    (childBound pivotBound : ℕ → ℕ) : TransferHistorySystem (ScheduleAtomState role) where
  leftProduct := scheduleAtomLeft role
  rightProduct := scheduleAtomRight role
  childBound := scheduleAtomBound role childBound
  pivotBound := scheduleAtomBound role pivotBound
  leftState := scheduleAtomChild role true
  rightState := scheduleAtomChild role false

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_WordTransferArrays
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Indexed arrays of the actual branching guards and Fourier leaves -/

namespace Ostmann.WordTransferTemplate

open scoped Classical

variable {σ : Type*} {n : ℕ}

noncomputable def guardAt (template : WordTransferTemplate σ n) (t : FrequencyTree ℤ n)
    (hn : NonzeroInternalFrequencies n t) (i : Fin (2 ^ n - 1)) : WordTransferGuard σ :=
  (template.guards t hn .prime)[i.val]'(by rw [template.guards_length]; exact i.isLt)

noncomputable def leafAt (template : WordTransferTemplate σ n) (t : FrequencyTree ℤ n)
    (hn : NonzeroInternalFrequencies n t) (i : Fin (2 ^ n)) : WeightedWordLeaf σ :=
  (template.weightedLeaves t hn .prime)[i.val]'(by rw [template.weightedLeaves_length]; exact i.isLt)

end Ostmann.WordTransferTemplate

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_WordTransferCoefficient
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The constructed coefficient for a branching word history -/

namespace Ostmann

open scoped BigOperators SchwartzMap Classical

structure WordFourierParameters (n : ℕ) where
  scale : Fin (2 ^ n) → ℝ
  profile : 𝓢(ℝ, ℂ)
  lower : Fin (2 ^ n) → ℝ
  upper : Fin (2 ^ n) → ℝ
  lower_one : ∀ i, 1 ≤ lower i
  lower_upper : ∀ i, lower i ≤ upper i

namespace WordFourierParameters

variable {σ : Type*} {n : ℕ}

noncomputable def frequency (_p : WordFourierParameters n) (template : WordTransferTemplate σ n)
    (t : FrequencyTree ℤ n) (hn : NonzeroInternalFrequencies n t) (i : Fin (2 ^ n)) : ℝ :=
  let z := template.leafAt t hn i
  if z.positive then (z.frequency : ℝ) else -(z.frequency : ℝ)

noncomputable def factors (p : WordFourierParameters n) (template : WordTransferTemplate σ n)
    (t : FrequencyTree ℤ n) (hn : NonzeroInternalFrequencies n t) (a : σ → ℤ) (coord : σ) :
    Fin (2 ^ n) → ClippedPolynomialFactor :=
  formulaFourierFactors (fun i => (template.leafAt t hn i).formula) (fun i => (a i : ℝ)) coord
    p.scale p.profile (p.frequency template t hn) p.lower p.upper p.lower_one p.lower_upper

noncomputable def polynomials (p : WordFourierParameters n) (template : WordTransferTemplate σ n)
    (t : FrequencyTree ℤ n) (hn : NonzeroInternalFrequencies n t) (a : σ → ℤ) (coord : σ) :=
  fullHistoryPolynomials (p.factors template t hn a coord)
    (wordGuardPolynomials (template.guardAt t hn) a coord)

noncomputable def keep (template : WordTransferTemplate σ n)
    (t : FrequencyTree ℤ n) (hn : NonzeroInternalFrequencies n t) :=
  fullHistoryKeep (n := 2 ^ n) (wordGuardKeep (template.guardAt t hn))

noncomputable def budget (p : WordFourierParameters n) (template : WordTransferTemplate σ n)
    (t : FrequencyTree ℤ n) (hn : NonzeroInternalFrequencies n t) : ℝ :=
  formulaFourierBudget p.profile (p.frequency template t hn) p.lower p.upper

noncomputable def coefficient (p : WordFourierParameters n) (template : WordTransferTemplate σ n)
    (t : FrequencyTree ℤ n) (hn : NonzeroInternalFrequencies n t) (x : σ → ℤ) : ℂ :=
  (if (∀ i, (template.guardAt t hn i).ValidAt x) ∧
      (∀ j, (template.leafAt t hn j).formula.realValue x / p.scale j ∈ Set.Icc (p.lower j) (p.upper j))
    then 1 else 0) *
      ∏ j, normalizedFourierProfile p.profile (p.frequency template t hn j)
        ((template.leafAt t hn j).formula.realValue x / p.scale j)

end WordFourierParameters
end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_WordTransferUniformCoefficient
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The original bounded-bin recursive weight is the constructed coefficient -/

namespace Ostmann

open scoped BigOperators SchwartzMap FourierTransform ComplexConjugate Classical

noncomputable def WordFourierParameters.uniform (n : ℕ) (profile : 𝓢(ℝ, ℂ))
    (X lo hi : ℝ) (hlo : 1 ≤ lo) (hhi : lo ≤ hi) : WordFourierParameters n where
  scale := fun _ => X
  profile := profile
  lower := fun _ => lo
  upper := fun _ => hi
  lower_one := fun _ => hlo
  lower_upper := fun _ => hhi

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Tree_TwoVertexReindex
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Isolating two selected actual vertices without changing a graph product -/

namespace Ostmann

open scoped Classical

abbrev OtherVertices {V : Type*} (a b : V) := {v : V // v ≠ a ∧ v ≠ b}

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_ExpandedWordPairBound
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The constructed prime-word coefficient under the original product law -/

namespace Ostmann

open scoped BigOperators ComplexConjugate Classical

/-- Unused internal coordinates start at one; each is overwritten before use. -/
def expandedPrimeValues {V : Type*} (n : ℕ) (x : V → ℤ) : ExpandedScheduledVariable V n → ℤ
  | .inl v => x v
  | .inr _ => 1

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_ExpandedHistoryFormula
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # History formulas on the original independent prime variables

Internal pivot addresses are initialized to one. Substitution removes them
from the polynomial variable type before the prime-divisibility estimate. -/

namespace Ostmann

open scoped Classical

namespace HistoryFormula

def originalPrimes {V : Type*} {n : ℕ}
    (F : HistoryFormula (ExpandedScheduledVariable V n)) : HistoryFormula V :=
  F.bind (Sum.elim prime (fun _ => external 1))

end HistoryFormula

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_TopPrimeSupport
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Actual-prime collisions and coprimality to a fixed external integer -/

namespace Ostmann

open scoped BigOperators Classical

inductive TopPrimeCondition (V : Type*) where
  | distinct (left right : V)
  | external (coordinate : V) (value : ℤ)

def TopPrimeCondition.coordinate {V : Type*} : TopPrimeCondition V → V
  | .distinct a _ => a
  | .external a _ => a

def TopPrimeCondition.formula {V : Type*} : TopPrimeCondition V → HistoryFormula V
  | .distinct _ b => .prime b
  | .external _ N => .external N

def TopPrimeCondition.target {V : Type*} : TopPrimeCondition V → (V → ℕ) → ℤ
  | .distinct _ b, x => x b
  | .external _ N, _ => N

def TopPrimeCondition.Holds {V : Type*} (g : TopPrimeCondition V) (x : V → ℕ) : Prop :=
  (x g.coordinate).Coprime (g.target x).natAbs

def TopPrimeCondition.Bounded {V : Type*} (R : ℝ) : TopPrimeCondition V → Prop
  | .distinct _ _ => True
  | .external _ N => |(N : ℝ)| ≤ R

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_ExpandedOutsideCoordinates
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Every outside coordinate is an original prime coordinate -/

namespace Ostmann

open scoped Classical

def ExpandedActualCoordinates {I α : Type*} (role : I → CopyScheduleRole)
    (depth n : ℕ) (current : CopyScheduleAtoms role n → List (ExpandedScheduledVariable α depth)) : Prop :=
  ∀ i, (∀ k, copyScheduleRole role n i.val ≠ .pivot k) →
    ∀ v ∈ current i, ∃ a : α, v = .inl a

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_WordRangeReplay
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Ostmann

open scoped Classical

structure WordRange (σ : Type*) where
  word : List σ
  lower : ℝ
  upper : ℝ

structure HistoryRange (σ : Type*) where
  formula : HistoryFormula σ
  lower : ℝ
  upper : ℝ

noncomputable def WordRange.Holds {σ : Type*} (r : WordRange σ) (x : σ → ℕ) : Prop :=
  ((r.word.map x).prod : ℝ) ∈ Set.Icc r.lower r.upper

noncomputable def HistoryRange.Holds {σ : Type*} (r : HistoryRange σ) (a : σ → ℤ) : Prop :=
  r.formula.realValue a ∈ Set.Icc r.lower r.upper

noncomputable def WordRange.toHistory {σ : Type*} (r : WordRange σ)
    (env : σ → HistoryFormula σ) : HistoryRange σ :=
  ⟨HistoryFormula.listProduct (r.word.map env), r.lower, r.upper⟩

inductive WordRangeDecoration (σ : Type*) : ℕ → Type _ where
  | leaf (ranges : List (WordRange σ)) : WordRangeDecoration σ 0
  | node {n : ℕ} (ranges : List (WordRange σ))
      (left right : WordRangeDecoration σ n) : WordRangeDecoration σ (n + 1)

noncomputable def WordRangeDecoration.ValidAt {σ : Type*} :
    {n : ℕ} → WordRangeDecoration σ n → WordTransferTemplate σ n →
      (σ → ℕ) → FrequencyTree ℤ n → Prop
  | 0, .leaf ranges, .leaf _, x, _ => ∀ r ∈ ranges, r.Holds x
  | n + 1, .node ranges L R, .node d l r, x, t =>
      let P := historyPivot (wordTransferSystem σ) ((WordTransferTemplate.node d l r).state x)
        t.1 (frequencyRoot n t.2.1) (frequencyRoot n t.2.2)
      (∀ q ∈ ranges, q.Holds x) ∧
        L.ValidAt l (Function.update x d.target P) t.2.1 ∧
        R.ValidAt r (Function.update x d.target P) t.2.2

noncomputable def WordRangeDecoration.formulas {σ : Type*} :
    {n : ℕ} → WordRangeDecoration σ n → WordTransferTemplate σ n →
      (t : FrequencyTree ℤ n) → NonzeroInternalFrequencies n t →
        (σ → HistoryFormula σ) → List (HistoryRange σ)
  | 0, .leaf ranges, .leaf _, _, _, env => ranges.map (fun r => r.toHistory env)
  | n + 1, .node ranges L R, .node d l r, t, ht, env =>
      let next := BranchingWordHistory.updatedFormulas
        (wordTransferStep d t.1 (frequencyRoot n t.2.1) (frequencyRoot n t.2.2) ht.1) env
      ranges.map (fun q => q.toHistory env) ++
        (L.formulas l t.2.1 ht.2.1 next ++ R.formulas r t.2.2 ht.2.2 next)

def WordRangeDecoration.count {σ : Type*} : {n : ℕ} → WordRangeDecoration σ n → ℕ
  | 0, .leaf ranges => ranges.length
  | _ + 1, .node ranges L R => ranges.length + L.count + R.count

theorem WordRangeDecoration.formulas_length {σ : Type*} {n : ℕ}
    (D : WordRangeDecoration σ n) (template : WordTransferTemplate σ n)
    (t : FrequencyTree ℤ n) (ht : NonzeroInternalFrequencies n t) (env : σ → HistoryFormula σ) :
    (D.formulas template t ht env).length = D.count := by
  induction template generalizing env with
  | leaf word => cases D; simp only [formulas, count, List.length_map]
  | node d l r ihL ihR =>
    cases D
    simp only [formulas, count, List.length_append, List.length_map, ihL, ihR]
    omega

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_WordRangeBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Concrete complexity of all replayed intermediate range tests -/

namespace Ostmann

open scoped Classical

def WordRangeDecoration.WordsBounded {σ : Type*} (B : ℕ) :
    {n : ℕ} → WordRangeDecoration σ n → Prop
  | 0, .leaf ranges => ∀ r ∈ ranges, r.word.length + 1 ≤ B
  | _ + 1, .node ranges L R =>
      (∀ r ∈ ranges, r.word.length + 1 ≤ B) ∧ L.WordsBounded B ∧ R.WordsBounded B

def WordRangeDecoration.CountBounded {σ : Type*} (K : ℕ) :
    {n : ℕ} → WordRangeDecoration σ n → Prop
  | 0, .leaf ranges => ranges.length ≤ K
  | _ + 1, .node ranges L R => ranges.length ≤ K ∧ L.CountBounded K ∧ R.CountBounded K

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_ExpandedScheduleRanges
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Original atom-product and word-bin ranges on the expanded schedule -/

namespace Ostmann

open scoped Classical

structure ScheduleAtomRange {I : Type*} (role : I → CopyScheduleRole) (n : ℕ) where
  atoms : List (CopyScheduleAtoms role n)
  lower : ℝ
  upper : ℝ

noncomputable def ScheduleAtomRange.Holds {I : Type*} {role : I → CopyScheduleRole} {n : ℕ}
    (r : ScheduleAtomRange role n) (x : CopyScheduleAtoms role n → ℕ) : Prop :=
  ((r.atoms.map x).prod : ℝ) ∈ Set.Icc r.lower r.upper

noncomputable def ScheduleAtomRange.toWord {I σ : Type*} {role : I → CopyScheduleRole} {n : ℕ}
    (r : ScheduleAtomRange role n) (current : CopyScheduleAtoms role n → List σ) : WordRange σ :=
  ⟨r.atoms.flatMap current, r.lower, r.upper⟩

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_WordRangeWeight
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The recursive weight with every intermediate range retained -/

namespace Ostmann

open scoped BigOperators Classical SchwartzMap FourierTransform ComplexConjugate

noncomputable def WordRangeDecoration.weight {σ : Type*}
    (leaf : WordTransferState σ → ℤ → ℂ) :
    {n : ℕ} → WordRangeDecoration σ n → WordTransferTemplate σ n →
      (σ → ℕ) → FrequencyTree ℤ n → ℂ
  | 0, .leaf ranges, .leaf word, x, v =>
      (if ∀ r ∈ ranges, r.Holds x then 1 else 0) * leaf ((WordTransferTemplate.leaf word).state x) v
  | n + 1, .node ranges L R, .node d l r, x, t =>
      let P := historyPivot (wordTransferSystem σ) ((WordTransferTemplate.node d l r).state x)
        t.1 (frequencyRoot n t.2.1) (frequencyRoot n t.2.2)
      if ValidTransferNode (wordTransferSystem σ) ((WordTransferTemplate.node d l r).state x)
          t.1 (frequencyRoot n t.2.1) (frequencyRoot n t.2.2) P then
        (if ∀ q ∈ ranges, q.Holds x then 1 else 0) *
          L.weight leaf l (Function.update x d.target P) t.2.1 *
          star (R.weight leaf r (Function.update x d.target P) t.2.2)
      else 0

noncomputable def WordFourierParameters.rangedCoefficient {σ : Type*} {n : ℕ}
    (p : WordFourierParameters n) (D : WordRangeDecoration σ n)
    (template : WordTransferTemplate σ n) (t : FrequencyTree ℤ n)
    (ht : NonzeroInternalFrequencies n t) (x : σ → ℤ) : ℂ :=
  (if ∀ r ∈ D.formulas template t ht .prime, r.Holds x then 1 else 0) * p.coefficient template t ht x

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_WordRangePolynomial
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The exact finite polynomial guard for all intermediate range tests -/

namespace Ostmann

open scoped BigOperators Classical

noncomputable def WordRangeDecoration.rangeAt {σ : Type*} {n : ℕ}
    (D : WordRangeDecoration σ n) (template : WordTransferTemplate σ n)
    (t : FrequencyTree ℤ n) (ht : NonzeroInternalFrequencies n t) (i : Fin D.count) : HistoryRange σ :=
  (D.formulas template t ht .prime)[i.val]'(by rw [D.formulas_length]; exact i.isLt)

noncomputable def WordRangeDecoration.polynomials {σ : Type*} {n : ℕ}
    (D : WordRangeDecoration σ n) (template : WordTransferTemplate σ n)
    (t : FrequencyTree ℤ n) (ht : NonzeroInternalFrequencies n t) (a : σ → ℤ) (coord : σ) :
    Fin (D.count + D.count) → Polynomial ℝ :=
  formulaRangePolynomials (fun i => (D.rangeAt template t ht i).formula)
    (fun i => (a i : ℝ)) coord (fun i => (D.rangeAt template t ht i).lower)
    (fun i => (D.rangeAt template t ht i).upper)

namespace WordFourierParameters

noncomputable def rangedPolynomials {σ : Type*} {n : ℕ} (p : WordFourierParameters n)
    (D : WordRangeDecoration σ n) (template : WordTransferTemplate σ n)
    (t : FrequencyTree ℤ n) (ht : NonzeroInternalFrequencies n t) (a : σ → ℤ) (coord : σ) :=
  Fin.append (p.polynomials template t ht a coord) (D.polynomials template t ht a coord)

noncomputable def rangedKeep {σ : Type*} {n : ℕ}
    (D : WordRangeDecoration σ n) (template : WordTransferTemplate σ n)
    (t : FrequencyTree ℤ n) (ht : NonzeroInternalFrequencies n t) :=
  pairedPolynomialKeep (keep template t ht) (polynomialRangeKeep D.count)

end WordFourierParameters

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_ExpandedRangeReplay
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The original atom ranges are exactly the replayed prime-word tests -/

namespace Ostmann

open scoped Classical

noncomputable def scheduleAtomRangesValid {I : Type*} [Fintype I]
    (role : I → CopyScheduleRole) (childBound pivotBound : ℕ → ℕ)
    (ranges : (n : ℕ) → List (ScheduleAtomRange role n)) :
    (n : ℕ) → (CopyScheduleAtoms role n → ℕ) → FrequencyTree ℤ n → Prop
  | 0, x, _ => ∀ r ∈ ranges 0, r.Holds x
  | n + 1, x, t =>
      let P := historyPivot (scheduleAtomSystem role childBound pivotBound) ⟨n + 1, x⟩
        t.1 (frequencyRoot n t.2.1) (frequencyRoot n t.2.2)
      (∀ r ∈ ranges (n + 1), r.Holds x) ∧
        scheduleAtomRangesValid role childBound pivotBound ranges n (reverseCopyLabelMap role n true P x) t.2.1 ∧
        scheduleAtomRangesValid role childBound pivotBound ranges n (reverseCopyLabelMap role n false P x) t.2.2

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_WordPrimeReplay
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Replaying the large-prime coprimalities at every reconstructed pivot -/

namespace Ostmann

open scoped Classical

structure HistoryPrimeCheck (σ V : Type*) where
  formula : HistoryFormula σ
  coordinate : V

noncomputable def HistoryPrimeCheck.Holds {σ V : Type*} (g : HistoryPrimeCheck σ V)
    (a : σ → ℤ) (prime : V → ℕ) : Prop :=
  (prime g.coordinate).Coprime (g.formula.integerValue a).natAbs

inductive WordPrimeDecoration (V : Type*) : ℕ → Type _ where
  | leaf : WordPrimeDecoration V 0
  | node {n : ℕ} (coordinates : List V)
      (left right : WordPrimeDecoration V n) : WordPrimeDecoration V (n + 1)

noncomputable def WordPrimeDecoration.ValidAt {σ V : Type*} :
    {n : ℕ} → WordPrimeDecoration V n → WordTransferTemplate σ n →
      (σ → ℕ) → (V → ℕ) → FrequencyTree ℤ n → Prop
  | 0, .leaf, .leaf _, _, _, _ => True
  | n + 1, .node coordinates L R, .node d l r, x, prime, t =>
      let P := historyPivot (wordTransferSystem σ) ((WordTransferTemplate.node d l r).state x)
        t.1 (frequencyRoot n t.2.1) (frequencyRoot n t.2.2)
      (∀ v ∈ coordinates, (prime v).Coprime P) ∧
        L.ValidAt l (Function.update x d.target P) prime t.2.1 ∧
        R.ValidAt r (Function.update x d.target P) prime t.2.2

noncomputable def WordPrimeDecoration.checks {σ V : Type*} :
    {n : ℕ} → WordPrimeDecoration V n → WordTransferTemplate σ n →
      (t : FrequencyTree ℤ n) → NonzeroInternalFrequencies n t →
        (σ → HistoryFormula σ) → List (HistoryPrimeCheck σ V)
  | 0, .leaf, .leaf _, _, _, _ => []
  | n + 1, .node coordinates L R, .node d l r, t, ht, env =>
      let step := wordTransferStep d t.1 (frequencyRoot n t.2.1) (frequencyRoot n t.2.2) ht.1
      let next := BranchingWordHistory.updatedFormulas step env
      coordinates.map (fun v => ⟨step.formula.bind env, v⟩) ++
        (L.checks l t.2.1 ht.2.1 next ++ R.checks r t.2.2 ht.2.2 next)

def WordPrimeDecoration.count {V : Type*} : {n : ℕ} → WordPrimeDecoration V n → ℕ
  | 0, .leaf => 0
  | _ + 1, .node coordinates L R => coordinates.length + L.count + R.count

theorem WordPrimeDecoration.checks_length {σ V : Type*} {n : ℕ}
    (D : WordPrimeDecoration V n) (template : WordTransferTemplate σ n)
    (t : FrequencyTree ℤ n) (ht : NonzeroInternalFrequencies n t) (env : σ → HistoryFormula σ) :
    (D.checks template t ht env).length = D.count := by
  induction template generalizing env with
  | leaf word => cases D; rfl
  | node d l r ihL ihR =>
    cases D
    simp only [checks, count, List.length_append, List.length_map, ihL, ihR]
    omega

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_WordPrimeBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Derived size, integrality and denominator bounds for the prime checks -/

namespace Ostmann

open scoped Classical

def WordPrimeDecoration.CountBounded {V : Type*} (K : ℕ) :
    {n : ℕ} → WordPrimeDecoration V n → Prop
  | 0, .leaf => True
  | _ + 1, .node coordinates L R =>
      coordinates.length ≤ K ∧ L.CountBounded K ∧ R.CountBounded K

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_WordUnitReplay
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Inherited frequency-unit tests along the actual word reconstruction -/

namespace Ostmann

open scoped Classical

structure HistoryUnitGuard (σ : Type*) where
  formula : HistoryFormula σ
  modulus : ℕ

noncomputable def HistoryUnitGuard.Holds {σ : Type*} (g : HistoryUnitGuard σ) (a : σ → ℤ) : Prop :=
  smallDivisionTest (MvPolynomial.eval₂Hom (RingHom.id ℤ) a g.formula.cleared.numerator)
    g.formula.cleared.denominator g.modulus

noncomputable def WordRange.toUnitGuard {σ : Type*} (r : WordRange σ)
    (env : σ → HistoryFormula σ) (s : ℤ) : HistoryUnitGuard σ :=
  ⟨(r.toHistory env).formula, s.natAbs⟩

/-- The same word lists that specify ranges also specify product-unit tests.
The interval endpoints are irrelevant for this additional support family. -/
noncomputable def WordRangeDecoration.UnitsAt {σ : Type*} :
    {n : ℕ} → WordRangeDecoration σ n → WordTransferTemplate σ n →
      (σ → ℕ) → FrequencyTree ℤ n → Prop
  | 0, .leaf ranges, .leaf _, x, v => ∀ r ∈ ranges, ((r.word.map x).prod).Coprime v.natAbs
  | n + 1, .node ranges L R, .node d l r, x, t =>
      let P := historyPivot (wordTransferSystem σ) ((WordTransferTemplate.node d l r).state x)
        t.1 (frequencyRoot n t.2.1) (frequencyRoot n t.2.2)
      (∀ q ∈ ranges, ((q.word.map x).prod).Coprime t.1.natAbs) ∧
        L.UnitsAt l (Function.update x d.target P) t.2.1 ∧
        R.UnitsAt r (Function.update x d.target P) t.2.2

noncomputable def WordRangeDecoration.unitGuards {σ : Type*} :
    {n : ℕ} → WordRangeDecoration σ n → WordTransferTemplate σ n →
      (t : FrequencyTree ℤ n) → NonzeroInternalFrequencies n t →
        (σ → HistoryFormula σ) → List (HistoryUnitGuard σ)
  | 0, .leaf ranges, .leaf _, v, _, env => ranges.map (fun r => r.toUnitGuard env v)
  | n + 1, .node ranges L R, .node d l r, t, ht, env =>
      let next := BranchingWordHistory.updatedFormulas
        (wordTransferStep d t.1 (frequencyRoot n t.2.1) (frequencyRoot n t.2.2) ht.1) env
      ranges.map (fun q => q.toUnitGuard env t.1) ++
        (L.unitGuards l t.2.1 ht.2.1 next ++ R.unitGuards r t.2.2 ht.2.2 next)

theorem WordRangeDecoration.unitGuards_length {σ : Type*} {n : ℕ}
    (D : WordRangeDecoration σ n) (template : WordTransferTemplate σ n)
    (t : FrequencyTree ℤ n) (ht : NonzeroInternalFrequencies n t) (env : σ → HistoryFormula σ) :
    (D.unitGuards template t ht env).length = D.count := by
  induction template generalizing env with
  | leaf word => cases D; simp only [unitGuards, count, List.length_map]
  | node d l r ihL ihR =>
    cases D
    simp only [unitGuards, count, List.length_append, List.length_map, ihL, ihR]
    omega

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_WordUnitCoefficient
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Exact residue support for all inherited word units -/

namespace Ostmann

open scoped Classical

noncomputable def WordRangeDecoration.unitAt {σ : Type*} {n : ℕ}
    (U : WordRangeDecoration σ n) (template : WordTransferTemplate σ n)
    (t : FrequencyTree ℤ n) (ht : NonzeroInternalFrequencies n t) (i : Fin U.count) : HistoryUnitGuard σ :=
  (U.unitGuards template t ht .prime)[i.val]'(by rw [U.unitGuards_length]; exact i.isLt)

namespace WordFourierParameters

noncomputable def unitRangedCoefficient {σ : Type*} {n : ℕ} (p : WordFourierParameters n)
    (U D : WordRangeDecoration σ n) (template : WordTransferTemplate σ n)
    (t : FrequencyTree ℤ n) (ht : NonzeroInternalFrequencies n t) (x : σ → ℤ) : ℂ :=
  (if ∀ g ∈ U.unitGuards template t ht .prime, g.Holds x then 1 else 0) *
    p.rangedCoefficient D template t ht x

end WordFourierParameters

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_ExpandedUnitReplay
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Original atom frequency-units on the expanded prime-word schedule -/

namespace Ostmann

open scoped Classical

noncomputable def scheduleAtomUnitsValid {I : Type*} [Fintype I]
    (role : I → CopyScheduleRole) (childBound pivotBound : ℕ → ℕ)
    (ranges : (n : ℕ) → List (ScheduleAtomRange role n)) :
    (n : ℕ) → (CopyScheduleAtoms role n → ℕ) → FrequencyTree ℤ n → Prop
  | 0, x, v => ∀ r ∈ ranges 0, ((r.atoms.map x).prod).Coprime v.natAbs
  | n + 1, x, t =>
      let P := historyPivot (scheduleAtomSystem role childBound pivotBound) ⟨n + 1, x⟩
        t.1 (frequencyRoot n t.2.1) (frequencyRoot n t.2.2)
      (∀ r ∈ ranges (n + 1), ((r.atoms.map x).prod).Coprime t.1.natAbs) ∧
        scheduleAtomUnitsValid role childBound pivotBound ranges n (reverseCopyLabelMap role n true P x) t.2.1 ∧
        scheduleAtomUnitsValid role childBound pivotBound ranges n (reverseCopyLabelMap role n false P x) t.2.2

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_TotalAtomUnits
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The actual unit condition on every current atom at every frequency -/

namespace Ostmann

open scoped BigOperators Classical

noncomputable def totalAtomUnitRanges {I : Type*} [Fintype I]
    (role : I → CopyScheduleRole) (n : ℕ) : List (ScheduleAtomRange role n) :=
  [⟨Finset.univ.toList, 0, 0⟩]

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_WordPrimeCheckBound
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Original-prior cancellation retains every reconstructed prime check -/

namespace Ostmann

open scoped BigOperators Classical

noncomputable def WordPrimeDecoration.checkAt {σ V : Type*} {n : ℕ}
    (D : WordPrimeDecoration V n) (template : WordTransferTemplate σ n)
    (t : FrequencyTree ℤ n) (ht : NonzeroInternalFrequencies n t)
    (i : Fin D.count) : HistoryPrimeCheck σ V :=
  (D.checks template t ht .prime)[i.val]'(by rw [D.checks_length]; exact i.isLt)

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_PrimeWordCoefficient
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The coefficient retaining the large-prime coprimality support -/

namespace Ostmann.WordFourierParameters

open scoped Classical

noncomputable def primeUnitRangedCoefficient {V : Type*} {n : ℕ} (p : WordFourierParameters n)
    (C : WordPrimeDecoration V n)
    (U D : WordRangeDecoration (ExpandedScheduledVariable V n) n)
    (template : WordTransferTemplate (ExpandedScheduledVariable V n) n)
    (t : FrequencyTree ℤ n) (ht : NonzeroInternalFrequencies n t) (x : V → ℕ) : ℂ :=
  if ∀ g ∈ C.checks template t ht .prime,
      g.Holds (expandedPrimeValues n (fun i => (x i : ℤ))) x then
    p.unitRangedCoefficient U D template t ht (expandedPrimeValues n (fun i => (x i : ℤ)))
  else 0

end Ostmann.WordFourierParameters

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_ScheduleFullCoprime
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Recovering the complete large-coprimality support from the reduced tests -/

namespace Ostmann

open scoped BigOperators Classical

/-- The original requirements at every reversed transfer: current atoms are
pairwise coprime, and the inserted pivot is coprime to every current atom. -/
noncomputable def scheduleAtomFullCoprimeValid {I : Type*} [Fintype I]
    (role : I → CopyScheduleRole) (childBound pivotBound : ℕ → ℕ) :
    (n : ℕ) → (CopyScheduleAtoms role n → ℕ) → FrequencyTree ℤ n → Prop
  | 0, x, _ => Pairwise (fun i j => (x i).Coprime (x j))
  | n + 1, x, t =>
      let P := historyPivot (scheduleAtomSystem role childBound pivotBound) ⟨n + 1, x⟩
        t.1 (frequencyRoot n t.2.1) (frequencyRoot n t.2.2)
      Pairwise (fun i j => (x i).Coprime (x j)) ∧ (∀ i, P.Coprime (x i)) ∧
        scheduleAtomFullCoprimeValid role childBound pivotBound n
          (reverseCopyLabelMap role n true P x) t.2.1 ∧
        scheduleAtomFullCoprimeValid role childBound pivotBound n
          (reverseCopyLabelMap role n false P x) t.2.2

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_FullAtomTransferWeight
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The complete grouped weight as a single supported recursive weight -/

namespace Ostmann

open scoped BigOperators Classical ComplexConjugate SchwartzMap FourierTransform

noncomputable def fullAtomWeightGuard {I : Type*} [Fintype I]
    (role : I → CopyScheduleRole) (childBound pivotBound : ℕ → ℕ)
    (ranges : (j : ℕ) → List (ScheduleAtomRange role j)) (n : ℕ)
    (x : CopyScheduleAtoms role n → ℕ) (t : FrequencyTree ℤ n) : Prop :=
  scheduleAtomFullCoprimeValid role childBound pivotBound n x t ∧
  scheduleAtomUnitsValid role childBound pivotBound (totalAtomUnitRanges role) n x t ∧
  scheduleAtomRangesValid role childBound pivotBound ranges n x t

noncomputable def fullAtomTransferWeight {I : Type*} [Fintype I]
    (role : I → CopyScheduleRole) (childBound pivotBound : ℕ → ℕ)
    (ranges : (j : ℕ) → List (ScheduleAtomRange role j))
    (leaf : ScheduleAtomState role → ℤ → ℂ) (n : ℕ)
    (x : CopyScheduleAtoms role n → ℕ) (t : FrequencyTree ℤ n) : ℂ :=
  if fullAtomWeightGuard role childBound pivotBound ranges n x t then
    recursiveTransferWeight (scheduleAtomSystem role childBound pivotBound) leaf (fun _ _ _ _ => 1)
      n ⟨n, x⟩ t else 0

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Tree_RationalQuartetCut
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Cutting an actual rational tree at its bottom quartets

The option-valued state records ancestor validity. On a valid cut each
state contains the original depth-two tree and its propagated current
entries. No quartet replacement or independence hypothesis is used.
-/

namespace Ostmann

open scoped BigOperators

@[implicit_reducible] def treeLeafMap {A B : Type*} (f : A → B) : (n : ℕ) →
    TreeLeafTuple A n → TreeLeafTuple B n
  | 0, a => f a
  | n + 1, a => (treeLeafMap f n a.1, treeLeafMap f n a.2)

def treeLeafZipProduct {A B R : Type*} [Mul R] (f : A → B → R) : (n : ℕ) →
    TreeLeafTuple A n → TreeLeafTuple B n → R
  | 0, a, b => f a b
  | n + 1, a, b => treeLeafZipProduct f n a.1 b.1 * treeLeafZipProduct f n a.2 b.2

def RationalTreeData.cutTwo {U : Type*} [CommGroup U] : (n : ℕ) → {C : U} →
    RationalTreeData U (n + 2) C → RationalTreeData U n C
  | 0, C, T => .leaf T.frequency C
  | n + 1, _, .node s CL CR u left right =>
    .node s CL CR u (left.cutTwo n) (right.cutTwo n)

@[simp] theorem RationalTreeData.frequency_cutTwo {U : Type*} [CommGroup U]
    (n : ℕ) {C : U} (T : RationalTreeData U (n + 2) C) :
    (T.cutTwo n).frequency = T.frequency := by
  cases n with
  | zero => rfl
  | succ n => cases T; rfl

structure RationalQuartetState (p : ℕ) [Fact p.Prime] where
  C : (ZMod p)ˣ
  tree : RationalTreeData (ZMod p)ˣ 2 C
  XL : (ZMod p)ˣ
  XR : (ZMod p)ˣ
  conjugations : TreeLeafTuple Bool 2

@[implicit_reducible] def treeLeafZip {A B : Type*} : (n : ℕ) → TreeLeafTuple A n → TreeLeafTuple B n →
    TreeLeafTuple (A × B) n
  | 0, a, b => (a, b)
  | n + 1, a, b => (treeLeafZip n a.1 b.1, treeLeafZip n a.2 b.2)

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_MovingGiantArchimedean
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The actual terminal moduli as quadratic functions of a top giant

Small prime values are fixed here. Every reconstructed giant is linear in the
initial pair, and each terminal modulus is a product of two such linear forms.
The identification uses the integer support equations of the original sampler.
-/

namespace Ostmann
open scoped Classical

noncomputable def MovingSlotReversal.realPivot {σ : Type*}
    (s : MovingSlotReversal σ) (value : σ → ℕ) (XL XR : ℝ) : ℝ :=
  ((s.leftFrequency : ℝ) * (MovingSlotReversal.naturalProduct value s.rightSlots : ℝ) * XR -
    (s.rightFrequency : ℝ) * (MovingSlotReversal.naturalProduct value s.leftSlots : ℝ) * XL) /
    ((s.rootFrequency : ℝ) * (MovingSlotReversal.naturalProduct value s.compensationSlots : ℝ))

noncomputable def MovingSlotReversal.pivotPolynomial {σ : Type*}
    (s : MovingSlotReversal σ) (value : σ → ℕ) (XL XR : Polynomial ℝ) : Polynomial ℝ :=
  Polynomial.C (((s.rootFrequency : ℝ) *
      (MovingSlotReversal.naturalProduct value s.compensationSlots : ℝ))⁻¹) *
    (Polynomial.C ((s.leftFrequency : ℝ) *
        (MovingSlotReversal.naturalProduct value s.rightSlots : ℝ)) * XR -
      Polynomial.C ((s.rightFrequency : ℝ) *
        (MovingSlotReversal.naturalProduct value s.leftSlots : ℝ)) * XL)

/-- The terminal integer moduli, with the same pivot divisions and child order
as the full recursive coefficient. -/
def MovingSlotData.leafModuli {σ : Type*} (value : σ → ℕ) :
    {n : ℕ} → MovingSlotData σ n → ℕ → ℕ → TreeLeafIndex n → ℕ
  | _, .leaf _ regular, XL, XR, _ => XL * XR * MovingSlotReversal.naturalProduct value regular
  | _, .node s CL CR u left right, XL, XR, i =>
      let p := (MovingSlotData.step s CL CR u left right false).naturalPivot value XL XR
      match i with
      | .inl i => left.leafModuli value p XL i
      | .inr i => right.leafModuli value p XR i

/-- Polynomial extension in one free top coordinate. Its coefficients may
contain reciprocals of the fixed frequency and compensation products. -/
noncomputable def MovingSlotData.leafPolynomials {σ : Type*} (value : σ → ℕ) :
    {n : ℕ} → MovingSlotData σ n → Polynomial ℝ → Polynomial ℝ →
      TreeLeafIndex n → Polynomial ℝ
  | _, .leaf _ regular, XL, XR, _ =>
      XL * XR * Polynomial.C (MovingSlotReversal.naturalProduct value regular : ℝ)
  | _, .node s CL CR u left right, XL, XR, i =>
      let p := (MovingSlotData.step s CL CR u left right false).pivotPolynomial value XL XR
      match i with
      | .inl i => left.leafPolynomials value p XL i
      | .inr i => right.leafPolynomials value p XR i

theorem MovingSlotReversal.naturalProduct_ne_zero {σ : Type*}
    (value : σ → ℕ) (hvalue : ∀ i, value i ≠ 0) (slots : List σ) :
    naturalProduct value slots ≠ 0 := by
  induction slots with
  | nil => simp [naturalProduct]
  | cons i slots ih =>
    simpa only [naturalProduct, List.map_cons, List.prod_cons] using mul_ne_zero (hvalue i) ih

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_MovingFourierPolynomials
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The concrete polynomial factors in the moving Fourier history -/

namespace Ostmann
open scoped Classical BigOperators ComplexConjugate SchwartzMap

def MovingSlotData.leafFrequencies {σ : Type*} :
    {n : ℕ} → MovingSlotData σ n → TreeLeafIndex n → ℤ
  | _, .leaf s _, _ => s
  | _, .node _ _ _ _ left _right, .inl i => left.leafFrequencies i
  | _, .node _ _ _ _ _left right, .inr i => right.leafFrequencies i

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_MovingFourierVariation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Constructed variation bounds for the actual moving Fourier factors -/

namespace Ostmann
open scoped Classical BigOperators SchwartzMap

theorem MovingSlotData.leafFrequencies_bound {σ : Type*} {n : ℕ}
    (T : MovingSlotData σ n) (V : ℝ) (h : T.Frequencies (fun s => |(s : ℝ)| ≤ V))
    (i : TreeLeafIndex n) : |(T.leafFrequencies i : ℝ)| ≤ V := by
  induction T with
  | leaf s regular => exact h
  | node s CL CR u left right ihL ihR =>
    cases i with
    | inl i => exact ihL h.2.1 i
    | inr i => exact ihR h.2.2 i

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_MovingNodeGuards
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Polynomial and residue tests for the actual moving-giant node -/

namespace Ostmann
open scoped Classical

def movingNodeWord (childBound pivotBound : ℕ) : WordTransferNode Bool where
  target := false
  left := [false]
  right := [true]
  childBound := childBound
  pivotBound := pivotBound

/-- The two word entries are the complete current child products, including
all regular factors. The reconstructed pivot here is the composite u*p. -/
noncomputable def movingNodeGuard (CL CR : ℕ) (s v w : ℤ) (hs : s ≠ 0)
    (childBound pivotBound : ℕ) (L R : HistoryFormula Bool) : WordTransferGuard Bool :=
  wordTransferGuard (movingNodeWord childBound pivotBound) s v w hs
    (fun b => if b then .product R (.external CR) else .product L (.external CL))

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_MovingGiantFormulas
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Rational formulas retain the actual compensation division -/

namespace Ostmann
open scoped Classical

noncomputable def MovingSlotReversal.giantFormula {σ : Type*}
    (step : MovingSlotReversal σ) (value : σ → ℕ)
    (hs : step.rootFrequency ≠ 0)
    (hu : MovingSlotReversal.naturalProduct value step.compensationSlots ≠ 0)
    (L R : HistoryFormula Bool) : HistoryFormula Bool :=
  .solve (.product L (.external (MovingSlotReversal.naturalProduct value step.leftSlots)))
    (.product R (.external (MovingSlotReversal.naturalProduct value step.rightSlots)))
    step.leftFrequency step.rightFrequency
    (step.rootFrequency * (MovingSlotReversal.naturalProduct value step.compensationSlots : ℤ))
    (mul_ne_zero hs (Int.natCast_ne_zero.mpr hu))

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_MovingFormulaNodes
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # All rational node formulas of the concrete moving sampler -/

namespace Ostmann
open scoped Classical

structure MovingFormulaNode where
  guard : WordTransferGuard Bool
  newGiant : HistoryFormula Bool

noncomputable def MovingSlotData.formulaNodes {σ : Type*} (value : σ → ℕ)
    (hvalue : ∀ i, value i ≠ 0) (childBound pivotBound : ℕ → ℕ) :
    {n : ℕ} → (T : MovingSlotData σ n) → T.Frequencies (· ≠ 0) →
      HistoryFormula Bool → HistoryFormula Bool → List MovingFormulaNode
  | _, .leaf _ _, _, _, _ => []
  | n + 1, .node s CL CR u left right, hf, L, R =>
      let step := MovingSlotData.step s CL CR u left right false
      let P := step.giantFormula value hf.1
        (MovingSlotReversal.naturalProduct_ne_zero value hvalue u) L R
      { guard := movingNodeGuard (MovingSlotReversal.naturalProduct value CL)
          (MovingSlotReversal.naturalProduct value CR) s left.frequency right.frequency hf.1
          (childBound (n + 1)) (pivotBound (n + 1)) L R
        newGiant := P } ::
        (left.formulaNodes value hvalue childBound pivotBound hf.2.1 P L ++
          right.formulaNodes value hvalue childBound pivotBound hf.2.2 P R)

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_MovingArithmeticSupport
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Exact arithmetic support of the constructed moving formulas -/

namespace Ostmann
open scoped Classical

/-- This support is exactly the original node validity together with the
sampled compensation division. It also specifies the actual child giants. -/
def MovingSlotData.ArithmeticSupport {σ : Type*} (value : σ → ℕ)
    (childBound pivotBound : ℕ → ℕ) :
    {n : ℕ} → MovingSlotData σ n → ℕ → ℕ → Prop
  | _, .leaf _ _, _, _ => True
  | n + 1, .node s CL CR u left right, XL, XR =>
      ∃ Q : ℕ, ValidTransferNode (movingSlotSystem value childBound pivotBound)
          ⟨n + 1, .node s CL CR u left right, XL, XR⟩ s left.frequency right.frequency Q ∧
        MovingSlotReversal.naturalProduct value u ∣ Q ∧
        left.ArithmeticSupport value childBound pivotBound (Q / MovingSlotReversal.naturalProduct value u) XL ∧
        right.ArithmeticSupport value childBound pivotBound (Q / MovingSlotReversal.naturalProduct value u) XR

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_MovingResidueTests
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Three explicit residue tests at each original moving node -/

namespace Ostmann
open scoped Classical BigOperators

noncomputable def MovingFormulaNode.testFormulas (f : MovingFormulaNode) : Fin 3 → HistoryFormula Bool :=
  ![f.guard.pivot, f.guard.rightProduct, f.newGiant]

def MovingFormulaNode.testModuli (f : MovingFormulaNode) : Fin 3 → ℕ :=
  ![f.guard.right.natAbs, f.guard.root.natAbs, 1]

noncomputable def MovingFormulaNode.residueTests (f : MovingFormulaNode) (a : Bool → ℤ) : Prop :=
  ∀ j, smallDivisionTest
    (MvPolynomial.eval₂Hom (RingHom.id ℤ) a (f.testFormulas j).cleared.numerator)
    (f.testFormulas j).cleared.denominator (f.testModuli j)

/-- The actual common period is built from the cleared formula denominators
and the two retained frequency moduli. -/
noncomputable def MovingFormulaNode.residuePeriod (f : MovingFormulaNode) : ℕ :=
  ∏ j : Fin 3, (f.testFormulas j).cleared.denominator.natAbs * f.testModuli j

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_MovingLogLeaves
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Logarithmic derivatives of the actual terminal moving moduli -/

namespace Ostmann

noncomputable def MovingSlotData.realLeafModuli {σ : Type*} (value : σ → ℕ) :
    {n : ℕ} → MovingSlotData σ n → ℝ → ℝ → TreeLeafIndex n → ℝ
  | _, .leaf _ regular, L, R, _ => L * R * MovingSlotReversal.naturalProduct value regular
  | _, .node s CL CR u left right, L, R, i =>
      let p := (MovingSlotData.step s CL CR u left right false).realPivot value L R
      match i with
      | .inl i => left.realLeafModuli value p L i
      | .inr i => right.realLeafModuli value p R i

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_MovingRealResidues
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Separating the original arithmetic gate into residues and real inequalities -/

namespace Ostmann
open scoped Classical

noncomputable def HistoryFormula.realEval {σ : Type*} (F : HistoryFormula σ) (x : σ → ℝ) : ℝ :=
  MvPolynomial.eval₂ (Int.castRingHom ℝ) x F.cleared.numerator / F.cleared.denominator

noncomputable def WordTransferGuard.archimedeanAt {σ : Type*}
    (g : WordTransferGuard σ) (x : σ → ℝ) : Prop :=
  1 ≤ g.pivot.realEval x ∧ g.pivot.realEval x ≤ g.pivotBound ∧
    ((2 * g.pivotBound * g.childBound + 1 : ℕ) : ℝ) ≤ g.rightProduct.realEval x

noncomputable def WordTransferGuard.realPolynomials {σ : Type*}
    (g : WordTransferGuard σ) (a : σ → ℝ) (coord : σ) : Fin 3 → Polynomial ℝ :=
  ![formulaPolynomial g.pivot a coord - Polynomial.C 1,
    Polynomial.C (g.pivotBound : ℝ) - formulaPolynomial g.pivot a coord,
    formulaPolynomial g.rightProduct a coord -
      Polynomial.C ((2 * g.pivotBound * g.childBound + 1 : ℕ) : ℝ)]

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_MovingSignedSpectator
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Signed residue representatives for the literal spectator recursion -/

namespace Ostmann
open scoped Classical

noncomputable def MovingSlotReversal.signedPivot {σ : Type*} (s : MovingSlotReversal σ)
    (value : σ → ℕ) (XL XR : ℤ) : ℤ :=
  (s.leftFrequency * (XR * (naturalProduct value s.rightSlots : ℤ)) -
    s.rightFrequency * (XL * (naturalProduct value s.leftSlots : ℤ))) /
      (s.rootFrequency * (naturalProduct value s.compensationSlots : ℤ))

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Characters_LogCutoffPolynomial
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Polynomial factors for the actual logarithmic node cutoff -/

namespace Ostmann

theorem log_lipschitz_on_positive_ray (a x y : ℝ) (ha : 0 < a)
    (hx : a ≤ x) (hy : a ≤ y) : |Real.log x - Real.log y| ≤ a⁻¹ * |x - y| := by
  have hordered (x y : ℝ) (hx : a ≤ x) (hxy : x ≤ y) :
      |Real.log x - Real.log y| ≤ a⁻¹ * |x - y| := by
    have hx0 : 0 < x := ha.trans_le hx
    have hy0 : 0 < y := hx0.trans_le hxy
    have hl := Real.log_le_sub_one_of_pos (div_pos hy0 hx0)
    rw [Real.log_div (ne_of_gt hy0) (ne_of_gt hx0)] at hl
    have he : y / x - 1 = (y - x) * x⁻¹ := by field_simp
    rw [he] at hl
    rw [abs_of_nonpos (sub_nonpos.mpr (Real.log_le_log hx0 hxy)),
      abs_of_nonpos (sub_nonpos.mpr hxy)]
    calc
      _ = Real.log y - Real.log x := by ring
      _ ≤ (y - x) * x⁻¹ := hl
      _ ≤ (y - x) * a⁻¹ :=
        mul_le_mul_of_nonneg_left (inv_anti₀ ha hx) (sub_nonneg.mpr hxy)
      _ = _ := by ring
  rcases le_total x y with hxy | hyx
  · exact hordered x y hx hxy
  · simpa only [abs_sub_comm] using hordered y x hy hyx

noncomputable def positiveLogCutoff (φ : ℝ → ℝ) (G x : ℝ) : ℝ :=
  if 0 < x then φ (Real.log x - G) else 0

/-- The center appears in the lower endpoint and its reciprocal Lipschitz
constant. These cancel in the total variation budget. -/
noncomputable def logCutoffPolynomialFactor (P : Polynomial ℝ) (φ : ℝ → ℝ)
    (G B D : ℝ) (hB : 0 ≤ B) (hD : 0 ≤ D)
    (hφ : ∀ x, |φ x| ≤ B) (hlip : ∀ x y, |φ x - φ y| ≤ D * |x - y|) :
    ClippedPolynomialFactor where
  polynomial := P
  profile x := (φ (Real.log x - G) : ℂ)
  lo := Real.exp (G - 1)
  hi := Real.exp (G + 1)
  bound := B
  lip := D * (Real.exp (G - 1))⁻¹
  lo_le_hi := Real.exp_le_exp.mpr (by linarith)
  bound_nonneg := hB
  lip_nonneg := mul_nonneg hD (inv_nonneg.mpr (Real.exp_pos _).le)
  norm_le x _ := by simpa only [Complex.norm_real, Real.norm_eq_abs] using hφ (Real.log x - G)
  lipschitz x hx y hy := by
    simp only [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
    calc
      _ ≤ D * |(Real.log x - G) - (Real.log y - G)| := hlip _ _
      _ = D * |Real.log x - Real.log y| := by congr 2; ring
      _ ≤ D * ((Real.exp (G - 1))⁻¹ * |x - y|) :=
        mul_le_mul_of_nonneg_left (log_lipschitz_on_positive_ray _ x y (Real.exp_pos _) hx.1 hy.1) hD
      _ = _ := by ring

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_MovingCutoffPolynomials
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # All actual logarithmic node cutoffs as polynomial factors -/

namespace Ostmann
open scoped Classical BigOperators

noncomputable def MovingSlotData.nodeCutoffPolynomials {σ : Type*} (value : σ → ℕ) :
    {n : ℕ} → MovingSlotData σ n → Polynomial ℝ → Polynomial ℝ → List (ℕ × Polynomial ℝ)
  | _, .leaf _ _, _, _ => []
  | n + 1, .node s CL CR u left right, L, R =>
      let P := (MovingSlotData.step s CL CR u left right false).pivotPolynomial value L R
      (n + 1, P) :: (left.nodeCutoffPolynomials value P L ++ right.nodeCutoffPolynomials value P R)

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_RealSlotEvaluation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Real bulk coordinates in the original smooth moving tree -/

namespace Ostmann
open scoped Classical BigOperators SchwartzMap ComplexConjugate

noncomputable def realSlotProduct {σ : Type*} (value : σ → ℝ) (slots : List σ) : ℝ :=
  (slots.map value).prod

noncomputable def MovingSlotReversal.realValuePivot {σ : Type*}
    (s : MovingSlotReversal σ) (value : σ → ℝ) (L R : ℝ) : ℝ :=
  ((s.leftFrequency : ℝ) * realSlotProduct value s.rightSlots * R -
    (s.rightFrequency : ℝ) * realSlotProduct value s.leftSlots * L) /
    ((s.rootFrequency : ℝ) * realSlotProduct value s.compensationSlots)

noncomputable def MovingSlotData.realValueLeafModuli {σ : Type*} (value : σ → ℝ) :
    {n : ℕ} → MovingSlotData σ n → ℝ → ℝ → TreeLeafIndex n → ℝ
  | _, .leaf _ regular, L, R, _ => L * R * realSlotProduct value regular
  | _, .node s CL CR u left right, L, R, j =>
      let p := (MovingSlotData.step s CL CR u left right false).realValuePivot value L R
      match j with
      | .inl j => left.realValueLeafModuli value p L j
      | .inr j => right.realValueLeafModuli value p R j

noncomputable def realValueNodeCutoff {σ : Type*} (value : σ → ℝ)
    (φ : ℝ → ℝ) (G : ℕ → ℝ) : {n : ℕ} → MovingSlotData σ n → ℝ → ℝ → ℂ
  | _, .leaf _ _, _, _ => 1
  | n + 1, .node s CL CR u left right, L, R =>
      let p := (MovingSlotData.step s CL CR u left right false).realValuePivot value L R
      (positiveLogCutoff φ (G (n + 1)) p : ℂ) *
        realValueNodeCutoff value φ G left p L * realValueNodeCutoff value φ G right p R

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_BulkSlotPolynomials
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Polynomial dependence on one original bulk-prime slot -/

namespace Ostmann
open scoped Classical

/-- A bulk coordinate never occurs in any compensation denominator. -/
def MovingSlotData.CompensationAbsent {σ : Type*} (i : σ) :
    {n : ℕ} → MovingSlotData σ n → Prop
  | _, .leaf _ _ => True
  | _, .node _ _ _ u left right =>
      i ∉ u ∧ left.CompensationAbsent i ∧ right.CompensationAbsent i

theorem MovingSlotData.compensationAbsent_of_levels {σ : Type*}
    (tier : σ → ℕ) {n : ℕ} (T : MovingSlotData σ n)
    (hT : T.Levels tier) (i : σ) (hi : n ≤ tier i) : T.CompensationAbsent i := by
  induction T with
  | leaf => trivial
  | @node n s CL CR u left right ihL ihR =>
    refine ⟨?_, ihL hT.2.2.2.1 (by omega), ihR hT.2.2.2.2 (by omega)⟩
    intro hu
    have := hT.2.2.1 i hu
    omega

noncomputable def bulkSlotProduct {σ : Type*} (value : σ → ℝ)
    (i : σ) (slots : List σ) : Polynomial ℝ :=
  (slots.map (fun j => if j = i then Polynomial.X else Polynomial.C (value j))).prod

theorem realSlotProduct_update_of_absent {σ : Type*} (value : σ → ℝ)
    (i : σ) (slots : List σ) (hi : i ∉ slots) (p : ℝ) :
    realSlotProduct (Function.update value i p) slots =
      realSlotProduct value slots := by
  unfold realSlotProduct
  congr 1
  apply List.map_congr_left
  intro j hj
  apply Function.update_of_ne
  intro h
  subst j
  exact hi hj

noncomputable def MovingSlotReversal.bulkPivotPolynomial {σ : Type*}
    (s : MovingSlotReversal σ) (value : σ → ℝ) (i : σ)
    (L R : Polynomial ℝ) : Polynomial ℝ :=
  Polynomial.C (((s.rootFrequency : ℝ) *
    realSlotProduct value s.compensationSlots)⁻¹) *
    (Polynomial.C (s.leftFrequency : ℝ) * bulkSlotProduct value i s.rightSlots * R -
      Polynomial.C (s.rightFrequency : ℝ) * bulkSlotProduct value i s.leftSlots * L)

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_SquareLiftExclusions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Dropping the prime-square exclusions in a two-history expansion -/

namespace Ostmann

open scoped BigOperators

/-- Uniform pairs over the fixed giant residues modulo `p`. -/
abbrev SquareLiftPairs (p : ℕ) (x₀ y₀ : ZMod p) :=
  {x : ZMod (p ^ 2) // squareReduction p x = x₀} ×
    {y : ZMod (p ^ 2) // squareReduction p y = y₀}

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_MovingRegularSlots
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The original regular slot lists in every moving child -/

namespace Ostmann
open scoped Classical

/-- Current regular slots, before sampling at this node. -/
def MovingSlotData.regularSlots {σ : Type*} : {n : ℕ} → MovingSlotData σ n → List σ
  | _, .leaf _ regular => regular
  | _, .node _ CL CR _ _ _ => CL ++ CR

/-- The child regular slots contain the same compensation vector and the
corresponding parent's regular slots, with their actual per-leaf allocation. -/
def MovingSlotData.RegularCoherent {σ : Type*} : {n : ℕ} → MovingSlotData σ n → Prop
  | _, .leaf _ _ => True
  | _, .node _ CL CR U left right =>
      left.regularSlots.Perm (U ++ CL) ∧ right.regularSlots.Perm (U ++ CR) ∧
        left.RegularCoherent ∧ right.RegularCoherent

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_MovingPairwiseSupport
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Reducing full moving-history coprimality to the new compensation tests -/

namespace Ostmann
open scoped Classical

def MovingSlotData.currentSlots {σ : Type*} (value : σ → ℕ) {n : ℕ}
    (T : MovingSlotData σ n) (XL XR : ℕ) : List ℕ :=
  XL :: XR :: T.regularSlots.map value

def MovingSlotData.CurrentPairwise {σ : Type*} (value : σ → ℕ) {n : ℕ}
    (T : MovingSlotData σ n) (XL XR : ℕ) : Prop :=
  (T.currentSlots value XL XR).Pairwise Nat.Coprime

/-- Cross-branch frequency tests are retained explicitly at every node. -/
def MovingSlotData.CrossFrequencyUnits {σ : Type*} (value : σ → ℕ) :
    {n : ℕ} → MovingSlotData σ n → ℕ → ℕ → Prop
  | _, .leaf _ _, _, _ => True
  | _, .node s CL CR U left right, XL, XR =>
      let p := (MovingSlotData.step s CL CR U left right false).naturalPivot value XL XR
      IsCoprime left.frequency (XL * MovingSlotReversal.naturalProduct value CL : ℤ) ∧
      IsCoprime right.frequency (XR * MovingSlotReversal.naturalProduct value CR : ℤ) ∧
      left.CrossFrequencyUnits value p XL ∧ right.CrossFrequencyUnits value p XR

def MovingSlotData.FullPairwise {σ : Type*} (value : σ → ℕ) :
    {n : ℕ} → MovingSlotData σ n → ℕ → ℕ → Prop
  | _, T@(.leaf _ _), XL, XR => T.CurrentPairwise value XL XR
  | _, T@(.node s CL CR U left right), XL, XR =>
      let p := (MovingSlotData.step s CL CR U left right false).naturalPivot value XL XR
      T.CurrentPairwise value XL XR ∧ left.FullPairwise value p XL ∧ right.FullPairwise value p XR

def MovingSlotData.NewCompensationUnits {σ : Type*} (value : σ → ℕ) :
    {n : ℕ} → MovingSlotData σ n → ℕ → ℕ → Prop
  | _, .leaf _ _, _, _ => True
  | _, .node s CL CR U left right, XL, XR =>
      let p := (MovingSlotData.step s CL CR U left right false).naturalPivot value XL XR
      ((U.map value).Pairwise Nat.Coprime ∧ p.Coprime (MovingSlotReversal.naturalProduct value U)) ∧
      left.NewCompensationUnits value p XL ∧ right.NewCompensationUnits value p XR

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_MovingSquareSupport
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The explicit prime-square tests for the full moving history -/

namespace Ostmann

def MovingSlotData.CompensationPrimeData {σ : Type*} (value : σ → ℕ) :
    {n : ℕ} → MovingSlotData σ n → Prop
  | _, .leaf _ _ => True
  | _, .node s _ _ U left right =>
      (∀ b ∈ U.map value, b.Prime) ∧ (U.map value).Pairwise Nat.Coprime ∧
      (∀ b ∈ U.map value, ¬ b ∣ s.natAbs) ∧
      left.CompensationPrimeData value ∧ right.CompensationPrimeData value

/-- Equality patterns may identify samples at different nodes; only the
entries made together in one compensation vector have to be distinct. -/
def MovingSlotData.CompensationDistinct {σ : Type*} (value : σ → ℕ) :
    {n : ℕ} → MovingSlotData σ n → Prop
  | _, .leaf _ _ => True
  | _, .node _ _ _ U left right =>
      (U.map value).Pairwise Nat.Coprime ∧
      left.CompensationDistinct value ∧ right.CompensationDistinct value

/-- The numerator at every node is tested before division by the node's
frequency or by its compensation product. -/
def MovingSlotData.PrimeSquareTests {σ : Type*} (value : σ → ℕ) :
    {n : ℕ} → MovingSlotData σ n → ℕ → ℕ → Prop
  | _, .leaf _ _, _, _ => True
  | _, .node s CL CR U left right, XL, XR =>
      let p := (MovingSlotData.step s CL CR U left right false).naturalPivot value XL XR
      (∀ b ∈ U.map value, ¬ (b : ℤ) ^ 2 ∣
        left.frequency * ((XR * MovingSlotReversal.naturalProduct value CR : ℕ) : ℤ) -
        right.frequency * ((XL * MovingSlotReversal.naturalProduct value CL : ℕ) : ℤ)) ∧
      left.PrimeSquareTests value p XL ∧ right.PrimeSquareTests value p XR

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_MovingOccurrenceSquares
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The full square support as the actual occurrence line tests -/

namespace Ostmann
open scoped Classical

def MovingSlotReversal.integerNumerator {σ : Type*} (value : σ → ℕ)
    (s : MovingSlotReversal σ) (pair : ℕ × ℕ) : ℤ :=
  s.leftFrequency * ((pair.2 * MovingSlotReversal.naturalProduct value s.rightSlots : ℕ) : ℤ) -
    s.rightFrequency * ((pair.1 * MovingSlotReversal.naturalProduct value s.leftSlots : ℕ) : ℤ)

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_MovingSignedUnits
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The giant unit tests on signed residue representatives -/

namespace Ostmann
open scoped Classical

/-- The product records every frequency at or below this state. -/
def MovingSlotData.frequencyProduct {σ : Type*} : {n : ℕ} → MovingSlotData σ n → ℤ
  | _, .leaf s _ => s
  | _, .node s _ _ _ left right => s * left.frequencyProduct * right.frequencyProduct

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_MovingFrequencyResidues
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Frequency residues with compensation factors inverted

Unlike the signed integer recursion, this recursion divides only by the
frequency. Compensation factors are inverted modulo a frequency power, so
no internal prime enters its period. One power is consumed per reversal.
-/

namespace Ostmann
open scoped Classical

def MovingSlotReversal.signedNumerator {σ : Type*} (s : MovingSlotReversal σ)
    (value : σ → ℕ) (XL XR : ℤ) : ℤ :=
  s.leftFrequency * (XR * (naturalProduct value s.rightSlots : ℤ)) -
    s.rightFrequency * (XL * (naturalProduct value s.leftSlots : ℤ))

def MovingSlotReversal.frequencyPivot {σ : Type*} (s : MovingSlotReversal σ)
    (value : σ → ℕ) (R : ℤ) (k : ℕ) (XL XR : ℤ) : ℤ :=
  (s.signedNumerator value XL XR / s.rootFrequency) *
    Int.gcdA (naturalProduct value s.compensationSlots : ℤ) (R ^ k)

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_BulkFrequencyResidues
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Frequency support depends only on bulk residue classes -/

namespace Ostmann
open scoped Classical

def MovingSlotData.CompensationAgreement {σ : Type*} (v w : σ → ℕ) :
    {n : ℕ} → MovingSlotData σ n → Prop
  | _, .leaf _ _ => True
  | _, .node _ _ _ u left right =>
      MovingSlotReversal.naturalProduct v u = MovingSlotReversal.naturalProduct w u ∧
        left.CompensationAgreement v w ∧ right.CompensationAgreement v w

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_MovingUnitSampleBound
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The actual sampled regular lists in the full unit-period estimate -/

namespace Ostmann
open scoped Classical

def MovingSlotData.RegularLengthLE {σ : Type*} (D : ℕ) :
    {n : ℕ} → MovingSlotData σ n → Prop
  | _, T@(.leaf _ _) => T.regularSlots.length ≤ D
  | _, T@(.node _ _ _ _ left right) =>
      T.regularSlots.length ≤ D ∧ left.RegularLengthLE D ∧ right.RegularLengthLE D

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_GiantOuterFactors
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The literal two outer cutoff priors and the diagonal reciprocal factor -/

namespace Ostmann
open scoped BigOperators Classical

noncomputable def onePolynomialFactor : ClippedPolynomialFactor where
  polynomial := 0
  profile := fun _ => 1
  lo := 0
  hi := 0
  bound := 1
  lip := 0
  lo_le_hi := le_rfl
  bound_nonneg := zero_le_one
  lip_nonneg := le_rfl
  norm_le := by intro _ _; simp
  lipschitz := by intro _ _ _ _; simp

@[simp] theorem onePolynomialFactor_polynomial : onePolynomialFactor.polynomial = 0 := rfl

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_MovingLineComposition
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Composition of the cleared occurrence lines

The identity works before any descendant division. It lets the current
internal-prime congruence establish integrality inductively, without assuming
the conclusion for the rest of the path.
-/

namespace Ostmann
open scoped Classical

noncomputable def PolynomialGiantRows.evalNumerator {σ R : Type*} [CommRing R]
    (T : PolynomialGiantRows σ) (φ : MvPolynomial σ ℤ →+* R) (x y : R) : R × R :=
  (φ T.rows.a * x + φ T.rows.b * y, φ T.rows.c * x + φ T.rows.d * y)

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_MovingIntegralFrequencySplit
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Exact frequency and internal-prime splitting before real restrictions

All divisions here are integer divisions. Positivity is deliberately left to
the existing real gate. The equivalence recovers integer divisibility from
the two disjoint residue blocks, including at every descendant node.
-/

namespace Ostmann
open scoped Classical

def MovingSlotReversal.SignedIntegralAt {σ : Type*} (s : MovingSlotReversal σ)
    (value : σ → ℕ) (x y : ℤ) : Prop :=
  s.signedNumerator value x y =
    s.rootFrequency * (naturalProduct value s.compensationSlots : ℤ) * s.signedPivot value x y

def MovingSlotData.SignedIntegral {σ : Type*} (value : σ → ℕ) :
    {n : ℕ} → MovingSlotData σ n → ℤ → ℤ → Prop
  | _, .leaf _ _, _, _ => True
  | _, .node s CL CR U left right, x, y =>
      let step := MovingSlotData.step s CL CR U left right false
      let p := step.signedPivot value x y
      step.SignedIntegralAt value x y ∧ left.SignedIntegral value p x ∧ right.SignedIntegral value p y

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_MovingModularSpectator
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Spectator evaluation without internal primes in the period

At a spectator prime the entire reversal denominator is a unit. The field
recursion therefore depends only on the two spectator residues, even though
the original recursion used integer division by compensation products.
-/

namespace Ostmann
open scoped Classical

noncomputable def MovingSlotReversal.modularPivot {σ : Type*} (step : MovingSlotReversal σ)
    (value : σ → ℕ) (q : ℕ) [Fact q.Prime] (x y : ZMod q) : ZMod q :=
  ((step.leftFrequency : ZMod q) * (y * MovingSlotReversal.naturalProduct value step.rightSlots) -
    (step.rightFrequency : ZMod q) * (x * MovingSlotReversal.naturalProduct value step.leftSlots)) /
      ((step.rootFrequency : ZMod q) * MovingSlotReversal.naturalProduct value step.compensationSlots)

def MovingSlotData.ModularDenominators {σ : Type*} (value : σ → ℕ) (q : ℕ) :
    {n : ℕ} → MovingSlotData σ n → Prop
  | _, .leaf _ _ => True
  | _, .node s _ _ U left right =>
      (s : ZMod q) ≠ 0 ∧ (MovingSlotReversal.naturalProduct value U : ZMod q) ≠ 0 ∧
        left.ModularDenominators value q ∧ right.ModularDenominators value q

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_BulkFrequencyFactor
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Separate the nonperiodic prime coincidences from frequency support -/

namespace Ostmann
open scoped Classical ComplexConjugate

def MovingSlotData.FrequencyBounds {σ : Type*} (childBound : ℕ → ℕ) :
    {n : ℕ} → MovingSlotData σ n → Prop
  | _, .leaf _ _ => True
  | n + 1, .node _ _ _ _ left right =>
      left.frequency.natAbs ≤ childBound (n + 1) ∧
      right.frequency.natAbs ≤ childBound (n + 1) ∧
      left.FrequencyBounds childBound ∧ right.FrequencyBounds childBound

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_BulkLeafPolynomials
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Terminal moduli as polynomials in a bulk-prime coordinate -/

namespace Ostmann
open scoped Classical

noncomputable def MovingSlotData.bulkLeafPolynomials {σ : Type*} (value : σ → ℝ) (i : σ) :
    {n : ℕ} → MovingSlotData σ n → Polynomial ℝ → Polynomial ℝ →
      TreeLeafIndex n → Polynomial ℝ
  | _, .leaf _ regular, L, R, _ => L * R * bulkSlotProduct value i regular
  | _, .node s CL CR u left right, L, R, j =>
      let p := (MovingSlotData.step s CL CR u left right false).bulkPivotPolynomial value i L R
      match j with
      | .inl j => left.bulkLeafPolynomials value i p L j
      | .inr j => right.bulkLeafPolynomials value i p R j

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_BulkNodePolynomials
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Every node cutoff in the same bulk-prime polynomial coordinate -/

namespace Ostmann
open scoped Classical BigOperators

noncomputable def MovingSlotData.bulkNodePolynomials {σ : Type*} (value : σ → ℝ) (i : σ) :
    {n : ℕ} → MovingSlotData σ n → Polynomial ℝ → Polynomial ℝ → List (ℕ × Polynomial ℝ)
  | _, .leaf _ _, _, _ => []
  | n + 1, .node s CL CR u left right, L, R =>
      let p := (MovingSlotData.step s CL CR u left right false).bulkPivotPolynomial value i L R
      (n + 1, p) :: (left.bulkNodePolynomials value i p L ++ right.bulkNodePolynomials value i p R)

theorem MovingSlotData.bulkNodePolynomials_length {σ : Type*} (value : σ → ℝ) (i : σ)
    {n : ℕ} (T : MovingSlotData σ n) (L R : Polynomial ℝ) :
    (T.bulkNodePolynomials value i L R).length = 2 ^ n - 1 := by
  induction T generalizing L R with
  | leaf => rfl
  | @node n s CL CR u left right ihL ihR =>
    simp only [bulkNodePolynomials, List.length_cons, List.length_append, ihL, ihR, pow_succ]
    have := Nat.one_le_two_pow (n := n)
    omega

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_BulkLogContinuity
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The smooth tree as a continuous function of the bulk logarithms -/

namespace Ostmann
open scoped Classical BigOperators SchwartzMap ComplexConjugate BoundedContinuousFunction

noncomputable def bulkLogValues {σ : Type*} (base : σ → ℝ) (S : Finset σ)
    (x : σ → ℝ) (i : σ) : ℝ := if i ∈ S then Real.exp (x i) else base i

theorem continuous_bulkLogValues {σ : Type*} (base : σ → ℝ) (S : Finset σ) (i : σ) :
    Continuous (fun x => bulkLogValues base S x i) := by
  unfold bulkLogValues
  split_ifs
  · exact Real.continuous_exp.comp (continuous_apply i)
  · exact continuous_const

theorem continuous_realSlotProduct {σ A : Type*} [TopologicalSpace A]
    (value : A → σ → ℝ) (hv : ∀ i, Continuous (fun x => value x i)) (l : List σ) :
    Continuous (fun x => realSlotProduct (value x) l) := by
  induction l with
  | nil => exact continuous_const
  | cons i l ih => exact (hv i).mul ih

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_HistoryRealEvaluation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Real evaluation of the original cleared history formulas -/

namespace Ostmann.HistoryFormula
open scoped Classical BigOperators

@[simp] theorem realEval_prime {σ : Type*} (i : σ) (x : σ → ℝ) :
    (prime i).realEval x = x i := by
  simp only [realEval, cleared, ClearedHistoryValue.ofVariable, MvPolynomial.eval₂_X,
    Int.cast_one, div_one]

@[simp] theorem realEval_external {σ : Type*} (a : ℤ) (x : σ → ℝ) :
    (external a).realEval x = a := by
  simp only [realEval, cleared, ClearedHistoryValue.constant, MvPolynomial.eval₂_C,
    Int.coe_castRingHom, Int.cast_one, div_one]

@[simp] theorem realEval_product {σ : Type*} (l r : HistoryFormula σ) (x : σ → ℝ) :
    (product l r).realEval x = l.realEval x * r.realEval x := by
  simp only [realEval, cleared, ClearedHistoryValue.prod, Fintype.prod_bool,
    Bool.false_eq_true, ite_false, if_false, ite_true, if_true, MvPolynomial.eval₂_mul, Int.cast_mul]
  ring

@[simp] theorem realEval_solve {σ : Type*} (l r : HistoryFormula σ) (v w s : ℤ)
    (hs : s ≠ 0) (x : σ → ℝ) :
    (solve l r v w s hs).realEval x = (v * r.realEval x - w * l.realEval x) / s := by
  have hL : (l.cleared.denominator : ℝ) ≠ 0 := Int.cast_ne_zero.mpr l.cleared.denominator_ne_zero
  have hR : (r.cleared.denominator : ℝ) ≠ 0 := Int.cast_ne_zero.mpr r.cleared.denominator_ne_zero
  have hS : (s : ℝ) ≠ 0 := Int.cast_ne_zero.mpr hs
  simp only [realEval, cleared, ClearedHistoryValue.pivot, MvPolynomial.eval₂_sub,
    MvPolynomial.eval₂_mul, MvPolynomial.eval₂_C, Int.coe_castRingHom, Int.cast_mul]
  field_simp

end Ostmann.HistoryFormula

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_RealNodeSupport
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The original real node inequalities with variable bulk values -/

namespace Ostmann
open scoped Classical

noncomputable def MovingSlotReversal.realCompositePivot {σ : Type*}
    (s : MovingSlotReversal σ) (value : σ → ℝ) (L R : ℝ) : ℝ :=
  ((s.leftFrequency : ℝ) * realSlotProduct value s.rightSlots * R -
    (s.rightFrequency : ℝ) * realSlotProduct value s.leftSlots * L) / s.rootFrequency

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_BulkNodeSupportPolynomials
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Exact polynomial inequalities for all original bulk node supports -/

namespace Ostmann
open scoped Classical

noncomputable def MovingSlotReversal.bulkCompositePolynomial {σ : Type*}
    (s : MovingSlotReversal σ) (value : σ → ℝ) (i : σ) (L R : Polynomial ℝ) : Polynomial ℝ :=
  { s with compensationSlots := [] }.bulkPivotPolynomial value i L R

noncomputable def MovingSlotData.bulkNodeSupportPolynomials {σ : Type*}
    (value : σ → ℝ) (i : σ) (childBound pivotBound : ℕ → ℕ) :
    {n : ℕ} → MovingSlotData σ n → Polynomial ℝ → Polynomial ℝ → List (Polynomial ℝ)
  | _, .leaf _ _, _, _ => []
  | n + 1, .node s CL CR u left right, L, R =>
      let step := MovingSlotData.step s CL CR u left right false
      let Q := step.bulkCompositePolynomial value i L R
      let p := step.bulkPivotPolynomial value i L R
      [Q - Polynomial.C 1, Polynomial.C (pivotBound (n + 1) : ℝ) - Q,
        R * bulkSlotProduct value i CR -
          Polynomial.C ((2 * pivotBound (n + 1) * childBound (n + 1) + 1 : ℕ) : ℝ)] ++
        (left.bulkNodeSupportPolynomials value i childBound pivotBound p L ++
          right.bulkNodeSupportPolynomials value i childBound pivotBound p R)

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_MovingFieldGiant
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The actual moving-giant recursion directly over the spectator field -/

namespace Ostmann
open scoped Classical ComplexConjugate

noncomputable def movingFieldGiantAmplitude {q : ℕ} [Fact q.Prime]
    (g : ZMod q → ℂ) (D : (ZMod q)ˣ) :
    {n C : ℕ} → MovingGiantTree n C → ZMod q → ZMod q →
      TreeLeafTuple (ZMod q)ˣ n → ℂ
  | _, _, .leaf s C, x, y, z =>
      g ((s : ZMod q) / ((D : ZMod q) * x * y * C * (show (ZMod q)ˣ from z)))
  | n + 1, _, .node s CL CR u left right, x, y, z =>
      let v := reconstructedEntry (s : ZMod q) (left.frequency : ZMod q)
        (right.frequency : ZMod q) (u : ZMod q)
        (x * CL * (treeLeafProduct n z.1 : (ZMod q)ˣ))
        (y * CR * (treeLeafProduct n z.2 : (ZMod q)ˣ))
      if v = 0 then 0 else
        movingFieldGiantAmplitude g D left v x z.1 *
          conj (movingFieldGiantAmplitude g D right v y z.2)

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_MovingFieldSpectator
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The separated spectator factor on every field residue pair -/

namespace Ostmann
open scoped Classical

@[simp] theorem MovingGiantTree.castConstant_fieldAmplitude {q : ℕ} [Fact q.Prime]
    (g : ZMod q → ℂ) (D : (ZMod q)ˣ) {n C E : ℕ} (h : C = E)
    (T : MovingGiantTree n C) (x y : ZMod q) (bulk : TreeLeafTuple (ZMod q)ˣ n) :
    movingFieldGiantAmplitude g D (T.castConstant h) x y bulk =
      movingFieldGiantAmplitude g D T x y bulk := by
  subst E
  rfl

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_SpectatorProductNorm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The full spectator cost under its independent residue law -/

namespace Ostmann

open scoped BigOperators Classical

/-- The data of one actual diagram at a spectator prime. -/
structure SpectatorDiagram (p n : ℕ) [Fact p.Prime] where
  D : (ZMod p)ˣ
  C : (ZMod p)ˣ
  tree : RationalTreeData (ZMod p)ˣ n C
  XL : (ZMod p)ˣ
  XR : (ZMod p)ˣ
  conjugations : TreeLeafTuple Bool n

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Characters_CycleQuartets
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # A simple cycle moves at most two leaves in each quartet -/

namespace Ostmann

open scoped BigOperators

/-- The exact combinatorial data required by the quartet projection. -/
structure BalancedIncidenceCycle {L C Q : Type*} [Fintype L]
    [DecidableEq L] [DecidableEq C] [DecidableEq Q]
    (component : L → C) (quartet : L → Q) where
  sign : L → ℤ
  nonzero : ∃ i, sign i = 1 ∨ sign i = -1
  values : ∀ i, sign i = 0 ∨ sign i = 1 ∨ sign i = -1
  component_balanced : ∀ c, (∑ i ∈ Finset.univ.filter (fun i => component i = c), sign i) = 0
  quartet_balanced : ∀ q, (∑ i ∈ Finset.univ.filter (fun i => quartet i = q), sign i) = 0
  quartet_support : ∀ q,
    (Finset.univ.filter (fun i => quartet i = q ∧ sign i ≠ 0)).card ≤ 2

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Characters_QuartetLocalBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The six possible moving-leaf pairs and their uniform local estimates -/

namespace Ostmann

open scoped BigOperators

inductive QuartetMovingCase where
  | cross (left right : Bool)
  | leftPair
  | rightPair

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Characters_QuartetMovingAction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The actual reciprocal leaf action in the six quartet coordinates -/

namespace Ostmann

open scoped BigOperators

def scaleOneLeaf {U : Type*} [CommGroup U] (s : ℤ) (z m : U) : U := z ^ s * m

@[implicit_reducible] def treeLeafScale {U : Type*} [CommGroup U] : (n : ℕ) →
    TreeLeafTuple ℤ n → U → TreeLeafTuple U n → TreeLeafTuple U n
  | 0, s, z, m => scaleOneLeaf (U := U) s z m
  | n + 1, s, z, m => (treeLeafScale n s.1 z m.1, treeLeafScale n s.2 z m.2)

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Tree_PartitionMatching
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Counting labeled arrangements that respect paired partitions -/

namespace Ostmann

open scoped BigOperators Classical

def PartitionMatching {A B C : Type*} (f : A → C) (g : B → C) :=
  {e : A ≃ B // ∀ a, g (e a) = f a}

def PartitionMatching.restrict {A B C : Type*} {f : A → C} {g : B → C}
    (e : PartitionMatching f g) (c : C) :
    {a : A // f a = c} ≃ {b : B // g b = c} where
  toFun a := ⟨e.1 a, (e.2 a).trans a.2⟩
  invFun b := ⟨e.1.symm b, by rw [← e.2]; simpa using b.2⟩
  left_inv a := Subtype.ext (e.1.symm_apply_apply a)
  right_inv b := Subtype.ext (e.1.apply_symm_apply b)

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Tree_ArrangementGraph
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The bipartite overlap graph of an actual bulk permutation -/

namespace Ostmann

open scoped Classical

def arrangementGraph {L : Type*} (m : ℕ) (e : Equiv.Perm (L × Fin m)) :
    SimpleGraph (L ⊕ L) where
  Adj x y := match x, y with
    | .inl a, .inr b => ∃ i j, e (a, i) = (b, j)
    | .inr b, .inl a => ∃ i j, e (a, i) = (b, j)
    | _, _ => False
  symm := ⟨by intro x y; cases x <;> cases y <;> exact id⟩
  loopless := ⟨by intro x; cases x <;> exact not_false⟩

noncomputable instance instFintypeConnectedComponentSumArrangementGraph {L : Type*} [Fintype L] (m : ℕ)
    (e : Equiv.Perm (L × Fin m)) : Fintype (arrangementGraph m e).ConnectedComponent :=
  Fintype.ofFinite _

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_ArrangementProducts
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Component products for the two arrangements of the same bulk variables -/

namespace Ostmann

open scoped BigOperators Classical

def bulkBlockProduct {L G : Type*} [CommMonoid G] {m : ℕ}
    (x : L × Fin m → G) (l : L) : G := ∏ j, x (l, j)

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_SpectatorBulkComparison
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Uniform signed comparison at all spectator primes -/

namespace Ostmann
open scoped Classical BigOperators ComplexConjugate

noncomputable def SpectatorDiagram.bulkValue {p n m : ℕ} [Fact p.Prime]
    (d : SpectatorDiagram p n) (g : ZMod p → ℂ)
    (x : TreeLeafIndex n × Fin m → (ZMod p)ˣ) : ℂ :=
  indexedRationalAmplitude g d.D d.tree d.XL d.XR d.conjugations (bulkBlockProduct x)

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Characters_NormalizedResidueIndicator
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The manuscript's normalized residue indicators and additive transforms -/

namespace Ostmann

open scoped BigOperators Classical ComplexConjugate

noncomputable def residueDensity {p : ℕ} (S : Finset (ZMod p)) : ℝ := (S.card : ℝ) / p

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_MovingRepresentativeSquares
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Uniform square-exclusion loss for each sampled representative prime -/

namespace Ostmann
open scoped Classical BigOperators

abbrev MovingRepresentativeOccurrences {σ : Type*} {n : ℕ}
    (T : MovingSlotData σ n) (rep : σ) :=
  {j : Fin T.occurrences.length // rep ∈ (T.occurrences.get j).current.compensationSlots}

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_MovingPrimeOccurrences
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Simultaneous occurrences of one actual internal prime in both histories -/

namespace Ostmann
open scoped Classical BigOperators

abbrev MovingPrimeOccurrences {σ : Type*} {n : ℕ}
    (value : σ → ℕ) (T : Bool → MovingSlotData σ n) (p : ℕ) :=
  Σ side : Bool, {j : Fin (T side).occurrences.length //
    ∃ i ∈ ((T side).occurrences.get j).current.compensationSlots, value i = p}

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_MovingArithmeticBlocks
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Concrete CRT blocks for the original moving-history coefficient -/

namespace Ostmann
open scoped Classical BigOperators

abbrev MovingArithmeticBlocks {I : Type*} (P : Finset ℕ) (S : Finset I) :=
  Unit ⊕ (P ⊕ S)

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_BulkSeparatedKernelBound
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Integrating a separated kernel over the original bulk cell mixtures -/

namespace Ostmann
open MeasureTheory
open scoped Classical BigOperators

noncomputable def BulkIntegrand.constMul {J : Type*}
    (f : BulkIntegrand J) (a : ℂ) : BulkIntegrand J where
  toFun y := a * f y
  measurable := measurable_const.mul f.measurable
  bounded := by
    obtain ⟨C, hC, hf⟩ := f.bounded
    exact ⟨‖a‖ * C, mul_nonneg (norm_nonneg _) hC, fun y => by
      simpa only [norm_mul] using mul_le_mul_of_nonneg_left (hf y) (norm_nonneg a)⟩

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_AncestorPivotPrecision
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Exposed products determine all earlier ancestor pivots

A nonbulk coefficient is its fixed label product times a specified set of
inserted ancestor pivots. A division loses one power of the frequency product
along its branch, rather than one power for every node already visited.
-/

namespace Ostmann

open scoped BigOperators

def ancestorCoefficient {N : ℕ} (C : ℤ) (A : Finset (Fin N)) (p : Fin N → ℤ) : ℤ :=
  C * ∏ i ∈ A, p i

/-- Only ancestors occur in a coefficient; their depth is strictly smaller.
The order is the preorder in which split products are exposed. -/
structure PivotDependencyScheme (N : ℕ) where
  frequencies : Fin N → NodeFrequencies
  depth : Fin N → ℕ
  fixedLeft : Fin N → ℤ
  fixedRight : Fin N → ℤ
  ancestorsLeft : Fin N → Finset (Fin N)
  ancestorsRight : Fin N → Finset (Fin N)
  earlierLeft : ∀ j i, i ∈ ancestorsLeft j → i.val < j.val ∧ depth i < depth j
  earlierRight : ∀ j i, i ∈ ancestorsRight j → i.val < j.val ∧ depth i < depth j

def PivotDependencyScheme.leftCoefficient {N : ℕ} (D : PivotDependencyScheme N)
    (p : Fin N → ℤ) (j : Fin N) : ℤ := ancestorCoefficient (D.fixedLeft j) (D.ancestorsLeft j) p

def PivotDependencyScheme.rightCoefficient {N : ℕ} (D : PivotDependencyScheme N)
    (p : Fin N → ℤ) (j : Fin N) : ℤ := ancestorCoefficient (D.fixedRight j) (D.ancestorsRight j) p

/-- The literal integer reversal equation, with the two selected bulk products. -/
def PivotDependencyScheme.equations {N : ℕ} (D : PivotDependencyScheme N)
    (L R p : Fin N → ℤ) : Prop :=
  ∀ j, (D.frequencies j).left * D.leftCoefficient p j * R j -
    (D.frequencies j).right * D.rightCoefficient p j * L j = (D.frequencies j).root * p j

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Tree_PreorderNodePaths
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Explicit preorder indices for internal nodes and their ancestors -/

namespace Ostmann

/-- `false` descends left, `true` descends right. -/
def nodePathIndex : ℕ → List Bool → ℕ
  | 0, _ => 0
  | _ + 1, [] => 0
  | n + 1, b :: p => (if b then 2 ^ n else 1) + nodePathIndex n p

theorem nodePathIndex_lt (n : ℕ) (p : List Bool) (hp : p.length < n) :
    nodePathIndex n p < 2 ^ n - 1 := by
  induction n generalizing p with
  | zero => simp at hp
  | succ n ih =>
    cases p with
    | nil =>
      simp only [nodePathIndex]
      have := Nat.one_le_two_pow (n := n)
      rw [pow_succ]
      omega
    | cons b p =>
      have hp' : p.length < n := by simpa using hp
      have hi := ih p hp'
      have := Nat.one_le_two_pow (n := n)
      cases b <;> simp only [nodePathIndex, Bool.false_eq_true, ite_false, if_false, ite_true, if_true]
      all_goals rw [pow_succ]; omega

def preorderNodePath : (n : ℕ) → Fin (2 ^ n - 1) → List Bool
  | 0, j => Fin.elim0 j
  | n + 1, j =>
      if h0 : j.val = 0 then []
      else if hL : j.val < 2 ^ n then
        false :: preorderNodePath n ⟨j.val - 1, by omega⟩
      else true :: preorderNodePath n ⟨j.val - 2 ^ n, by
        have hj : j.val < 2 ^ n * 2 - 1 := by
          calc
            j.val < 2 ^ (n + 1) - 1 := j.isLt
            _ = 2 ^ n * 2 - 1 := by rw [pow_succ]
        have := Nat.one_le_two_pow (n := n)
        omega⟩

theorem preorderNodePath_length (n : ℕ) (j : Fin (2 ^ n - 1)) :
    (preorderNodePath n j).length < n := by
  induction n with
  | zero => exact Fin.elim0 j
  | succ n ih =>
    simp only [preorderNodePath]
    split_ifs
    · simp
    · simpa only [List.length_cons, Nat.add_lt_add_iff_right] using ih _
    · simpa only [List.length_cons, Nat.add_lt_add_iff_right] using ih _

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Characters_TreeAncestorScheme
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Ostmann

open scoped Classical

/-- The prefix of length i is an earlier internal node. -/
def ancestorNodeIndex (n : ℕ) (j : Fin (2 ^ n - 1))
    (i : Fin (preorderNodePath n j).length) : Fin (2 ^ n - 1) :=
  ⟨nodePathIndex n ((preorderNodePath n j).take i.val), nodePathIndex_lt n _ (by
    have h := preorderNodePath_length n j
    rw [List.length_take]
    exact (min_le_right _ _).trans_lt h)⟩

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_HistoryGiantSources
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The two current giants refer only to previously reconstructed pivots -/

namespace Ostmann

open scoped Classical

inductive HistoryGiantSource where
  | fixed : ℤ → HistoryGiantSource
  | ancestor : ℕ → HistoryGiantSource

def HistoryGiantSource.knownBefore : HistoryGiantSource → ℕ → Prop
  | .fixed _, _ => True
  | .ancestor i, d => i < d

def HistoryGiantSource.eval (p : ℕ → ℤ) : HistoryGiantSource → ℤ
  | .fixed c => c
  | .ancestor i => p i

def HistoryGiantSource.fixedFactor : HistoryGiantSource → ℤ
  | .fixed c => c
  | .ancestor _ => 1

def HistoryGiantSource.ancestorLevels (path : List Bool) (s : HistoryGiantSource)
    (hs : s.knownBefore path.length) : Finset (Fin path.length) :=
  match s with
  | .fixed _ => ∅
  | .ancestor i => {⟨i, hs⟩}

def HistoryGiantSource.nodeValue (n : ℕ) (j : Fin (2 ^ n - 1))
    (p : Fin (2 ^ n - 1) → ℤ) (s : HistoryGiantSource)
    (hs : s.knownBefore (preorderNodePath n j).length) : ℤ :=
  match s with
  | .fixed c => c
  | .ancestor i => p (ancestorNodeIndex n j ⟨i, hs⟩)

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_ScheduledRegularUnary
attribute [-instance] _root_.OAI.Ostmann.copyScheduleVertexFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Frequency-independent multipliers of the regular copied rows -/

namespace Ostmann

open scoped ComplexConjugate

/-- Copying never conjugates the underlying Dirichlet character. -/
def copyScheduleOrigin {I : Type*} : (n : ℕ) → CopyScheduleVertex I n → I
  | 0, i => i
  | n + 1, .inl (_, i) => copyScheduleOrigin n i
  | n + 1, .inr i => copyScheduleOrigin n i

@[simp] theorem copyScheduleOrigin_path {I : Type*} (n : ℕ) (t : Fin n → Bool) (i : I) :
    copyScheduleOrigin n (copySchedulePath n t i) = i := by
  induction n with
  | zero => rfl
  | succ n ih => exact ih _

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_ScheduleGraphInvariants
attribute [-instance] _root_.OAI.Ostmann.copyScheduleVertexFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Regular rows and pivot columns on the surviving template slots -/

namespace Ostmann

/-- The row assertion is restricted to surviving slots, as required by the
actual H/Y partition; unused ambient labels are irrelevant. -/
def ScheduledRegularRow {I : Type*} (role : I → CopyScheduleRole)
    (g : I → I → ℤ) (pivot : ℕ → I) (n : ℕ)
    (i : CopyScheduleVertex I n) (ε : ℤ) : Prop :=
  ∀ j, CopyScheduleSurvives role n j → j ≠ i → copyScheduleGraph g pivot n i j = ε

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_SchedulePivotUnary
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The actual unary on every still-active pivot constituent -/

namespace Ostmann

open scoped Classical

@[simp] theorem copyScheduleOrigin_positive {I : Type*} (n : ℕ) (i : I) :
    copyScheduleOrigin n (copySchedulePositive n i) = i := by
  induction n with
  | zero => rfl
  | succ n ih => exact ih

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_ScheduledPivotPartition
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The exact current pivot/H/Y partition of surviving prime slots -/

namespace Ostmann

open scoped Classical

abbrev CurrentPivotConstituent {I : Type*} (role : I → CopyScheduleRole) (n : ℕ) :=
  {i : I // role i = .pivot n}

noncomputable def scheduledPartitionMap {I : Type*} (role : I → CopyScheduleRole) (n : ℕ) :
    CurrentPivotConstituent role n ⊕ (CopyScheduleH role n ⊕ CopyScheduleY role n) →
      {i : CopyScheduleVertex I n // CopyScheduleSurvives role n i}
  | .inl p => ⟨copySchedulePositive n p.val,
      copyScheduleSurvives_positive role p.val n p.property n le_rfl⟩
  | .inr (.inl h) => ⟨h.val, h.property.1⟩
  | .inr (.inr y) => ⟨y.val, y.property.1⟩

theorem scheduledPartitionMap_injective {I : Type*}
    (role : I → CopyScheduleRole) (n : ℕ) :
    Function.Injective (scheduledPartitionMap role n) := by
  intro a b he
  have hv := congrArg Subtype.val he
  rcases a with p | h | y <;> rcases b with q | h' | y' <;>
    dsimp only [scheduledPartitionMap] at hv
  · exact congrArg Sum.inl (Subtype.ext (copySchedulePositive_injective n hv))
  · have hc := h'.property.2
    rw [← hv, copyScheduleRole_positive role p.val n p.property] at hc
    simp [CopyScheduleRole.copiedAt] at hc
  · have hc := y'.property.2.2
    rw [← hv, copyScheduleRole_positive role p.val n p.property] at hc
    simp [CopyScheduleRole.erasedAt] at hc
  · have hc := h.property.2
    rw [hv, copyScheduleRole_positive role q.val n q.property] at hc
    simp [CopyScheduleRole.copiedAt] at hc
  · exact congrArg (fun x => Sum.inr (Sum.inl x)) (Subtype.ext hv)
  · have hc := h.property.2
    rw [hv, y'.property.2.1] at hc
    cases hc
  · have hc := y.property.2.2
    rw [hv, copyScheduleRole_positive role q.val n q.property] at hc
    simp [CopyScheduleRole.erasedAt] at hc
  · have hc := h'.property.2
    rw [← hv, y.property.2.1] at hc
    cases hc
  · exact congrArg (fun x => Sum.inr (Sum.inr x)) (Subtype.ext hv)

theorem scheduledPartitionMap_surjective {I : Type*}
    (role : I → CopyScheduleRole) (n : ℕ) :
    Function.Surjective (scheduledPartitionMap role n) := by
  intro v
  by_cases hc : (copyScheduleRole role n v.val).copiedAt n = true
  · exact ⟨.inr (.inl ⟨v.val, v.property, hc⟩), rfl⟩
  have hc' : (copyScheduleRole role n v.val).copiedAt n = false := by
    cases hh : (copyScheduleRole role n v.val).copiedAt n <;> simp_all
  by_cases he : (copyScheduleRole role n v.val).erasedAt n = true
  · have hp : copyScheduleRole role n v.val = .pivot n := by
      cases hr : copyScheduleRole role n v.val with
      | pivot k =>
        have : n = k := by simpa [CopyScheduleRole.erasedAt, hr] using he
        subst k
        rfl
      | word => simp [CopyScheduleRole.erasedAt, hr] at he
      | anchor k => simp [CopyScheduleRole.erasedAt, hr] at he
      | outside => simp [CopyScheduleRole.erasedAt, hr] at he
    obtain ⟨_, p, hp, hv⟩ := surviving_pivot_is_positive role n n v.val v.property hp
    exact ⟨.inl ⟨p, hp⟩, Subtype.ext hv.symm⟩
  · have he' : (copyScheduleRole role n v.val).erasedAt n = false := by
      cases hh : (copyScheduleRole role n v.val).erasedAt n <;> simp_all
    exact ⟨.inr (.inr ⟨v.val, v.property, hc', he'⟩), rfl⟩

noncomputable def scheduledPartitionEquiv {I : Type*} (role : I → CopyScheduleRole) (n : ℕ) :
    CurrentPivotConstituent role n ⊕ (CopyScheduleH role n ⊕ CopyScheduleY role n) ≃
      {i : CopyScheduleVertex I n // CopyScheduleSurvives role n i} :=
  Equiv.ofBijective (scheduledPartitionMap role n)
    ⟨scheduledPartitionMap_injective role n, scheduledPartitionMap_surjective role n⟩

@[simp] theorem scheduledPartitionEquiv_pivot {I : Type*} (role : I → CopyScheduleRole)
    (n : ℕ) (p : CurrentPivotConstituent role n) :
    (scheduledPartitionEquiv role n (.inl p)).val = copySchedulePositive n p.val := rfl

@[simp] theorem scheduledPartitionEquiv_rest {I : Type*} (role : I → CopyScheduleRole)
    (n : ℕ) (i : CopyScheduleH role n ⊕ CopyScheduleY role n) :
    (scheduledPartitionEquiv role n (.inr i)).val = Sum.elim Subtype.val Subtype.val i := by
  cases i <;> rfl

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_EnumeratedSchedulePhase
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The actual pivot phase in the enumeration used by the harmonic prior -/

namespace Ostmann

open scoped BigOperators Classical

noncomputable def enumeratedPartitionEquiv {I : Type*} (role : I → CopyScheduleRole)
    (n r : ℕ) (e : Fin r ≃ CurrentPivotConstituent role n) :
    Fin r ⊕ (CopyScheduleH role n ⊕ CopyScheduleY role n) ≃
      {i : CopyScheduleVertex I n // CopyScheduleSurvives role n i} :=
  (Equiv.sumCongr e (Equiv.refl _)).trans (scheduledPartitionEquiv role n)

@[simp] theorem enumeratedPartitionEquiv_pivot {I : Type*} (role : I → CopyScheduleRole)
    (n r : ℕ) (e : Fin r ≃ CurrentPivotConstituent role n) (i : Fin r) :
    (enumeratedPartitionEquiv role n r e (.inl i)).val = copySchedulePositive n (e i).val := rfl

@[simp] theorem enumeratedPartitionEquiv_rest {I : Type*} (role : I → CopyScheduleRole)
    (n r : ℕ) (e : Fin r ≃ CurrentPivotConstituent role n)
    (i : CopyScheduleH role n ⊕ CopyScheduleY role n) :
    (enumeratedPartitionEquiv role n r e (.inr i)).val = Sum.elim Subtype.val Subtype.val i := by
  cases i <;> rfl

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_InsertedAtomAssignment
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Inserting the reconstructed composite pivot in either old branch -/

namespace Ostmann

open scoped Classical

noncomputable def scheduledInsertedAtoms {I : Type*} (role : I → CopyScheduleRole)
    (n : ℕ) (P : ℕ) (l : CopyScheduleH role n → ℕ) (u : CopyScheduleY role n → ℕ) :
    CopyScheduleAtoms role n → ℕ :=
  fun i => match (scheduledPartitionEquiv role n).symm i with
    | .inl _ => P
    | .inr (.inl h) => l h
    | .inr (.inr y) => u y

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_AtomSourceDescent
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Actual reverse paths with freshly indexed ancestor pivot sources -/

namespace Ostmann
open scoped Classical

def AtomSourceBefore {B : Type*} (d : ℕ) : B ⊕ ℕ → Prop
  | .inl _ => True
  | .inr j => j < d

theorem AtomSourceBefore.mono {B : Type*} {d e : ℕ} {s : B ⊕ ℕ}
    (h : AtomSourceBefore d s) (hde : d ≤ e) : AtomSourceBefore e s := by
  cases s with
  | inl _ => trivial
  | inr j => exact lt_of_lt_of_le h hde

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_SplitPrefixProducts
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Computing every current parent product from previously exposed splits -/

namespace Ostmann

def actualSplitValues {G : Type*} [CommMonoid G] : (n : ℕ) → TreeLeafTuple G n → List G
  | 0, _ => []
  | n + 1, x => treeLeafProduct n x.1 :: (actualSplitValues n x.1 ++ actualSplitValues n x.2)

def actualParentSplits {G : Type*} [CommMonoid G] : (n : ℕ) → TreeLeafTuple G n → List (G × G)
  | 0, _ => []
  | n + 1, x => (treeLeafProduct (n + 1) x, treeLeafProduct n x.1) ::
      (actualParentSplits n x.1 ++ actualParentSplits n x.2)

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Characters_TreeSplitResidues
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Integer bulk products and their exposed unit residues -/

namespace Ostmann

/-- Both actual child products, in the same preorder as the frequencies. -/
def actualChildProducts {G : Type*} [CommMonoid G] : (n : ℕ) → TreeLeafTuple G n → List (G × G)
  | 0, _ => []
  | n + 1, x => (treeLeafProduct n x.1, treeLeafProduct n x.2) ::
      (actualChildProducts n x.1 ++ actualChildProducts n x.2)

/-- Equality of all leaf residues, expressed on the original binary tuple. -/
def treeIntegerResidues (Q : ℕ) : (n : ℕ) → TreeLeafTuple ℤ n →
    TreeLeafTuple (ZMod Q)ˣ n → Prop
  | 0, a, u => Units.val (show (ZMod Q)ˣ from u) = ((show ℤ from a) : ZMod Q)
  | n + 1, a, u => treeIntegerResidues Q n a.1 u.1 ∧ treeIntegerResidues Q n a.2 u.2

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_AdaptivePivotCoefficients
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Constructing coefficients from the already exposed product prefix -/

namespace Ostmann

open scoped Classical

/-- Actual integer products together with their exact unit residues. -/
structure SampledPivotHistory (n Q : ℕ) where
  bulk : TreeLeafTuple ℤ n
  residue : TreeLeafTuple (ZMod Q)ˣ n
  pivots : Fin (2 ^ n - 1) → ℤ
  compatible : treeIntegerResidues Q n bulk residue

def SampledPivotHistory.leftProduct {n Q : ℕ} (a : SampledPivotHistory n Q)
    (j : Fin (2 ^ n - 1)) : ℤ := ((actualChildProducts n a.bulk).getD j.val (1, 1)).1

def SampledPivotHistory.rightProduct {n Q : ℕ} (a : SampledPivotHistory n Q)
    (j : Fin (2 ^ n - 1)) : ℤ := ((actualChildProducts n a.bulk).getD j.val (1, 1)).2

def SampledPivotHistory.valid {n Q : ℕ} (a : SampledPivotHistory n Q)
    (D : PivotDependencyScheme (2 ^ n - 1)) : Prop :=
  D.equations a.leftProduct a.rightProduct a.pivots ∧
    ∀ j, IsCoprime (D.leftCoefficient a.pivots j) (D.frequencies j).root ∧
      IsCoprime (D.rightCoefficient a.pivots j) (D.frequencies j).root

def SampledPivotHistory.matches {n Q : ℕ} (a : SampledPivotHistory n Q)
    (total : (ZMod Q)ˣ) (past : List (ZMod Q)ˣ) : Prop :=
  treeLeafProduct n a.residue = total ∧
    ((actualSplitValues n a.residue).take past.length).reverse = past

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_MovingBulkFrames
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Fixed nonbulk factors and literal bulk products at each moving node -/

namespace Ostmann
open scoped Classical

structure MovingFrameConstants where
  leftSmall : ℕ
  rightSmall : ℕ
  compensation : ℕ

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_ScheduledNodeFrequencies
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The exact frequency triple of each reconstructed scheduled node -/

namespace Ostmann

def ReconstructedTransferNode.frequencies {State : Type*}
    (node : ReconstructedTransferNode State) : NodeFrequencies :=
  ⟨node.root, node.left, node.right⟩

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_MovingSampledRecursion
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Expanding the sampled giant recursion into its literal histories

This is the recursion of Section 7.4 (7.10)--(7.11), rather than the
whole-atom recursion of Section 4. Each root sample is used by both children.
The child sample trees are independent under the original finite law.
-/

namespace Ostmann
open scoped Classical BigOperators

def MovingSlotData.frequencyTree {σ : Type*} : {n : ℕ} →
    MovingSlotData σ n → FrequencyTree ℤ n
  | _, .leaf s _ => s
  | _, .node s _ _ _ l r => (s, l.frequencyTree, r.frequencyTree)

/-- Discard descendant prime data, keeping all their frequencies. Root
cutoffs may still impose the cross-branch frequency tests of Section 7.4. -/
def movingFrequencySkeleton (σ : Type*) : (n : ℕ) → FrequencyTree ℤ n → MovingSlotData σ n
  | 0, t => .leaf t []
  | n + 1, t => .node t.1 [] [] []
      (movingFrequencySkeleton σ n t.2.1) (movingFrequencySkeleton σ n t.2.2)

def MovingSlotData.rootData {σ : Type*} : {n : ℕ} → MovingSlotData σ n → MovingSlotData σ n
  | _, .leaf s regular => .leaf s regular
  | n + 1, .node s CL CR u l r => .node s CL CR u
      (movingFrequencySkeleton σ n l.frequencyTree) (movingFrequencySkeleton σ n r.frequencyTree)

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_ModularCompensatedPrecision
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Prefix precision after retaining only the frequency congruences

The frequency model in the arithmetic replacement divides by compensation
factors modulo the remaining power. Its equations are congruences, with one
power lost at each branch level.
-/

namespace Ostmann
open scoped BigOperators

/-- The equation of the moving construction, keeping its compensation
product instead of replacing the new giant by a composite pivot. -/
def PivotDependencyScheme.modularCompensatedEquations {N : ℕ} (D : PivotDependencyScheme N)
    (M : ℤ) (k : ℕ) (U L R p : Fin N → ℤ) : Prop :=
  ∀ j, (D.frequencies j).left * D.leftCoefficient p j * R j -
    (D.frequencies j).right * D.rightCoefficient p j * L j ≡
      (D.frequencies j).root * U j * p j [ZMOD M ^ (k + 1 - D.depth j)]

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_ModularAdaptiveCoefficients
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Adaptive coefficients for the frequency-only arithmetic model -/

namespace Ostmann

open scoped Classical

def SampledPivotHistory.modularValid {n Q : ℕ} (a : SampledPivotHistory n Q)
    (D : PivotDependencyScheme (2 ^ n - 1)) (R k : ℕ)
    (U : Fin (2 ^ n - 1) → ℤ) : Prop :=
  D.modularCompensatedEquations R k U a.leftProduct a.rightProduct a.pivots ∧
    ∀ j, IsCoprime (D.leftCoefficient a.pivots j) (D.frequencies j).root ∧
      IsCoprime (D.rightCoefficient a.pivots j) (D.frequencies j).root

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_FrequencyModelPaths
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Paths in the frequency-only arithmetic recursion

These states follow `movingFrequencyGate`, whose pivots invert the fixed
compensation modulo a power of the frequency modulus.
-/

namespace Ostmann
open scoped Classical

structure FrequencyModelState (σ : Type*) where
  level : ℕ
  data : MovingSlotData σ level
  leftGiant : ℤ
  rightGiant : ℤ

def FrequencyModelState.pivot {σ : Type*} (value : σ → ℕ) (R : ℤ) :
    FrequencyModelState σ → ℤ
  | ⟨0, _, _, _⟩ => 0
  | ⟨n + 1, .node s CL CR U l r, x, y⟩ =>
      (MovingSlotData.step s CL CR U l r false).frequencyPivot value R (n + 1) x y

def FrequencyModelState.frequencies {σ : Type*} : FrequencyModelState σ → NodeFrequencies
  | ⟨0, .leaf s _, _, _⟩ => ⟨s, s, s⟩
  | ⟨_ + 1, .node s _ _ _ l r, _, _⟩ => ⟨s, l.frequency, r.frequency⟩

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_FrequencyModelCoefficients
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Fixed factors and ancestor coefficients of the frequency model -/

namespace Ostmann
open scoped Classical

def FrequencyModelState.leftProduct {σ : Type*} (value : σ → ℕ) : FrequencyModelState σ → ℤ
  | ⟨0, _, _, _⟩ => 1
  | ⟨_ + 1, .node _ CL _ _ _ _, x, _⟩ => x * (MovingSlotReversal.naturalProduct value CL : ℤ)

def FrequencyModelState.rightProduct {σ : Type*} (value : σ → ℕ) : FrequencyModelState σ → ℤ
  | ⟨0, _, _, _⟩ => 1
  | ⟨_ + 1, .node _ _ CR _ _ _, _, y⟩ => y * (MovingSlotReversal.naturalProduct value CR : ℤ)

def FrequencyModelState.compensation {σ : Type*} (value : σ → ℕ) : FrequencyModelState σ → ℤ
  | ⟨0, _, _, _⟩ => 1
  | ⟨_ + 1, .node _ _ _ U _ _, _, _⟩ => MovingSlotReversal.naturalProduct value U

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_FrozenRegularSupport
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The retained nonbulk coprimality support for the complete sampled tree -/

namespace Ostmann
open scoped Classical

def MovingSlotData.regularLists {σ : Type*} : {n : ℕ} → MovingSlotData σ n → List (List σ)
  | _, .leaf _ regular => [regular]
  | _, .node _ CL CR _ left right => (CL ++ CR) :: (left.regularLists ++ right.regularLists)

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_MovingSlotRelabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Relabelling repeated sampled slots by their equality-pattern classes -/

namespace Ostmann
open scoped Classical

def MovingSlotReversal.map {σ τ : Type*} (f : σ → τ) (s : MovingSlotReversal σ) :
    MovingSlotReversal τ where
  left := s.left
  rootFrequency := s.rootFrequency
  leftFrequency := s.leftFrequency
  rightFrequency := s.rightFrequency
  leftSlots := s.leftSlots.map f
  rightSlots := s.rightSlots.map f
  compensationSlots := s.compensationSlots.map f

def MovingSlotData.map {σ τ : Type*} (f : σ → τ) :
    {n : ℕ} → MovingSlotData σ n → MovingSlotData τ n
  | _, .leaf s regular => .leaf s (regular.map f)
  | _, .node s CL CR u left right =>
      .node s (CL.map f) (CR.map f) (u.map f) (left.map f) (right.map f)

@[simp] theorem MovingSlotData.frequency_map {σ τ : Type*} (f : σ → τ)
    {n : ℕ} (T : MovingSlotData σ n) : (T.map f).frequency = T.frequency := by
  cases T <;> rfl

theorem MovingSlotData.levels_map {σ τ : Type*} (f : σ → τ) (tier : σ → ℕ) (tier' : τ → ℕ)
    (htier : ∀ i, tier' (f i) = tier i) {n : ℕ} (T : MovingSlotData σ n) :
    (T.map f).Levels tier' ↔ T.Levels tier := by
  induction T with
  | leaf => rfl
  | node s CL CR u left right ihL ihR =>
    simp only [MovingSlotData.map, MovingSlotData.Levels, List.forall_mem_map, htier, ihL, ihR]

theorem MovingSlotData.step_map {σ τ : Type*} (f : σ → τ)
    {n : ℕ} (s : ℤ) (CL CR u : List σ) (left right : MovingSlotData σ n) (b : Bool) :
    step s (CL.map f) (CR.map f) (u.map f) (left.map f) (right.map f) b =
      (step s CL CR u left right b).map f := by
  simp only [step, MovingSlotReversal.map, frequency_map]

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_MovingOccurrenceRelabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Actual internal-prime line systems commute with slot relabelling -/

namespace Ostmann
open scoped Classical

def MovingSlotOccurrence.map {σ τ : Type*} (f : σ → τ)
    (o : MovingSlotOccurrence σ) : MovingSlotOccurrence τ :=
  ⟨o.level, o.current.map f, o.path.map (MovingSlotReversal.map f)⟩

theorem MovingSlotData.occurrences_map {σ τ : Type*} (f : σ → τ)
    {n : ℕ} (T : MovingSlotData σ n) :
    (T.map f).occurrences = T.occurrences.map (MovingSlotOccurrence.map f) := by
  induction T with
  | leaf => rfl
  | node s CL CR u left right ihL ihR =>
    simp only [MovingSlotData.map, occurrences, step_map, ihL, ihR,
      List.map_cons, List.map_append, List.map_map, Function.comp_def,
      MovingSlotOccurrence.map, MovingSlotOccurrence.extend, List.map_nil]

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_MovingSampleCoordinates
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Fixed coordinates for the actual internal prime samples

The coordinates count each sample when it is made, not its later occurrences
in descendant lists. Their number is independent of the number of bulk slots.
-/

namespace Ostmann
open scoped Classical BigOperators

def MovingSampleIndex : ℕ → Type
  | 0 => Empty
  | n + 1 => (TreeLeafIndex n × Fin 4) ⊕ (Bool × MovingSampleIndex n)

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Tree_SampleEqualityPatterns
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Exact decomposition of finite samples by equality pattern -/

namespace Ostmann
open scoped Classical BigOperators

/-- A pattern records exactly which sampled positions coincide. Its class values
are distinct; independence is imposed only on their dominating product prior. -/
abbrev SampleEqualityPattern (I A : Type*) :=
  Σ s : Setoid I, {x : Quotient s → A // Function.Injective x}

def SampleEqualityPattern.evaluate {I A : Type*} (p : SampleEqualityPattern I A) : I → A :=
  fun i => p.2.val (Quotient.mk'' i)

theorem SampleEqualityPattern.kernel_evaluate {I A : Type*}
    (p : SampleEqualityPattern I A) : Setoid.ker p.evaluate = p.1 := by
  ext i j
  exact ⟨fun h => Quotient.exact (p.2.property h), fun h => congrArg p.2.val (Quotient.sound h)⟩

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_MovingSampleMap
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Evaluating the fixed indexed sample tree

This identifies the original sampled prime tree with evaluation of fixed
slot data. Thus equality-pattern and polynomial arguments use the same
literal constructor as the sampled coefficient.
-/

namespace Ostmann
open scoped Classical

def MovingSampleSlots.map {A B : Type*} (f : A → B) :
    {n : ℕ} → MovingSampleSlots A n → MovingSampleSlots B n
  | _, .leaf => .leaf
  | n + 1, .node u l r =>
      .node (treeLeafMap (fun a : Fin 4 → A => f ∘ a) n u) (l.map f) (r.map f)

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_MovingRepresentativeLineSystem
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Fixed occurrence systems for a representative sampled prime -/

namespace Ostmann
open scoped Classical BigOperators

abbrev MovingPairRepresentativeOccurrences {σ : Type*} {n : ℕ}
    (T : Bool → MovingSlotData σ n) (rep : σ) :=
  Σ side : Bool, MovingRepresentativeOccurrences (T side) rep

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_MovingIndexedLineSystem
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # A fixed finite index for every representative's actual line system -/

namespace Ostmann
open scoped Classical BigOperators

abbrev MovingPairOccurrenceIndex {σ : Type*} {n : ℕ}
    (T : Bool → MovingSlotData σ n) := Σ side : Bool, Fin (T side).occurrences.length

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Tree_BadPartitionCounts
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Uniform counting bound for paired leaf partitions -/

namespace Ostmann

open scoped BigOperators Classical

abbrev BadPartitionPair (r t : ℕ) :=
  {fg : (Fin r → Fin t) × (Fin r → Fin t) //
    Function.Surjective fg.1 ∧ Function.Surjective fg.2 ∧
    (∀ c, Fintype.card {l : Fin r // fg.1 l = c} =
      Fintype.card {l : Fin r // fg.2 l = c}) ∧ 4 * (r - t) ≤ r}

abbrev BadPartitionWitness (r : ℕ) := Σ t : Fin (r + 1), BadPartitionPair r t

abbrev BadPartitionWitness.Matching {r : ℕ} (w : BadPartitionWitness r) (m : ℕ) :=
  PartitionMatching (fun x : Fin r × Fin m => w.2.1.1 x.1)
    (fun x : Fin r × Fin m => w.2.1.2 x.1)

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Tree_BadArrangementCount
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Counting bad permutations through their actual overlap components -/

namespace Ostmann

open scoped BigOperators Classical

def BadBulkArrangement {r m : ℕ} (e : Equiv.Perm (Fin r × Fin m)) : Prop :=
  3 * r < 4 * Fintype.card (arrangementGraph m e).ConnectedComponent

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_ConstituentScheduleMap
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Forgetting constituent indices commutes with the literal copy schedule -/

namespace Ostmann

/-- Apply a map of original labels without changing any copy/retain choice. -/
def copyScheduleMap {I J : Type*} (f : I → J) :
    (n : ℕ) → CopyScheduleVertex I n → CopyScheduleVertex J n
  | 0, i => f i
  | n + 1, .inl (b, i) => .inl (b, copyScheduleMap f n i)
  | n + 1, .inr i => .inr (copyScheduleMap f n i)

@[simp] theorem copyScheduleOrigin_map {I J : Type*} (f : I → J)
    (n : ℕ) (i : CopyScheduleVertex I n) :
    copyScheduleOrigin n (copyScheduleMap f n i) = f (copyScheduleOrigin n i) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rcases i with ⟨b, i⟩ | i <;> exact ih i

@[simp] theorem copyScheduleMap_positive {I J : Type*} (f : I → J) (n : ℕ) (i : I) :
    copyScheduleMap f n (copySchedulePositive n i) = copySchedulePositive n (f i) := by
  induction n with
  | zero => rfl
  | succ n ih => exact congrArg (fun i => Sum.inl (true, i)) ih

@[simp] theorem copyScheduleMap_path {I J : Type*} (f : I → J) (n : ℕ)
    (path : Fin n → Bool) (i : I) :
    copyScheduleMap f n (copySchedulePath n path i) = copySchedulePath n path (f i) := by
  induction n with
  | zero => rfl
  | succ n ih => exact congrArg (fun i => Sum.inl (path (Fin.last n), i)) (ih _)

@[simp] theorem copyScheduleRole_map {I J : Type*} (f : I → J)
    (role : J → CopyScheduleRole) (n : ℕ) (i : CopyScheduleVertex I n) :
    copyScheduleRole role n (copyScheduleMap f n i) = copyScheduleRole (role ∘ f) n i := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rcases i with ⟨b, i⟩ | i
    · exact congrArg (fun r => r.afterCopy b) (ih i)
    · exact ih i

/-- The prime constituents of an atom survive precisely when the atom does. -/
theorem copyScheduleSurvives_map_iff {I J : Type*} (f : I → J)
    (role : J → CopyScheduleRole) (n : ℕ) (i : CopyScheduleVertex I n) :
    CopyScheduleSurvives role n (copyScheduleMap f n i) ↔
      CopyScheduleSurvives (role ∘ f) n i := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rcases i with ⟨b, i⟩ | i
    · change (_ ∧ _) ↔ (_ ∧ _)
      rw [ih, copyScheduleRole_map]
    · change (_ ∧ _ ∧ _) ↔ (_ ∧ _ ∧ _)
      rw [ih, copyScheduleRole_map]

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_ConstituentScheduleEquiv
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Every current atom retains precisely its original constituent indices -/

namespace Ostmann

/-- The copied constituent labels are the current atom labels paired with
an original index inside that atom. No new prime slots appear. -/
noncomputable def copyConstituentEquiv {I : Type*} (size : I → ℕ) : (n : ℕ) →
    CopyScheduleVertex (Σ i, Fin (size i)) n ≃
      (Σ v : CopyScheduleVertex I n, Fin (size (copyScheduleOrigin n v)))
  | 0 => Equiv.refl _
  | n + 1 =>
    let e := copyConstituentEquiv size n
    { toFun := fun i => match i with
        | .inl (b, i) => ⟨.inl (b, (e i).1), (e i).2⟩
        | .inr i => ⟨.inr (e i).1, (e i).2⟩
      invFun := fun i => match i with
        | ⟨.inl (b, v), k⟩ => .inl (b, e.symm ⟨v, k⟩)
        | ⟨.inr v, k⟩ => .inr (e.symm ⟨v, k⟩)
      left_inv := by
        intro i
        rcases i with ⟨b, i⟩ | i
        · change Sum.inl (b, e.symm (e i)) = _
          rw [e.symm_apply_apply]
        · change Sum.inr (e.symm (e i)) = _
          rw [e.symm_apply_apply]
      right_inv := by
        rintro ⟨v, k⟩
        rcases v with ⟨b, v⟩ | v
        · exact congrArg
            (fun a : Σ v : CopyScheduleVertex I n, Fin (size (copyScheduleOrigin n v)) =>
              (⟨.inl (b, a.1), a.2⟩ : Σ v : CopyScheduleVertex I (n + 1),
                Fin (size (copyScheduleOrigin (n + 1) v)))) (e.apply_symm_apply ⟨v, k⟩)
        · exact congrArg
            (fun a : Σ v : CopyScheduleVertex I n, Fin (size (copyScheduleOrigin n v)) =>
              (⟨.inr a.1, a.2⟩ : Σ v : CopyScheduleVertex I (n + 1),
                Fin (size (copyScheduleOrigin (n + 1) v)))) (e.apply_symm_apply ⟨v, k⟩) }

theorem copyConstituentEquiv_atom {I : Type*} (size : I → ℕ)
    (n : ℕ) (i : CopyScheduleVertex (Σ i, Fin (size i)) n) :
    (copyConstituentEquiv size n i).1 = copyScheduleMap Sigma.fst n i := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rcases i with ⟨b, i⟩ | i
    · exact congrArg (fun v => Sum.inl (b, v)) (ih i)
    · exact congrArg Sum.inr (ih i)

theorem constituentForget_injective {I : Type*} (role : I → CopyScheduleRole)
    (size : I → ℕ) (n : ℕ) :
    Function.Injective (fun i : Σ v : {v : CopyScheduleVertex I n // CopyScheduleSurvives role n v},
        Fin (size (copyScheduleOrigin n v.val)) =>
      (⟨i.1.val, i.2⟩ : Σ v : CopyScheduleVertex I n, Fin (size (copyScheduleOrigin n v)))) := by
  rintro ⟨⟨a, ha⟩, i⟩ ⟨⟨b, hb⟩, j⟩ hij
  change (⟨a, i⟩ : Σ v : CopyScheduleVertex I n, Fin (size (copyScheduleOrigin n v))) = ⟨b, j⟩ at hij
  cases hij
  rfl

/-- Surviving constituent slots are exactly a surviving atom and one of its
original prime positions. -/
noncomputable def survivingConstituentEquiv {I : Type*} (role : I → CopyScheduleRole)
    (size : I → ℕ) (n : ℕ) :
    {v : CopyScheduleVertex (Σ i, Fin (size i)) n //
      CopyScheduleSurvives (role ∘ Sigma.fst) n v} ≃
    (Σ v : {v : CopyScheduleVertex I n // CopyScheduleSurvives role n v},
      Fin (size (copyScheduleOrigin n v.val))) where
  toFun i := ⟨⟨(copyConstituentEquiv size n i.val).1, by
    rw [copyConstituentEquiv_atom]
    exact (copyScheduleSurvives_map_iff Sigma.fst role n i.val).mpr i.property⟩,
    (copyConstituentEquiv size n i.val).2⟩
  invFun i := ⟨(copyConstituentEquiv size n).symm ⟨i.1.val, i.2⟩, by
    apply (copyScheduleSurvives_map_iff Sigma.fst role n _).mp
    rw [← copyConstituentEquiv_atom]
    have he := congrArg Sigma.fst ((copyConstituentEquiv size n).apply_symm_apply ⟨i.1.val, i.2⟩)
    rw [he]
    exact i.1.property⟩
  left_inv i := by
    apply Subtype.ext
    exact (copyConstituentEquiv size n).symm_apply_apply i.val
  right_inv i := by
    apply constituentForget_injective role size n
    exact (copyConstituentEquiv size n).apply_symm_apply ⟨i.1.val, i.2⟩

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_ConstituentWords
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The exact constituent words of the surviving grouped atoms -/

namespace Ostmann

open scoped BigOperators Classical

abbrev SurvivingConstituent {I : Type*} (role : I → CopyScheduleRole) (size : I → ℕ) (n : ℕ) :=
  {v : CopyScheduleVertex (Σ i, Fin (size i)) n // CopyScheduleSurvives (role ∘ Sigma.fst) n v}

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_ConstituentCopiedAssignment
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Grouping the actual copied prime assignment -/

namespace Ostmann

open scoped BigOperators Classical

theorem constituent_inverse_atom {I : Type*} (role : I → CopyScheduleRole)
    (size : I → ℕ) (n : ℕ) (v : CopyScheduleAtoms role n)
    (k : Fin (size (copyScheduleOrigin n v.val))) :
    copyScheduleMap Sigma.fst n
      ((survivingConstituentEquiv role size n).symm ⟨v, k⟩).val = v.val := by
  rw [← copyConstituentEquiv_atom]
  exact congrArg Sigma.fst ((copyConstituentEquiv size n).apply_symm_apply ⟨v.val, k⟩)

noncomputable def constituentH {I : Type*} (role : I → CopyScheduleRole)
    (size : I → ℕ) (n : ℕ) (v : CopyScheduleH role n)
    (k : Fin (size (copyScheduleOrigin n v.val))) : CopyScheduleH (fun i : Σ a, Fin (size a) => role i.1) n :=
  let j := (survivingConstituentEquiv role size n).symm ⟨⟨v.val, v.property.1⟩, k⟩
  ⟨j.val, j.property, by
    have he := constituent_inverse_atom role size n ⟨v.val, v.property.1⟩ k
    have hr := copyScheduleRole_map Sigma.fst role n j.val
    rw [he] at hr
    exact hr ▸ v.property.2⟩

noncomputable def constituentY {I : Type*} (role : I → CopyScheduleRole)
    (size : I → ℕ) (n : ℕ) (v : CopyScheduleY role n)
    (k : Fin (size (copyScheduleOrigin n v.val))) : CopyScheduleY (fun i : Σ a, Fin (size a) => role i.1) n :=
  let j := (survivingConstituentEquiv role size n).symm ⟨⟨v.val, v.property.1⟩, k⟩
  ⟨j.val, j.property, by
    have he := constituent_inverse_atom role size n ⟨v.val, v.property.1⟩ k
    have hr := copyScheduleRole_map Sigma.fst role n j.val
    rw [he] at hr
    exact hr ▸ v.property.2⟩

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_ScheduledInputPhase
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The actual current phase under independent pivot/H/Y assignments -/

namespace Ostmann

open scoped BigOperators Classical

noncomputable def scheduledInputLabels {I : Type*} (role : I → CopyScheduleRole)
    (n r : ℕ) (e : Fin r ≃ CurrentPivotConstituent role n)
    (P : Fin r → ℕ) (L : CopyScheduleH role n → ℕ) (U : CopyScheduleY role n → ℕ) :
    {i : CopyScheduleVertex I n // CopyScheduleSurvives role n i} → ℕ :=
  fun i => Sum.elim P (Sum.elim L U) ((enumeratedPartitionEquiv role n r e).symm i)

@[simp] theorem scheduledInputLabels_apply {I : Type*} (role : I → CopyScheduleRole)
    (n r : ℕ) (e : Fin r ≃ CurrentPivotConstituent role n)
    (P : Fin r → ℕ) (L : CopyScheduleH role n → ℕ) (U : CopyScheduleY role n → ℕ)
    (i : Fin r ⊕ (CopyScheduleH role n ⊕ CopyScheduleY role n)) :
    scheduledInputLabels role n r e P L U (enumeratedPartitionEquiv role n r e i) =
      Sum.elim P (Sum.elim L U) i := by
  simp only [scheduledInputLabels, Equiv.symm_apply_apply]

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_ScheduledFrequencyHistory
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Finite frequency histories with the actual cutoff at every level -/

namespace Ostmann

open scoped Classical

def ScheduledFrequencyIndex (V : ℕ → ℕ) : ℕ → Type
  | 0 => transferFrequencyRange (V 0)
  | n + 1 => (transferFrequencyRange (V (n + 1))) ×
      (ScheduledFrequencyIndex V n × ScheduledFrequencyIndex V n)

noncomputable def scheduledFrequencyHistory (V : ℕ → ℕ) :
    (n : ℕ) → ScheduledFrequencyIndex V n → FrequencyTree ℤ n
  | 0, a => a.val
  | n + 1, a => (a.1.val, scheduledFrequencyHistory V n a.2.1, scheduledFrequencyHistory V n a.2.2)

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_ScheduledHistoryEmbedding
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Embedding the actual varying-cutoff histories without adding bottom frequencies -/

namespace Ostmann
open scoped BigOperators Classical

abbrev NonzeroScheduledHistory (V : ℕ → ℕ) (n : ℕ) :=
  {a : ScheduledFrequencyIndex V n //
    ∀ s ∈ allFrequencyList n (scheduledFrequencyHistory V n a), s ≠ 0}

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Preliminaries_DivisorPowerBound
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The elementary divisor bound needed for the frequency moduli

For every fixed power `k`, the `k`th power of the divisor count is bounded
by a constant times `n`. The constant is independent of the modulus.
-/

namespace Ostmann

open scoped BigOperators Classical
open Filter

theorem successor_le_two_pow (e : ℕ) : e + 1 ≤ 2 ^ e := by
  induction e with
  | zero => simp
  | succ e ih =>
    rw [pow_succ]
    omega

theorem exists_successor_power_bound (k : ℕ) :
    ∃ C : ℕ, 1 ≤ C ∧ ∀ e : ℕ, (e + 1) ^ k ≤ C * 2 ^ e := by
  have he := (tendsto_pow_const_div_const_pow_of_one_lt k (by norm_num : (1 : ℝ) < 2)).eventually
    (gt_mem_nhds (by norm_num : (0 : ℝ) < 1))
  obtain ⟨N, hN⟩ := eventually_atTop.mp he
  refine ⟨N ^ k + 2, by omega, fun e => ?_⟩
  by_cases hn : N ≤ e + 1
  · have hpow : ((e + 1 : ℕ) : ℝ) ^ k < (2 : ℝ) ^ (e + 1) :=
      (div_lt_one (by positivity)).mp (hN (e + 1) hn)
    have hnat : (e + 1) ^ k ≤ 2 ^ (e + 1) := by exact_mod_cast hpow.le
    rw [pow_succ] at hnat
    exact hnat.trans (by simpa only [Nat.mul_comm] using
      Nat.mul_le_mul_right (2 ^ e) (show 2 ≤ N ^ k + 2 by omega))
  · have hsmall : (e + 1) ^ k ≤ N ^ k := Nat.pow_le_pow_left (by omega) k
    have ht : 1 ≤ 2 ^ e := Nat.one_le_two_pow
    exact hsmall.trans ((Nat.le_mul_of_pos_right _ (lt_of_lt_of_le Nat.zero_lt_one ht)).trans
      (Nat.mul_le_mul_right _ (show N ^ k ≤ N ^ k + 2 by omega)))

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_MovingFrequencyCoefficient
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Summing the actual sampled coefficient over its internal frequencies -/

namespace Ostmann
open scoped Classical BigOperators

/-- The root frequency is fixed by the amplitude; only its descendants are
summed here, each under its own level cutoff. -/
def MovingDescendantFrequencyIndex (V : ℕ → ℕ) : ℕ → Type
  | 0 => Unit
  | n + 1 => ScheduledFrequencyIndex V n × ScheduledFrequencyIndex V n

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_FiniteFormulaRenaming
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Reindexing the polynomial support bound onto actual finite prime slots -/

namespace Ostmann

open scoped BigOperators Classical

namespace HistoryFormula

def rename {V W : Type*} (f : V → W) (F : HistoryFormula V) : HistoryFormula W :=
  F.bind (fun i => .prime (f i))

end HistoryFormula

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_RealBulkKernel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The full original kernel on real bulk coordinates -/

namespace Ostmann
open MeasureTheory
open scoped Classical BigOperators SchwartzMap ComplexConjugate

theorem MovingSlotReversal.continuous_bulkLogComposite {σ : Type*}
    (base : σ → ℝ) (S : Finset σ) (s : MovingSlotReversal σ)
    (L R : (σ → ℝ) → ℝ) (hL : Continuous L) (hR : Continuous R) :
    Continuous (fun x => s.realCompositePivot (bulkLogValues base S x) (L x) (R x)) := by
  unfold realCompositePivot
  exact (((continuous_const.mul
    (continuous_realSlotProduct _ (continuous_bulkLogValues base S) s.rightSlots)).mul hR).sub
    ((continuous_const.mul
    (continuous_realSlotProduct _ (continuous_bulkLogValues base S) s.leftSlots)).mul hL)).div_const _

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_MovingPatternBulkBudgets
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Concrete length and frequency budgets for the original pattern pair -/

namespace Ostmann
open scoped Classical

/-- The literal frequency list controls every actual formula-node frequency. -/
theorem MovingSlotData.Follows.frequencies_iff {A : Type*} {n : ℕ}
    {T : MovingSlotData A n} {t : FrequencyTree ℤ n} (h : T.Follows t) (P : ℤ → Prop) :
    T.Frequencies P ↔ ∀ s ∈ allFrequencyList n t, P s := by
  induction T with
  | leaf s L =>
    change s = t at h
    subst s
    simp only [MovingSlotData.Frequencies, allFrequencyList, List.mem_singleton, forall_eq]
  | node s CL CR u l r hl hr =>
    rcases h with ⟨hs, hL, hR⟩
    simp only [MovingSlotData.Frequencies, hs, allFrequencyList,
      List.mem_cons, List.mem_append, or_imp, forall_and, forall_eq,
      hl hL, hr hR]

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_MovingSlotStateRelabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Evaluating the original recursion in finite pattern coordinates -/

namespace Ostmann
open scoped Classical

def MovingSlotState.map {σ τ : Type*} (f : σ → τ) (x : MovingSlotState σ) :
    MovingSlotState τ := ⟨x.depth, x.data.map f, x.leftGiant, x.rightGiant⟩

@[simp] theorem MovingSlotState.map_depth {σ τ : Type*} (f : σ → τ)
    (x : MovingSlotState σ) : (x.map f).depth = x.depth := rfl

@[simp] theorem MovingSlotState.map_data {σ τ : Type*} (f : σ → τ)
    (x : MovingSlotState σ) : (x.map f).data = x.data.map f := rfl

@[simp] theorem MovingSlotState.map_leftGiant {σ τ : Type*} (f : σ → τ)
    (x : MovingSlotState σ) : (x.map f).leftGiant = x.leftGiant := rfl

@[simp] theorem MovingSlotState.map_rightGiant {σ τ : Type*} (f : σ → τ)
    (x : MovingSlotState σ) : (x.map f).rightGiant = x.rightGiant := rfl

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_MovingOriginalWeightRelabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The original giant weight commutes with evaluating pattern labels -/

namespace Ostmann
open scoped Classical BigOperators SchwartzMap

@[simp] theorem MovingSlotData.regularSlots_map {σ τ : Type*} (f : σ → τ)
    {n : ℕ} (T : MovingSlotData σ n) : (T.map f).regularSlots = T.regularSlots.map f := by
  cases T <;> simp only [MovingSlotData.map, MovingSlotData.regularSlots, List.map_append]

@[simp] theorem MovingSlotData.frequencyProduct_map {σ τ : Type*} (f : σ → τ)
    {n : ℕ} (T : MovingSlotData σ n) : (T.map f).frequencyProduct = T.frequencyProduct := by
  induction T with
  | leaf => rfl
  | node s CL CR u l r ihL ihR =>
    simp only [MovingSlotData.map, MovingSlotData.frequencyProduct, ihL, ihR]

@[simp] theorem MovingSlotData.currentSlots_map {σ τ : Type*} (f : σ → τ)
    (value : τ → ℕ) {n : ℕ} (T : MovingSlotData σ n) (XL XR : ℕ) :
    (T.map f).currentSlots value XL XR = T.currentSlots (value ∘ f) XL XR := by
  simp only [MovingSlotData.currentSlots, MovingSlotData.regularSlots_map, List.map_map]

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Characters_MixedExternalAverage
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The original root, prime and integer average as one finite positive law -/

namespace Ostmann
open scoped Classical BigOperators

abbrev MixedExternalPoint (B A : Type*) (N : ℕ) (u v r w : ℝ) :=
  transferFrequencyRange N × (B → A) ×
    (Finset.Ioc ⌊Real.exp r⌋₊ ⌊Real.exp w⌋₊) × (Finset.Ioc ⌊Real.exp u⌋₊ ⌊Real.exp v⌋₊)

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Characters_TreeArrangementFraction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Bad-arrangement fractions on the actual recursive leaf index -/

namespace Ostmann
open scoped Classical

def BadTreeArrangement {n m : ℕ} (e : Equiv.Perm (TreeLeafIndex n × Fin m)) : Prop :=
  3 * Fintype.card (TreeLeafIndex n) <
    4 * Fintype.card (arrangementGraph m e).ConnectedComponent

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_MovingRegularTemplate
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The actual small and bulk slots at a moving-giant level -/

namespace Ostmann
open scoped Classical BigOperators

/-- Each surviving leaf has its remaining small slots and its original bulk. -/
abbrev MovingRegularSlot (n r m : ℕ) := TreeLeafIndex n × (Fin r ⊕ Fin m)

def movingTemplateBulk (n r m : ℕ) : (TreeLeafIndex n × Fin m) ↪ MovingRegularSlot n r m where
  toFun j := (j.1, .inr j.2)
  inj' := by intro i j h; cases i; cases j; cases h; rfl

/-- Restoring a removed type puts its four sampled compensation primes back
before the surviving small slots. Bulk labels retain their identity. -/
def movingReverseTemplate (n r m : ℕ) :
    ((TreeLeafIndex n × Fin 4) ⊕ MovingRegularSlot n r m) ≃ MovingRegularSlot n (4 + r) m where
  toFun
    | .inl (j, i) => (j, .inl (Fin.castAdd r i))
    | .inr (j, .inl i) => (j, .inl (Fin.natAdd 4 i))
    | .inr (j, .inr i) => (j, .inr i)
  invFun
    | (j, .inl i) => Fin.addCases (fun a => .inl (j, a)) (fun b => .inr (j, .inl b)) i
    | (j, .inr i) => .inr (j, .inr i)
  left_inv := by
    intro x
    rcases x with (⟨j, i⟩ | ⟨j, i | i⟩) <;> simp
  right_inv := by
    rintro ⟨j, i | i⟩
    · refine Fin.addCases (fun a => ?_) (fun b => ?_) i <;> simp
    · rfl

@[simp] theorem movingReverseTemplate_bulk (n r m : ℕ) (j : TreeLeafIndex n × Fin m) :
    movingReverseTemplate n r m (.inr (movingTemplateBulk n r m j)) =
      movingTemplateBulk n (4 + r) m j := rfl

@[simp] theorem movingReverseTemplate_compensation (n r m : ℕ) (j : TreeLeafIndex n × Fin 4) :
    movingReverseTemplate n r m (.inl j) = (j.1, .inl (Fin.castAdd r j.2)) := rfl

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_MovingTemplatePrior
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The unchanged independent prime law under one template restoration -/

namespace Ostmann
open scoped Classical BigOperators

noncomputable def movingRestoreSample {A : Type*} (n r m : ℕ)
    (u : TreeLeafIndex n × Fin 4 → A) (y : MovingRegularSlot n r m → A) :
    MovingRegularSlot n (4 + r) m → A :=
  Sum.elim u y ∘ (movingReverseTemplate n r m).symm

@[simp] theorem movingRestoreSample_compensation {A : Type*} (n r m : ℕ)
    (u : TreeLeafIndex n × Fin 4 → A) (y : MovingRegularSlot n r m → A)
    (i : TreeLeafIndex n × Fin 4) :
    movingRestoreSample n r m u y (i.1, .inl (Fin.castAdd r i.2)) = u i := by
  change Sum.elim u y ((movingReverseTemplate n r m).symm
    (movingReverseTemplate n r m (.inl i))) = _
  rw [Equiv.symm_apply_apply]
  rfl

@[simp] theorem movingRestoreSample_small {A : Type*} (n r m : ℕ)
    (u : TreeLeafIndex n × Fin 4 → A) (y : MovingRegularSlot n r m → A)
    (j : TreeLeafIndex n) (i : Fin r) :
    movingRestoreSample n r m u y (j, .inl (Fin.natAdd 4 i)) = y (j, .inl i) := by
  change Sum.elim u y ((movingReverseTemplate n r m).symm
    (movingReverseTemplate n r m (.inr (j, .inl i)))) = _
  rw [Equiv.symm_apply_apply]
  rfl

@[simp] theorem movingRestoreSample_bulk {A : Type*} (n r m : ℕ)
    (u : TreeLeafIndex n × Fin 4 → A) (y : MovingRegularSlot n r m → A)
    (i : TreeLeafIndex n × Fin m) :
    movingRestoreSample n r m u y (movingTemplateBulk n (4 + r) m i) =
      y (movingTemplateBulk n r m i) := by
  rw [← movingReverseTemplate_bulk n r m i]
  change Sum.elim u y ((movingReverseTemplate n r m).symm
    (movingReverseTemplate n r m (.inr (movingTemplateBulk n r m i)))) = _
  rw [Equiv.symm_apply_apply]
  rfl

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_QuadraticCenter_SquarefreeFrequency
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The unique squarefree frequency decomposition -/

namespace Ostmann

/-- The squarefree kernel is divided into the part supported on `L` and
the part coprime to `L`. Positivity excludes the zero frequency. -/
structure SquarefreeFrequency (L u : ℕ) where
  s : ℕ
  v : ℕ
  w : ℕ
  s_pos : 0 < s
  v_pos : 0 < v
  w_pos : 0 < w
  kernel_squarefree : Squarefree (s * v)
  v_dvd : v ∣ L
  s_coprime : s.Coprime L
  value : s * v * w ^ 2 = u

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Defs
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Ostmann
open scoped Pointwise symmDiff

def EventuallyEqual (S T : Set ℕ) : Prop :=
  ∃ N : ℕ, ∀ n : ℕ, N ≤ n → (n ∈ S ↔ n ∈ T)

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Preliminaries_Residues
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Complementary residue supports

The elementary reduction in §2 of the manuscript. Only the exclusion of
composite sums is used to separate the tail supports at a prime.
-/

namespace Ostmann

/-- Residues of a summand after deleting the initial interval through `N + p`. -/
def tailResidues (A : Set ℕ) (N p : ℕ) : Set (ZMod p) :=
  (fun a : ℕ => (a : ZMod p)) '' {a | a ∈ A ∧ N + p < a}

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Preliminaries_Projection
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Residue projection of finite probability measures

These identities connect the pair count in `WeightedCollision` with the
collision norm of a projected measure, as used in Lemma 2.5 of the paper.
-/

namespace Ostmann

open scoped BigOperators

/-- Mass of a fiber of a map, for a measure supported on a finite set. -/
noncomputable def fiberMass {α β : Type*} [DecidableEq β]
    (s : Finset α) (μ : α → ℝ) (f : α → β) (y : β) : ℝ :=
  ∑ a ∈ s with f a = y, μ a

/-- The probability mass function obtained by reduction modulo `p`. -/
noncomputable def residueMass (s : Finset ℕ) (μ : ℕ → ℝ) (p r : ℕ) : ℝ :=
  fiberMass s μ (fun a => a % p) r

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Preliminaries_Stability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# The finite collision-stability inequality

This is the finite quantitative calculation in Lemma 2.5 of the manuscript.
The final theorem takes the exact numerical consequences of Chebyshev's
bound and Mertens' first theorem at the chosen cutoff as explicit hypotheses.
No main theorem of the manuscript is assumed here.
-/

namespace Ostmann

open scoped BigOperators

/-- The three nonnegative terms in the collision stability estimate. -/
noncomputable def collisionDefect (p : ℕ) (s t : Finset ℕ) (μ ν : ℕ → ℝ) : ℝ :=
  (∑ r ∈ s, (μ r - 1 / (s.card : ℝ)) ^ 2) +
  (∑ r ∈ t, (ν r - 1 / (t.card : ℝ)) ^ 2) +
  (1 / (s.card : ℝ) + 1 / (t.card : ℝ) - 4 / (p : ℝ))

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Preliminaries_TailStability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Collision stability on the two summand tails

This specializes the finite collision bound to the complementary supports
forced by an eventual prime decomposition. Prime-sum estimates remain
explicit hypotheses; no statement about the existence of a decomposition
is assumed as an analytic input.
-/

namespace Ostmann

open scoped BigOperators

/-- Natural-number label for the negative residue of a summand element. -/
def negativeResidue (p a : ℕ) : ℕ := (-(a : ZMod p)).val

/-- All residues of the first summand's infinite tail, labeled in `[0,p)`. -/
noncomputable def tailSupport (A : Set ℕ) (N p : ℕ) : Finset ℕ := by
  classical
  exact (Finset.range p).filter (fun r => (r : ZMod p) ∈ tailResidues A N p)

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_ZeroDensity_PrimeSumInputs
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Ostmann

open scoped BigOperators

/-- The precise one-sided consequence of Mertens' first theorem needed by
the collision argument. `C` is fixed independently of the cutoff. -/
def MertensLowerBound (C : ℝ) : Prop :=
  ∀ Q : ℕ, 1 ≤ Q → Real.log (Q : ℝ) - C ≤
    ∑ p ∈ Nat.primesLE Q, Real.log (p : ℝ) / (p : ℝ)

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_QuadraticSieve_PublishedQuadraticSieve
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The published quadratic large-sieve input

D. R. Heath-Brown, *A mean value estimate for real character sums*,
Acta Arithmetica 72 (1995), 235–275, Theorem 1,
DOI 10.4064/aa-72-3-235-275.

Only the finite odd-squarefree coefficient inequality is retained. The
symbol is Mathlib's Jacobi symbol.
-/

namespace Ostmann

open scoped BigOperators Classical

def oddSquarefreeRange (N : ℕ) : Finset ℕ :=
  (Finset.Icc 1 N).filter fun n => Odd n ∧ Squarefree n

noncomputable def quadraticSieveSum (N : ℕ) (b : ℕ → ℂ) (m : ℕ) : ℂ :=
  ∑ n ∈ oddSquarefreeRange N, b n * (jacobiSym (n : ℤ) m : ℂ)

noncomputable def quadraticSieveEnergy (N : ℕ) (b : ℕ → ℂ) : ℝ :=
  ∑ n ∈ oddSquarefreeRange N, ‖b n‖ ^ 2

/-- Heath-Brown's Theorem 1, specialized to integer bounds and finite
coefficient arrays. This is an explicit hypothesis, not a global axiom. -/
def PublishedQuadraticLargeSieve : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 < C ∧
    ∀ M N : ℕ, 1 ≤ M → 1 ≤ N → ∀ b : ℕ → ℂ,
      (∑ m ∈ oddSquarefreeRange M, ‖quadraticSieveSum N b m‖ ^ 2) ≤
        C * ((M : ℝ) * N) ^ ε * ((M : ℝ) + N) * quadraticSieveEnergy N b

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_ScheduledFinalPermutation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The final parity reassignments as permutations of actual active slots -/

namespace Ostmann
open scoped Classical BigOperators

/-- An actual copied word coordinate belongs to H at every depth. -/
noncomputable def scheduledWordH {I : Type*} (role : I → CopyScheduleRole)
    (n : ℕ) (t : Fin n → Bool) (i : {i : I // role i = .word}) :
    CopyScheduleH role n :=
  ⟨copySchedulePath n t i.val, copyScheduleSurvives_path role i.val i.property n t,
    by rw [copyScheduleRole_path role i.val i.property n t]; rfl⟩

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_ScheduledWordLeafCoordinates
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # One original word-prime coordinate at each arithmetic tree leaf -/

namespace Ostmann
open scoped BigOperators Classical

/-- Left arithmetic children use the positive copy of H. -/
def treeLeafCopyPath : (n : ℕ) → TreeLeafIndex n → Fin n → Bool
  | 0, _ => fun j => Fin.elim0 j
  | n + 1, .inl t => Fin.snoc (treeLeafCopyPath n t) true
  | n + 1, .inr t => Fin.snoc (treeLeafCopyPath n t) false

theorem treeLeafCopyPath_injective (n : ℕ) : Function.Injective (treeLeafCopyPath n) := by
  induction n with
  | zero =>
    intro x y _
    exact @Subsingleton.elim Unit _ x y
  | succ n ih =>
    intro x y h
    cases x with
    | inl x =>
      cases y with
      | inl y =>
        apply congrArg Sum.inl
        apply ih
        funext j
        simpa only [treeLeafCopyPath, Fin.snoc_castSucc] using congrFun h j.castSucc
      | inr y =>
        have hh := congrFun h (Fin.last n)
        simp only [treeLeafCopyPath, Fin.snoc_last] at hh
        cases hh
    | inr x =>
      cases y with
      | inl y =>
        have hh := congrFun h (Fin.last n)
        simp only [treeLeafCopyPath, Fin.snoc_last] at hh
        cases hh
      | inr y =>
        apply congrArg Sum.inr
        apply ih
        funext j
        simpa only [treeLeafCopyPath, Fin.snoc_castSucc] using congrFun h j.castSucc

noncomputable def wordLeafSlot {I : Type*} (role : I → CopyScheduleRole)
    (i : I) (hi : role i = .word) (n : ℕ) : TreeLeafIndex n ↪ CopyScheduleAtoms role n where
  toFun t := ⟨copySchedulePath n (treeLeafCopyPath n t) i,
    copyScheduleSurvives_path role i hi n _⟩
  inj' := by
    intro x y h
    apply treeLeafCopyPath_injective n
    exact congrArg Prod.fst (copySchedulePath_injective n
      (a₁ := (treeLeafCopyPath n x, i)) (a₂ := (treeLeafCopyPath n y, i))
      (congrArg Subtype.val h))

theorem wordLeafSlot_role {I : Type*} (role : I → CopyScheduleRole)
    (i : I) (hi : role i = .word) (n : ℕ) (t : TreeLeafIndex n) :
    copyScheduleRole role n (wordLeafSlot role i hi n t).val = .word :=
  copyScheduleRole_path role i hi n _

abbrev WordLeafOutside {I : Type*} (role : I → CopyScheduleRole)
    (i : I) (hi : role i = .word) (n : ℕ) :=
  {v : CopyScheduleAtoms role n // v ∉ Set.range (wordLeafSlot role i hi n)}

noncomputable def wordLeafPartition {I : Type*} (role : I → CopyScheduleRole)
    (i : I) (hi : role i = .word) (n : ℕ) :
    TreeLeafIndex n ⊕ WordLeafOutside role i hi n ≃ CopyScheduleAtoms role n :=
  (Equiv.sumCongr (Equiv.ofInjective _ (wordLeafSlot role i hi n).injective)
    (Equiv.refl _)).trans (Equiv.Set.sumCompl (Set.range (wordLeafSlot role i hi n)))

noncomputable def wordLeafAssignment {I A : Type*} (role : I → CopyScheduleRole)
    (i : I) (hi : role i = .word) (n : ℕ)
    (y : WordLeafOutside role i hi n → A) (x : TreeLeafIndex n → A) :
    CopyScheduleAtoms role n → A :=
  fun v => Sum.elim x y ((wordLeafPartition role i hi n).symm v)

@[simp] theorem wordLeafAssignment_leaf {I A : Type*} (role : I → CopyScheduleRole)
    (i : I) (hi : role i = .word) (n : ℕ)
    (y : WordLeafOutside role i hi n → A) (x : TreeLeafIndex n → A) (t : TreeLeafIndex n) :
    wordLeafAssignment role i hi n y x (wordLeafSlot role i hi n t) = x t := by
  change Sum.elim x y ((wordLeafPartition role i hi n).symm
    (wordLeafPartition role i hi n (.inl t))) = _
  rw [Equiv.symm_apply_apply]
  rfl

@[simp] theorem wordLeafAssignment_outside {I A : Type*} (role : I → CopyScheduleRole)
    (i : I) (hi : role i = .word) (n : ℕ)
    (y : WordLeafOutside role i hi n → A) (x : TreeLeafIndex n → A)
    (v : WordLeafOutside role i hi n) : wordLeafAssignment role i hi n y x v.val = y v := by
  change Sum.elim x y ((wordLeafPartition role i hi n).symm
    (wordLeafPartition role i hi n (.inr v))) = _
  rw [Equiv.symm_apply_apply]
  rfl

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_ScheduledWordLeafProducts
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The selected prime products in the two actual H branches -/

namespace Ostmann
open scoped BigOperators Classical

noncomputable def wordLeafHSlot {I : Type*} (role : I → CopyScheduleRole)
    (i : I) (hi : role i = .word) (n : ℕ) : TreeLeafIndex n ↪ CopyScheduleH role n where
  toFun t := ⟨(wordLeafSlot role i hi n t).val, (wordLeafSlot role i hi n t).property, by
    rw [wordLeafSlot_role]
    rfl⟩
  inj' := by
    intro a b h
    apply (wordLeafSlot role i hi n).injective
    have hv : (wordLeafSlot role i hi n a).val = (wordLeafSlot role i hi n b).val :=
      congrArg (fun z : CopyScheduleH role n => z.val) h
    exact Subtype.ext hv

abbrev WordLeafHOutside {I : Type*} (role : I → CopyScheduleRole)
    (i : I) (hi : role i = .word) (n : ℕ) :=
  {h : CopyScheduleH role n // h ∉ Set.range (wordLeafHSlot role i hi n)}

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_MovingTemplatePair
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The two independent surviving regular templates -/

namespace Ostmann
open scoped Classical BigOperators

def movingTemplatePairEquiv (n r m : ℕ) :
    MovingRegularSlot n r m ⊕ MovingRegularSlot n r m ≃ MovingRegularSlot (n + 1) r m :=
  (Equiv.sumProdDistrib (TreeLeafIndex n) (TreeLeafIndex n) (Fin r ⊕ Fin m)).symm

noncomputable def movingTemplatePairSample {A : Type*} (n r m : ℕ)
    (left right : MovingRegularSlot n r m → A) : MovingRegularSlot (n + 1) r m → A :=
  Sum.elim left right ∘ (movingTemplatePairEquiv n r m).symm

@[simp] theorem movingTemplatePairSample_left {A : Type*} (n r m : ℕ)
    (left right : MovingRegularSlot n r m → A) (j : MovingRegularSlot n r m) :
    movingTemplatePairSample n r m left right (.inl j.1, j.2) = left j := rfl

@[simp] theorem movingTemplatePairSample_right {A : Type*} (n r m : ℕ)
    (left right : MovingRegularSlot n r m → A) (j : MovingRegularSlot n r m) :
    movingTemplatePairSample n r m left right (.inr j.1, j.2) = right j := rfl

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_MovingTransferSlots
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Reindexing the original pivot, compensation, and surviving slots -/

namespace Ostmann
open scoped Classical BigOperators

/-- The first block is the removed giant and compensation. The second is
one surviving giant and its remaining regular slots. -/
def movingTransferSlotEquiv (n r m : ℕ) :
    ((Unit ⊕ (TreeLeafIndex n × Fin 4)) ⊕ (Unit ⊕ MovingRegularSlot n r m)) ≃
      (Bool ⊕ MovingRegularSlot n (4 + r) m) where
  toFun
    | .inl (.inl _) => .inl true
    | .inl (.inr i) => .inr (movingReverseTemplate n r m (.inl i))
    | .inr (.inl _) => .inl false
    | .inr (.inr i) => .inr (movingReverseTemplate n r m (.inr i))
  invFun
    | .inl true => .inl (.inl ())
    | .inl false => .inr (.inl ())
    | .inr j => match (movingReverseTemplate n r m).symm j with
      | .inl i => .inl (.inr i)
      | .inr i => .inr (.inr i)
  left_inv := by
    intro i
    rcases i with ((u | i) | (u | i))
    · cases u; rfl
    · change (match (movingReverseTemplate n r m).symm (movingReverseTemplate n r m (.inl i)) with
        | .inl j => Sum.inl (Sum.inr j)
        | .inr j => Sum.inr (Sum.inr j)) = _
      rw [Equiv.symm_apply_apply]
    · cases u; rfl
    · change (match (movingReverseTemplate n r m).symm (movingReverseTemplate n r m (.inr i)) with
        | .inl j => Sum.inl (Sum.inr j)
        | .inr j => Sum.inr (Sum.inr j)) = _
      rw [Equiv.symm_apply_apply]
  right_inv := by
    intro i
    rcases i with (b | j)
    · cases b <;> rfl
    · have h := (movingReverseTemplate n r m).apply_symm_apply j
      cases he : (movingReverseTemplate n r m).symm j with
      | inl k =>
        simp only [he] at h ⊢
        exact congrArg Sum.inr h
      | inr k =>
        simp only [he] at h ⊢
        exact congrArg Sum.inr h

@[simp] theorem movingTransferSlotEquiv_pivot (n r m : ℕ) :
    movingTransferSlotEquiv n r m (.inl (.inl ())) = .inl true := rfl

@[simp] theorem movingTransferSlotEquiv_old_giant (n r m : ℕ) :
    movingTransferSlotEquiv n r m (.inr (.inl ())) = .inl false := rfl

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_MovingAmplitudeIndex
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The surviving giant, regular tuple and frequency as one transfer index -/

namespace Ostmann
open scoped Classical BigOperators

abbrev MovingAmplitudeIndex (σ : Type) (Pg : Finset ℕ) (n r m : ℕ) (V : ℕ → ℕ) :=
  Pg × ((MovingRegularSlot n r m → σ) × transferFrequencyRange (V n))

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_SmoothLogCellProfile
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # A fixed smooth partition profile for the original logarithmic cells -/

namespace Ostmann
open Filter
open scoped Classical

noncomputable def logCellProfile (x : ℝ) : ℝ :=
  Real.smoothTransition (x + 1) - Real.smoothTransition x

theorem logCellProfile_nonneg (x : ℝ) : 0 ≤ logCellProfile x :=
  sub_nonneg.mpr (Real.smoothTransition.monotone (by linarith))

theorem logCellProfile_le_one (x : ℝ) : logCellProfile x ≤ 1 := by
  unfold logCellProfile
  linarith [Real.smoothTransition.le_one (x + 1), Real.smoothTransition.nonneg x]

theorem logCellProfile_zero_outside (x : ℝ) (hx : 1 ≤ |x|) : logCellProfile x = 0 := by
  unfold logCellProfile
  rcases le_total 0 x with h | h
  · rw [abs_of_nonneg h] at hx
    rw [Real.smoothTransition.one_of_one_le (by linarith), Real.smoothTransition.one_of_one_le hx]
    norm_num
  · rw [abs_of_nonpos h] at hx
    rw [Real.smoothTransition.zero_of_nonpos (by linarith), Real.smoothTransition.zero_of_nonpos h]
    norm_num

theorem logCellProfile_contDiff {n : ℕ∞} : ContDiff ℝ n logCellProfile :=
  (Real.smoothTransition.contDiff.comp (contDiff_id.add contDiff_const)).sub
    Real.smoothTransition.contDiff

theorem logCellProfile_compactSupport : HasCompactSupport logCellProfile := by
  apply HasCompactSupport.intro (K := Set.Icc (-1 : ℝ) 1) isCompact_Icc
  intro x hx
  apply logCellProfile_zero_outside
  by_contra h
  have hh := abs_lt.mp (lt_of_not_ge h)
  exact hx ⟨by linarith, by linarith⟩

/-- One fixed finite Lipschitz constant supplies every later variation bound. -/
theorem logCellProfile_lipschitz : ∃ D : ℝ, 0 ≤ D ∧
    ∀ x y, |logCellProfile x - logCellProfile y| ≤ D * |x - y| := by
  obtain ⟨D, hD⟩ := ContDiff.lipschitzWith_of_hasCompactSupport
    (𝕂 := ℝ) logCellProfile_compactSupport
    (logCellProfile_contDiff (n := 1)) (by norm_num)
  refine ⟨D, D.coe_nonneg, ?_⟩
  intro x y
  simpa only [Real.dist_eq] using hD.dist_le_mul x y

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_MovingBulkLogFactors
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The retained bulk logarithmic cutoffs as polynomial factors -/

namespace Ostmann
open scoped Classical BigOperators

noncomputable def bulkLogCutoffWeight {σ : Type*} (value : σ → ℝ)
    (cb : ℝ) (slots : List σ) : ℝ :=
  positiveLogCutoff logCellProfile cb (realSlotProduct value slots)

theorem bulkLogCutoffWeight_bounds {σ : Type*} (value : σ → ℝ)
    (cb : ℝ) (slots : List σ) :
    0 ≤ bulkLogCutoffWeight value cb slots ∧ bulkLogCutoffWeight value cb slots ≤ 1 := by
  unfold bulkLogCutoffWeight positiveLogCutoff
  split_ifs
  · exact ⟨logCellProfile_nonneg _, logCellProfile_le_one _⟩
  · exact ⟨le_rfl, zero_le_one⟩

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Preliminaries_MertensPrimeBands
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The exact published Mertens input for logarithmic prime bands

F. Mertens, J. reine angew. Math. 78 (1874), 46–62, first theorem,
DOI 10.1515/crll.1874.78.46. Both sides of the bounded-error estimate
are needed to subtract the lower cutoff; the collision argument uses
only its previously recorded lower-bound consequence.
-/

namespace Ostmann

open scoped BigOperators Classical

def MertensEstimate (C : ℝ) : Prop :=
  ∀ Q : ℕ, 1 ≤ Q → |(∑ p ∈ Nat.primesLE Q, Real.log (p : ℝ) / p) - Real.log Q| ≤ C

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_TargetPrimeWords
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Actual prime-cell words for every pivot and filler target -/

namespace Ostmann

open Filter
open scoped BigOperators Classical

noncomputable def loglogShell (P : Finset ℕ) (u : ℝ) : Finset ℕ :=
  P.filter (fun p => u < Real.log (Real.log (p : ℝ)) ∧
    Real.log (Real.log (p : ℝ)) ≤ u + 1)

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Characters_CharacterTargetWords
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Simultaneous positive-length words for every character pivot and the filler -/
namespace Ostmann
open Filter
open scoped Classical BigOperators

/-- A word consists of cells from one whole, previously tested rich shell. -/
structure CharacterTargetWord (P : Finset ℕ) (F : ℕ → ℂ)
    (c δ U : ℝ) (k : ℕ) (T : ℝ) where
  shell : ℕ
  indices : List ℕ
  shell_le : shell ≤ 5 * k
  rich : c ≤ ∑ p ∈ loglogShell P (U + shell), (p : ℝ)⁻¹
  lower : Real.log T - 2 * (k : ℝ) / 10000 ≤ U + shell
  upper : U + shell + 1 ≤ Real.log T - (k : ℝ) / 10000
  cells : ∀ h ∈ indices,
    δ * c / (32 * Real.exp (U + shell)) ≤
      finiteCellMass (loglogShell P (U + shell)) primeLogIndex (fun p => (p : ℝ)⁻¹) h ∧
    (∑ p : loglogShell P (U + shell), primeCellWordPrior _ h p) = 1 ∧
    δ / 2 ≤ (∑ p : loglogShell P (U + shell), (primeCellWordPrior _ h p : ℂ) * F p).re
  error : |(indices.sum : ℝ) - T| < 64 / (δ * c)
  length_le : (indices.length : ℝ) ≤ 256 / (δ * c) * Real.exp (2 * (k : ℝ) / 10000)

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_MatchedRetainedPhase
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Exact diagonal phase quotients with a fixed external pivot -/

namespace Ostmann

open scoped BigOperators ComplexConjugate Classical

def retainedInternalGraph {I : Type*} (b : Option I → Option I → ℤ) (i j : I) : ℤ :=
  b (some i) (some j)

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Characters_CharacterScheduleRoles
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The finite role set used in the nonquadratic character argument

A positive word, finitely many pivot groups, two fresh anchors at each step,
and one filler have independent negative copies. Only the positive word,
pivots and anchors participate in the copy schedule.
-/
namespace Ostmann
open scoped Classical BigOperators

abbrev CharacterCell (k : ℕ) := Fin k ⊕ ((Fin k × Bool) ⊕ Unit)
abbrev CharacterRole (k : ℕ) := Bool × Option (CharacterCell k)

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_InsertedConstituentWords
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Word coordinates for the fixed integer pivot and the retained primes -/

namespace Ostmann

open scoped BigOperators Classical

abbrev InsertedConstituentVariable {I : Type*} (role : I → CopyScheduleRole)
    (size : I → ℕ) (n : ℕ) :=
  Option (CopyScheduleH (fun i : Σ a, Fin (size a) => role i.1) n ⊕
    CopyScheduleY (fun i : Σ a, Fin (size a) => role i.1) n)

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_FixedPivotFormulas
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Removing the fixed pivot from the independent polynomial variables -/

namespace Ostmann.HistoryFormula

open scoped Classical

def fixNone {V : Type*} (M : ℤ) (F : HistoryFormula (Option V)) : HistoryFormula V :=
  F.bind (fun i => match i with | none => .external M | some v => .prime v)

def fixedOriginalPrimes {V : Type*} {n : ℕ} (M : ℤ)
    (F : HistoryFormula (ExpandedScheduledVariable (Option V) n)) : HistoryFormula V :=
  F.originalPrimes.fixNone M

end Ostmann.HistoryFormula

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_FixedPivotTopConditions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Original-prime tests for a top atom pair containing a fixed pivot -/

namespace Ostmann

open scoped Classical

def TopPrimeCondition.HasVariable {V : Type*} : TopPrimeCondition (Option V) → Prop
  | .distinct none none => False
  | .external none _ => False
  | _ => True

def TopPrimeCondition.fixPivot {V : Type*} (M : ℕ) :
    (c : TopPrimeCondition (Option V)) → c.HasVariable → TopPrimeCondition V
  | .distinct none none, h => False.elim h
  | .distinct (some a) none, _ => .external a M
  | .distinct none (some b), _ => .external b M
  | .distinct (some a) (some b), _ => .distinct a b
  | .external none _, h => False.elim h
  | .external (some a) N, _ => .external a N

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Characters_CharacterHCoordinates
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Exact whole-atom coordinates of the character argument's copied block -/
namespace Ostmann
open scoped Classical BigOperators

abbrev CharacterHIndex (k n : ℕ) := (Fin n → Bool) ⊕ ({j : Fin k // n < j.val} ⊕ Bool)

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Characters_CharacterTargetCellData
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The selected target words as actual harmonic cells in the common prime space -/
namespace Ostmann
open Filter
open scoped Classical BigOperators

noncomputable def CharacterTargetWord.cell {P : Finset ℕ} {F : ℕ → ℂ}
    {c δ U : ℝ} {k : ℕ} {T : ℝ} (w : CharacterTargetWord P F c δ U k T) (h : ℕ) :
    Finset ℕ := (loglogShell P (U + w.shell)).filter (fun p => primeLogIndex p = h)

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Characters_CharacterAnchorCells
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Actual small and large anchor cells with their original harmonic laws -/
namespace Ostmann
open Filter
open scoped Classical BigOperators

structure CharacterAnchorCell (P : Finset ℕ) (F : ℕ → ℂ) (c δ u : ℝ) where
  index : ℕ
  lower : Real.exp u / 2 ≤ index
  upper : (index : ℝ) ≤ 3 * Real.exp u
  mass : δ * c / (32 * Real.exp u) ≤
    ∑ p ∈ (loglogShell P u).filter (fun p => primeLogIndex p = index), (p : ℝ)⁻¹
  mean : δ / 2 ≤ (∑ p : P,
    (primeSubsetPrior P ((loglogShell P u).filter
      (fun p => primeLogIndex p = index)) p : ℂ) * F p).re

noncomputable def CharacterAnchorCell.cell {P : Finset ℕ} {F : ℕ → ℂ} {c δ u : ℝ}
    (a : CharacterAnchorCell P F c δ u) : Finset ℕ :=
  (loglogShell P u).filter (fun p => primeLogIndex p = a.index)

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_ZeroDensity_FiniteLaplaceDensity
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Ostmann
open scoped Classical BigOperators

theorem finite_exp_density_square_sum {ι : Type*} (S : Finset ι)
    (y : ι → ℝ) (A B : ℝ) (hB : 0 ≤ B)
    (hy : ∀ i ∈ S, 0 ≤ y i)
    (hc : ∀ t : ℝ, 0 ≤ t →
      ((S.filter (fun i => y i ≤ t)).card : ℝ) ≤ B * Real.exp (A * t)) :
    (∑ i ∈ S, Real.exp (-(2 * A) * y i)) ≤
      B ^ 2 * ∑ j ∈ Finset.range S.card, ((j + 1 : ℕ) : ℝ)⁻¹ ^ 2 := by
  revert hy hc
  refine Finset.strongInductionOn S ?_
  intro S ih hy hc
  by_cases hn : S.Nonempty
  · obtain ⟨i, hi, hmax⟩ := S.exists_max_image y hn
    have hf : S.filter (fun j => y j ≤ y i) = S := by
      apply Finset.filter_eq_self.mpr
      exact hmax
    have hcard := hc (y i) (hy i hi)
    rw [hf] at hcard
    have hn0 : (0 : ℝ) < S.card := by exact_mod_cast Finset.card_pos.mpr hn
    have hm := mul_le_mul_of_nonneg_right hcard (Real.exp_nonneg (-(A * y i)))
    have he : Real.exp (A * y i) * Real.exp (-(A * y i)) = 1 := by
      rw [← Real.exp_add, add_neg_cancel, Real.exp_zero]
    rw [mul_assoc, he, mul_one] at hm
    have hpoint : Real.exp (-(2 * A) * y i) ≤ B ^ 2 * (S.card : ℝ)⁻¹ ^ 2 := by
      have hd : Real.exp (-(A * y i)) ≤ B / S.card := by
        apply (le_div_iff₀ hn0).mpr
        simpa only [mul_comm] using hm
      have hs := (sq_le_sq₀ (Real.exp_nonneg _) (div_nonneg hB hn0.le)).mpr hd
      refine (le_of_eq ?_).trans (hs.trans (le_of_eq ?_))
      · rw [pow_two, ← Real.exp_add]
        congr 1
        ring
      · rw [div_pow, div_eq_mul_inv, inv_pow]
    have hrest := ih (S.erase i) (Finset.erase_ssubset hi)
      (fun j hj => hy j (Finset.mem_of_mem_erase hj))
      (fun t ht => (show (((S.erase i).filter (fun j => y j ≤ t)).card : ℝ) ≤
        (S.filter (fun j => y j ≤ t)).card from by
          exact_mod_cast Finset.card_le_card (Finset.filter_subset_filter _ (Finset.erase_subset _ _))).trans
          (hc t ht))
    have hsize : (S.erase i).card + 1 = S.card := Finset.card_erase_add_one hi
    rw [← Finset.sum_erase_add S (fun i => Real.exp (-(2 * A) * y i)) hi]
    rw [← hsize, Finset.sum_range_succ, mul_add]
    exact add_le_add hrest (by simpa only [hsize] using hpoint)
  · have he : S = ∅ := Finset.not_nonempty_iff_eq_empty.mp hn
    simp only [he, Finset.sum_empty, Finset.card_empty, Finset.range_zero, mul_zero, le_refl]

theorem finite_reciprocal_square_sum_le_two (N : ℕ) :
    (∑ j ∈ Finset.range N, ((j + 1 : ℕ) : ℝ)⁻¹ ^ 2) ≤ 2 := by
  have he : (∑ j ∈ Finset.range N, ((j + 1 : ℕ) : ℝ)⁻¹ ^ 2) =
      ∑ j ∈ Finset.Ioo 0 (N + 1), ((j : ℝ) ^ 2)⁻¹ := by
    have hset : Finset.Ioo 0 (N + 1) = Finset.Ico 1 (N + 1) := by
      ext j
      simp only [Finset.mem_Ioo, Finset.mem_Ico]
      omega
    rw [hset, Finset.sum_Ico_eq_sum_range]
    simp only [Nat.add_sub_cancel, inv_pow, Nat.add_comm]
  rw [he]
  simpa only [Nat.cast_zero, zero_add, div_one] using
    (sum_Ioo_inv_sq_le (α := ℝ) 0 (N + 1))

/-- An exponential counting bound and a zero-free gap give exponential
decay for the whole finite zero sum. Squaring the counting constant is harmless
for the subsequent `exp(-D L)` estimates. -/
theorem finite_laplace_density_bound {ι : Type*} (S : Finset ι)
    (y : ι → ℝ) (A B M u : ℝ) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hM : 4 * A ≤ M) (hu : 0 ≤ u) (hy : ∀ i ∈ S, u ≤ y i)
    (hc : ∀ t : ℝ, 0 ≤ t →
      ((S.filter (fun i => y i ≤ t)).card : ℝ) ≤ B * Real.exp (A * t)) :
    (∑ i ∈ S, Real.exp (-M * y i)) ≤
      2 * B ^ 2 * Real.exp (-(M * u) / 2) := by
  have hy0 (i) (hi : i ∈ S) : 0 ≤ y i := hu.trans (hy i hi)
  have hM0 : 0 ≤ M := by linarith
  calc
    _ ≤ ∑ i ∈ S, Real.exp (-(M * u) / 2) * Real.exp (-(2 * A) * y i) := by
      apply Finset.sum_le_sum
      intro i hi
      rw [← Real.exp_add]
      apply Real.exp_le_exp.mpr
      have h1 := mul_nonneg (sub_nonneg.mpr (hy i hi)) hM0
      have h2 := mul_nonneg (by linarith : 0 ≤ M - 4 * A) (hy0 i hi)
      nlinarith
    _ = Real.exp (-(M * u) / 2) * ∑ i ∈ S, Real.exp (-(2 * A) * y i) :=
      (Finset.mul_sum ..).symm
    _ ≤ Real.exp (-(M * u) / 2) * (B ^ 2 *
        ∑ j ∈ Finset.range S.card, ((j + 1 : ℕ) : ℝ)⁻¹ ^ 2) :=
      mul_le_mul_of_nonneg_left (finite_exp_density_square_sum S y A B hB hy0 hc)
        (Real.exp_nonneg _)
    _ ≤ Real.exp (-(M * u) / 2) * (B ^ 2 * 2) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left
        (finite_reciprocal_square_sum_le_two S.card) (sq_nonneg B)) (Real.exp_nonneg _)
    _ = _ := by ring

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_ZeroDensity_HighZeroTailBound
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Rapid Mellin decay summed against an ordinary zero count -/

namespace Ostmann
open scoped Classical BigOperators

theorem zero_height_log_count {ι : Type*} (S : Finset ι) (h : ι → ℝ)
    (Q K : ℝ) (hQ : 1 ≤ Q) (hK : 0 ≤ K) (hh : ∀ i ∈ S, 0 ≤ h i)
    (hcount : ∀ t : ℝ, 0 ≤ t →
      ((S.filter (fun i => h i ≤ t)).card : ℝ) ≤ K * (t + 1) * Real.log (Q * (t + 2))) :
    ∀ s : ℝ, 0 ≤ s →
      ((S.filter (fun i => Real.log (1 + h i) ≤ s)).card : ℝ) ≤
        (2 * K * (Real.log Q + 3)) * Real.exp (2 * s) := by
  intro s hs
  have hQp : 0 < Q := by linarith
  have he : 1 ≤ Real.exp s := Real.one_le_exp hs
  have hlogQ : 0 ≤ Real.log Q := Real.log_nonneg hQ
  have hsub : S.filter (fun i => Real.log (1 + h i) ≤ s) ⊆
      S.filter (fun i => h i ≤ Real.exp s) := by
    intro i hi
    obtain ⟨hiS, hi⟩ := Finset.mem_filter.mp hi
    refine Finset.mem_filter.mpr ⟨hiS, ?_⟩
    have hpos : 0 < 1 + h i := by linarith [hh i hiS]
    have hex := (Real.log_le_iff_le_exp hpos).mp hi
    linarith
  have hlog : Real.log (Q * (Real.exp s + 2)) ≤ (Real.log Q + 3) * Real.exp s := by
    rw [Real.log_mul hQp.ne' (by positivity : Real.exp s + 2 ≠ 0)]
    have he2 : 3 ≤ Real.exp (2 : ℝ) := by linarith [Real.add_one_le_exp (2 : ℝ)]
    have hinside : Real.exp s + 2 ≤ Real.exp (s + 2) := by
      rw [Real.exp_add]
      nlinarith
    have hl := Real.log_le_log (by positivity : 0 < Real.exp s + 2) hinside
    rw [Real.log_exp] at hl
    have hq := mul_le_mul_of_nonneg_left he (by linarith : 0 ≤ Real.log Q + 2)
    have hs' := Real.add_one_le_exp s
    nlinarith
  have hlog0 : 0 ≤ Real.log (Q * (Real.exp s + 2)) :=
    Real.log_nonneg (by nlinarith)
  calc
    _ ≤ ((S.filter (fun i => h i ≤ Real.exp s)).card : ℝ) := by
      exact_mod_cast Finset.card_le_card hsub
    _ ≤ K * (Real.exp s + 1) * Real.log (Q * (Real.exp s + 2)) :=
      hcount (Real.exp s) (Real.exp_nonneg _)
    _ ≤ (K * (2 * Real.exp s)) * ((Real.log Q + 3) * Real.exp s) := by
      apply mul_le_mul
      · exact mul_le_mul_of_nonneg_left (by linarith) hK
      · exact hlog
      · exact hlog0
      · positivity
    _ = (2 * K * (Real.log Q + 3)) * Real.exp (2 * s) := by
      rw [show 2 * s = s + s by ring, Real.exp_add]
      ring

theorem finite_high_zero_tail_bound {ι : Type*} (S : Finset ι) (h : ι → ℝ)
    (Q K T : ℝ) (hQ : 1 ≤ Q) (hK : 0 ≤ K) (hT : 0 ≤ T)
    (hh : ∀ i ∈ S, T ≤ h i)
    (hcount : ∀ t : ℝ, 0 ≤ t →
      ((S.filter (fun i => h i ≤ t)).card : ℝ) ≤ K * (t + 1) * Real.log (Q * (t + 2))) :
    (∑ i ∈ S, Real.exp (-8 * Real.log (1 + h i))) ≤
      2 * (2 * K * (Real.log Q + 3)) ^ 2 * Real.exp (-4 * Real.log (1 + T)) := by
  have hh0 (i) (hi : i ∈ S) : 0 ≤ h i := hT.trans (hh i hi)
  have hlogQ : 0 ≤ Real.log Q := Real.log_nonneg hQ
  have hu : 0 ≤ Real.log (1 + T) := Real.log_nonneg (by linarith)
  have hh' := finite_laplace_density_bound S (fun i => Real.log (1 + h i)) 2
    (2 * K * (Real.log Q + 3)) 8 (Real.log (1 + T)) (by norm_num) (by positivity)
    (by norm_num) hu
    (fun i hi => Real.log_le_log (by linarith : 0 < 1 + T) (by linarith [hh i hi]))
    (zero_height_log_count S h Q K hQ hK hh0 hcount)
  rw [show -(8 * Real.log (1 + T)) / 2 = -4 * Real.log (1 + T) by ring] at hh'
  exact hh'

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_SmoothPrimeMeanTest
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # A fixed smooth test for the prime mean of the sparse weight -/

namespace Ostmann
open MeasureTheory
open scoped BigOperators

noncomputable def primeMeanTest (t : ℝ) : ℝ := logCellProfile (8 * (t - 3 / 4))

theorem primeMeanTest_nonneg (t : ℝ) : 0 ≤ primeMeanTest t := logCellProfile_nonneg _

theorem primeMeanTest_le_one (t : ℝ) : primeMeanTest t ≤ 1 := logCellProfile_le_one _

theorem primeMeanTest_contDiff {n : ℕ∞} : ContDiff ℝ n primeMeanTest :=
  logCellProfile_contDiff.comp (contDiff_const.mul (contDiff_id.sub contDiff_const))

theorem primeMeanTest_zero_outside (t : ℝ) (ht : t ∉ Set.Icc (5 / 8 : ℝ) (7 / 8)) :
    primeMeanTest t = 0 := by
  apply logCellProfile_zero_outside
  by_contra h
  have hh := abs_lt.mp (lt_of_not_ge h)
  exact ht ⟨by linarith, by linarith⟩

noncomputable def primeMeanMellin (s : ℂ) : ℂ :=
  ∫ t in Set.Ioi (0 : ℝ), (primeMeanTest t : ℂ) *
    Complex.exp ((s - 1) * (Real.log t : ℂ))

noncomputable def smoothMangoldtMean (q : ℕ) (χ : DirichletCharacter ℂ q) (X : ℝ) : ℂ :=
  ∑' n : ℕ, (ArithmeticFunction.vonMangoldt n : ℂ) * χ (n : ZMod q) * primeMeanTest (n / X)

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_ZeroDensity_SmoothMellinDerivatives
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Ostmann

open MeasureTheory
open scoped BigOperators Interval

theorem primeMeanTest_iteratedDeriv_continuous (n : ℕ) :
    Continuous (iteratedDeriv n primeMeanTest) :=
  (primeMeanTest_contDiff (n := (n : ℕ∞))).continuous_iteratedDeriv' n

theorem primeMeanTest_iteratedDeriv_zero_outside (n : ℕ) (t : ℝ)
    (ht : t ∉ Set.Icc (5 / 8 : ℝ) (7 / 8)) : iteratedDeriv n primeMeanTest t = 0 := by
  induction n generalizing t with
  | zero => simpa using primeMeanTest_zero_outside t ht
  | succ n ih =>
    rw [iteratedDeriv_succ]
    have hs : tsupport (iteratedDeriv n primeMeanTest) ⊆
        Set.Icc (5 / 8 : ℝ) (7 / 8) := by
      apply closure_minimal _ isClosed_Icc
      intro x hx
      by_contra hn
      exact hx (ih x hn)
    exact deriv_of_notMem_tsupport (fun h => ht (hs h))

theorem primeMeanTest_iteratedDeriv_bound (n : ℕ) :
    ∃ D : ℝ, 0 < D ∧ ∀ t : ℝ, |iteratedDeriv n primeMeanTest t| ≤ D := by
  obtain ⟨D, hD⟩ := isCompact_Icc.exists_bound_of_continuousOn
    (primeMeanTest_iteratedDeriv_continuous n).continuousOn
  refine ⟨|D| + 1, by positivity, ?_⟩
  intro t
  by_cases ht : t ∈ Set.Icc (5 / 8 : ℝ) (7 / 8)
  · have h := hD t ht
    rw [Real.norm_eq_abs] at h
    linarith [le_abs_self D]
  · rw [primeMeanTest_iteratedDeriv_zero_outside n t ht, abs_zero]
    positivity

theorem exp_log_shift (z : ℂ) {t : ℝ} (ht : 0 < t) :
    Complex.exp (z * (Real.log t : ℂ)) =
      (t : ℂ) * Complex.exp ((z - 1) * (Real.log t : ℂ)) := by
  have he : z * (Real.log t : ℂ) = (Real.log t : ℂ) +
      (z - 1) * (Real.log t : ℂ) := by ring
  rw [he, Complex.exp_add, ← Complex.ofReal_exp, Real.exp_log ht]

theorem hasDerivAt_exp_log (z : ℂ) {t : ℝ} (ht : 0 < t) :
    HasDerivAt (fun t : ℝ => Complex.exp (z * (Real.log t : ℂ)))
      (z * Complex.exp ((z - 1) * (Real.log t : ℂ))) t := by
  have h := (((Real.hasDerivAt_log ht.ne').ofReal_comp).const_mul z).cexp
  convert h using 1
  all_goals try with_reducible_and_instances rfl
  rw [exp_log_shift z ht, Complex.ofReal_inv]
  field_simp [Complex.ofReal_ne_zero.mpr ht.ne']

noncomputable def shiftedPrimeMeanMellin (n : ℕ) (s : ℂ) : ℂ :=
  ∫ t in (1 / 2 : ℝ)..1,
    ((iteratedDeriv n primeMeanTest t : ℝ) : ℂ) *
      Complex.exp ((s + n - 1) * (Real.log t : ℂ))

theorem shiftedPrimeMeanMellin_zero (s : ℂ) :
    shiftedPrimeMeanMellin 0 s = primeMeanMellin s := by
  simp only [shiftedPrimeMeanMellin, iteratedDeriv_zero, Nat.cast_zero, add_zero,
    primeMeanMellin]
  rw [setIntegral_eq_integral_of_forall_compl_eq_zero]
  · apply intervalIntegral.integral_eq_integral_of_support_subset
    intro t ht
    have hmem : t ∈ Set.Icc (5 / 8 : ℝ) (7 / 8) := by
      by_contra hn
      exact ht (by simp only [primeMeanTest_zero_outside t hn, Complex.ofReal_zero, zero_mul])
    exact ⟨by linarith [hmem.1], by linarith [hmem.2]⟩
  · intro t ht
    rw [primeMeanTest_zero_outside t (by
      intro hm
      exact ht (by linarith [hm.1] : 0 < t)), Complex.ofReal_zero, zero_mul]

theorem shiftedPrimeMeanMellin_succ (n : ℕ) (s : ℂ) :
    shiftedPrimeMeanMellin (n + 1) s = -(s + n) * shiftedPrimeMeanMellin n s := by
  have hu (t : ℝ) : HasDerivAt (fun x : ℝ => ((iteratedDeriv n primeMeanTest x : ℝ) : ℂ))
      ((iteratedDeriv (n + 1) primeMeanTest t : ℝ) : ℂ) t := by
    have hd := (primeMeanTest_contDiff (n := ((n + 1 : ℕ) : ℕ∞))).differentiable_iteratedDeriv' n
    have h := (hd t).hasDerivAt.ofReal_comp
    simpa only [iteratedDeriv_succ] using h
  have hv (t : ℝ) (ht : t ∈ Set.uIcc (1 / 2 : ℝ) 1) :
      HasDerivAt (fun x : ℝ => Complex.exp ((s + n) * (Real.log x : ℂ)))
        ((s + n) * Complex.exp ((s + n - 1) * (Real.log t : ℂ))) t :=
    hasDerivAt_exp_log _ (by rw [Set.uIcc_of_le (by norm_num)] at ht; linarith [ht.1])
  have hui : IntervalIntegrable (fun t : ℝ =>
      ((iteratedDeriv (n + 1) primeMeanTest t : ℝ) : ℂ)) volume (1 / 2) 1 :=
    (Complex.continuous_ofReal.comp (primeMeanTest_iteratedDeriv_continuous _)).intervalIntegrable _ _
  have hvi : IntervalIntegrable (fun t : ℝ =>
      (s + n) * Complex.exp ((s + n - 1) * (Real.log t : ℂ))) volume (1 / 2) 1 := by
    apply ContinuousOn.intervalIntegrable
    rw [Set.uIcc_of_le (by norm_num : (1 / 2 : ℝ) ≤ 1)]
    fun_prop (disch := grind)
  have hi := intervalIntegral.integral_mul_deriv_eq_deriv_mul (fun t _ => hu t) hv hui hvi
  have hleft : (∫ t in (1 / 2 : ℝ)..1,
      ((iteratedDeriv n primeMeanTest t : ℝ) : ℂ) *
        ((s + n) * Complex.exp ((s + n - 1) * (Real.log t : ℂ)))) =
      (s + n) * shiftedPrimeMeanMellin n s := by
    rw [shiftedPrimeMeanMellin, ← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro t ht
    ring
  rw [hleft, primeMeanTest_iteratedDeriv_zero_outside n 1 (by norm_num),
    primeMeanTest_iteratedDeriv_zero_outside n (1 / 2) (by norm_num),
    Complex.ofReal_zero] at hi
  simp only [zero_mul, sub_self, zero_sub] at hi
  have hr : (∫ t in (1 / 2 : ℝ)..1,
      ((iteratedDeriv (n + 1) primeMeanTest t : ℝ) : ℂ) *
        Complex.exp ((s + n) * (Real.log t : ℂ))) = shiftedPrimeMeanMellin (n + 1) s := by
    simp only [shiftedPrimeMeanMellin, Nat.cast_add, Nat.cast_one, ← add_assoc, add_sub_cancel_right]
  rw [hr] at hi
  linear_combination hi

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_ZeroDensity_SmoothMellinBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Uniform Mellin decay of the fixed test in the required strip -/

namespace Ostmann

open MeasureTheory Finset
open scoped BigOperators Interval

theorem shiftedPrimeMeanMellin_product (n : ℕ) (s : ℂ) :
    shiftedPrimeMeanMellin n s =
      (-1 : ℂ) ^ n * (∏ j ∈ range n, (s + j)) * primeMeanMellin s := by
  induction n with
  | zero => simp [shiftedPrimeMeanMellin_zero]
  | succ n ih =>
    rw [shiftedPrimeMeanMellin_succ, ih, pow_succ, prod_range_succ]
    ring

/-- All shifted integrals needed below have a uniform bound on the fixed
half-unit interval. The power of t is bounded using only Re(s) >= -1/2. -/
theorem shiftedPrimeMeanMellin_norm_bound (n : ℕ) (s : ℂ) (D : ℝ)
    (hD : 0 ≤ D) (hd : ∀ t : ℝ, |iteratedDeriv n primeMeanTest t| ≤ D)
    (hs : -(1 / 2 : ℝ) ≤ s.re) :
    ‖shiftedPrimeMeanMellin n s‖ ≤ 4 * D := by
  have hi := intervalIntegral.norm_integral_le_of_norm_le_const
    (a := (1 / 2 : ℝ)) (b := 1) (C := 4 * D)
    (f := fun t : ℝ => ((iteratedDeriv n primeMeanTest t : ℝ) : ℂ) *
      Complex.exp ((s + n - 1) * (Real.log t : ℂ))) (fun t ht => ?_)
  · change ‖shiftedPrimeMeanMellin n s‖ ≤ _ at hi
    norm_num at hi
    nlinarith
  rw [Set.uIoc_of_le (by norm_num : (1 / 2 : ℝ) ≤ 1)] at ht
  have ht0 : 0 < t := by linarith [ht.1]
  have hloglo : -Real.log 2 ≤ Real.log t := by
    have h := Real.log_le_log (by norm_num : (0 : ℝ) < 1 / 2) ht.1.le
    rw [Real.log_div (by norm_num : (1 : ℝ) ≠ 0) (by norm_num : (2 : ℝ) ≠ 0),
      Real.log_one, zero_sub] at h
    exact h
  have hloghi : Real.log t ≤ 0 := Real.log_nonpos ht0.le ht.2
  have hcoef : -2 ≤ s.re + (n : ℝ) - 1 := by linarith [Nat.cast_nonneg (α := ℝ) n]
  have hcost : (s.re + (n : ℝ) - 1) * Real.log t ≤ 2 * Real.log 2 := by
    have h := mul_le_mul_of_nonpos_right hcoef hloghi
    linarith
  have he : ‖Complex.exp ((s + n - 1) * (Real.log t : ℂ))‖ ≤ 4 := by
    rw [Complex.norm_exp]
    simp only [Complex.mul_re, Complex.sub_re, Complex.add_re, Complex.natCast_re,
      Complex.one_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero]
    calc
      _ ≤ Real.exp (2 * Real.log 2) := Real.exp_le_exp.mpr hcost
      _ = 4 := by rw [show (2 : ℝ) * Real.log 2 = Real.log 2 + Real.log 2 by ring,
        Real.exp_add, Real.exp_log (by norm_num : (0 : ℝ) < 2)]; norm_num
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
  calc
    _ ≤ D * 4 := mul_le_mul (hd t) he (norm_nonneg _) hD
    _ = _ := by ring

/-- The product introduced by eight integrations by parts controls the
imaginary height without excluding real s. -/
theorem primeMeanMellin_height_bound (s : ℂ) (D : ℝ) (hD : 0 ≤ D)
    (hd : ∀ t : ℝ, |iteratedDeriv 8 primeMeanTest t| ≤ D)
    (hs : -(1 / 2 : ℝ) ≤ s.re) :
    |s.im| ^ 8 * ‖primeMeanMellin s‖ ≤ 4 * D := by
  have hp : |s.im| ^ 8 ≤ ∏ j ∈ range 8, ‖s + (j : ℕ)‖ := by
    have h := prod_le_prod (f := fun _ : ℕ => |s.im|)
      (g := fun j : ℕ => ‖s + (j : ℂ)‖) (s := range 8)
      (fun j _ => abs_nonneg s.im) (fun j _ => ?_)
    · simpa using h
    simpa only [Complex.add_im, Complex.natCast_im, add_zero] using
      Complex.abs_im_le_norm (s + (j : ℂ))
  calc
    _ ≤ (∏ j ∈ range 8, ‖s + (j : ℕ)‖) * ‖primeMeanMellin s‖ :=
      mul_le_mul_of_nonneg_right hp (norm_nonneg _)
    _ = ‖shiftedPrimeMeanMellin 8 s‖ := by
      rw [shiftedPrimeMeanMellin_product, norm_mul, norm_mul, norm_pow, norm_neg, norm_one]
      simp only [one_pow, one_mul, norm_prod]
    _ ≤ _ := shiftedPrimeMeanMellin_norm_bound 8 s D hD hd hs

/-- The precise eighth-order decay field needed in the published explicit
formula structure is unconditional for the actual fixed test. -/
theorem primeMeanMellin_decay : ∃ C : ℝ, 0 < C ∧
    ∀ s : ℂ, -(1 / 2 : ℝ) ≤ s.re → s.re ≤ 2 →
      ‖primeMeanMellin s‖ ≤ C * Real.exp (-8 * Real.log (1 + |s.im|)) := by
  obtain ⟨D, hD, hd⟩ := primeMeanTest_iteratedDeriv_bound 8
  refine ⟨1024 * (D + 1), by positivity, ?_⟩
  intro s hs hs2
  have hb : ‖primeMeanMellin s‖ ≤ 4 := by
    have h := shiftedPrimeMeanMellin_norm_bound 0 s 1 (by norm_num) (fun t => ?_) hs
    · simpa only [shiftedPrimeMeanMellin_zero, mul_one] using h
    simp only [iteratedDeriv_zero]
    rw [abs_of_nonneg (primeMeanTest_nonneg t)]
    exact primeMeanTest_le_one t
  have hh := primeMeanMellin_height_bound s D hD.le hd hs
  have hm : ‖primeMeanMellin s‖ * (1 + |s.im|) ^ 8 ≤ 1024 * (D + 1) := by
    by_cases hsmall : |s.im| ≤ 1
    · have hpow : (1 + |s.im|) ^ 8 ≤ 256 := by
        calc
          _ ≤ (2 : ℝ) ^ 8 := pow_le_pow_left₀ (by positivity) (by linarith) 8
          _ = _ := by norm_num
      have h := mul_le_mul hb hpow (by positivity) (by norm_num : (0 : ℝ) ≤ 4)
      nlinarith
    · have hlarge : 1 ≤ |s.im| := le_of_lt (lt_of_not_ge hsmall)
      have hpow : (1 + |s.im|) ^ 8 ≤ 256 * |s.im| ^ 8 := by
        calc
          _ ≤ (2 * |s.im|) ^ 8 := pow_le_pow_left₀ (by positivity) (by linarith) 8
          _ = _ := by ring
      have h := mul_le_mul_of_nonneg_left hpow (norm_nonneg (primeMeanMellin s))
      nlinarith
  have hx : 0 < 1 + |s.im| := by positivity
  have he : Real.exp (-8 * Real.log (1 + |s.im|)) = ((1 + |s.im|) ^ 8)⁻¹ := by
    rw [show -(8 : ℝ) * Real.log (1 + |s.im|) =
      -((8 : ℕ) * Real.log (1 + |s.im|)) by norm_num, Real.exp_neg,
      Real.exp_nat_mul, Real.exp_log hx]
  rw [he, ← div_eq_mul_inv]
  exact (le_div_iff₀ (pow_pos hx 8)).mpr hm

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_ZeroDensity_CharacterTrivialZero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The residue at the origin in the primitive explicit formula -/

namespace Ostmann

open Filter
open scoped Topology Classical

theorem gammaReal_inverse_factor (s : ℂ) :
    (Complex.Gammaℝ s)⁻¹ = s * ((2 * (Real.pi : ℂ))⁻¹ * (Complex.Gammaℝ (s + 2))⁻¹) := by
  by_cases hs : s = 0
  · subst s
    simp [Complex.Gammaℝ_def, Complex.Gamma_zero]
  rw [Complex.Gammaℝ_add_two hs]
  simp [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm, hs,
    Complex.ofReal_ne_zero.mpr Real.pi_ne_zero]

theorem gammaReal_inverse_order_zero :
    analyticOrderAt (fun s : ℂ => (Complex.Gammaℝ s)⁻¹) 0 = 1 := by
  let H : ℂ → ℂ := fun s => (2 * (Real.pi : ℂ))⁻¹ * (Complex.Gammaℝ (s + 2))⁻¹
  have hH : AnalyticAt ℂ H 0 :=
    ((Complex.differentiable_Gammaℝ_inv.comp (differentiable_id.add_const 2)).const_mul _).analyticAt 0
  have hHne : H 0 ≠ 0 := by
    dsimp only [H]
    exact mul_ne_zero (inv_ne_zero (mul_ne_zero two_ne_zero (by exact_mod_cast Real.pi_ne_zero)))
      (inv_ne_zero (Complex.Gammaℝ_ne_zero_of_re_pos (by norm_num)))
  have he : (fun s : ℂ => (Complex.Gammaℝ s)⁻¹) = (fun s => s) * H := by
    funext s
    exact gammaReal_inverse_factor s
  rw [he]
  change analyticOrderAt (id * H) 0 = 1
  rw [analyticOrderAt_mul analyticAt_id hH, hH.analyticOrderAt_eq_zero.mpr hHne, add_zero]
  simp

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_ZeroDensity_GammaContourBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Gamma logarithmic derivatives on the four contour lines -/

namespace Ostmann

open Complex

theorem gamma_not_pole_of_re (z : ℂ) (hz : -1 < z.re) (hne : z.re ≠ 0) :
    ∀ n : ℕ, z ≠ -(n : ℂ) := by
  intro n he
  have hh := congrArg Complex.re he
  cases n with
  | zero => simp at hh; exact hne hh
  | succ n =>
    simp at hh
    have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    linarith

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_ZeroDensity_GammaRealContourBound
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Bounds for the real-place Gamma factor on the shifted contour -/

namespace Ostmann

open Complex

theorem gammaReal_contour_regular (s : ℂ)
    (hs : s.re = -(1 / 2 : ℝ) ∨ s.re = 1 / 2 ∨ s.re = 3 / 2 ∨ s.re = 5 / 2) :
    ∀ n : ℕ, s / 2 ≠ -(n : ℂ) := by
  apply gamma_not_pole_of_re
  · simp only [div_ofNat_re]
    rcases hs with h | h | h | h <;> linarith
  · simp only [div_ofNat_re]
    rcases hs with h | h | h | h <;> rw [h] <;> norm_num

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_ZeroDensity_CharacterGammaContour
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The actual character Gamma factors on both vertical contour lines -/

namespace Ostmann

open Complex
open scoped Classical

theorem contourLine_expanded (s : ℂ) (hs : s.re = -(1 / 2 : ℝ) ∨ s.re = 3 / 2) :
    s.re = -(1 / 2 : ℝ) ∨ s.re = 1 / 2 ∨ s.re = 3 / 2 ∨ s.re = 5 / 2 := by
  rcases hs with h | h
  · exact .inl h
  · exact .inr (.inr (.inl h))

theorem contourLine_shift (s : ℂ) (hs : s.re = -(1 / 2 : ℝ) ∨ s.re = 3 / 2) :
    (s + 1).re = -(1 / 2 : ℝ) ∨ (s + 1).re = 1 / 2 ∨
      (s + 1).re = 3 / 2 ∨ (s + 1).re = 5 / 2 := by
  simp only [add_re, one_re]
  rcases hs with h | h
  · right; left; linarith
  · right; right; right; linarith

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_ZeroDensity_RectangleLogIntegrals
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The reciprocal integral around a rectangle

These explicit logarithmic primitives fix the orientation and the factor
`2 * pi * I` used by the character contour shift.
-/

namespace Ostmann

open Complex MeasureTheory Set
open scoped Interval

noncomputable def rectangleBoundaryIntegral (f : ℂ → ℂ) (a b c d : ℝ) : ℂ :=
  (∫ x in a..b, f (x + c * I)) - (∫ x in a..b, f (x + d * I)) +
    I * (∫ y in c..d, f (b + y * I)) - I * (∫ y in c..d, f (a + y * I))

theorem reciprocal_horizontal_integral (a b h : ℝ) (hh : h ≠ 0) :
    (∫ x in a..b, ((x : ℂ) + h * I)⁻¹) = log (b + h * I) - log (a + h * I) := by
  have hne (x : ℝ) : (x : ℂ) + h * I ≠ 0 := by
    intro he
    have := congrArg Complex.im he
    simp only [add_im, ofReal_im, mul_im, I_im, I_re, ofReal_re, mul_one,
      mul_zero, add_zero, zero_add, zero_im] at this
    exact hh this
  have hc : Continuous (fun x : ℝ => ((x : ℂ) + h * I)⁻¹) :=
    (Complex.continuous_ofReal.add continuous_const).inv₀ hne
  apply intervalIntegral.integral_eq_sub_of_hasDerivAt _ (hc.intervalIntegrable _ _)
  intro x _
  have hp := (Complex.ofRealCLM.hasDerivAt (x := x)).add_const ((h : ℂ) * I)
  have hs : (x : ℂ) + h * I ∈ slitPlane := by
    rw [mem_slitPlane_iff]
    right
    simpa using hh
  simpa using hp.clog_real hs

theorem reciprocal_vertical_integral_right (x c d : ℝ) (hx : 0 < x) :
    I * (∫ y in c..d, ((x : ℂ) + y * I)⁻¹) =
      log (x + d * I) - log (x + c * I) := by
  have hne (y : ℝ) : (x : ℂ) + y * I ≠ 0 := by
    intro he
    have := congrArg Complex.re he
    simp at this
    linarith
  have hc : Continuous (fun y : ℝ => I * ((x : ℂ) + y * I)⁻¹) :=
    continuous_const.mul ((continuous_const.add (Complex.continuous_ofReal.mul continuous_const)).inv₀ hne)
  rw [← intervalIntegral.integral_const_mul]
  apply intervalIntegral.integral_eq_sub_of_hasDerivAt _ (hc.intervalIntegrable _ _)
  intro y _
  have hp := ((Complex.ofRealCLM.hasDerivAt (x := y)).mul_const I).const_add (x : ℂ)
  have hs : (x : ℂ) + y * I ∈ slitPlane := by
    rw [mem_slitPlane_iff]
    left
    simpa using hx
  simpa [div_eq_mul_inv] using hp.clog_real hs

theorem reciprocal_vertical_integral_left (x c d : ℝ) (hx : x < 0) :
    I * (∫ y in c..d, ((x : ℂ) + y * I)⁻¹) =
      log (-(x + d * I)) - log (-(x + c * I)) := by
  have hne (y : ℝ) : (x : ℂ) + y * I ≠ 0 := by
    intro he
    have := congrArg Complex.re he
    simp at this
    linarith
  have hc : Continuous (fun y : ℝ => I * ((x : ℂ) + y * I)⁻¹) :=
    continuous_const.mul ((continuous_const.add (Complex.continuous_ofReal.mul continuous_const)).inv₀ hne)
  rw [← intervalIntegral.integral_const_mul]
  apply intervalIntegral.integral_eq_sub_of_hasDerivAt _ (hc.intervalIntegrable _ _)
  intro y _
  have hp := (((Complex.ofRealCLM.hasDerivAt (x := y)).mul_const I).const_add (x : ℂ)).neg
  have hs : -((x : ℂ) + y * I) ∈ slitPlane := by
    rw [mem_slitPlane_iff]
    left
    simpa using neg_pos.mpr hx
  simpa only [Pi.neg_apply, Complex.ofRealCLM_apply, Complex.ofReal_one, mul_one, one_mul, neg_div_neg_eq, div_eq_mul_inv, inv_neg, neg_mul_neg] using hp.clog_real hs

theorem log_neg_of_im_pos {z : ℂ} (hz : 0 < z.im) :
    log (-z) = log z - (Real.pi : ℂ) * I := by
  apply Complex.ext
  · simp [log_re]
  · simpa only [log_im, sub_im, add_im, mul_im, ofReal_im, ofReal_re, I_re, I_im, mul_one, mul_zero, add_zero, zero_mul] using arg_neg_eq_arg_sub_pi_of_im_pos hz

theorem log_neg_of_im_neg {z : ℂ} (hz : z.im < 0) :
    log (-z) = log z + (Real.pi : ℂ) * I := by
  apply Complex.ext
  · simp [log_re]
  · simpa only [log_im, sub_im, add_im, mul_im, ofReal_im, ofReal_re, I_re, I_im, mul_one, mul_zero, add_zero, zero_mul] using arg_neg_eq_arg_add_pi_of_im_neg hz

theorem rectangleBoundaryIntegral_reciprocal (a b c d : ℝ)
    (ha : a < 0) (hb : 0 < b) (hc : c < 0) (hd : 0 < d) :
    rectangleBoundaryIntegral (fun z => z⁻¹) a b c d = 2 * (Real.pi : ℂ) * I := by
  rw [rectangleBoundaryIntegral, reciprocal_horizontal_integral a b c hc.ne,
    reciprocal_horizontal_integral a b d hd.ne', reciprocal_vertical_integral_right b c d hb,
    reciprocal_vertical_integral_left a c d ha,
    log_neg_of_im_pos (by simpa using hd), log_neg_of_im_neg (by simpa using hc)]
  ring

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_ZeroDensity_RectangleBoundary
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Ostmann

open Complex MeasureTheory Set
open scoped Interval BigOperators

structure RectangleIntegrable (f : ℂ → ℂ) (a b c d : ℝ) : Prop where
  bottom : IntervalIntegrable (fun x : ℝ => f (x + c * I)) volume a b
  top : IntervalIntegrable (fun x : ℝ => f (x + d * I)) volume a b
  right : IntervalIntegrable (fun y : ℝ => f (b + y * I)) volume c d
  left : IntervalIntegrable (fun y : ℝ => f (a + y * I)) volume c d

theorem RectangleIntegrable.add {f g : ℂ → ℂ} {a b c d : ℝ}
    (hf : RectangleIntegrable f a b c d) (hg : RectangleIntegrable g a b c d) :
    RectangleIntegrable (fun z => f z + g z) a b c d :=
  ⟨hf.bottom.add hg.bottom, hf.top.add hg.top, hf.right.add hg.right, hf.left.add hg.left⟩

theorem rectangleBoundaryIntegral_add {f g : ℂ → ℂ} {a b c d : ℝ}
    (hf : RectangleIntegrable f a b c d) (hg : RectangleIntegrable g a b c d) :
    rectangleBoundaryIntegral (fun z => f z + g z) a b c d =
      rectangleBoundaryIntegral f a b c d + rectangleBoundaryIntegral g a b c d := by
  simp only [rectangleBoundaryIntegral, intervalIntegral.integral_add hf.bottom hg.bottom,
    intervalIntegral.integral_add hf.top hg.top, intervalIntegral.integral_add hf.right hg.right,
    intervalIntegral.integral_add hf.left hg.left]
  ring

theorem RectangleIntegrable.const_mul {f : ℂ → ℂ} {a b c d : ℝ}
    (hf : RectangleIntegrable f a b c d) (v : ℂ) :
    RectangleIntegrable (fun z => v * f z) a b c d :=
  ⟨hf.bottom.const_mul v, hf.top.const_mul v, hf.right.const_mul v, hf.left.const_mul v⟩

theorem rectangleBoundaryIntegral_const_mul (f : ℂ → ℂ) (v : ℂ) (a b c d : ℝ) :
    rectangleBoundaryIntegral (fun z => v * f z) a b c d = v * rectangleBoundaryIntegral f a b c d := by
  simp only [rectangleBoundaryIntegral, intervalIntegral.integral_const_mul]
  ring

theorem RectangleIntegrable.sum {ι : Type*} (S : Finset ι) {f : ι → ℂ → ℂ} {a b c d : ℝ}
    (h : ∀ i ∈ S, RectangleIntegrable (f i) a b c d) :
    RectangleIntegrable (fun z => ∑ i ∈ S, f i z) a b c d := by
  classical
  induction S using Finset.induction_on with
  | empty => simp only [Finset.sum_empty]; exact ⟨by simp, by simp, by simp, by simp⟩
  | @insert i S hi ih =>
    simp only [Finset.sum_insert hi]
    exact (h i (Finset.mem_insert_self _ _)).add
      (ih fun j hj => h j (Finset.mem_insert_of_mem hj))

theorem rectangleBoundaryIntegral_translate (f : ℂ → ℂ) (z : ℂ) (a b c d : ℝ) :
    rectangleBoundaryIntegral (fun s => f (s - z)) a b c d =
      rectangleBoundaryIntegral f (a - z.re) (b - z.re) (c - z.im) (d - z.im) := by
  have hh (h : ℝ) (x : ℝ) : (x : ℂ) + h * I - z =
      ((x - z.re : ℝ) : ℂ) + (h - z.im) * I := by
    apply Complex.ext <;> simp
  have hv (h : ℝ) (y : ℝ) : (h : ℂ) + y * I - z =
      ((h - z.re : ℝ) : ℂ) + (y - z.im) * I := by
    apply Complex.ext <;> simp
  have hi (h : ℝ) : (∫ x in a..b, f ((x : ℂ) + h * I - z)) =
      ∫ x in a - z.re..b - z.re, f ((x : ℂ) + (h - z.im) * I) := by
    rw [← intervalIntegral.integral_comp_sub_right (fun x : ℝ => f ((x : ℂ) + (h - z.im) * I)) z.re]
    apply intervalIntegral.integral_congr
    intro x _
    exact congrArg f (hh h x)
  have hj (h : ℝ) : (∫ y in c..d, f ((h : ℂ) + y * I - z)) =
      ∫ y in c - z.im..d - z.im, f (((h - z.re : ℝ) : ℂ) + y * I) := by
    rw [← intervalIntegral.integral_comp_sub_right (fun y : ℝ => f (((h - z.re : ℝ) : ℂ) + y * I)) z.im]
    apply intervalIntegral.integral_congr
    intro y _
    simpa only [Complex.ofReal_sub] using congrArg f (hv h y)
  unfold rectangleBoundaryIntegral
  rw [hi, hi, hj, hj]
  simp only [Complex.ofReal_sub]

theorem rectangleBoundaryIntegral_sub_inv (z : ℂ) (a b c d : ℝ)
    (ha : a < z.re) (hb : z.re < b) (hc : c < z.im) (hd : z.im < d) :
    rectangleBoundaryIntegral (fun s => (s - z)⁻¹) a b c d = 2 * (Real.pi : ℂ) * I := by
  rw [rectangleBoundaryIntegral_translate]
  exact rectangleBoundaryIntegral_reciprocal _ _ _ _ (sub_neg.mpr ha) (sub_pos.mpr hb)
    (sub_neg.mpr hc) (sub_pos.mpr hd)

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_ZeroDensity_RectangleGeometry
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Ostmann

open Complex MeasureTheory Set
open scoped Interval

def contourRectangleBoundary (a b c d : ℝ) : Set ℂ :=
  {z | z.re ∈ uIcc a b ∧ z.im ∈ uIcc c d ∧
    (z.re = a ∨ z.re = b ∨ z.im = c ∨ z.im = d)}

theorem contourBoundary_bottom {a b c d x : ℝ} (hx : x ∈ uIcc a b) :
    (x : ℂ) + c * I ∈ contourRectangleBoundary a b c d := by
  simpa [contourRectangleBoundary] using hx

theorem contourBoundary_top {a b c d x : ℝ} (hx : x ∈ uIcc a b) :
    (x : ℂ) + d * I ∈ contourRectangleBoundary a b c d := by
  simpa [contourRectangleBoundary] using hx

theorem contourBoundary_right {a b c d y : ℝ} (hy : y ∈ uIcc c d) :
    (b : ℂ) + y * I ∈ contourRectangleBoundary a b c d := by
  simpa [contourRectangleBoundary] using hy

theorem contourBoundary_left {a b c d y : ℝ} (hy : y ∈ uIcc c d) :
    (a : ℂ) + y * I ∈ contourRectangleBoundary a b c d := by
  simpa [contourRectangleBoundary] using hy

theorem rectangleIntegrable_of_continuousOn {f : ℂ → ℂ} {a b c d : ℝ}
    (hf : ContinuousOn f (contourRectangleBoundary a b c d)) :
    RectangleIntegrable f a b c d := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact (hf.comp (continuous_ofReal.add continuous_const).continuousOn
      (fun _ hx => contourBoundary_bottom hx)).intervalIntegrable
  · exact (hf.comp (continuous_ofReal.add continuous_const).continuousOn
      (fun _ hx => contourBoundary_top hx)).intervalIntegrable
  · exact (hf.comp (continuous_const.add (continuous_ofReal.mul continuous_const)).continuousOn
      (fun _ hy => contourBoundary_right hy)).intervalIntegrable
  · exact (hf.comp (continuous_const.add (continuous_ofReal.mul continuous_const)).continuousOn
      (fun _ hy => contourBoundary_left hy)).intervalIntegrable

theorem rectangleBoundaryIntegral_congr {f g : ℂ → ℂ} {a b c d : ℝ}
    (h : EqOn f g (contourRectangleBoundary a b c d)) :
    rectangleBoundaryIntegral f a b c d = rectangleBoundaryIntegral g a b c d := by
  unfold rectangleBoundaryIntegral
  rw [intervalIntegral.integral_congr (fun x hx => h (contourBoundary_bottom hx)),
    intervalIntegral.integral_congr (fun x hx => h (contourBoundary_top hx)),
    intervalIntegral.integral_congr (fun y hy => h (contourBoundary_right hy)),
    intervalIntegral.integral_congr (fun y hy => h (contourBoundary_left hy))]

theorem contourBoundary_ne_interior {a b c d : ℝ} {z w : ℂ}
    (hz : a < z.re ∧ z.re < b ∧ c < z.im ∧ z.im < d)
    (hw : w ∈ contourRectangleBoundary a b c d) : w ≠ z := by
  intro he
  subst w
  rcases hw.2.2 with ha | hb | hc | hd <;> linarith [hz.1, hz.2.1, hz.2.2.1, hz.2.2.2]

theorem rectangleIntegrable_sub_inv {a b c d : ℝ} {z : ℂ}
    (hz : a < z.re ∧ z.re < b ∧ c < z.im ∧ z.im < d) :
    RectangleIntegrable (fun w => (w - z)⁻¹) a b c d := by
  apply rectangleIntegrable_of_continuousOn
  exact (continuous_id.sub continuous_const).continuousOn.inv₀
    (fun w hw => sub_ne_zero.mpr (contourBoundary_ne_interior hz hw))

theorem rectangleBoundaryIntegral_eq_zero {f : ℂ → ℂ} {a b c d : ℝ}
    (hf : AnalyticOnNhd ℂ f (uIcc a b ×ℂ uIcc c d)) :
    rectangleBoundaryIntegral f a b c d = 0 := by
  have h := Complex.integral_boundary_rect_eq_zero_of_differentiableOn f
    ((a : ℂ) + c * I) ((b : ℂ) + d * I) (by simpa using hf.differentiableOn)
  simpa [rectangleBoundaryIntegral, smul_eq_mul] using h

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_ZeroDensity_RealCharacterTrigonometric
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The positive trigonometric polynomial for real characters -/

namespace Ostmann

open Complex
open scoped BigOperators

theorem real_character_unit_polynomial (a : ℝ) (ha : |a| ≤ 1) (u : ℂ)
    (hu : ‖u‖ = 1) : 0 ≤ 3 + 4 * a * u.re + (u * u).re := by
  have hsq := Complex.sq_norm u
  rw [hu] at hsq
  simp only [one_pow, Complex.normSq_apply] at hsq
  rw [Complex.mul_re]
  rcases le_total 0 u.re with hr | hr
  · have hm := mul_nonneg (show 0 ≤ a + 1 by linarith [(abs_le.mp ha).1]) hr
    nlinarith [sq_nonneg (u.re - 1)]
  · have hm := mul_nonneg (show 0 ≤ 1 - a by linarith [(abs_le.mp ha).2]) (neg_nonneg.mpr hr)
    nlinarith [sq_nonneg (u.re + 1)]

theorem LSeries_term_vertical (c : ℕ → ℂ) (n : ℕ) (hn : n ≠ 0) (σ t : ℝ) :
    LSeries.term c ((σ : ℂ) + (t : ℂ) * I) n =
      c n * ((n : ℝ) ^ (-σ) : ℝ) * (n : ℂ) ^ (-(t : ℂ) * I) := by
  rw [LSeries.term_of_ne_zero hn, div_eq_mul_inv, ← Complex.cpow_neg]
  rw [show -((σ : ℂ) + (t : ℂ) * I) = (-(σ : ℝ) : ℂ) + (-(t : ℂ) * I) by ring,
    Complex.cpow_add _ _ (by exact_mod_cast hn)]
  have hr : (n : ℂ) ^ (-(σ : ℂ)) = ((n : ℝ) ^ (-σ) : ℝ) := by
    simpa using (Complex.ofReal_cpow (Nat.cast_nonneg n) (-σ)).symm
  rw [hr]
  ring

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_ZeroDensity_ComplexCharacterTrigonometric
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The 3-4-1 Euler inequality for every complex Dirichlet character -/

namespace Ostmann

open Complex
open scoped BigOperators

theorem complex_character_polynomial_nonneg (v : ℂ) (hv : ‖v‖ ≤ 1) :
    0 ≤ 3 + 4 * v.re + (v * v).re := by
  have hsq := Complex.sq_norm v
  have hn := norm_nonneg v
  simp only [Complex.normSq_apply] at hsq
  rw [Complex.mul_re]
  nlinarith [sq_nonneg (v.re + 1)]

theorem complex_character_trigonometric_term_nonneg {q : ℕ}
    (χ : DirichletCharacter ℂ q) (σ t : ℝ) (n : ℕ) :
    0 ≤ 3 * (LSeries.term (fun n => (ArithmeticFunction.vonMangoldt n : ℂ)) (σ : ℂ) n).re +
      4 * (LSeries.term (fun n => χ n * (ArithmeticFunction.vonMangoldt n : ℂ))
        ((σ : ℂ) + (t : ℂ) * I) n).re +
      (LSeries.term (fun n => (χ ^ 2) n * (ArithmeticFunction.vonMangoldt n : ℂ))
        ((σ : ℂ) + ((2 * t : ℝ) : ℂ) * I) n).re := by
  by_cases hn : n = 0
  · subst n; simp
  let u : ℂ := (n : ℂ) ^ (-(t : ℂ) * I)
  have hu : ‖u‖ = 1 := by
    dsimp [u]
    rw [Complex.norm_natCast_cpow_of_pos (Nat.pos_of_ne_zero hn)]
    simp
  have hv : ‖χ n * u‖ ≤ 1 := by simpa [norm_mul, hu] using χ.norm_le_one n
  have hp := complex_character_polynomial_nonneg (χ n * u) hv
  have hb : 0 ≤ ArithmeticFunction.vonMangoldt n * (n : ℝ) ^ (-σ) :=
    mul_nonneg ArithmeticFunction.vonMangoldt_nonneg (Real.rpow_nonneg (Nat.cast_nonneg n) _)
  have hphase : (n : ℂ) ^ (-((2 * t : ℝ) : ℂ) * I) = u * u := by
    rw [show -((2 * t : ℝ) : ℂ) * I = -(t : ℂ) * I + -(t : ℂ) * I by push_cast; ring]
    exact Complex.cpow_add _ _ (by exact_mod_cast hn)
  have hzero := LSeries_term_vertical (fun n => (ArithmeticFunction.vonMangoldt n : ℂ)) n hn σ 0
  simp only [Complex.ofReal_zero, neg_zero, zero_mul, Complex.cpow_zero, mul_one, add_zero] at hzero
  rw [hzero, LSeries_term_vertical _ n hn, LSeries_term_vertical _ n hn, hphase]
  have hsquare : (χ ^ 2) n = χ n * χ n := by simp [pow_two]
  rw [hsquare]
  convert mul_nonneg hb hp using 1
  all_goals try with_reducible_and_instances rfl
  simp only [Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im]
  ring

theorem dirichlet_mangoldt_LSeries_eq {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (s : ℂ) (hs : 1 < s.re) :
    LSeries (fun n => χ n * (ArithmeticFunction.vonMangoldt n : ℂ)) s =
      -logDeriv (DirichletCharacter.LFunction χ) s := by
  have he := χ.LSeries_twist_vonMangoldt_eq hs
  rw [← χ.deriv_LFunction_eq_deriv_LSeries hs, ← χ.LFunction_eq_LSeries hs] at he
  exact he.trans (neg_div _ _)

theorem complex_character_trigonometric_sum_nonneg {q : ℕ}
    (χ : DirichletCharacter ℂ q) (σ t : ℝ) (hσ : 1 < σ) :
    0 ≤ 3 * (LSeries (fun n => (ArithmeticFunction.vonMangoldt n : ℂ)) (σ : ℂ)).re +
      4 * (LSeries (fun n => χ n * (ArithmeticFunction.vonMangoldt n : ℂ))
        ((σ : ℂ) + (t : ℂ) * I)).re +
      (LSeries (fun n => (χ ^ 2) n * (ArithmeticFunction.vonMangoldt n : ℂ))
        ((σ : ℂ) + ((2 * t : ℝ) : ℂ) * I)).re := by
  have h0 := ArithmeticFunction.LSeriesSummable_vonMangoldt (s := (σ : ℂ)) hσ
  have h1 := χ.LSeriesSummable_twist_vonMangoldt
    (s := (σ : ℂ) + (t : ℂ) * I) (by simpa using hσ)
  change LSeriesSummable (fun n => χ n * (ArithmeticFunction.vonMangoldt n : ℂ))
    ((σ : ℂ) + (t : ℂ) * I) at h1
  have h2 := (χ ^ 2).LSeriesSummable_twist_vonMangoldt
    (s := (σ : ℂ) + ((2 * t : ℝ) : ℂ) * I) (by simpa using hσ)
  change LSeriesSummable (fun n => (χ ^ 2) n * (ArithmeticFunction.vonMangoldt n : ℂ))
    ((σ : ℂ) + ((2 * t : ℝ) : ℂ) * I) at h2
  have hh := tsum_nonneg (L := SummationFilter.unconditional ℕ)
    (complex_character_trigonometric_term_nonneg χ σ t)
  have h0r := (Complex.hasSum_re h0.hasSum).summable
  have h1r := (Complex.hasSum_re h1.hasSum).summable
  have h2r := (Complex.hasSum_re h2.hasSum).summable
  rw [Summable.tsum_add ((h0r.mul_left 3).add (h1r.mul_left 4)) h2r,
    Summable.tsum_add (h0r.mul_left 3) (h1r.mul_left 4), tsum_mul_left, tsum_mul_left,
    ← Complex.re_tsum h0, ← Complex.re_tsum h1, ← Complex.re_tsum h2] at hh
  exact hh

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_ZeroDensity_ImprimitiveEulerBound
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The finite Euler-factor cost of changing a character's level -/

namespace Ostmann

open Complex Filter
open scoped BigOperators Topology

theorem euler_tail_norm_le_half {q : ℕ} (χ : DirichletCharacter ℂ q)
    {p : ℕ} (hp : p.Prime) (s : ℂ) (hs : 1 ≤ s.re) :
    ‖χ p * (p : ℂ) ^ (-s)‖ ≤ 1 / 2 := by
  have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast hp.one_lt.le
  have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
  calc
    _ ≤ ‖(p : ℂ) ^ (-s)‖ := by rw [norm_mul]; exact mul_le_of_le_one_left (norm_nonneg _) (χ.norm_le_one _)
    _ = (p : ℝ) ^ (-s.re) := by rw [Complex.norm_natCast_cpow_of_pos hp.pos]; simp
    _ ≤ (p : ℝ) ^ (-1 : ℝ) := Real.rpow_le_rpow_of_exponent_le hp1 (by linarith)
    _ = (p : ℝ)⁻¹ := Real.rpow_neg_one _
    _ ≤ 1 / 2 := by simpa using inv_anti₀ (by norm_num : (0 : ℝ) < 2) hp2

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_ZeroDensity_NonquadraticZeroBound
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The full-height zero-sum bound when the squared character is nonprincipal -/

namespace Ostmann

open Complex

theorem log_double_abs_height_le (t : ℝ) :
    Real.log (|2 * t| + 2) ≤ 2 * Real.log (|t| + 2) := by
  have ht : 0 ≤ |t| := abs_nonneg t
  have hl : Real.log 2 ≤ Real.log (|t| + 2) :=
    Real.log_le_log (by norm_num) (by linarith)
  calc
    Real.log (|2 * t| + 2) ≤ Real.log (2 * (|t| + 2)) := by
      apply Real.log_le_log (by positivity)
      rw [abs_mul]
      norm_num
      linarith
    _ = Real.log 2 + Real.log (|t| + 2) := Real.log_mul (by norm_num) (by positivity)
    _ ≤ 2 * Real.log (|t| + 2) := by linarith

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_ZeroDensity_RegularizedZeta
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Removing the zeta pole and bounding the resulting entire function -/

namespace Ostmann

open Complex Filter Metric Set
open scoped Topology

noncomputable def regularizedZeta : ℂ → ℂ :=
  Function.update (fun s : ℂ => (s - 1) * riemannZeta s) 1 1

@[simp] theorem regularizedZeta_one : regularizedZeta 1 = 1 := by simp [regularizedZeta]

theorem regularizedZeta_eq (s : ℂ) (hs : s ≠ 1) :
    regularizedZeta s = (s - 1) * riemannZeta s := by
  simp [regularizedZeta, hs]

theorem regularizedZeta_analytic (s : ℂ) : AnalyticAt ℂ regularizedZeta s := by
  have hoff (z : ℂ) (hz : z ≠ 1) : AnalyticAt ℂ regularizedZeta z := by
    have he : regularizedZeta =ᶠ[𝓝 z] (fun w => (w - 1) * riemannZeta w) := by
      filter_upwards [isOpen_ne.mem_nhds hz] with w hw
      exact regularizedZeta_eq w hw
    exact ((analyticAt_id.sub analyticAt_const).mul (analyticOn_riemannZeta z hz)).congr he.symm
  by_cases hs : s = 1
  · subst s
    apply Complex.analyticAt_of_differentiable_on_punctured_nhds_of_continuousAt
    · filter_upwards [self_mem_nhdsWithin] with z hz
      exact (hoff z hz).differentiableAt
    · exact continuousAt_update_same.mpr riemannZeta_residue_one
  · exact hoff s hs

theorem regularizedZeta_ne_zero_right (s : ℂ) (hs : 1 ≤ s.re) : regularizedZeta s ≠ 0 := by
  by_cases he : s = 1
  · simp [he]
  · rw [regularizedZeta_eq s he]
    exact mul_ne_zero (sub_ne_zero.mpr he) (riemannZeta_ne_zero_of_one_le_re hs)

theorem regularizedZeta_logDeriv (s : ℂ) (hs : 1 < s.re) :
    logDeriv regularizedZeta s = (s - 1)⁻¹ + logDeriv riemannZeta s := by
  have hne : s ≠ 1 := by intro he; simp [he] at hs
  have he : regularizedZeta =ᶠ[𝓝 s] (fun z : ℂ => (z - 1) * riemannZeta z) := by
    filter_upwards [isOpen_ne.mem_nhds hne] with z hz
    exact regularizedZeta_eq z hz
  rw [(logDeriv_congr_nhds he).self_of_nhds,
    logDeriv_mul (f := fun z : ℂ => z - 1) (g := riemannZeta) s
      (sub_ne_zero.mpr hne) (riemannZeta_ne_zero_of_one_le_re hs.le)
      (differentiableAt_id.sub_const _) (differentiableAt_riemannZeta hne)]
  simp [logDeriv_apply]

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_ZeroDensity_ZeroFreeNumerics
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Concrete kernel comparisons for the low-height zero-free region -/

namespace Ostmann

theorem real_zero_shifted_mass (δ a : ℝ) (hδ : 0 < δ) (ha : δ ≤ a)
    (ha' : a ≤ (21 / 20) * δ) : 18 / 5 < δ * (4 / a) := by
  have ha0 : 0 < a := hδ.trans_le ha
  rw [← mul_div_assoc, lt_div_iff₀ ha0]
  nlinarith

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Characters_CharacterResolventBound
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Uniform control of differences of zero resolvents -/

namespace Ostmann

open Complex

theorem ratio_triangle_bound (U V D A δ : ℝ)
    (hU : 0 < U) (hV : 0 < V) (_hD : 0 ≤ D) (hA : 0 ≤ A)
    (hδ : 0 < δ) (hsep : δ ≤ U) (hDA : D ≤ A) (htri : V ≤ U + D) :
    D / (U * V) ≤ A * (1 + A / δ) / V ^ 2 := by
  have hratio : V / U ≤ 1 + A / δ := by
    calc
      V / U ≤ (U + D) / U := div_le_div_of_nonneg_right htri hU.le
      _ = 1 + D / U := by rw [add_div, div_self hU.ne']
      _ ≤ 1 + A / U := by gcongr
      _ ≤ 1 + A / δ := by gcongr
  calc
    D / (U * V) = (D * (V / U)) / V ^ 2 := by field_simp
    _ ≤ (A * (1 + A / δ)) / V ^ 2 := by
      apply div_le_div_of_nonneg_right _ (sq_nonneg _)
      exact mul_le_mul hDA hratio (div_nonneg hV.le hU.le) hA

/-- An inverse difference is controlled by the positive real zero kernel at
its reference point. This makes the bound summable over actual zeros. -/
theorem zero_resolvent_difference_bound (s w ρ : ℂ) (A δ : ℝ)
    (hA : 0 ≤ A) (hδ : 0 < δ) (hsep : δ ≤ ‖s - ρ‖)
    (hshift : ‖w - s‖ ≤ A) (hre : 1 ≤ (w - ρ).re) :
    ‖(s - ρ)⁻¹ - (w - ρ)⁻¹‖ ≤
      A * (1 + A / δ) * ((w - ρ)⁻¹).re := by
  have hsp : 0 < ‖s - ρ‖ := hδ.trans_le hsep
  have hwp : 0 < ‖w - ρ‖ := by
    have hh := (Complex.re_le_norm (w - ρ))
    linarith
  have hsn : s - ρ ≠ 0 := norm_pos_iff.mp hsp
  have hwn : w - ρ ≠ 0 := norm_pos_iff.mp hwp
  have htri : ‖w - ρ‖ ≤ ‖s - ρ‖ + ‖w - s‖ := by
    have hh := norm_add_le (s - ρ) (w - s)
    rw [show s - ρ + (w - s) = w - ρ by ring] at hh
    exact hh
  have hkernel : 1 / ‖w - ρ‖ ^ 2 ≤ ((w - ρ)⁻¹).re := by
    rw [Complex.inv_re, Complex.normSq_eq_norm_sq]
    exact div_le_div_of_nonneg_right hre (sq_nonneg _)
  calc
    _ = ‖w - s‖ / (‖s - ρ‖ * ‖w - ρ‖) := by
      rw [inv_sub_inv hsn hwn, norm_div, norm_mul]
      congr 2
      ring
    _ ≤ A * (1 + A / δ) / ‖w - ρ‖ ^ 2 :=
      ratio_triangle_bound _ _ _ _ _ hsp hwp (norm_nonneg _) hA hδ hsep hshift htri
    _ = (A * (1 + A / δ)) * (1 / ‖w - ρ‖ ^ 2) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hkernel (by positivity)

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Characters_CharacterTargetCode
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Fixing the actual target shells and their ordered cell lists -/
namespace Ostmann
open scoped Classical BigOperators

noncomputable def CharacterTargetWord.code {P : Finset ℕ} {F : ℕ → ℂ}
    {c δ U : ℝ} {k : ℕ} {T : ℝ} (w : CharacterTargetWord P F c δ U k T) : List ℕ :=
  w.shell :: w.indices

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Characters_PrimitiveCharacterReduction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Reduction to the actual primitive character, without multiplicities

At a fixed ambient modulus, passage to primitive characters is injective.
Thus grouping the sparse expansion introduces no coefficient multiplicity.
-/
namespace Ostmann
open scoped Classical

theorem primitiveCharacter_nontrivial {N : ℕ} [NeZero N]
    (χ : DirichletCharacter ℂ N) (hχ : χ ≠ 1) : χ.primitiveCharacter ≠ 1 := by
  intro hh
  have he := χ.changeLevel_primitiveCharacter
  rw [hh, map_one] at he
  exact hχ he.symm

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Characters_TensorUnitMean
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The independent unit-residue mean of the sparse polynomial -/

namespace Ostmann
open scoped Classical BigOperators

abbrev NonzeroResidue (p : ℕ) [NeZero p] := ↥(Finset.univ.erase (0 : ZMod p))

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_ConstituentHProductLower
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # A lower endpoint for the actual supported H product -/
namespace Ostmann
open scoped Classical BigOperators

/-- The endpoint is required only where the full inherited coefficient is live. -/
def ConstituentHProductLower {I : Type*} [Fintype I]
    (role : I → CopyScheduleRole) (size : I → ℕ) (n : ℕ)
    (childBound pivotBound : ℕ → ℕ) (ranges : (j : ℕ) → List (ScheduleAtomRange role j))
    (leaf : ScheduleAtomState role → ℤ → ℂ) (Z : ℝ) : Prop :=
  ∀ (M : ℕ) (t : FrequencyTree ℤ n)
    (l : CopyScheduleH (fun i : Σ a, Fin (size a) => role i.1) n → ℕ)
    (u : CopyScheduleY (fun i : Σ a, Fin (size a) => role i.1) n → ℕ),
    fullAtomTransferWeight role childBound pivotBound ranges leaf n
      (scheduledInsertedAtoms role n M
        (fun h => ∏ k, l (constituentH role size n h k))
        (fun y => ∏ k, u (constituentY role size n y k))) t ≠ 0 →
      Z ≤ ∏ h, (l h : ℝ)

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_FixedPivotCoordinates
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Every reconstructed prime check excludes the fixed pivot coordinate -/

namespace Ostmann

open scoped Classical

def ExpandedUnfixedCoordinates {I V : Type*} (role : I → CopyScheduleRole)
    (depth n : ℕ)
    (current : CopyScheduleAtoms role n → List (ExpandedScheduledVariable (Option V) depth)) : Prop :=
  ∀ i, (∀ k, copyScheduleRole role n i.val ≠ .pivot k) →
    ∀ v ∈ current i, ∃ a : V, v = .inl (some a)

def WordPrimeDecoration.Coordinates {V : Type*} (p : V → Prop) :
    {n : ℕ} → WordPrimeDecoration V n → Prop
  | 0, .leaf => True
  | _ + 1, .node xs l r => (∀ v ∈ xs, p v) ∧ l.Coordinates p ∧ r.Coordinates p

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Supply_CollisionPrimeCellBudget
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Good cells from the proved collision-stability budget -/

namespace Ostmann
open scoped Classical BigOperators

noncomputable def collisionExceptionalPrimes (P : Finset ℕ)
    (S T : ℕ → Finset ℕ) (μ ν : ℕ → ℕ → ℝ) : Finset ℕ :=
  P.filter (fun p => 1 / 4 < (p : ℝ) * collisionDefect p (S p) (T p) (μ p) (ν p))

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Preliminaries_SummandTails
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Actual finite tails of the two summands -/

namespace Ostmann

open scoped Classical

noncomputable def summandPrefix (A : Set ℕ) (N : ℕ) : Finset ℕ :=
  (Finset.range (N + 1)).filter fun n => n ∈ A

noncomputable def summandTail (A : Set ℕ) (lo hi : ℕ) : Finset ℕ :=
  (Finset.Ioc lo hi).filter fun n => n ∈ A

noncomputable def positiveSummandTail (A : Set ℕ) (lo hi : ℕ) : Finset ℤ :=
  (summandTail A lo hi).image fun n : ℕ => (n : ℤ)

noncomputable def negativeSummandTail (B : Set ℕ) (lo hi : ℕ) : Finset ℤ :=
  (summandTail B lo hi).image fun n : ℕ => -(n : ℤ)

@[simp] theorem mem_summandPrefix (A : Set ℕ) (N n : ℕ) :
    n ∈ summandPrefix A N ↔ n ∈ A ∧ n ≤ N := by
  simp only [summandPrefix, Finset.mem_filter, Finset.mem_range, Nat.lt_succ_iff]
  tauto

@[simp] theorem mem_summandTail (A : Set ℕ) (lo hi n : ℕ) :
    n ∈ summandTail A lo hi ↔ n ∈ A ∧ lo < n ∧ n ≤ hi := by
  simp only [summandTail, Finset.mem_filter, Finset.mem_Ioc]
  tauto

@[simp] theorem positiveSummandTail_card (A : Set ℕ) (lo hi : ℕ) :
    (positiveSummandTail A lo hi).card = (summandTail A lo hi).card := by
  apply Finset.card_image_of_injective
  intro a b hab
  change (a : ℤ) = (b : ℤ) at hab
  exact_mod_cast hab

@[simp] theorem negativeSummandTail_card (B : Set ℕ) (lo hi : ℕ) :
    (negativeSummandTail B lo hi).card = (summandTail B lo hi).card := by
  apply Finset.card_image_of_injective
  intro a b hab
  exact_mod_cast neg_injective hab

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Preliminaries_PublishedSummandBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Published counting bounds for the summands

Christian Elsholtz, *Additive decomposability of multiplicatively defined sets*,
Functiones et Approximatio Commentarii Mathematici 35 (2006), 61–77,
Theorem 1.9, printed p. 63. DOI: 10.7169/facm/1229442617.
https://www.math.tugraz.at/~elsholtz/WWW/papers/papers22wirsing04.pdf

We record just its square-root counting consequence for a hypothetical
asymptotic decomposition, in the nonnegative-integer convention of the target
manuscript (Section 2, Lemma `size`). This is an explicit conditional input;
no instance is postulated globally. The tail truncation is proved separately.
-/

namespace Ostmann

/-- The only counting-function estimates needed from Elsholtz's Theorem 1.9. -/
def PublishedSummandSizeBound : Prop :=
  ∀ A B : Set ℕ, A.Infinite → B.Infinite → EventuallyPrimeSumset A B →
    ∃ a C : ℝ, 0 < a ∧ 0 < C ∧ ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → 2 ≤ N →
      a * Real.sqrt (N : ℝ) / Real.log (N : ℝ) ^ 3 ≤ (summandPrefix A N).card ∧
      (summandPrefix A N).card ≤ C * Real.sqrt (N : ℝ) * Real.log (N : ℝ) ^ 2 ∧
      a * Real.sqrt (N : ℝ) / Real.log (N : ℝ) ^ 3 ≤ (summandPrefix B N).card ∧
      (summandPrefix B N).card ≤ C * Real.sqrt (N : ℝ) * Real.log (N : ℝ) ^ 2

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Preliminaries_LargeSummandTails
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Large actual tails from the published summand counting bounds -/

namespace Ostmann

open Filter
open scoped Classical

noncomputable def summandTailCutoff (L : ℝ) : ℕ := ⌊Real.exp (9 * L / 10)⌋₊

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Preliminaries_TailCollisionCutoff
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The square-root prime cutoff and its logarithmic collision budget -/

namespace Ostmann

open Filter
open scoped BigOperators Classical

noncomputable def tailCollisionCutoff (L : ℝ) : ℕ :=
  ⌊Real.exp (L / 2) / L ^ 5⌋₊

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_ZeroDensity_TailDensityMask
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Actual residue masks for the positive endpoint tail -/

namespace Ostmann

open scoped Classical

noncomputable def tailDensityMask (A : Set ℕ) (N p : ℕ) : Finset (ZMod p) :=
  (tailSupport A N p).image fun r : ℕ => (r : ZMod p)

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Preliminaries_StableSummandTails
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Stable biased primes for the actual large summand tails -/

namespace Ostmann

open Filter
open scoped BigOperators Classical

noncomputable def tailDefectBudget (a C L : ℝ) : ℝ :=
  20 * Real.log L + 4 * C + 4 * Real.log 2 + 2 * Real.log 4 / a

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_TailGoodPrimeCells
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Nearby balanced cells for the actual summand tails -/

namespace Ostmann
open Filter
open scoped Classical BigOperators

noncomputable def tailCellExceptionalPrimes (A B : Set ℕ) (N lo hi Q : ℕ) : Finset ℕ :=
  collisionExceptionalPrimes (Nat.primesLE Q) (tailSupport A N)
    (fun p => Finset.range p \ tailSupport A N p)
    (fun p => residueMass (summandTail A lo hi)
      (fun _ => 1 / ((summandTail A lo hi).card : ℝ)) p)
    (fun p => fiberMass (summandTail B lo hi)
      (fun _ => 1 / ((summandTail B lo hi).card : ℝ)) (negativeResidue p))

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_SelectedCompensationCells
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Actual top and compensation cell lists -/

namespace Ostmann
open Filter
open scoped Classical BigOperators

noncomputable def selectedTailCellPrimes (A B : Set ℕ) (N : ℕ) (X : ℝ)
    (hi : ℕ) (D : Finset ℕ) (j : ℕ) : Finset ℕ :=
  (primeLogCellSet 1 0 j ((j : ℝ) + 1) \
    tailCellExceptionalPrimes A B N (summandTailCutoff X) hi (tailCollisionCutoff X)) \ D

def SelectedSmallTailCell (A B : Set ℕ) (N : ℕ) (a C L X : ℝ)
    (hi : ℕ) (D : Finset ℕ) (target : ℝ) (j : ℕ) : Prop :=
  target ≤ j ∧ (j : ℝ) ≤ target + 64 * tailDefectBudget a C X + 1 ∧
    (j : ℝ) + 1 ≤ Real.exp ((11 / 1000 : ℝ) * L) ∧
    let Q := selectedTailCellPrimes A B N X hi D j
    Real.exp (-(2 * L)) ≤ (∑ p ∈ Q, (p : ℝ)⁻¹) ∧
    0 < (∑ p ∈ Q, (p : ℝ)⁻¹) ∧
    (∑ p ∈ Q, (p : ℝ)⁻¹)⁻¹ ≤ Real.exp (2 * L) ∧
    (∀ p ∈ Q, p.Prime ∧ Real.exp (j : ℝ) < p ∧
      (p : ℝ) ≤ Real.exp ((j : ℝ) + 1) ∧
      (p : ℝ) / 3 ≤ (tailSupport A N p).card ∧
      ((tailSupport A N p).card : ℝ) ≤ 2 * p / 3)

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Supply_BilinearCube
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Coefficients of a finite product of bilinear factors -/

namespace Ostmann
open scoped Classical BigOperators

abbrev BilinearCube (n : ℕ) := Fin n → Bool × Bool

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Preliminaries_PublishedAdditiveSieve
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The classical additive large-sieve input

H. L. Montgomery and R. C. Vaughan, *The large sieve*, Mathematika 20 (1973),
119–134, Theorem 1. The separated-frequency inequality gives the constant
`M - 1 + Q^2` on reduced fractions of denominator at most `Q`; below it is
weakened to `M + Q^2`. This is exactly the finite-interval specialization (2.1)
stated in the assigned manuscript, and applies to arbitrary complex coefficients.
-/

namespace Ostmann
open scoped Classical BigOperators

noncomputable def sieveAdditivePhase (q h : ℕ) (n : ℤ) : ℂ :=
  Complex.exp (2 * (Real.pi : ℂ) * Complex.I * ((n : ℂ) * h / q))

def reducedNumerators (q : ℕ) : Finset ℕ :=
  (Finset.range q).filter (fun h => h.Coprime q)

noncomputable def additiveSieveSum {M : ℕ} (c : Fin M → ℂ) (J : ℤ) (q h : ℕ) : ℂ :=
  ∑ n, c n * sieveAdditivePhase q h (J + (n.val : ℤ))

/-- The additive large sieve for separated frequencies and arbitrary complex
coefficients. -/
def PublishedAdditiveLargeSieve : Prop :=
  ∀ M Q : ℕ, 1 ≤ M → 1 ≤ Q → ∀ J : ℤ, ∀ c : Fin M → ℂ,
    (∑ q ∈ Finset.Icc 1 Q, ∑ h ∈ reducedNumerators q, ‖additiveSieveSum c J q h‖ ^ 2) ≤
      ((M : ℝ) + (Q : ℝ) ^ 2) * ∑ n, ‖c n‖ ^ 2

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_InitialMovingSlots
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The original two half-lists in the moving-slot order -/
namespace Ostmann
open scoped Classical BigOperators

abbrev InitialRetainedSlot (b r : ℕ) := Unit ⊕ (Fin b ⊕ Fin r)

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_InitialMovingBulkTree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The literal two half-bulk weights through every moving branch -/
namespace Ostmann
open scoped Classical BigOperators

def MovingLeafLengthEq {P : Type*} : (n : ℕ) → TreeLeafTuple (List P) n → ℕ → Prop
  | 0, x, r => (show List P from x).length = r
  | n + 1, x, r => MovingLeafLengthEq n x.1 r ∧ MovingLeafLengthEq n x.2 r

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_SeparatedMatchingCount
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Counting bad bulk matchings while retaining every nonbulk slot -/

namespace Ostmann
open scoped Classical

def sumSide {A B : Type*} : A ⊕ B → Bool := Sum.elim (fun _ => true) (fun _ => false)

noncomputable def sumSideLeftEquiv (A B : Type*) :
    A ≃ {x : A ⊕ B // sumSide x = true} :=
  Equiv.ofBijective (fun a => ⟨Sum.inl a, rfl⟩) (by
    constructor
    · intro a b h; exact Sum.inl.inj (congrArg Subtype.val h)
    · rintro ⟨a | b, h⟩
      · exact ⟨a, rfl⟩
      · cases h)

noncomputable def separatedMatchingLeft {A B : Type*}
    (e : PartitionMatching (@sumSide A B) (@sumSide A B)) : Equiv.Perm A :=
  ((sumSideLeftEquiv A B).trans (e.restrict true)).trans (sumSideLeftEquiv A B).symm

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_ScheduledBulkMatchingCount
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Bad overlap matchings on the actual bulk and nonbulk prime coordinates -/

namespace Ostmann
open scoped Classical

noncomputable def scheduledPathEnumeration (n : ℕ) : Fin (2 ^ n) ≃ (Fin n → Bool) :=
  Fintype.equivOfCardEq (by simp)

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_ScheduledTreeBulkCoordinates
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The counted bulk slots are the actual recursive arithmetic leaves -/

namespace Ostmann
open scoped Classical

noncomputable def treeLeafPathEquiv (n : ℕ) : TreeLeafIndex n ≃ (Fin n → Bool) :=
  Equiv.ofBijective (treeLeafCopyPath n) ((Fintype.bijective_iff_injective_and_card _).mpr
    ⟨treeLeafCopyPath_injective n, by simp [card_treeLeafIndex]⟩)

noncomputable def treeLeafEnumeration (n : ℕ) : TreeLeafIndex n ≃ Fin (2 ^ n) :=
  (treeLeafPathEquiv n).trans (scheduledPathEnumeration n).symm

@[simp] theorem scheduledPathEnumeration_treeLeafEnumeration (n : ℕ) (t : TreeLeafIndex n) :
    scheduledPathEnumeration n (treeLeafEnumeration n t) = treeLeafCopyPath n t := by
  simp only [treeLeafEnumeration, Equiv.trans_apply, Equiv.apply_symm_apply]
  rfl

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_SelectedBulkCoordinates
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Bulk coordinates inside a larger word

The selected bulk slots are copied with the whole word. The top slot is
retained in that word but belongs to the complementary matching block.
-/
namespace Ostmann
open scoped Classical

noncomputable def selectedBulkH {I : Type*} (role : I → CopyScheduleRole)
    (n m : ℕ) (bulk : Fin m ↪ I) (hbulk : ∀ i, role (bulk i) = .word) :
    (Fin (2 ^ n) × Fin m) ↪ CopyScheduleH role n where
  toFun x := scheduledWordH role n (scheduledPathEnumeration n x.1) ⟨bulk x.2, hbulk x.2⟩
  inj' := by
    intro x y h
    have he := @copySchedulePath_injective I n
      (scheduledPathEnumeration n x.1, bulk x.2) (scheduledPathEnumeration n y.1, bulk y.2)
      (congrArg Subtype.val h)
    exact Prod.ext ((scheduledPathEnumeration n).injective (congrArg Prod.fst he))
      (bulk.injective (congrArg Prod.snd he))

abbrev SelectedNonbulkH {I : Type*} (role : I → CopyScheduleRole)
    (n m : ℕ) (bulk : Fin m ↪ I) (hbulk : ∀ i, role (bulk i) = .word) :=
  {h : CopyScheduleH role n // h ∉ Set.range (selectedBulkH role n m bulk hbulk)}

noncomputable def selectedBulkCoordinates {I : Type*} (role : I → CopyScheduleRole)
    (n m : ℕ) (bulk : Fin m ↪ I) (hbulk : ∀ i, role (bulk i) = .word) :
    (Fin (2 ^ n) × Fin m) ≃
      {h : CopyScheduleH role n // h ∈ Set.range (selectedBulkH role n m bulk hbulk)} :=
  Equiv.ofInjective _ (selectedBulkH role n m bulk hbulk).injective

noncomputable def selectedSplitHCoordinates {I : Type*} (role : I → CopyScheduleRole)
    (n m : ℕ) (bulk : Fin m ↪ I) (hbulk : ∀ i, role (bulk i) = .word) :
    (Fin (2 ^ n) × Fin m) ⊕ SelectedNonbulkH role n m bulk hbulk ≃ CopyScheduleH role n :=
  ((selectedBulkCoordinates role n m bulk hbulk).sumCongr (Equiv.refl _)).trans
    (Equiv.Set.sumCompl (Set.range (selectedBulkH role n m bulk hbulk)))

noncomputable def selectedBulkLabel {I : Type*} (role : I → CopyScheduleRole)
    (n m : ℕ) (bulk : Fin m ↪ I) (hbulk : ∀ i, role (bulk i) = .word)
    (h : CopyScheduleH role n) : Bool :=
  decide (h ∈ Set.range (selectedBulkH role n m bulk hbulk))

theorem selectedBulkLabel_coordinates {I : Type*} (role : I → CopyScheduleRole)
    (n m : ℕ) (bulk : Fin m ↪ I) (hbulk : ∀ i, role (bulk i) = .word)
    (x : (Fin (2 ^ n) × Fin m) ⊕ SelectedNonbulkH role n m bulk hbulk) :
    selectedBulkLabel role n m bulk hbulk (selectedSplitHCoordinates role n m bulk hbulk x) =
      sumSide x := by
  cases x with
  | inl b =>
    change decide ((selectedBulkCoordinates role n m bulk hbulk b).val ∈
      Set.range (selectedBulkH role n m bulk hbulk)) = true
    exact decide_eq_true (selectedBulkCoordinates role n m bulk hbulk b).property
  | inr h =>
    change decide (h.val ∈ Set.range (selectedBulkH role n m bulk hbulk)) = false
    exact decide_eq_false h.property

noncomputable def selectedSeparatedMatching {I : Type*} (role : I → CopyScheduleRole)
    (n m : ℕ) (bulk : Fin m ↪ I) (hbulk : ∀ i, role (bulk i) = .word)
    (e : PartitionMatching (selectedBulkLabel role n m bulk hbulk)
      (selectedBulkLabel role n m bulk hbulk)) :
    PartitionMatching (@sumSide (Fin (2 ^ n) × Fin m) (SelectedNonbulkH role n m bulk hbulk))
      (@sumSide (Fin (2 ^ n) × Fin m) (SelectedNonbulkH role n m bulk hbulk)) :=
  ⟨((selectedSplitHCoordinates role n m bulk hbulk).trans e.val).trans
      (selectedSplitHCoordinates role n m bulk hbulk).symm, by
    intro x
    have h := e.property (selectedSplitHCoordinates role n m bulk hbulk x)
    change sumSide ((selectedSplitHCoordinates role n m bulk hbulk).symm
      (e.val (selectedSplitHCoordinates role n m bulk hbulk x))) = sumSide x
    rw [← selectedBulkLabel_coordinates role n m bulk hbulk
      ((selectedSplitHCoordinates role n m bulk hbulk).symm
        (e.val (selectedSplitHCoordinates role n m bulk hbulk x))),
      Equiv.apply_symm_apply, h, selectedBulkLabel_coordinates]⟩

@[simp] theorem selectedSplitHCoordinates_inl {I : Type*} (role : I → CopyScheduleRole)
    (n m : ℕ) (bulk : Fin m ↪ I) (hbulk : ∀ i, role (bulk i) = .word)
    (x : Fin (2 ^ n) × Fin m) :
    selectedSplitHCoordinates role n m bulk hbulk (.inl x) = selectedBulkH role n m bulk hbulk x := rfl

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_ScheduledAnchorMatchingCount
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Code-preserving matchings of the actual scheduled bulk slots -/

namespace Ostmann
open scoped Classical

noncomputable def scheduledBulkAnchorCode (n : ℕ) {m : ℕ}
    (x : Fin (2 ^ n) × Fin m) : Fin n → ℤ × ℤ :=
  finiteAnchorCode (fun _ => 1) (scheduledPathEnumeration n x.1)

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_SelectedAnchorMatchingCount
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Code-preserving matchings of the selected bulk, excluding the top slot -/
namespace Ostmann
open scoped Classical

def PreservesSelectedAnchorCode {I : Type*} (role : I → CopyScheduleRole)
    (n m : ℕ) (bulk : Fin m ↪ I) (hbulk : ∀ i, role (bulk i) = .word)
    (e : PartitionMatching (selectedBulkLabel role n m bulk hbulk) (selectedBulkLabel role n m bulk hbulk)) : Prop :=
  ∀ x, scheduledBulkAnchorCode n
    (separatedMatchingLeft (selectedSeparatedMatching role n m bulk hbulk e) x) =
      scheduledBulkAnchorCode n x

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_ScheduledNodeUnits
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Original full-weight unit guards at every reconstructed preorder node -/

namespace Ostmann
open scoped Classical

def ScheduleNodeUnits {I : Type*} (role : I → CopyScheduleRole)
    (node : ReconstructedTransferNode (ScheduleAtomState role)) : Prop :=
  ∀ v : CopyScheduleAtoms role node.state.1, (node.state.2 v).Coprime node.root.natAbs

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_WordRootRange
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Adding one exact product cutoff at the root of a history -/

namespace Ostmann

open scoped BigOperators Classical

noncomputable def WordRangeDecoration.prependRoot {σ : Type*} (r : WordRange σ) :
    {n : ℕ} → WordRangeDecoration σ n → WordRangeDecoration σ n
  | 0, .leaf ranges => .leaf (r :: ranges)
  | _ + 1, .node ranges L R => .node (r :: ranges) L R

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_TypicalCharacterShells
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # A fixed finite test family covers precisely the needed character shells -/
namespace Ostmann
open Filter
open scoped Classical BigOperators

abbrev CharacterShellTestIndex (k : ℕ) := Fin (5 * k + 1) ⊕ ((Fin k × Bool) ⊕ Bool)

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_QuadraticCenter_FixedQuadraticFamily
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # A fixed finite family containing all discretized arithmetic arrays -/

namespace Ostmann

open Filter
open scoped BigOperators SchwartzMap

abbrev QuadraticFamilyIndex := ℕ × (ℕ × (ℕ × (ℕ × ℕ)))

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Quadratic_QuadraticSieveTranspose
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Reciprocity supplies the transpose needed for quadratic kernels -/

namespace Ostmann

open scoped BigOperators Classical

noncomputable def quadraticTransposeSum (N : ℕ) (b : ℕ → ℂ) (u : ℤ) : ℂ :=
  ∑ s ∈ oddSquarefreeRange N, b s * (jacobiSym u s : ℂ)

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_FrozenInitialSpectatorData
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Ostmann
open scoped Classical

/-- This packages consequences of the selected support, without selecting another family. -/
structure FrozenInitialSpectatorData (A : Set ℕ) (N : ℕ) {d : ℕ}
    (p : Fin (d + d) → ℕ) (L ε : ℝ) (cutoff : ℕ) (D : Finset ℕ) : Prop where
  injective : Function.Injective p
  prime : ∀ i, (p i).Prime
  ge_cutoff : ∀ i, cutoff ≤ p i
  avoids : ∀ i, p i ∉ D
  lower : ∀ i, Real.exp (Real.exp ((4 / 10000 : ℝ) * L)) ≤ p i
  upper : ∀ i, (p i : ℝ) ≤ Real.exp (Real.exp ((6 / 10000 : ℝ) * L))
  balanced_lower : ∀ i, (1 / 3 : ℝ) ≤ residueDensity (tailDensityMask A N (p i))
  balanced_upper : ∀ i, residueDensity (tailDensityMask A N (p i)) ≤ 2 / 3
  nonempty : ∀ i, (tailDensityMask A N (p i)).Nonempty
  proper : ∀ i, (tailDensityMask A N (p i)).card < p i
  character_bound : ∀ i (χ : DirichletCharacter ℂ (p i)), χ ≠ 1 → ∀ a : ZMod (p i),
    ‖((tailDensityMask A N (p i)).card : ℂ)⁻¹ *
      ∑ x ∈ tailDensityMask A N (p i), χ⁻¹ (-a - x)‖ ≤ ε / 2

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Preliminaries_CircleSeparatedPoints
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Centering a separated finite family on the circle -/

namespace Ostmann

open scoped BigOperators

def CircleSeparated {ι : Type*} (x : ι → ℝ) (δ : ℝ) : Prop :=
  ∀ s t, s ≠ t → ∀ m : ℤ, δ ≤ |x s - x t - m|

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Preliminaries_AdditiveSieveProof
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The published additive large sieve, with its precise downstream constant

The finite cosecant Hilbert inequality and duality prove the separated-frequency
estimate. Reduced fractions of denominator at most Q are 1/Q²-separated.
This proves the specialization of Montgomery--Vaughan (1973), Theorem 1,
used throughout the conditional development.
-/

namespace Ostmann

open scoped BigOperators

abbrev ReducedFractionIndex (Q : ℕ) :=
  Σ q : {q : ℕ // q ∈ Finset.Icc 1 Q}, {h : ℕ // h ∈ reducedNumerators q.val}

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Preliminaries_MertensHarmonicBands
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Mertens' second theorem on the iterated-logarithm band

F. Mertens, *Ein Beitrag zur analytischen Zahlentheorie*, J. reine angew.
Math. 78 (1874), 46–62, second theorem. We only require its weaker bounded
error consequence `sum_{p≤Q} 1/p = log log Q + O(1)`. The pinned PNT library
states this specialization as `Mertens.sum_prime_div_eq_log_log`.
-/

namespace Ostmann
open Filter
open scoped Classical BigOperators

/-- Precise published Mertens-second input, weaker than its convergent-error
form and sufficient for the favorable-prime harmonic mass. -/
def MertensHarmonicEstimate (C : ℝ) : Prop :=
  ∀ Q : ℕ, 2 ≤ Q → |(∑ p ∈ Nat.primesLE Q, (p : ℝ)⁻¹) - Real.log (Real.log Q)| ≤ C

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_ZeroDensity_SmoothPrincipalMean
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The principal term of the smooth character estimate

Published input: the conductor-one case of Montgomery–Vaughan (2007),
Corollary 11.20, equations (11.32)/(11.34), p.381, with the usual smooth
partial summation. This is the classical prime number theorem with its
zero-free-region error, specialized to our single fixed compactly supported
smooth function. It makes no assertion about a growing character family.
-/
namespace Ostmann
open Filter MeasureTheory
open scoped Classical BigOperators

noncomputable def smoothPrincipalMain (X : ℝ) : ℂ :=
  ((X * ∫ t : ℝ, primeMeanTest t : ℝ) : ℂ)

noncomputable def smoothPrincipalError (X : ℝ) : ℝ :=
  ‖smoothMangoldtMean 1 1 X - smoothPrincipalMain X‖

/-- The fixed-test, conductor-one consequence of the classical PNT. -/
def PublishedSmoothPrincipalPNT : Prop :=
  ∃ C c : ℝ, 0 < C ∧ 0 < c ∧ ∀ X : ℝ, 2 ≤ X →
    smoothPrincipalError X ≤ C * X * Real.exp (-c * Real.sqrt (Real.log X))

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Preliminaries_MertensThetaKernel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Integrating the conductor-one theta error

The exponential square-root error has a bounded logarithmic integral. This
concrete antiderivative suffices for the first Mertens estimate.
-/

namespace Ostmann

open MeasureTheory
open scoped Interval

noncomputable def thetaErrorPrimitive (c t : ℝ) : ℝ :=
  -(2 / c ^ 2) * (c * Real.sqrt (Real.log t) + 1) *
    Real.exp (-c * Real.sqrt (Real.log t))

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Preliminaries_OccupiedResidueCollision
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The larger-sieve bound for the full residue support of a summand

The support is taken from the entire infinite summand, even when the probability
measure is supported on one finite prefix. This is the upper bound for H in
manuscript Lemma 2.4 and Elsholtz's summand-size argument.
-/

namespace Ostmann

open scoped BigOperators Classical

noncomputable def occupiedResidues (A : Set ℕ) (p : ℕ) : Finset ℕ :=
  (Finset.range p).filter fun r => ∃ a ∈ A, a % p = r

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Quadratic_QuadraticSieveFinite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Finite quadratic-sieve bounds and their reciprocity symmetry

These are the elementary initial steps of Heath-Brown (1995), sections 2--3.
The bound predicate refers to the actual Jacobi matrix and finite coefficients.
-/

namespace Ostmann

open Matrix
open scoped BigOperators Classical

/-- A bound for the actual finite odd-squarefree Jacobi matrix. -/
def QuadraticSieveBound (M N : ℕ) (K : ℝ) : Prop :=
  ∀ b : ℕ → ℂ, (∑ m ∈ oddSquarefreeRange M, ‖quadraticSieveSum N b m‖ ^ 2) ≤
    K * quadraticSieveEnergy N b

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Quadratic_QuadraticSquarefreePart
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Unique square-times-squarefree decomposition for the Poisson comparison -/

namespace Ostmann

theorem exists_quadratic_factor (m : ℕ) :
    ∃ a b : ℕ, a ^ 2 * b = m ∧ Squarefree b := by
  by_cases hm : m = 0
  · exact ⟨0, 1, by simp [hm], squarefree_one⟩
  · obtain ⟨b, a, _, _, he, hs⟩ := Nat.sq_mul_squarefree_of_pos (Nat.pos_of_ne_zero hm)
    exact ⟨a, b, he, hs⟩

noncomputable def quadraticSquarefreePart (m : ℕ) : ℕ :=
  Classical.choose (Classical.choose_spec (exists_quadratic_factor m))

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Quadratic_QuadraticSieveWeight
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The fixed nonnegative smoothing weight in Heath-Brown's argument -/

namespace Ostmann

open scoped SchwartzMap BigOperators

noncomputable def quadraticSieveBump : ContDiffBump (3 / 2 : ℝ) :=
  ⟨1 / 2, 1, by norm_num, by norm_num⟩

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Quadratic_QuadraticSmoothedEnergy
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The literal smoothed odd moment and its large-kernel part -/

namespace Ostmann

open scoped Classical BigOperators

noncomputable def quadraticOddRange (R : ℕ) : Finset ℕ :=
  (Finset.Icc 1 R).filter Odd

noncomputable def quadraticRoughKernelRange (R K : ℕ) : Finset ℕ :=
  (quadraticOddRange R).filter (fun m => K < quadraticSquarefreePart m)

noncomputable def quadraticRoughEnergy (M N K : ℕ) (b : ℕ → ℂ) : ℝ :=
  ∑ m ∈ quadraticRoughKernelRange (3 * M) K,
    quadraticSieveBump ((m : ℝ) / M) * ‖quadraticTransposeSum N b m‖ ^ 2

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Quadratic_QuadraticRoughBound
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Restriction and divisor descent for the actual rough moment -/

namespace Ostmann

open scoped Classical BigOperators ComplexConjugate

def QuadraticRoughBound (M N K : ℕ) (T : ℝ) : Prop :=
  ∀ v : ℕ → ℂ, quadraticRoughEnergy M N K v ≤ T * quadraticSieveEnergy N v

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Quadratic_QuadraticRowNorm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The least constant for an actual finite set of quadratic rows -/

namespace Ostmann

open scoped Classical BigOperators

noncomputable def quadraticRowEnergy (S : Finset ℕ) (N : ℕ) (v : ℕ → ℂ) : ℝ :=
  ∑ m ∈ S, ‖quadraticTransposeSum N v m‖ ^ 2

def QuadraticRowBound (S : Finset ℕ) (N : ℕ) (T : ℝ) : Prop :=
  ∀ v : ℕ → ℂ, quadraticRowEnergy S N v ≤ T * quadraticSieveEnergy N v

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Quadratic_QuadraticSieveGrowth
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The precise exponent induction for the actual quadratic-sieve matrices -/

namespace Ostmann

/-- Heath-Brown's induction statement, with an arbitrary small-power loss. -/
def QuadraticSieveGrowth (ξ : ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 < C ∧ ∀ M N : ℕ, 1 ≤ M → 1 ≤ N →
    QuadraticSieveBound M N
      (C * ((M : ℝ) * N) ^ ε * ((M : ℝ) + (N : ℝ) ^ ξ))

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Quadratic_QuadraticSignedInfiniteSum
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Exact infinite signed-frequency coordinates for the first transform -/

namespace Ostmann

open scoped Classical BigOperators

abbrev QuadraticOddKernel := {b : ℕ+ // Odd (b : ℕ) ∧ Squarefree (b : ℕ)}
abbrev QuadraticFrequencyIndex := ({1, -1, 2, -2} : Finset ℤ) × (QuadraticOddKernel × ℕ+)

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_ZeroDensity_RealCharacterPairEuler
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The positive Euler combination for two real characters -/

namespace Ostmann

open Complex
open scoped BigOperators

theorem self_inverse_character_im_zero {N : ℕ} [NeZero N]
    (a : DirichletCharacter ℂ N) (ha : a⁻¹ = a) (n : ℕ) : (a n).im = 0 := by
  have hh : star a = a := (MulChar.star_eq_inv a).trans ha
  have hv := congrArg (fun χ : DirichletCharacter ℂ N => (χ n).im) hh
  simp at hv
  linarith

theorem real_character_pair_term_nonneg {N : ℕ} (a b : DirichletCharacter ℂ N)
    (ha : ∀ n : ℕ, (a n).im = 0) (hb : ∀ n : ℕ, (b n).im = 0) (σ : ℝ) (n : ℕ) :
    0 ≤ (LSeries.term (fun n => (ArithmeticFunction.vonMangoldt n : ℂ)) (σ : ℂ) n).re +
      (LSeries.term (fun n => a n * (ArithmeticFunction.vonMangoldt n : ℂ)) (σ : ℂ) n).re +
      (LSeries.term (fun n => b n * (ArithmeticFunction.vonMangoldt n : ℂ)) (σ : ℂ) n).re +
      (LSeries.term (fun n => (a * b) n * (ArithmeticFunction.vonMangoldt n : ℂ)) (σ : ℂ) n).re := by
  by_cases hn : n = 0
  · subst n; simp
  have h1 : 0 ≤ 1 + (a n).re := by linarith [(Complex.abs_re_le_norm (a n)).trans (a.norm_le_one n), neg_abs_le (a n).re]
  have h2 : 0 ≤ 1 + (b n).re := by linarith [(Complex.abs_re_le_norm (b n)).trans (b.norm_le_one n), neg_abs_le (b n).re]
  have hw : 0 ≤ ArithmeticFunction.vonMangoldt n * (n : ℝ) ^ (-σ) :=
    mul_nonneg ArithmeticFunction.vonMangoldt_nonneg (Real.rpow_nonneg (Nat.cast_nonneg n) _)
  have he (f : ℕ → ℂ) : LSeries.term f (σ : ℂ) n = f n * ((n : ℝ) ^ (-σ) : ℝ) := by
    simpa using LSeries_term_vertical f n hn σ 0
  rw [he, he, he, he]
  simp only [MulChar.mul_apply, Complex.mul_re, Complex.mul_im, Complex.ofReal_re,
    Complex.ofReal_im, ha, hb, mul_zero, zero_mul, sub_zero, add_zero]
  convert mul_nonneg hw (mul_nonneg h1 h2) using 1
  all_goals try with_reducible_and_instances rfl
  ring

theorem real_character_pair_sum_nonneg {N : ℕ} (a b : DirichletCharacter ℂ N)
    (ha : ∀ n : ℕ, (a n).im = 0) (hb : ∀ n : ℕ, (b n).im = 0) (σ : ℝ) (hσ : 1 < σ) :
    0 ≤ (LSeries (fun n => (ArithmeticFunction.vonMangoldt n : ℂ)) (σ : ℂ)).re +
      (LSeries (fun n => a n * (ArithmeticFunction.vonMangoldt n : ℂ)) (σ : ℂ)).re +
      (LSeries (fun n => b n * (ArithmeticFunction.vonMangoldt n : ℂ)) (σ : ℂ)).re +
      (LSeries (fun n => (a * b) n * (ArithmeticFunction.vonMangoldt n : ℂ)) (σ : ℂ)).re := by
  have h0 := ArithmeticFunction.LSeriesSummable_vonMangoldt (s := (σ : ℂ)) hσ
  have h1 := a.LSeriesSummable_twist_vonMangoldt (s := (σ : ℂ)) hσ
  have h2 := b.LSeriesSummable_twist_vonMangoldt (s := (σ : ℂ)) hσ
  have h3 := (a * b).LSeriesSummable_twist_vonMangoldt (s := (σ : ℂ)) hσ
  change LSeriesSummable (fun n => a n * (ArithmeticFunction.vonMangoldt n : ℂ)) (σ : ℂ) at h1
  change LSeriesSummable (fun n => b n * (ArithmeticFunction.vonMangoldt n : ℂ)) (σ : ℂ) at h2
  change LSeriesSummable (fun n => (a * b) n * (ArithmeticFunction.vonMangoldt n : ℂ)) (σ : ℂ) at h3
  have hh := tsum_nonneg (L := SummationFilter.unconditional ℕ) (real_character_pair_term_nonneg a b ha hb σ)
  have h0r := (Complex.hasSum_re h0.hasSum).summable
  have h1r := (Complex.hasSum_re h1.hasSum).summable
  have h2r := (Complex.hasSum_re h2.hasSum).summable
  have h3r := (Complex.hasSum_re h3.hasSum).summable
  rw [Summable.tsum_add ((h0r.add h1r).add h2r) h3r,
    Summable.tsum_add (h0r.add h1r) h2r, Summable.tsum_add h0r h1r,
    ← Complex.re_tsum h0, ← Complex.re_tsum h1, ← Complex.re_tsum h2,
    ← Complex.re_tsum h3] at hh
  exact hh

theorem real_character_pair_logDeriv_le {N : ℕ} [NeZero N] (a b : DirichletCharacter ℂ N)
    (ha : a⁻¹ = a) (hb : b⁻¹ = b) (σ : ℝ) (hσ : 1 < σ) :
    (logDeriv (DirichletCharacter.LFunction a) (σ : ℂ)).re +
      (logDeriv (DirichletCharacter.LFunction b) (σ : ℂ)).re ≤
        (LSeries (fun n => (ArithmeticFunction.vonMangoldt n : ℂ)) (σ : ℂ)).re -
          (logDeriv (DirichletCharacter.LFunction (a * b)) (σ : ℂ)).re := by
  have hh := real_character_pair_sum_nonneg a b (self_inverse_character_im_zero a ha)
    (self_inverse_character_im_zero b hb) σ hσ
  rw [dirichlet_mangoldt_LSeries_eq a _ hσ, dirichlet_mangoldt_LSeries_eq b _ hσ,
    dirichlet_mangoldt_LSeries_eq (a * b) _ hσ, Complex.neg_re, Complex.neg_re, Complex.neg_re] at hh
  linarith

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_ZeroDensity_RealZeroPairExclusion
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The real Page exclusion from one-pole bounds -/

namespace Ostmann

open Complex

theorem near_real_zero_inverse_mass (δ β : ℝ) (hδ : 0 < δ) (hβ : β < 1)
    (hnear : 1 - δ / 20 ≤ β) : 9 / 10 < δ * (1 / (1 + δ - β)) := by
  have hh := real_zero_shifted_mass δ (1 + δ - β) hδ (by linarith) (by linarith)
  simp only [div_eq_mul_inv] at hh ⊢
  nlinarith

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_ZeroDensity_RieszMellinKernel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # A single integral of the Chebyshev sum

The continuous weight max(1-u,0) has Mellin transform 1/(s(s+1)). This is the
one-sided smoothing needed to recover the sharp progression count.
-/

namespace Ostmann

open Complex MeasureTheory Set

noncomputable def rieszPrimeTest (u : ℝ) : ℂ := (max (1 - u) 0 : ℝ)

noncomputable def rieszMellinKernel (s : ℂ) : ℂ := 1 / (s * (s + 1))

theorem rieszPrimeTest_continuous : Continuous rieszPrimeTest := by
  unfold rieszPrimeTest
  fun_prop

theorem rieszPrimeTest_hasMellin (s : ℂ) (hs : 0 < s.re) :
    HasMellin rieszPrimeTest s (rieszMellinKernel s) := by
  let f : ℝ → ℂ := indicator (Ioc 0 1) (fun _ => 1)
  let g : ℝ → ℂ := indicator (Ioc 0 1) (fun u => (u : ℂ) ^ (1 : ℂ))
  have hf : HasMellin f s (1 / s) := hasMellin_one_Ioc hs
  have hg : HasMellin g s (1 / (s + 1)) :=
    hasMellin_cpow_Ioc 1 (by simpa using (show 0 < s.re + 1 by linarith))
  have hsub := hasMellin_sub hf.1 hg.1
  rw [hf.2, hg.2] at hsub
  have heq : EqOn (fun u => f u - g u) rieszPrimeTest (Ioi 0) := by
    intro u hu
    change 0 < u at hu
    by_cases hle : u ≤ 1
    · have hm : u ∈ Ioc (0 : ℝ) 1 := ⟨hu, hle⟩
      simp [f, g, hm, rieszPrimeTest,
        max_eq_left (sub_nonneg.mpr hle), Complex.ofReal_sub]
    · have hn : u ∉ Ioc (0 : ℝ) 1 := fun h => hle h.2
      simp [f, g, indicator_of_notMem hn, rieszPrimeTest,
        max_eq_right (by linarith : 1 - u ≤ 0)]
  refine ⟨hsub.1.congr_fun (fun u hu =>
    congrArg (fun a : ℂ => (u : ℂ) ^ (s - 1) • a) (heq hu)) measurableSet_Ioi, ?_⟩
  have hi : mellin rieszPrimeTest s = mellin (fun u => f u - g u) s := by
    apply setIntegral_congr_fun measurableSet_Ioi
    intro u hu
    exact congrArg (fun a : ℂ => (u : ℂ) ^ (s - 1) • a) (heq hu).symm
  rw [hi, hsub.2]
  have hsn : s ≠ 0 := by intro h; simp [h] at hs
  have hs1 : s + 1 ≠ 0 := by
    intro h
    have hh := congrArg Complex.re h
    simp only [Complex.add_re, Complex.one_re, Complex.zero_re] at hh
    linarith
  dsimp [rieszMellinKernel]
  field_simp
  ring

theorem rieszMellinKernel_line_bound (σ t : ℝ) (hσ : 1 ≤ σ) :
    ‖rieszMellinKernel ((σ : ℂ) + (t : ℂ) * I)‖ ≤
      4 * (1 + |t|) ^ (-(2 : ℝ)) := by
  let s : ℂ := (σ : ℂ) + (t : ℂ) * I
  have hsre : s.re = σ := by simp [s]
  have hsim : s.im = t := by simp [s]
  have h1 : 1 ≤ ‖s‖ := by linarith [Complex.re_le_norm s]
  have h2 : 1 ≤ ‖s + 1‖ := by
    have hh := Complex.re_le_norm (s + 1)
    simp only [Complex.add_re, Complex.one_re, hsre] at hh
    linarith
  have ht1 : |t| ≤ ‖s‖ := by simpa only [hsim] using Complex.abs_im_le_norm s
  have ht2 : |t| ≤ ‖s + 1‖ := by simpa [hsim] using Complex.abs_im_le_norm (s + 1)
  have ha : 0 < 1 + |t| := by positivity
  have hp : (1 + |t|) ^ 2 ≤ 4 * (‖s‖ * ‖s + 1‖) := by
    have hh := mul_le_mul (show 1 + |t| ≤ 2 * ‖s‖ by linarith)
      (show 1 + |t| ≤ 2 * ‖s + 1‖ by linarith) (by positivity) (by positivity)
    nlinarith
  change ‖1 / (s * (s + 1))‖ ≤ _
  rw [norm_div, norm_one, norm_mul, Real.rpow_neg (by positivity : 0 ≤ 1 + |t|),
    Real.rpow_two]
  rw [← div_eq_mul_inv]
  apply (div_le_div_iff₀ (by positivity : 0 < ‖s‖ * ‖s + 1‖) (sq_pos_of_pos ha)).mpr
  nlinarith

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_ZeroDensity_RieszMellinInversion
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Mellin inversion for the one-sided Riesz weight -/

namespace Ostmann

open Complex MeasureTheory

theorem rieszMellinKernel_verticalIntegrable (σ : ℝ) (hσ : 1 ≤ σ) :
    Complex.VerticalIntegrable rieszMellinKernel σ := by
  have hmajor : Integrable (fun t : ℝ => 4 * (1 + ‖t‖) ^ (-(2 : ℝ))) :=
    (integrable_one_add_norm (E := ℝ) (by norm_num : (Module.finrank ℝ ℝ : ℝ) < 2)).const_mul 4
  have hc : Continuous (fun t : ℝ => rieszMellinKernel ((σ : ℂ) + (t : ℂ) * I)) := by
    unfold rieszMellinKernel
    apply continuous_const.div
    · fun_prop
    · intro t
      apply mul_ne_zero
      · intro h
        have hh := congrArg Complex.re h
        simp at hh
        linarith
      · intro h
        have hh := congrArg Complex.re h
        simp at hh
        linarith
  apply hmajor.mono' hc.aestronglyMeasurable
  filter_upwards with t
  simpa only [Real.norm_eq_abs] using rieszMellinKernel_line_bound σ t hσ

theorem rieszPrimeTest_mellin_inversion (σ x : ℝ) (hσ : 1 ≤ σ) (hx : 0 < x) :
    mellinInv σ rieszMellinKernel x = rieszPrimeTest x := by
  have hσp : 0 < σ := by linarith
  have hF : Complex.VerticalIntegrable (mellin rieszPrimeTest) σ := by
    have hfun : (fun t : ℝ => mellin rieszPrimeTest ((σ : ℂ) + (t : ℂ) * I)) =
        (fun t : ℝ => rieszMellinKernel ((σ : ℂ) + (t : ℂ) * I)) := by
      funext t
      exact (rieszPrimeTest_hasMellin _ (by simpa using hσp)).2
    change Integrable (fun t : ℝ => mellin rieszPrimeTest ((σ : ℂ) + (t : ℂ) * I))
    rw [hfun]
    exact rieszMellinKernel_verticalIntegrable σ hσ
  have hi := mellinInv_mellin_eq σ rieszPrimeTest hx
    (rieszPrimeTest_hasMellin (σ : ℂ) hσp).1 hF rieszPrimeTest_continuous.continuousAt
  rw [← hi]
  unfold mellinInv
  congr 1
  apply integral_congr_ae
  filter_upwards with t
  rw [(rieszPrimeTest_hasMellin ((σ : ℂ) + (t : ℂ) * I) (by simpa using hσp)).2]

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_ZeroDensity_RieszVerticalWeight
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The absolutely convergent Riesz contour weight -/

namespace Ostmann

open Complex MeasureTheory

noncomputable def rieszMellinLine (σ t : ℝ) : ℂ := (σ : ℂ) + (t : ℂ) * I

@[simp] theorem rieszMellinLine_re (σ t : ℝ) : (rieszMellinLine σ t).re = σ := by
  simp [rieszMellinLine]

@[fun_prop] theorem rieszMellinLine_continuous (σ : ℝ) : Continuous (rieszMellinLine σ) := by
  unfold rieszMellinLine
  fun_prop

theorem rieszMellinKernel_analyticAt_pos (s : ℂ) (hs : 0 < s.re) :
    AnalyticAt ℂ rieszMellinKernel s := by
  apply analyticAt_const.div (analyticAt_id.mul (analyticAt_id.add analyticAt_const))
  apply mul_ne_zero
  · intro h
    change s = 0 at h
    simp [h] at hs
  · intro h
    change s + 1 = 0 at h
    have hh := congrArg Complex.re h
    simp only [Complex.add_re, Complex.one_re, Complex.zero_re] at hh
    linarith

noncomputable def rieszVerticalWeight (X σ t : ℝ) : ℂ :=
  (X : ℂ) ^ rieszMellinLine σ t * rieszMellinKernel (rieszMellinLine σ t)

theorem rieszVerticalWeight_continuous (X σ : ℝ) (hX : 0 < X) (hσ : 0 < σ) :
    Continuous (rieszVerticalWeight X σ) := by
  apply Continuous.mul
  · exact (rieszMellinLine_continuous σ).const_cpow (.inl (by exact_mod_cast hX.ne'))
  · apply continuous_iff_continuousAt.mpr
    intro t
    exact ((rieszMellinKernel_analyticAt_pos _ (by simpa using hσ)).continuousAt).comp
      (rieszMellinLine_continuous σ).continuousAt

theorem rieszVerticalWeight_norm (X σ t : ℝ) (hX : 0 < X) :
    ‖rieszVerticalWeight X σ t‖ = X ^ σ * ‖rieszMellinKernel (rieszMellinLine σ t)‖ := by
  rw [rieszVerticalWeight, norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hX,
    rieszMellinLine_re]

theorem rieszVerticalWeight_integrable (X σ : ℝ) (hX : 0 < X) (hσ : 1 ≤ σ) :
    Integrable (rieszVerticalWeight X σ) := by
  have hk : Integrable (fun t => rieszMellinKernel (rieszMellinLine σ t)) :=
    rieszMellinKernel_verticalIntegrable σ hσ
  apply (hk.norm.const_mul (X ^ σ)).mono'
    (rieszVerticalWeight_continuous X σ hX (by linarith)).aestronglyMeasurable
  exact Filter.Eventually.of_forall (fun t => (rieszVerticalWeight_norm X σ t hX).le)

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_ZeroDensity_RieszContourRectangle
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The finite Riesz contour displacement when the rectangle is zero-free -/

namespace Ostmann

open Complex Set
open scoped Interval

noncomputable def rieszContourWeight (X : ℝ) (s : ℂ) : ℂ :=
  (X : ℂ) ^ s * rieszMellinKernel s

theorem rieszContourWeight_analyticAt (X : ℝ) (hX : 0 < X) (s : ℂ) (hs : 0 < s.re) :
    AnalyticAt ℂ (rieszContourWeight X) s := by
  exact ((differentiable_id.const_cpow (.inl (by exact_mod_cast hX.ne'))).analyticAt s).mul
    (rieszMellinKernel_analyticAt_pos s hs)

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_ZeroDensity_RieszPoleRectangle
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The exact contribution of a real pole to the Riesz rectangle -/

namespace Ostmann

open Complex Filter Set
open scoped Topology Interval

theorem rieszWeight_dslope_analytic (X : ℝ) (hX : 0 < X) (β : ℂ) (hβ : 0 < β.re)
    (s : ℂ) (hs : 0 < s.re) : AnalyticAt ℂ (dslope (rieszContourWeight X) β) s := by
  by_cases he : s = β
  · subst s
    obtain ⟨p, hp⟩ := rieszContourWeight_analyticAt X hX β hβ
    exact ⟨p.fslope, hp.has_fpower_series_dslope_fslope⟩
  · have hh : dslope (rieszContourWeight X) β =ᶠ[𝓝 s]
        (fun z => (z - β)⁻¹ * (rieszContourWeight X z - rieszContourWeight X β)) := by
      filter_upwards [isOpen_ne.mem_nhds he] with z hz
      rw [dslope_of_ne _ hz]
      rfl
    exact (((analyticAt_id.sub analyticAt_const).inv (sub_ne_zero.mpr he)).mul
      ((rieszContourWeight_analyticAt X hX s hs).sub analyticAt_const)).congr hh.symm

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_ZeroDensity_OneZeroBoundaryCut
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Choosing one of two left boundaries away from a unique real zero -/

namespace Ostmann

open Complex

theorem exists_two_point_cut (δ β : ℝ) (hδ : 0 < δ) :
    ∃ a : ℝ, 1 - 2 * δ ≤ a ∧ a ≤ 1 - δ ∧ δ / 2 ≤ |a - β| := by
  by_cases hβ : β ≤ 1 - 3 * δ / 2
  · refine ⟨1 - δ, by linarith, le_rfl, ?_⟩
    exact (show δ / 2 ≤ 1 - δ - β by linarith).trans (le_abs_self _)
  · refine ⟨1 - 2 * δ, le_rfl, by linarith, ?_⟩
    exact (show δ / 2 ≤ -(1 - 2 * δ - β) by linarith).trans (neg_le_abs _)

theorem one_zero_boundary_cut (Z : ℕ → ℂ) (δ T : ℝ)
    (hδ : 0 < δ) (hδ4 : δ ≤ 1 / 4) (hT : 2 ≤ T)
    (hreal : ∀ i, |(Z i).im| ≤ T + 2 → 1 - 4 * δ ≤ (Z i).re → (Z i).im = 0)
    (hunique : ∀ i j, |(Z i).im| ≤ T + 2 → |(Z j).im| ≤ T + 2 →
      1 - 4 * δ ≤ (Z i).re → 1 - 4 * δ ≤ (Z j).re → i = j) :
    ∃ a : ℝ, 1 - 2 * δ ≤ a ∧ a ≤ 1 - δ ∧
      ∀ s : ℂ, ((s.re = a ∧ |s.im| ≤ T) ∨ (a ≤ s.re ∧ s.re ≤ 2 ∧ |s.im| = T)) →
      ∀ i : ℕ, δ / 2 ≤ ‖s - Z i‖ := by
  classical
  have hcut : ∃ a : ℝ, 1 - 2 * δ ≤ a ∧ a ≤ 1 - δ ∧
      ∀ i, |(Z i).im| ≤ T + 2 → 1 - 4 * δ ≤ (Z i).re → δ / 2 ≤ |a - (Z i).re| := by
    by_cases hex : ∃ i, |(Z i).im| ≤ T + 2 ∧ 1 - 4 * δ ≤ (Z i).re
    · obtain ⟨i, hi, hni⟩ := hex
      obtain ⟨a, ha, ha', hagap⟩ := exists_two_point_cut δ (Z i).re hδ
      refine ⟨a, ha, ha', ?_⟩
      intro j hj hnj
      have he := hunique j i hj hi hnj hni
      simpa only [he] using hagap
    · refine ⟨1 - δ, by linarith, le_rfl, ?_⟩
      intro i hi hni
      exact (hex ⟨i, hi, hni⟩).elim
  obtain ⟨a, ha, ha', hasep⟩ := hcut
  refine ⟨a, ha, ha', ?_⟩
  intro s hs i
  have hsa : a ≤ s.re := by rcases hs with h | h <;> linarith [h.1]
  have hst : |s.im| ≤ T := by
    rcases hs with h | h
    · exact h.2
    · exact h.2.2.le
  by_cases hi : |(Z i).im| ≤ T + 2
  · by_cases hni : 1 - 4 * δ ≤ (Z i).re
    · rcases hs with hs | hs
      · have hg := hasep i hi hni
        have hn := Complex.abs_re_le_norm (s - Z i)
        simp only [Complex.sub_re, hs.1] at hn
        exact hg.trans hn
      · have him := hreal i hi hni
        have hn := Complex.abs_im_le_norm (s - Z i)
        rw [Complex.sub_im, him, sub_zero, hs.2.2] at hn
        linarith
    · have hn := Complex.re_le_norm (s - Z i)
      simp only [Complex.sub_re] at hn
      linarith
  · have htall := abs_add_le (s.im - (Z i).im) (-s.im)
    rw [show s.im - (Z i).im + -s.im = -(Z i).im by ring, abs_neg, abs_neg] at htall
    have hn := Complex.abs_im_le_norm (s - Z i)
    simp only [Complex.sub_im] at hn
    linarith [lt_of_not_ge hi]

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_ZeroDensity_RieszTailEstimate
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Explicit right-contour tails for the Riesz integral -/

namespace Ostmann

open Complex MeasureTheory Set

theorem rieszMellinKernel_im_bound (s : ℂ) (ht : 0 < |s.im|) :
    ‖rieszMellinKernel s‖ ≤ 1 / |s.im| ^ 2 := by
  have hs : 0 < ‖s‖ := ht.trans_le (Complex.abs_im_le_norm s)
  have hs1 : |s.im| ≤ ‖s + 1‖ := by simpa using Complex.abs_im_le_norm (s + 1)
  have hprod : |s.im| ^ 2 ≤ ‖s‖ * ‖s + 1‖ := by
    simpa only [pow_two] using mul_le_mul (Complex.abs_im_le_norm s) hs1 ht.le (norm_nonneg s)
  rw [rieszMellinKernel, norm_div, norm_one, norm_mul]
  exact div_le_div_of_nonneg_left zero_le_one (sq_pos_of_pos ht) hprod

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_ZeroDensity_RieszTruncation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The exact finite-rectangle truncation of the Riesz integral -/

namespace Ostmann

open Complex MeasureTheory Set
open scoped Interval

theorem integral_three_parts (f : ℝ → ℂ) (hf : Integrable f) (T : ℝ) :
    (∫ t : ℝ, f t) = (∫ t in Iic (-T), f t) + (∫ t in -T..T, f t) +
      (∫ t in Ioi T, f t) := by
  have hfull := intervalIntegral.integral_Iic_add_Ioi (b := T) hf.integrableOn hf.integrableOn
  have hseg := intervalIntegral.integral_Iic_sub_Iic (a := -T) (b := T)
    hf.integrableOn hf.integrableOn
  linear_combination hseg - hfull

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_ZeroDensity_RieszLeftEstimate
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The bounded left vertical segment of the Riesz contour -/

namespace Ostmann

open Complex MeasureTheory Set

noncomputable def rieszLineMajorant (t : ℝ) : ℝ := 9 * (1 + |t|) ^ (-(2 : ℝ))

theorem rieszLineMajorant_nonneg (t : ℝ) : 0 ≤ rieszLineMajorant t := by
  unfold rieszLineMajorant
  positivity

theorem rieszLineMajorant_integrable : Integrable rieszLineMajorant := by
  have hp : Integrable (fun t : ℝ => (1 + ‖t‖) ^ (-(2 : ℝ))) :=
    integrable_one_add_norm (μ := volume) (E := ℝ)
      (by norm_num : (Module.finrank ℝ ℝ : ℝ) < 2)
  change Integrable (fun t : ℝ => 9 * (1 + |t|) ^ (-(2 : ℝ)))
  simpa only [Real.norm_eq_abs] using hp.const_mul 9

theorem rieszMellinKernel_half_strip (s : ℂ) (hs : 1 / 2 ≤ s.re) :
    ‖rieszMellinKernel s‖ ≤ rieszLineMajorant s.im := by
  have h1 : 1 ≤ 2 * ‖s‖ := by linarith [Complex.re_le_norm s]
  have h2 : 1 ≤ 2 * ‖s + 1‖ := by
    have hh := Complex.re_le_norm (s + 1)
    simp only [Complex.add_re, Complex.one_re] at hh
    linarith
  have hsp : 0 < ‖s‖ := by linarith
  have hsp1 : 0 < ‖s + 1‖ := by linarith
  have ht1 := Complex.abs_im_le_norm s
  have ht2 : |s.im| ≤ ‖s + 1‖ := by simpa using Complex.abs_im_le_norm (s + 1)
  have ha : 0 < 1 + |s.im| := by positivity
  have hp : (1 + |s.im|) ^ 2 ≤ 9 * (‖s‖ * ‖s + 1‖) := by
    have hh := mul_le_mul (show 1 + |s.im| ≤ 3 * ‖s‖ by linarith)
      (show 1 + |s.im| ≤ 3 * ‖s + 1‖ by linarith) (by positivity) (by positivity)
    nlinarith
  rw [rieszMellinKernel, norm_div, norm_one, norm_mul, rieszLineMajorant,
    Real.rpow_neg (by positivity : 0 ≤ 1 + |s.im|), Real.rpow_two, ← div_eq_mul_inv]
  apply (div_le_div_iff₀ (by positivity : 0 < ‖s‖ * ‖s + 1‖) (sq_pos_of_pos ha)).mpr
  nlinarith

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_ZeroDensity_WeightedRieszRectangle
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Weighted Riesz edge bounds and a retained residue -/

namespace Ostmann

open Complex MeasureTheory Set
open scoped Interval

theorem weightedRiesz_left_segment_bound : ∃ K : ℝ, 0 < K ∧
    ∀ (f : ℂ → ℂ) (X a T M : ℝ), 0 < X → 1 / 2 ≤ a → 0 ≤ M →
      (∀ t ∈ Icc (-T) T, ‖f (rieszMellinLine a t)‖ ≤ M) →
      ‖∫ t in Icc (-T) T, f (rieszMellinLine a t) * rieszVerticalWeight X a t‖ ≤ K * M * X ^ a := by
  let J := ∫ t : ℝ, rieszLineMajorant t
  have hJ : 0 ≤ J := integral_nonneg rieszLineMajorant_nonneg
  refine ⟨J + 1, by linarith, ?_⟩
  intro f X a T M hX ha hM hb
  have hg : Integrable (fun t : ℝ => (M * X ^ a) * rieszLineMajorant t) :=
    rieszLineMajorant_integrable.const_mul _
  have hnorm : ‖∫ t in Icc (-T) T, f (rieszMellinLine a t) * rieszVerticalWeight X a t‖ ≤
      ∫ t in Icc (-T) T, (M * X ^ a) * rieszLineMajorant t := by
    apply norm_integral_le_of_norm_le hg.integrableOn
    filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
    have hk := rieszMellinKernel_half_strip (rieszMellinLine a t) (by simpa using ha)
    simp only [rieszMellinLine, Complex.add_im, Complex.ofReal_im, Complex.mul_im,
      Complex.ofReal_re, Complex.I_im, mul_one, Complex.I_re, mul_zero, add_zero,
      zero_add] at hk
    rw [norm_mul, rieszVerticalWeight_norm X a t hX]
    have hh := mul_le_mul (hb t ht) (mul_le_mul_of_nonneg_left hk (Real.rpow_nonneg hX.le a))
      (by positivity) hM
    exact hh.trans_eq (by ring)
  have hfull := setIntegral_le_integral hg
    (Filter.Eventually.of_forall (fun t => mul_nonneg (by positivity) (rieszLineMajorant_nonneg t)))
    (s := Icc (-T) T)
  simp only [integral_const_mul] at hnorm hfull
  apply (hnorm.trans hfull).trans
  dsimp only [J] at hJ ⊢
  nlinarith [mul_nonneg hM (Real.rpow_nonneg hX.le a)]

theorem weightedRiesz_horizontal_segment_bound (f : ℂ → ℂ)
    (X a b t M : ℝ) (hX : 1 ≤ X) (hab : a ≤ b) (ht : 0 < |t|) (hM : 0 ≤ M)
    (hb : ∀ σ ∈ Icc a b, ‖f ((σ : ℂ) + (t : ℂ) * I)‖ ≤ M) :
    ‖∫ σ in a..b, f ((σ : ℂ) + (t : ℂ) * I) *
        rieszContourWeight X ((σ : ℂ) + (t : ℂ) * I)‖ ≤
      (M * X ^ b / t ^ 2) * (b - a) := by
  have hXp : 0 < X := by linarith
  have hpoint : ∀ σ ∈ Ι a b,
      ‖f ((σ : ℂ) + (t : ℂ) * I) *
        rieszContourWeight X ((σ : ℂ) + (t : ℂ) * I)‖ ≤ M * X ^ b / t ^ 2 := by
    intro σ hσ
    have hσ' : σ ∈ Icc a b := by
      have hh := uIoc_subset_uIcc hσ
      rwa [uIcc_of_le hab] at hh
    have hk := rieszMellinKernel_im_bound ((σ : ℂ) + (t : ℂ) * I) (by simpa using ht)
    simp only [Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.ofReal_re,
      Complex.I_im, mul_one, Complex.I_re, mul_zero, add_zero, zero_add, sq_abs] at hk
    have hx : X ^ σ ≤ X ^ b := Real.rpow_le_rpow_of_exponent_le hX hσ'.2
    rw [norm_mul, rieszContourWeight, norm_mul,
      Complex.norm_cpow_eq_rpow_re_of_pos hXp]
    simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re,
      mul_zero, Complex.ofReal_im, Complex.I_im, zero_mul, sub_zero, add_zero]
    have hh := mul_le_mul (hb σ hσ') (mul_le_mul hx hk (norm_nonneg _) (Real.rpow_nonneg hXp.le _))
      (by positivity) hM
    exact hh.trans_eq (by ring)
  have hi := intervalIntegral.norm_integral_le_of_norm_le_const hpoint
  simpa only [abs_of_nonneg (sub_nonneg.mpr hab)] using hi

theorem rectangle_vertical_shift_residue_norm_bound (f : ℂ → ℂ) (a b c d : ℝ)
    (z : ℂ) (hzero : rectangleBoundaryIntegral f a b c d = I * z) :
    ‖(∫ y in c..d, f ((b : ℂ) + (y : ℂ) * I)) - z‖ ≤
      ‖∫ y in c..d, f ((a : ℂ) + (y : ℂ) * I)‖ +
      ‖∫ x in a..b, f ((x : ℂ) + (d : ℂ) * I)‖ +
      ‖∫ x in a..b, f ((x : ℂ) + (c : ℂ) * I)‖ := by
  let R := ∫ y in c..d, f ((b : ℂ) + (y : ℂ) * I)
  let L := ∫ y in c..d, f ((a : ℂ) + (y : ℂ) * I)
  let U := ∫ x in a..b, f ((x : ℂ) + (d : ℂ) * I)
  let D := ∫ x in a..b, f ((x : ℂ) + (c : ℂ) * I)
  have he : I * (R - z) = I * L + U - D := by
    dsimp [rectangleBoundaryIntegral] at hzero
    dsimp [R, L, U, D]
    linear_combination hzero
  change ‖R - z‖ ≤ ‖L‖ + ‖U‖ + ‖D‖
  calc
    ‖R - z‖ = ‖I * (R - z)‖ := by rw [norm_mul, Complex.norm_I, one_mul]
    _ = ‖I * L + U - D‖ := by rw [he]
    _ ≤ ‖I * L + U‖ + ‖D‖ := norm_sub_le _ _
    _ ≤ (‖I * L‖ + ‖U‖) + ‖D‖ := add_le_add (norm_add_le _ _) le_rfl
    _ = _ := by rw [norm_mul, Complex.norm_I, one_mul]

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_ZeroDensity_WeightedRieszTails
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Both tails for a bounded vertical coefficient in the Riesz integral -/

namespace Ostmann

open Complex MeasureTheory Set

theorem inverse_square_tail_bound (f : ℝ → ℂ) (K T : ℝ) (hT : 0 < T)
    (hb : ∀ t > T, ‖f t‖ ≤ K / t ^ 2) :
    ‖∫ t in Ioi T, f t‖ ≤ K / T := by
  have hg : IntegrableOn (fun t : ℝ => K * t ^ (-(2 : ℝ))) (Ioi T) :=
    (integrableOn_Ioi_rpow_of_lt (by norm_num) hT).const_mul K
  have hn : ‖∫ t in Ioi T, f t‖ ≤ ∫ t in Ioi T, K * t ^ (-(2 : ℝ)) := by
    apply norm_integral_le_of_norm_le hg
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    have hp : 0 < t := hT.trans ht
    simpa only [Real.rpow_neg hp.le, Real.rpow_two, div_eq_mul_inv] using hb t ht
  apply hn.trans_eq
  rw [integral_const_mul, integral_Ioi_rpow_of_lt (by norm_num : -(2 : ℝ) < -1) hT]
  norm_num only [neg_add_cancel_left, neg_div_neg_eq, div_one, Real.rpow_neg_one]
  ring

theorem weightedRiesz_integrable (f : ℂ → ℂ) (X b M : ℝ) (hX : 0 < X) (hb : 1 ≤ b)
    (hc : Continuous (fun t : ℝ => f (rieszMellinLine b t)))
    (hbound : ∀ t : ℝ, ‖f (rieszMellinLine b t)‖ ≤ M) :
    Integrable (fun t => f (rieszMellinLine b t) * rieszVerticalWeight X b t) := by
  apply ((rieszVerticalWeight_integrable X b hX hb).norm.const_mul M).mono'
    ((hc.mul (rieszVerticalWeight_continuous X b hX (by linarith))).aestronglyMeasurable)
  filter_upwards with t
  rw [Pi.mul_apply, norm_mul]
  exact mul_le_mul_of_nonneg_right (hbound t) (norm_nonneg _)

theorem weightedRiesz_both_tails (f : ℂ → ℂ) (X b M T : ℝ)
    (hX : 0 < X) (hM : 0 ≤ M) (hT : 0 < T)
    (hbound : ∀ t : ℝ, ‖f (rieszMellinLine b t)‖ ≤ M) :
    ‖∫ t in Ioi T, f (rieszMellinLine b t) * rieszVerticalWeight X b t‖ ≤ M * X ^ b / T ∧
    ‖∫ t in Iic (-T), f (rieszMellinLine b t) * rieszVerticalWeight X b t‖ ≤ M * X ^ b / T := by
  have hpoint (t : ℝ) (ht : t ≠ 0) :
      ‖f (rieszMellinLine b t) * rieszVerticalWeight X b t‖ ≤ M * X ^ b / t ^ 2 := by
    have hi : 0 < |(rieszMellinLine b t).im| := by
      simpa [rieszMellinLine] using abs_pos.mpr ht
    have hk := rieszMellinKernel_im_bound (rieszMellinLine b t) hi
    simp only [rieszMellinLine, Complex.add_im, Complex.ofReal_im, Complex.mul_im,
      Complex.ofReal_re, Complex.I_im, mul_one, Complex.I_re, mul_zero, add_zero,
      zero_add, sq_abs] at hk
    rw [norm_mul, rieszVerticalWeight_norm X b t hX]
    calc
      _ ≤ M * (X ^ b * (1 / t ^ 2)) :=
        mul_le_mul (hbound t) (mul_le_mul_of_nonneg_left hk (Real.rpow_nonneg hX.le _))
          (by positivity) hM
      _ = _ := by ring
  constructor
  · exact inverse_square_tail_bound _ (M * X ^ b) T hT
      (fun t ht => hpoint t (ne_of_gt (hT.trans ht)))
  · rw [← integral_comp_neg_Ioi T (fun t => f (rieszMellinLine b t) * rieszVerticalWeight X b t)]
    apply inverse_square_tail_bound _ (M * X ^ b) T hT
    intro t ht
    simpa only [neg_sq] using hpoint (-t) (neg_ne_zero.mpr (ne_of_gt (hT.trans ht)))

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_ZeroDensity_RieszResidueTruncation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Truncation while retaining the precise main residue -/

namespace Ostmann

open Complex MeasureTheory Set
open scoped Interval

theorem riesz_residue_truncation (f : ℂ → ℂ) (X b M T : ℝ) (v : ℂ)
    (hX : 0 < X) (hb : 1 ≤ b) (hM : 0 ≤ M) (hT : 0 < T)
    (hc : Continuous (fun t : ℝ => f (rieszMellinLine b t)))
    (hbound : ∀ t : ℝ, ‖f (rieszMellinLine b t)‖ ≤ M) :
    ‖((1 / (2 * Real.pi) : ℝ) : ℂ) *
        (∫ t : ℝ, f (rieszMellinLine b t) * rieszVerticalWeight X b t) - v‖ ≤
      ‖(∫ t in -T..T, f (rieszMellinLine b t) * rieszVerticalWeight X b t) -
          ((2 * Real.pi : ℝ) : ℂ) * v‖ + 2 * M * X ^ b / T := by
  let F : ℝ → ℂ := fun t => f (rieszMellinLine b t) * rieszVerticalWeight X b t
  let τ : ℂ := ((1 / (2 * Real.pi) : ℝ) : ℂ)
  let q : ℂ := ((2 * Real.pi : ℝ) : ℂ)
  have hnorm : ‖τ‖ ≤ 1 := by
    dsimp [τ]
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by positivity)]
    exact (div_le_one (by positivity : 0 < 2 * Real.pi)).mpr (by linarith [Real.pi_gt_three])
  have hτ : τ * q = 1 := by
    dsimp [τ, q]
    norm_cast
    exact div_mul_cancel₀ 1 (by positivity : 2 * Real.pi ≠ 0)
  have hi : Integrable F := weightedRiesz_integrable f X b M hX hb hc hbound
  obtain ⟨hp, hn⟩ := weightedRiesz_both_tails f X b M T hX hM hT hbound
  have he : τ * (∫ t : ℝ, F t) - v = τ *
      ((∫ t in Iic (-T), F t) + ((∫ t in -T..T, F t) - q * v) + (∫ t in Ioi T, F t)) := by
    rw [integral_three_parts F hi T]
    linear_combination (congrArg (fun z : ℂ => z * v) hτ)
  change ‖τ * (∫ t : ℝ, F t) - v‖ ≤ ‖(∫ t in -T..T, F t) - q * v‖ + _
  rw [he, norm_mul]
  apply (mul_le_of_le_one_left (norm_nonneg _) hnorm).trans
  have hh := (norm_add_le ((∫ t in Iic (-T), F t) + ((∫ t in -T..T, F t) - q * v))
    (∫ t in Ioi T, F t)).trans
    (add_le_add (norm_add_le (∫ t in Iic (-T), F t) ((∫ t in -T..T, F t) - q * v)) le_rfl)
  change ‖∫ t in Ioi T, F t‖ ≤ _ at hp
  change ‖∫ t in Iic (-T), F t‖ ≤ _ at hn
  calc
    _ ≤ ‖∫ t in Iic (-T), F t‖ + ‖(∫ t in -T..T, F t) - q * v‖ +
        ‖∫ t in Ioi T, F t‖ := hh
    _ ≤ M * X ^ b / T + ‖(∫ t in -T..T, F t) - q * v‖ + M * X ^ b / T :=
      add_le_add (add_le_add hn le_rfl) hp
    _ = _ := by ring

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_ZeroDensity_RieszExponentialParameters
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Exponential parameter choice for the Riesz contour

The height is `exp y`, the length is `exp (y²)` and the right abscissa is
`1 + 1/y²`.  Fixed polynomial losses are absorbed into a smaller decay rate.
-/

namespace Ostmann

open Filter Asymptotics

theorem riesz_polynomial_absorption (C d : ℝ) (hd : 0 < d) :
    ∀ᶠ y : ℝ in atTop, C * (y ^ 2 + 1) ≤ Real.exp (d * y) := by
  have hp := (isLittleO_pow_exp_pos_mul_atTop 2 hd).const_mul_left C
  have hc := (isLittleO_pow_exp_pos_mul_atTop 0 hd).const_mul_left C
  have hb := (hp.add hc).bound (by norm_num : (0 : ℝ) < 1)
  filter_upwards [hb] with y hy
  have hh := (le_abs_self (C * y ^ 2 + C)).trans (by
    simpa only [pow_zero, mul_one, Real.norm_eq_abs,
      abs_of_pos (Real.exp_pos _), one_mul] using hy)
  nlinarith

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_ZeroDensity_PrincipalRieszIntegral
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The exact starting contour for the principal Riesz mean -/

namespace Ostmann

open Complex MeasureTheory
open scoped BigOperators

noncomputable def principalMangoldtCoefficient (n : ℕ) : ℂ := ArithmeticFunction.vonMangoldt n

theorem principalMangoldt_riesz_term_norm (σ t : ℝ) (n : ℕ) :
    ‖LSeries.term principalMangoldtCoefficient (rieszMellinLine σ t) n‖ =
      ‖LSeries.term principalMangoldtCoefficient (σ : ℂ) n‖ := by
  simp [LSeries.norm_term_eq]

theorem principalMangoldt_riesz_term_continuous (σ : ℝ) (n : ℕ) :
    Continuous (fun t => LSeries.term principalMangoldtCoefficient (rieszMellinLine σ t) n) := by
  by_cases hn : n = 0
  · subst n
    simp only [LSeries.term_zero]
    exact continuous_const
  · simp only [LSeries.term_of_ne_zero hn]
    exact continuous_const.div ((rieszMellinLine_continuous σ).const_cpow
      (.inl (by exact_mod_cast hn))) (fun _ => Complex.cpow_ne_zero_iff.mpr
        (.inl (by exact_mod_cast hn)))

noncomputable def principalRieszMean (X : ℝ) : ℂ :=
  ∑' n : ℕ, principalMangoldtCoefficient n * rieszPrimeTest (n / X)

noncomputable def principalRieszVerticalTerm
    (X σ : ℝ) (n : ℕ) (t : ℝ) : ℂ :=
  LSeries.term (principalMangoldtCoefficient) (rieszMellinLine σ t) n *
    rieszVerticalWeight X σ t

theorem principalRieszVerticalTerm_norm
    (X σ : ℝ) (n : ℕ) (t : ℝ) :
    ‖principalRieszVerticalTerm X σ n t‖ =
      ‖LSeries.term (principalMangoldtCoefficient) (σ : ℂ) n‖ *
        ‖rieszVerticalWeight X σ t‖ := by
  rw [principalRieszVerticalTerm, norm_mul, principalMangoldt_riesz_term_norm]

theorem principalMangoldt_riesz_term_inversion
    (X σ : ℝ) (hX : 0 < X) (hσ : 1 ≤ σ) (n : ℕ) :
    ((1 / (2 * Real.pi) : ℝ) : ℂ) *
      (∫ t : ℝ, principalRieszVerticalTerm X σ n t) =
      principalMangoldtCoefficient n * rieszPrimeTest (n / X) := by
  by_cases hn : n = 0
  · subst n
    simp [principalRieszVerticalTerm, principalMangoldtCoefficient]
  have hnR : 0 < (n : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hn
  have hkernel (t : ℝ) : principalRieszVerticalTerm X σ n t =
      principalMangoldtCoefficient n *
        (((n : ℝ) / X : ℝ) : ℂ) ^ (-rieszMellinLine σ t) *
          rieszMellinKernel (rieszMellinLine σ t) := by
    rw [principalRieszVerticalTerm, LSeries.term_of_ne_zero hn, rieszVerticalWeight,
      Complex.cpow_neg, Complex.ofReal_div,
      Complex.div_cpow_ofReal_nonneg hnR.le hX.le, inv_div]
    push_cast
    ring
  simp_rw [hkernel, mul_assoc]
  rw [integral_const_mul]
  have hinv := rieszPrimeTest_mellin_inversion σ ((n : ℝ) / X) hσ (div_pos hnR hX)
  change ((1 / (2 * Real.pi) : ℝ) : ℂ) * (∫ t : ℝ,
    (((n : ℝ) / X : ℝ) : ℂ) ^ (-rieszMellinLine σ t) *
      rieszMellinKernel (rieszMellinLine σ t)) = _ at hinv
  rw [← hinv]
  ring

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_ZeroDensity_ArithmeticRieszMean
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Literal finite Riesz sums and character orthogonality -/

namespace Ostmann

open Complex
open scoped BigOperators

noncomputable def rieszTwistMean (g : ℕ → ℂ) (X : ℝ) : ℂ :=
  ∑ n ∈ Finset.Ioc 0 ⌊X⌋₊, (ArithmeticFunction.vonMangoldt n : ℂ) * g n * rieszPrimeTest (n / X)

noncomputable def rieszResidueMean (q : ℕ) (a : ZMod q) (X : ℝ) : ℂ :=
  rieszTwistMean (fun n => if (n : ZMod q) = a then 1 else 0) X

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_ZeroDensity_CanonicalThetaSize
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Elementary size of the canonical progression main term -/

namespace Ostmann

open Complex

theorem thetaMainTerm_size (φ χ β X B : ℝ) (hφ : 0 < φ) (hχ : |χ| ≤ 1)
    (hβ : 0 < β) (hβ1 : β ≤ 1) (hX : 1 ≤ X) (_hB : 0 ≤ B) (hinv : β⁻¹ ≤ B) :
    |thetaMainTerm φ χ β X| ≤ (1 + B) * X / φ := by
  have hXp : 0 ≤ X := by linarith
  have hp : 0 ≤ X ^ β := Real.rpow_nonneg hXp _
  have hpow : X ^ β ≤ X := by
    simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le hX hβ1
  have hc : |χ * X ^ β / β| ≤ X * B := by
    rw [abs_div, abs_mul, abs_of_nonneg hp, abs_of_pos hβ, div_eq_mul_inv]
    have h1 : |χ| * X ^ β ≤ X := (mul_le_mul_of_nonneg_right hχ hp).trans (by simpa using hpow)
    exact mul_le_mul h1 hinv (inv_nonneg.mpr hβ.le) hXp
  rw [thetaMainTerm, abs_div, abs_of_pos hφ]
  apply div_le_div_of_nonneg_right _ hφ.le
  have hh := abs_sub X (χ * X ^ β / β)
  rw [abs_of_nonneg hXp] at hh
  nlinarith

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_ZeroDensity_PrimitiveRieszErrorDecay
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The primitive-reduction error is smaller than the Riesz contour error -/

namespace Ostmann

open Filter

theorem primitive_riesz_error_decay_log (d : ℝ) (hd : 0 < d) :
    ∀ᶠ y : ℝ in atTop, ∀ q : ℕ, (q : ℝ) ≤ Real.exp y →
      2 * q * Real.log (Real.exp (y ^ 2)) +
          4 * Real.sqrt (Real.exp (y ^ 2)) * Real.log (Real.exp (y ^ 2)) ≤
        Real.exp (y ^ 2) * Real.exp (-d * y) := by
  filter_upwards [riesz_polynomial_absorption 6 1 (by norm_num),
    eventually_ge_atTop (2 * (d + 1)), eventually_ge_atTop (2 : ℝ)] with y hp hy hy2
  intro q hq
  simp only [one_mul] at hp
  have he : (q : ℝ) ≤ Real.exp (y ^ 2 / 2) := hq.trans
    (Real.exp_le_exp.mpr (by nlinarith))
  have hp' : 6 * y ^ 2 ≤ Real.exp y := by linarith
  have hmul := mul_le_mul_of_nonneg_left hp' (Real.exp_nonneg (y ^ 2 / 2))
  have hqmul := mul_le_mul_of_nonneg_right he (sq_nonneg y)
  rw [Real.log_exp, ← Real.exp_half]
  calc
    _ ≤ Real.exp (y ^ 2 / 2) * (6 * y ^ 2) := by nlinarith
    _ ≤ Real.exp (y ^ 2 / 2) * Real.exp y := hmul
    _ = Real.exp (y ^ 2 / 2 + y) := (Real.exp_add _ _).symm
    _ ≤ Real.exp (y ^ 2 - d * y) := Real.exp_le_exp.mpr (by nlinarith)
    _ = _ := by simp only [Real.exp_sub, neg_mul, Real.exp_neg, div_eq_mul_inv]

theorem primitive_riesz_error_decay (d : ℝ) (hd : 0 < d) :
    ∀ᶠ X : ℝ in atTop, ∀ q : ℕ, (q : ℝ) ≤ Real.exp (Real.sqrt (Real.log X)) →
      2 * q * Real.log X + 4 * Real.sqrt X * Real.log X ≤
        X * Real.exp (-d * Real.sqrt (Real.log X)) := by
  have ht := Real.tendsto_sqrt_atTop.comp Real.tendsto_log_atTop
  filter_upwards [ht.eventually (primitive_riesz_error_decay_log d hd),
    eventually_ge_atTop (1 : ℝ)] with X hX hX1
  intro q hq
  have hx : 0 < X := by linarith
  have heq : Real.exp ((Real.sqrt (Real.log X)) ^ 2) = X := by
    rw [Real.sq_sqrt (Real.log_nonneg hX1), Real.exp_log hx]
  have hh := hX q hq
  dsimp only [Function.comp_apply] at hh
  simpa only [heq] using hh

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_ZeroDensity_PrincipalRieszRectangle
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The principal Riesz rectangle, including zeta's actual pole -/

namespace Ostmann

open Complex Filter Set
open scoped Topology Interval

theorem regularizedZeta_logDeriv_off_one (s : ℂ) (hs : s ≠ 1) (hz : riemannZeta s ≠ 0) :
    logDeriv regularizedZeta s = (s - 1)⁻¹ + logDeriv riemannZeta s := by
  have he : regularizedZeta =ᶠ[𝓝 s] (fun z : ℂ => (z - 1) * riemannZeta z) := by
    filter_upwards [isOpen_ne.mem_nhds hs] with z hz
    exact regularizedZeta_eq z hz
  rw [(logDeriv_congr_nhds he).self_of_nhds,
    logDeriv_mul (f := fun z : ℂ => z - 1) (g := riemannZeta) s
      (sub_ne_zero.mpr hs) hz (differentiableAt_id.sub_const _) (differentiableAt_riemannZeta hs)]
  simp [logDeriv_apply]

noncomputable def principalRieszContour (X : ℝ) (s : ℂ) : ℂ :=
  -logDeriv riemannZeta s * rieszContourWeight X s

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_ZeroDensity_RieszUnsmoothing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Recovering sharp positive counts from the integrated count -/

namespace Ostmann

open scoped BigOperators

noncomputable def finiteRieszSum (S : Finset ℕ) (w : ℕ → ℝ) (x : ℝ) : ℝ :=
  ∑ n ∈ S, w n * max (x - n) 0

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_ZeroDensity_RieszCharacterMainSum
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The exact principal and exceptional terms after character summation -/

namespace Ostmann

open Complex
open scoped BigOperators

theorem principal_character_inverse_value (q : ℕ) (a : ZMod q) (ha : IsUnit a) :
    (1 : DirichletCharacter ℂ q) a⁻¹ = 1 := by
  obtain ⟨u, rfl⟩ := ha
  rw [ZMod.inv_coe_unit]
  exact MulChar.one_apply_coe _

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_ZeroDensity_ResidueRieszFinite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Exact real finite sums underlying the residue-class contour -/

namespace Ostmann

open Complex
open scoped BigOperators

noncomputable def residueMangoldtWeight (q a n : ℕ) : ℝ :=
  if (n : ZMod q) = (a : ZMod q) then ArithmeticFunction.vonMangoldt n else 0

noncomputable def residuePsi (q a : ℕ) (X : ℝ) : ℝ :=
  ∑ n ∈ Finset.Icc 0 ⌊X⌋₊, residueMangoldtWeight q a n

theorem residueMangoldtWeight_nonneg (q a n : ℕ) : 0 ≤ residueMangoldtWeight q a n := by
  unfold residueMangoldtWeight
  split_ifs <;> positivity

@[simp] theorem residueMangoldtWeight_zero (q a : ℕ) : residueMangoldtWeight q a 0 = 0 := by
  simp [residueMangoldtWeight]

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_ZeroDensity_ResidueCountingBound
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # An elementary bound for residue-class Mangoldt sums -/

namespace Ostmann

open scoped BigOperators

theorem residue_index_card_bound (q a N : ℕ) (_hq : 0 < q) :
    ((Finset.Icc 0 N).filter (fun n : ℕ => (n : ZMod q) = (a : ZMod q))).card ≤ N / q + 1 := by
  classical
  let S := (Finset.Icc 0 N).filter (fun n : ℕ => (n : ZMod q) = (a : ZMod q))
  have hinj : Set.InjOn (fun n : ℕ => n / q) S := by
    intro n hn m hm hnm
    have hnmod : n % q = a % q := by
      exact (ZMod.natCast_eq_natCast_iff n a q).mp (Finset.mem_filter.mp hn).2
    have hmmod : m % q = a % q := by
      exact (ZMod.natCast_eq_natCast_iff m a q).mp (Finset.mem_filter.mp hm).2
    have he := Nat.div_add_mod n q
    have he' := Nat.div_add_mod m q
    change n / q = m / q at hnm
    rw [hnm, hnmod] at he
    rw [hmmod] at he'
    omega
  have hsub : S.image (fun n => n / q) ⊆ Finset.range (N / q + 1) := by
    intro k hk
    obtain ⟨n, hn, rfl⟩ := Finset.mem_image.mp hk
    apply Finset.mem_range.mpr
    have hnN := (Finset.mem_Icc.mp (Finset.mem_filter.mp hn).1).2
    exact Nat.lt_succ_of_le (Nat.div_le_div_right hnN)
  calc
    _ = (S.image (fun n => n / q)).card := (Finset.card_image_of_injOn hinj).symm
    _ ≤ (Finset.range (N / q + 1)).card := Finset.card_le_card hsub
    _ = _ := Finset.card_range _

theorem residuePsi_nonneg (q a : ℕ) (X : ℝ) : 0 ≤ residuePsi q a X :=
  Finset.sum_nonneg (fun n _ => residueMangoldtWeight_nonneg q a n)

theorem residuePsi_counting_bound (q a : ℕ) (X : ℝ) (hq : 0 < q) (hX : 1 ≤ X) :
    residuePsi q a X ≤ (X / q + 1) * Real.log X := by
  classical
  let S := (Finset.Icc 0 ⌊X⌋₊).filter (fun n : ℕ => (n : ZMod q) = (a : ZMod q))
  have he : residuePsi q a X = ∑ n ∈ S, ArithmeticFunction.vonMangoldt n := by
    simp only [residuePsi, residueMangoldtWeight, S, Finset.sum_filter]
  have hlog : 0 ≤ Real.log X := Real.log_nonneg hX
  have hb (n : ℕ) (hn : n ∈ S) : ArithmeticFunction.vonMangoldt n ≤ Real.log X := by
    by_cases hn0 : n = 0
    · subst n; simpa using hlog
    have hnX : (n : ℝ) ≤ X := (Nat.le_floor_iff (by linarith : 0 ≤ X)).mp
      (Finset.mem_Icc.mp (Finset.mem_filter.mp hn).1).2
    exact ArithmeticFunction.vonMangoldt_le_log.trans
      (Real.log_le_log (by exact_mod_cast Nat.pos_of_ne_zero hn0) hnX)
  have hcard : (S.card : ℝ) ≤ X / q + 1 := by
    have hc : (S.card : ℝ) ≤ (⌊X⌋₊ / q : ℕ) + 1 := by
      exact_mod_cast residue_index_card_bound q a ⌊X⌋₊ hq
    have hqR : (0 : ℝ) < q := by exact_mod_cast hq
    have hquot : ((⌊X⌋₊ / q : ℕ) : ℝ) ≤ X / q := by
      apply (le_div_iff₀ hqR).mpr
      have hh : (((⌊X⌋₊ / q) * q : ℕ) : ℝ) ≤ (⌊X⌋₊ : ℝ) := by
        exact_mod_cast Nat.div_mul_le_self ⌊X⌋₊ q
      simp only [Nat.cast_mul] at hh
      exact hh.trans (Nat.floor_le (by linarith))
    linarith
  rw [he]
  calc
    _ ≤ ∑ _n ∈ S, Real.log X := Finset.sum_le_sum hb
    _ = (S.card : ℝ) * Real.log X := by simp
    _ ≤ (X / q + 1) * Real.log X := mul_le_mul_of_nonneg_right hcard hlog

end Ostmann

end OAI
end


